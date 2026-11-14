//! `obb-v6` (`0.6.0`) end-to-end CLI & library separation tests:
//! 1. `lean/test-in-library` flags `#guard`, `#guard_msgs`, `#tooth`, and `#eval` inside Tier-1
//!    `lean/Obend/` library modules (excluding `lean/Obend/Teeth/`) with `Severity::Error` under `--strict-tests`.
//! 2. Comments (`--`, `/- ... -/`, nested `/- /- ... -/ -/`, `/-- ... -/`), string literals (`"..."`,
//!    `s!"..."`, `r#"..."#`), syntax quotes `` `(...) ``, and BitVec width suffixes `x#eval` are ignored.
//! 3. `lean/Obend/Teeth/FooTeeth.lean` and `lean/tests/FooTest.lean` permit `#guard`, `#tooth`,
//!    `#eval`, and `#guard_msgs` without counting toward `tier1_*` or firing `lean/test-in-library`.
//! 4. Wave-7 compatibility: `--strict --strict-expose --strict-harnesses --strict-vacuity --strict-wire`
//!    exits `0` without emitting `lean/test-in-library` findings, while STILL populating exact
//!    `tier1_guards`, `tier1_teeth`, and `tier1_evals` in both JSON and human summary output.

use std::fs;
use std::path::Path;
use std::process::Command;

fn obb_bin() -> &'static str {
    env!("CARGO_BIN_EXE_obb")
}

fn write_rel(root: &Path, rel: &str, content: &str) {
    let full = root.join(rel);
    if let Some(p) = full.parent() {
        fs::create_dir_all(p).unwrap();
    }
    fs::write(full, content).unwrap();
}

#[test]
fn cli_v6_enforces_3way_proof_test_mutation_separation_and_tracks_tier1_metrics() {
    // Verify crate version matches workspace Cargo.toml (`0.7.0`)
    let ver_out = Command::new(obb_bin())
        .arg("--version")
        .output()
        .expect("obb --version");
    assert!(ver_out.status.success());
    let ver_str = String::from_utf8_lossy(&ver_out.stdout);
    let expected_ver = format!("obb {}", env!("CARGO_PKG_VERSION"));
    assert!(
        ver_str.trim() == expected_ver,
        "expected `{expected_ver}`, got `{}`",
        ver_str.trim()
    );

    let repo = tempfile::tempdir().unwrap();

    // 1. Tier-1 library module `lean/Obend/Foo.lean`
    write_rel(
        repo.path(),
        "lean/Obend/Foo.lean",
        r###"module
public section
namespace Obend.Foo

-- Line comment: #guard true #tooth t #eval 1 #guard_msgs
/- Outer block comment
   #guard true
   /- Nested block comment: #tooth inner_t #eval 2 -/
   #guard_msgs in #eval 3
-/

/-- Docstring referencing `#guard`, `#tooth`, `#eval`, `#guard_msgs`. -/
def docConst : String := "#guard #tooth #eval #guard_msgs"
def interpConst (k : Nat) : String := m!"msg {k}: #guard #tooth #eval #guard_msgs"
def rawConst : String := r#"raw "quoted" #guard #tooth #eval #guard_msgs"#

def addTwo (n : Nat) : Nat := n + 2

theorem addTwo_ge (n : Nat) : addTwo n >= n := by
  unfold addTwo
  omega

#guard addTwo 3 == 5

#tooth addTwo_ge by mutation addTwo := fun n => n - 1

/-- info: 9 -/
#guard_msgs in
#eval addTwo 7

end Obend.Foo
"###,
    );

    // 2. Permitted Tier-2 mutation module `lean/Obend/Teeth/FooTeeth.lean`
    write_rel(
        repo.path(),
        "lean/Obend/Teeth/FooTeeth.lean",
        r#"module
import Obend.Foo
namespace Obend.Teeth

#tooth Obend.Foo.addTwo_ge by mutation Obend.Foo.addTwo := fun n => n - 1
#guard Obend.Foo.addTwo 10 == 12
#guard_msgs in #eval Obend.Foo.addTwo 1

end Obend.Teeth
"#,
    );

    // 3. Permitted compiled test module `lean/tests/FooTest.lean`
    write_rel(
        repo.path(),
        "lean/tests/FooTest.lean",
        r#"import Obend.Foo

#guard Obend.Foo.addTwo 20 == 22
#tooth Obend.Foo.addTwo_ge by mutation Obend.Foo.addTwo := fun n => n - 1
#guard_msgs in
#eval Obend.Foo.addTwo 0
"#,
    );

    // A. Wave-7 strict flags WITHOUT `--strict-tests`: must exit 0 with 0 errors/findings,
    //    while still reporting exact `tier1_guards=2`, `tier1_teeth=1`, `tier1_evals=1`!
    let wave7_out = Command::new(obb_bin())
        .args([
            "lint",
            "--repo",
            repo.path().to_str().unwrap(),
            "--strict",
            "--strict-expose",
            "--strict-harnesses",
            "--strict-vacuity",
            "--strict-wire",
            "--json",
        ])
        .output()
        .expect("run wave7 obb lint");
    assert!(
        wave7_out.status.success(),
        "Wave-7 gate without --strict-tests must exit 0: {}",
        String::from_utf8_lossy(&wave7_out.stdout)
    );
    let wave7_json: serde_json::Value = serde_json::from_slice(&wave7_out.stdout).unwrap();
    assert_eq!(wave7_json["errors"], 0);
    assert_eq!(wave7_json["total_findings"], 0);
    assert_eq!(wave7_json["tier1_guards"], 2);
    assert_eq!(wave7_json["tier1_teeth"], 1);
    assert_eq!(wave7_json["tier1_evals"], 1);

    // Check human summary output also includes `tier1_guards=2 tier1_teeth=1 tier1_evals=1` when `--strict-tests` is off
    let human_out = Command::new(obb_bin())
        .args(["lint", "--repo", repo.path().to_str().unwrap()])
        .output()
        .expect("run human obb lint");
    assert!(human_out.status.success());
    let human_stdout = String::from_utf8_lossy(&human_out.stdout);
    assert!(
        human_stdout.contains("tier1_guards=2")
            && human_stdout.contains("tier1_teeth=1")
            && human_stdout.contains("tier1_evals=1"),
        "human summary must report tier1 counts: {human_stdout}"
    );

    // B. Wave C1 gate WITH `--strict --strict-tests`: exits 2 and flags all 4 commands in `lean/Obend/Foo.lean`!
    let c1_out = Command::new(obb_bin())
        .args([
            "lint",
            "--repo",
            repo.path().to_str().unwrap(),
            "--strict",
            "--strict-tests",
            "--json",
        ])
        .output()
        .expect("run obb lint --strict --strict-tests");
    assert_eq!(c1_out.status.code(), Some(2));
    let c1_json: serde_json::Value = serde_json::from_slice(&c1_out.stdout).unwrap();
    assert_eq!(c1_json["errors"], 4);
    assert_eq!(c1_json["by_rule"]["lean/test-in-library"], 4);
    assert_eq!(c1_json["tier1_guards"], 2);
    assert_eq!(c1_json["tier1_teeth"], 1);
    assert_eq!(c1_json["tier1_evals"], 1);

    let findings = c1_json["findings"].as_array().unwrap();
    assert_eq!(findings.len(), 4);
    for f in findings {
        assert_eq!(f["rule_id"], "lean/test-in-library");
        assert_eq!(f["severity"], "error");
        assert_eq!(f["path"], "lean/Obend/Foo.lean");
    }

    let symbols: Vec<&str> = findings
        .iter()
        .map(|f| f["symbol"].as_str().unwrap())
        .collect();
    assert_eq!(symbols, vec!["#guard", "#tooth", "#guard_msgs", "#eval"]);
}
