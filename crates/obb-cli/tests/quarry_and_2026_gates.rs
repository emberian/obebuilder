//! Planted-fault & end-to-end integration tests for:
//! 1. `obb quarry` (`sync`, `status`, `inspect`, `quarry/obend-quarry.toml`, 6-Gate Surgery Checklist)
//! 2. 2026 Soundness, Crypto-Landmine & Compositional Modularity Gates (`obb-lint`):
//!    - `lean/native-decide-in-proof` (`arXiv:2606.29493`)
//!    - `lean/narrow-digest-weld` (`breadstuffs` 1-limb / <=64-bit digest bug class)
//!    - `lean/uninhabited-premise-risk` (`HypothesisLedger` anti-vacuity tracking)
//!    - `obb lint --modularity` + `lean/monolithic-module` (>4,000-line cap)

use obb_lint::run_repo_lints;
use obb_quarry::{QuarryManifest, QuarryState, inspect_quarry_target, status_quarry, sync_quarry};
use std::collections::BTreeSet;
use std::fs;
use std::path::Path;
use std::process::Command;

fn write_rel(root: &Path, rel: &str, content: &str) {
    let full = root.join(rel);
    if let Some(parent) = full.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    fs::write(full, content).unwrap();
}

fn git_in(repo: &Path, args: &[&str]) -> String {
    let out = Command::new("git")
        .current_dir(repo)
        .args(args)
        .env("GIT_AUTHOR_NAME", "obb-test")
        .env("GIT_AUTHOR_EMAIL", "obb@example.com")
        .env("GIT_COMMITTER_NAME", "obb-test")
        .env("GIT_COMMITTER_EMAIL", "obb@example.com")
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "git {:?} failed in {}: {}",
        args,
        repo.display(),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).trim().to_string()
}

#[test]
fn rule_native_decide_in_proof_catches_library_bypasses_and_allows_tests_and_syntax_quotes() {
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();

    // 1. Unaudited `native_decide` in library theorem -> MUST FAIL
    write_rel(
        root,
        "lean/Obend/Crypto/BadNative.lean",
        r#"
namespace Obend.Crypto

def checkTag (x : Nat) : Bool := x == 0

theorem checkTag_zero_holds (x : Nat) (h : x = 0) : checkTag x = true := by
  subst h
  native_decide

end Obend.Crypto
"#,
    );

    // 2. Raw `Lean.ofReduceBool` bypass -> MUST FAIL even if `#assert_compiled` is present
    write_rel(
        root,
        "lean/Obend/Crypto/BadReduceBool.lean",
        r#"
namespace Obend.Crypto

theorem forged_bool_claim : true = true :=
  Lean.ofReduceBool true true rfl

#assert_compiled forged_bool_claim

end Obend.Crypto
"#,
    );

    // 3. Allowed sites: `tests/` smoke file, syntax-quoted metaprogram in `Elab/`, and `#assert_compiled` KAT
    write_rel(
        root,
        "lean/tests/SmokeNativeTest.lean",
        r#"
theorem smoke_kat : (2 + 2 == 4) = true := by
  native_decide
"#,
    );

    write_rel(
        root,
        "lean/Obend/Elab/QuoteGen.lean",
        r#"
namespace Obend.Elab

def mkNativeDecideStx : Lean.MacroM ( Lean.TSyntax `tactic ) := do
  `(by native_decide)

end Obend.Elab
"#,
    );

    write_rel(
        root,
        "lean/Obend/Core/AuditedKat.lean",
        r#"
namespace Obend.Core

theorem kat_digest_pin : (1 + 1 == 2) = true := by
  native_decide

#assert_compiled kat_digest_pin

end Obend.Core
"#,
    );

    let report = run_repo_lints(root).unwrap();
    let nd_findings: Vec<_> = report
        .findings
        .iter()
        .filter(|f| f.rule_id == "lean/native-decide-in-proof")
        .collect();

    assert_eq!(
        nd_findings.len(),
        2,
        "expected exactly 2 `lean/native-decide-in-proof` errors, got: {nd_findings:#?}"
    );
    let flagged_paths: BTreeSet<&str> = nd_findings.iter().map(|f| f.path.as_str()).collect();
    assert!(flagged_paths.contains("lean/Obend/Crypto/BadNative.lean"));
    assert!(flagged_paths.contains("lean/Obend/Crypto/BadReduceBool.lean"));
}

#[test]
fn rule_narrow_digest_weld_catches_all_1_limb_and_narrow_field_patterns_with_zero_false_positives()
{
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();

    // Planted narrow digest alias, narrow struct field, `[0]` weld, `.get! 0` weld, and `(m.newRoot 0)` weld
    write_rel(
        root,
        "lean/Obend/Vault/BadDigestWelds.lean",
        r#"
namespace Obend.Vault

abbrev CommitRoot := UInt64

structure BatchHeader where
  epoch      : Nat
  stateRoot  : UInt32
  merkleRoot : BitVec 64

def verifyIndexWeld (digest expectedDigest : Array UInt64) : Bool :=
  digest[0] == expectedDigest[0]

def verifyGetBangWeld (certDigest : Array UInt64) (limb0 : UInt64) : Bool :=
  certDigest.get! 0 == limb0

structure MapStep where
  root    : Nat → Nat
  newRoot : Nat → Nat

def holdsLaneZeroOnly (m : MapStep) : Prop :=
  (m.newRoot 0) = (m.root 0)

end Obend.Vault
"#,
    );

    // Clean full-width 256-bit / multi-limb / width-suffixed hardware tags -> MUST PRODUCE 0 FINDINGS
    write_rel(
        root,
        "lean/Obend/Vault/CleanDigest.lean",
        r#"
namespace Obend.Vault

structure CleanHeader where
  stateRoot      : ByteArray
  wordSchedule   : Array UInt32
  envPinDigest64 : UInt64

def eqAllFourLimbs (digest expectedDigest : Array UInt64) : Bool :=
  digest[0] == expectedDigest[0] &&
  digest[1] == expectedDigest[1] &&
  digest[2] == expectedDigest[2] &&
  digest[3] == expectedDigest[3]

end Obend.Vault
"#,
    );

    let report = run_repo_lints(root).unwrap();
    let weld_findings: Vec<_> = report
        .findings
        .iter()
        .filter(|f| f.rule_id == "lean/narrow-digest-weld")
        .collect();

    assert_eq!(
        weld_findings.len(),
        6,
        "expected all 6 planted narrow-digest welds (1 alias + 2 fields + 3 1-limb comparisons) to fire, got: {weld_findings:#?}"
    );
    assert!(
        weld_findings
            .iter()
            .all(|f| f.path == "lean/Obend/Vault/BadDigestWelds.lean"),
        "CleanDigest.lean must have zero false positives: {weld_findings:#?}"
    );
}

#[test]
fn rule_uninhabited_premise_risk_catches_unwitnessed_soundness_and_clears_witnessed_modules() {
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();

    // 1. Vacuous soundness module: `checkAlwaysRefuses` is never shown satisfiable, and `UninhabitedInv` has no witness
    write_rel(
        root,
        "lean/Obend/Judge/VacuousSound.lean",
        r#"
namespace Obend.Judge

inductive Verdict where
  | ok
  | refused (msg : String)

def checkAlwaysRefuses (x : Nat) : Verdict :=
  .refused "not implemented"

theorem checkAlwaysRefuses_sound (x : Nat) (h : checkAlwaysRefuses x = .ok) : x > 100 := by
  cases h

inductive ImpossibleEnvelope : Nat → Prop where

theorem envelope_sound (x : Nat) (h : ImpossibleEnvelope x) : x = 42 := by
  cases h

end Obend.Judge
"#,
    );

    // 2. Properly witnessed soundness module: companion `_complete` theorem proves `.ok` is inhabited
    write_rel(
        root,
        "lean/Obend/Judge/WitnessedSound.lean",
        r#"
namespace Obend.Judge

inductive Verdict2 where
  | ok
  | refused

def checkThreshold (x : Nat) : Verdict2 :=
  if x >= 10 then .ok else .refused

theorem checkThreshold_sound (x : Nat) (h : checkThreshold x = .ok) : x >= 10 := by
  unfold checkThreshold at h
  split at h
  · assumption
  · cases h

theorem checkThreshold_complete (x : Nat) (hx : x >= 10) : checkThreshold x = .ok := by
  unfold checkThreshold
  simp [hx]

end Obend.Judge
"#,
    );

    let report = run_repo_lints(root).unwrap();
    let prem_findings: Vec<_> = report
        .findings
        .iter()
        .filter(|f| f.rule_id == "lean/uninhabited-premise-risk")
        .collect();

    assert_eq!(
        prem_findings.len(),
        2,
        "expected 2 uninhabited-premise warnings in VacuousSound.lean and 0 in WitnessedSound.lean, got: {prem_findings:#?}"
    );
    assert!(
        prem_findings
            .iter()
            .all(|f| f.path == "lean/Obend/Judge/VacuousSound.lean")
    );
}

#[test]
fn modularity_index_and_monolithic_module_detector_measure_compositionality_and_4000_line_cap() {
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();

    write_rel(
        root,
        "lean/Obend/Ledger/Algebra.lean",
        r#"
namespace Obend.Ledger

class Conserved (α : Type) where
  measure : α → Int

structure LedgerState where
  bal : Int

instance : Conserved LedgerState where
  measure s := s.bal

theorem helper_refl (s : LedgerState) : s.bal = s.bal := rfl

theorem composed_conservation (s : LedgerState) : s.bal = s.bal :=
  helper_refl s

end Obend.Ledger
"#,
    );

    // Build a >4,000-line monolithic `.lean` module (4,015 lines) and a 2,000-line non-monolithic module
    let mut mid_src = String::from("namespace Obend.Mid\n\ndef midId (n : Nat) : Nat := n\n");
    for i in 0..1995 {
        mid_src.push_str(&format!("-- padding line {i}\n"));
    }
    mid_src.push_str("end Obend.Mid\n");
    write_rel(root, "lean/Obend/Mid/Medium.lean", &mid_src);

    let mut big_src = String::from("namespace Obend.Monolith\n\ndef stepId (n : Nat) : Nat := n\n");
    for i in 0..4010 {
        big_src.push_str(&format!("-- padding line {i}\n"));
    }
    big_src.push_str(
        "theorem isolated_leaf_claim (n : Nat) : stepId n = n := rfl\nend Obend.Monolith\n",
    );
    write_rel(root, "lean/Obend/Monolith/Giant.lean", &big_src);

    let report = run_repo_lints(root).unwrap();
    assert!(
        !report
            .findings
            .iter()
            .any(|f| f.rule_id == "lean/monolithic-module"
                && f.path == "lean/Obend/Mid/Medium.lean"),
        "2,000-line Medium.lean should NOT trigger `lean/monolithic-module` under 4,000-line threshold"
    );
    assert!(
        report
            .findings
            .iter()
            .any(|f| f.rule_id == "lean/monolithic-module"
                && f.path == "lean/Obend/Monolith/Giant.lean"),
        "expected `lean/monolithic-module` warning on >4,000-line Giant.lean"
    );

    let m = &report.modularity;
    assert_eq!(m.lean_files, 3);
    assert_eq!(m.structures, 1);
    assert_eq!(m.classes, 1);
    assert_eq!(m.instances, 1);
    assert_eq!(m.total_theorems, 3);
    assert_eq!(
        m.composed_theorems, 1,
        "helper_refl is reused by composed_conservation"
    );
    assert_eq!(m.isolated_leaf_theorems, 2);
    assert_eq!(m.monolithic_modules.len(), 1);
    assert_eq!(
        m.monolithic_modules[0].path,
        "lean/Obend/Monolith/Giant.lean"
    );
    assert!(m.monolithic_modules[0].lines > 4000);
    assert!((m.carrier_to_leaf_ratio - 1.0).abs() < 1e-6);
}

#[test]
fn quarry_sync_status_and_6_gate_inspect_end_to_end_on_temp_git_repos() {
    let ws = tempfile::tempdir().unwrap();
    let base = ws.path();

    // 1. Create target `obend` git repo with an existing commit, tag, branch, and clean index
    let target_repo = base.join("obend");
    fs::create_dir_all(&target_repo).unwrap();
    git_in(&target_repo, &["init", "-b", "dev"]);
    write_rel(
        &target_repo,
        "lean/Obend/Ledger/Book.lean",
        "namespace Obend.Ledger\ndef okBook : Nat := 1\nend Obend.Ledger\n",
    );
    git_in(&target_repo, &["add", "lean/Obend/Ledger/Book.lean"]);
    git_in(&target_repo, &["commit", "-m", "initial cathedral commit"]);
    let target_head_before = git_in(&target_repo, &["rev-parse", "HEAD"]);
    let index_bytes_before = fs::read(target_repo.join(".git/index")).unwrap();

    // 2. Create donor repos (`breadstuffs` with planted slop + clean GPaco, `minidregg`, `svenvs`, `lean-transport`)
    let bread_repo = base.join("breadstuffs");
    fs::create_dir_all(&bread_repo).unwrap();
    git_in(&bread_repo, &["init", "-b", "main"]);
    write_rel(
        &bread_repo,
        "orb/Crypto.lean",
        r#"
namespace Crypto
axiom forged_hash_collision_free : ∀ (x y : Nat), x = y
def badRootWeld (digest : Array UInt64) : Bool := digest[0] == 0
theorem bad_native (n : Nat) : n = n := by native_decide
end Crypto
"#,
    );
    write_rel(
        &bread_repo,
        "metatheory/Paco/GPaco.lean",
        r#"
namespace Paco
structure MonoRel (α : Type) where
  rel : α → α → Prop
theorem id_mono (r : MonoRel Nat) (x : Nat) : r.rel x x → r.rel x x := fun h => h
end Paco
"#,
    );
    git_in(
        &bread_repo,
        &["add", "orb/Crypto.lean", "metatheory/Paco/GPaco.lean"],
    );
    git_in(&bread_repo, &["commit", "-m", "breadstuffs root"]);
    // Add a donor git tag to prove `--no-tags` prevents tag pollution in `target_repo`!
    git_in(&bread_repo, &["tag", "donor-v0.1"]);
    let bread_sha = git_in(&bread_repo, &["rev-parse", "HEAD"]);

    let minidregg_repo = base.join("minidregg");
    fs::create_dir_all(&minidregg_repo).unwrap();
    git_in(&minidregg_repo, &["init", "-b", "main"]);
    write_rel(
        &minidregg_repo,
        "Kernel/PayLedger.lean",
        "def floorOk (b : Int) : Bool := b >= 0\n",
    );
    git_in(&minidregg_repo, &["add", "Kernel/PayLedger.lean"]);
    git_in(&minidregg_repo, &["commit", "-m", "minidregg root"]);
    let minidregg_sha = git_in(&minidregg_repo, &["rev-parse", "HEAD"]);

    let svenvs_repo = base.join("svenvs");
    fs::create_dir_all(&svenvs_repo).unwrap();
    git_in(&svenvs_repo, &["init", "-b", "main"]);
    write_rel(
        &svenvs_repo,
        "corrigibility/corrigibilityScript.sml",
        "Theorem bad_hol4_thm:\n  T\nProof\n  cheat\nQED\n",
    );
    git_in(
        &svenvs_repo,
        &["add", "corrigibility/corrigibilityScript.sml"],
    );
    git_in(&svenvs_repo, &["commit", "-m", "svenvs root"]);
    let svenvs_sha = git_in(&svenvs_repo, &["rev-parse", "HEAD"]);

    let transport_repo = base.join("lean-transport");
    fs::create_dir_all(&transport_repo).unwrap();
    git_in(&transport_repo, &["init", "-b", "dev"]);
    write_rel(
        &transport_repo,
        "Transport/Walk.lean",
        "def walkDag (n : Nat) : Nat := n\n",
    );
    git_in(&transport_repo, &["add", "Transport/Walk.lean"]);
    git_in(&transport_repo, &["commit", "-m", "transport root"]);
    let transport_sha = git_in(&transport_repo, &["rev-parse", "HEAD"]);

    // 3. Write `quarry.toml` manifest
    let manifest_path = base.join("quarry.toml");
    let manifest_toml = format!(
        r#"
version = 1
target_name = "obend"
default_target_repo = "{target}"

[donors.breadstuffs]
path = "{bread}"
branches = ["main"]

[donors.minidregg]
path = "{mini}"
branches = ["main"]

[donors.svenvs]
path = "{svenvs}"
branches = ["main"]

[donors.lean-transport]
path = "{trans}"
branches = ["dev"]

[[entries]]
id = "mini-ledger"
donor = "minidregg"
source_path = "Kernel/PayLedger.lean"
state = "uptaken"
target_repo = "obend"
destination_path = "lean/Obend/Ledger/Book.lean"
audit_notes = "Floors uptaken cleanly."

[[entries]]
id = "bread-gpaco"
donor = "breadstuffs"
source_path = "metatheory/Paco/GPaco.lean"
state = "queued_for_upgrade"
target_repo = "obend"
destination_path = "lean/Obend/Coinductive/GPaco.lean"
audit_notes = "Parameterized coinduction queued."

[[entries]]
id = "bread-orb-crypto"
donor = "breadstuffs"
source_path = "orb/Crypto.lean"
state = "retired_slop"
target_repo = "obend"
audit_notes = "Retired axiom-heavy crypto module."
"#,
        target = target_repo.display(),
        bread = bread_repo.display(),
        mini = minidregg_repo.display(),
        svenvs = svenvs_repo.display(),
        trans = transport_repo.display(),
    );
    fs::write(&manifest_path, &manifest_toml).unwrap();
    let manifest = QuarryManifest::load_from_path(&manifest_path).unwrap();

    // 4. Dry-run sync: must NOT create `refs/quarry/*` or `FETCH_HEAD`
    let dry_rep = sync_quarry(&manifest, &target_repo, true).unwrap();
    assert!(dry_rep.dry_run);
    assert_eq!(dry_rep.actions.len(), 4);
    assert!(dry_rep.head_unchanged && dry_rep.index_unchanged && dry_rep.worktree_unchanged);
    let quarry_refs_after_dry = git_in(&target_repo, &["for-each-ref", "refs/quarry"]);
    assert!(
        quarry_refs_after_dry.is_empty(),
        "dry-run must not write any refs/quarry/*"
    );

    // 5. Real sync: fetches all 4 donors into `refs/quarry/<donor>/<branch>` without touching HEAD, index, tags, or FETCH_HEAD
    let sync_rep = sync_quarry(&manifest, &target_repo, false).unwrap();
    assert!(!sync_rep.dry_run);
    assert!(sync_rep.head_unchanged && sync_rep.index_unchanged && sync_rep.worktree_unchanged);
    assert_eq!(
        git_in(&target_repo, &["rev-parse", "HEAD"]),
        target_head_before
    );
    assert_eq!(
        fs::read(target_repo.join(".git/index")).unwrap(),
        index_bytes_before
    );
    assert!(
        !target_repo.join(".git/FETCH_HEAD").exists(),
        "`--no-write-fetch-head` must prevent `.git/FETCH_HEAD` creation"
    );
    assert!(
        git_in(&target_repo, &["tag", "-l"]).is_empty(),
        "`--no-tags` must prevent donor tags from polluting target repo"
    );
    assert_eq!(
        git_in(&target_repo, &["rev-parse", "refs/quarry/breadstuffs/main"]),
        bread_sha
    );
    assert_eq!(
        git_in(&target_repo, &["rev-parse", "refs/quarry/minidregg/main"]),
        minidregg_sha
    );
    assert_eq!(
        git_in(&target_repo, &["rev-parse", "refs/quarry/svenvs/main"]),
        svenvs_sha
    );
    assert_eq!(
        git_in(
            &target_repo,
            &["rev-parse", "refs/quarry/lean-transport/dev"]
        ),
        transport_sha
    );

    // 6. Status check: valid manifest passes; broken `uptaken` destination fails!
    let st_ok = status_quarry(&manifest, Some(&target_repo), None).unwrap();
    assert!(
        st_ok.all_uptaken_verified,
        "violations: {:#?}",
        st_ok.uptake_violations
    );
    assert_eq!(st_ok.by_state.get("uptaken"), Some(&1));
    assert_eq!(st_ok.by_state.get("queued_for_upgrade"), Some(&1));
    assert_eq!(st_ok.by_state.get("retired_slop"), Some(&1));

    let mut broken_manifest = manifest.clone();
    broken_manifest.entries[0].destination_path = Some("lean/Obend/MissingDestination.lean".into());
    let st_bad = status_quarry(
        &broken_manifest,
        Some(&target_repo),
        Some(QuarryState::Uptaken),
    )
    .unwrap();
    assert!(!st_bad.all_uptaken_verified);
    assert_eq!(st_bad.uptake_violations.len(), 1);

    // 7. Inspect directly from `refs/quarry/<donor>/*` git blobs (even without `--donor-path`!)
    let bad_inspect = inspect_quarry_target(
        "breadstuffs:orb/Crypto.lean",
        Some(&target_repo),
        None,
        Some(&manifest),
        None,
    )
    .unwrap();
    assert!(
        bad_inspect
            .resolution_source
            .starts_with("git:refs/quarry/breadstuffs/main@"),
        "expected git blob inspection, got {}",
        bad_inspect.resolution_source
    );
    assert!(!bad_inspect.ready_for_uptake);
    let bad_rules: BTreeSet<&str> = bad_inspect
        .findings
        .iter()
        .map(|f| f.rule_id.as_str())
        .collect();
    for must_fire in [
        "quarry/retired-slop-blocked",
        "lean/sorry-or-axiom",
        "lean/narrow-digest-weld",
        "lean/native-decide-in-proof",
    ] {
        assert!(
            bad_rules.contains(must_fire),
            "expected `{must_fire}` in quarry inspect of orb/Crypto.lean, got {bad_rules:?}"
        );
    }

    // HOL4 `cheat` in `svenvs:corrigibility` must also fail Gate 1!
    let hol4_inspect = inspect_quarry_target(
        "svenvs:corrigibility",
        Some(&target_repo),
        None,
        Some(&manifest),
        None,
    )
    .unwrap();
    assert!(!hol4_inspect.ready_for_uptake);
    assert!(
        hol4_inspect
            .findings
            .iter()
            .any(|f| f.rule_id == "hol4/cheat-or-axiom")
    );

    // Clean `breadstuffs:metatheory/Paco/GPaco.lean` passes all 6 gates!
    let clean_inspect = inspect_quarry_target(
        "breadstuffs:metatheory/Paco/GPaco.lean",
        Some(&target_repo),
        None,
        Some(&manifest),
        None,
    )
    .unwrap();
    assert!(
        clean_inspect.ready_for_uptake,
        "clean GPaco module must pass all 6 gates, got: {:#?}",
        clean_inspect.findings
    );
    assert!(clean_inspect.gates.iter().all(|g| g.passed));

    // 8. Exercise compiled `obb` CLI binary on `quarry status` and `lint --modularity --json`
    let obb_bin = env!("CARGO_BIN_EXE_obb");
    let cli_out = Command::new(obb_bin)
        .args([
            "quarry",
            "status",
            "--repo",
            &target_repo.to_string_lossy(),
            "--manifest",
            &manifest_path.to_string_lossy(),
            "--json",
        ])
        .output()
        .unwrap();
    assert!(cli_out.status.success());

    // Also verify shipped `quarry/obend-quarry.toml` parses cleanly and covers all 4 donors
    let shipped_manifest_path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../quarry/obend-quarry.toml");
    let shipped = QuarryManifest::load_from_path(&shipped_manifest_path).unwrap();
    for required_donor in ["breadstuffs", "minidregg", "svenvs", "lean-transport"] {
        assert!(
            shipped.donors.contains_key(required_donor),
            "shipped obend-quarry.toml missing donor `{required_donor}`"
        );
    }
    assert!(
        shipped.entries.len() >= 35,
        "expected comprehensive quarry manifest (>=35 entries), got {}",
        shipped.entries.len()
    );
}
