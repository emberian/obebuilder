//! `obb-v5` end-to-end CLI & broker integration tests:
//! 1. `lean/judge-fragment-restates-check` (`SameOpening.lean:782` pattern vs semantic `Fragment`)
//! 2. `lean/pigeonhole-vacuous-premise` (`ModuleSISHard`, `¬ BoundedCollision` > 32B, `∨ CshakeCollision` vs `PSum` & `MSISGame`)
//! 3. `cross-lang/domain-tag-drift` (shared tag framing-arity mismatch & orphaned Rust `/v1` / `_V1` wire tags)
//! 4. `M3` gate compatibility (`--strict --strict-expose --strict-harnesses` exits `0` on warnings, while `--strict-vacuity` and `--strict-wire` exit `2`)
//! 5. `obb-broker` resilient `hbox` / `bb2` `BASE_REPO` auto-detection and writable `SEED_POOL` fallback.

pub mod support;
use support::MockSshExecutor;

use obb_broker::{BuildPlanOptions, HostChoice, plan_build};
use std::fs;
use std::os::unix::fs::PermissionsExt;
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
fn cli_v5_rules_catch_vacuity_and_wire_drift_while_preserving_m3_strict_gate() {
    let repo = tempfile::tempdir().unwrap();

    // 1. Lean module with `SameOpening` tautological `Fragment` + compressing `ModuleSISHard` + `¬ BoundedCollision _ 65`
    write_rel(
        repo.path(),
        "lean/Obend/Crypto/SameOpeningAndSis.lean",
        r#"module
public section
namespace Obend.Crypto

def ModuleSISHard (pp : AjtaiParams) (B : Nat) : Prop :=
  Unbroken (.moduleSISShortVec pp.modulus B pp.matrix)

theorem dual_binding_vacuous (pp : AjtaiParams) (H : Hash32) (x y : Witness)
    (hOr : ¬ BoundedCollision H.eval 65 ∨ ModuleSISHard pp 131070)
    (hEq : commit pp H x = commit pp H y) :
    x = y := by
  exact vacuous_step hOr hEq

instance privateConvexSameOpeningJudge :
    Obend.Judge SameOpeningInstance SameOpeningWitness where
  Clause := SameOpeningRefusal
  Meaning := SameOpeningMeaning
  check _ q c := verifySameOpening q c
  sound {_ _ _} h := verifySameOpening_sound h
  refutes := sameOpeningRefutes
  refuted {_ _ _ _ _} h hr c' hm := verifySameOpening_refuted h hr c' hm
  Fragment q := ∃ c, verifySameOpening q c = .ok
  complete {q} ⟨c, hc⟩ _ := ⟨c, 0, hc⟩
  mono _ _ := rfl

end Obend.Crypto
"#,
    );

    // 2. Clean Lean module with genuine `Fragment`, `PSum` extractor, and shared `"OBEND.CUSTODY.AUTHORITY/v1"` (5 fields)
    write_rel(
        repo.path(),
        "lean/Obend/Polis/GrainPowerbox.lean",
        r#"module
public section
namespace Obend.Polis

def authorityRoot (a b c d e : List UInt8) : ByteArray :=
  hash "OBEND.CUSTODY.AUTHORITY/v1" [a, b, c, d, e]

def extractOpeningOrCollision (a b : List UInt8)
    (hEq : digest a = digest b) :
    PSum (a = b) (HashCollisionWitness cshakeHasher 64) :=
  extractImpl a b hEq

instance cleanSemanticJudge : Obend.Judge DomainObj DomainCert where
  Clause := String
  Meaning := DomainMeaning
  check _ o c := verifyDomain o c
  sound {_ _ _} h := verifyDomain_sound h
  refutes _ := true
  refuted {_ _ _ _ _} h hr c' hm := verifyDomain_refuted h hr c' hm
  Fragment := DomainObj.WellFormed
  complete {o} hWf hMean := buildDomainCert o hWf hMean
  mono _ _ := rfl

end Obend.Polis
"#,
    );

    // 3. Rust sandbox crate with framing mismatch (3 vs 5 fields on `"OBEND.CUSTODY.AUTHORITY/v1"`) + orphaned `"OBEND_AMEND_ROOT_V1"`
    write_rel(
        repo.path(),
        "crates/obend-sandbox/src/cloud_custody.rs",
        r#"
pub fn authority_root(a: Vec<u8>, b: Vec<u8>, c: Vec<u8>) -> [u8; 32] {
    hash("OBEND.CUSTODY.AUTHORITY/v1", &[a, b, c])
}

pub fn amend_root(payload: &[u8]) -> [u8; 32] {
    cshake("OBEND_AMEND_ROOT_V1", payload)
}
"#,
    );

    // A. Default M3 gate (`--strict --strict-expose --strict-harnesses`): exits 0 while reporting all v5 warnings!
    let m3_out = Command::new(obb_bin())
        .args([
            "lint",
            "--repo",
            repo.path().to_str().unwrap(),
            "--strict",
            "--strict-expose",
            "--strict-harnesses",
            "--json",
        ])
        .output()
        .expect("run obb lint m3 gate");
    assert!(
        m3_out.status.success(),
        "M3 default strict gate must exit 0 when only v5 warnings fire: {}",
        String::from_utf8_lossy(&m3_out.stdout)
    );
    let m3_json: serde_json::Value = serde_json::from_slice(&m3_out.stdout).unwrap();
    assert_eq!(m3_json["errors"], 0);
    assert_eq!(m3_json["by_rule"]["lean/judge-fragment-restates-check"], 1);
    assert_eq!(m3_json["by_rule"]["lean/pigeonhole-vacuous-premise"], 2);
    assert_eq!(m3_json["by_rule"]["cross-lang/domain-tag-drift"], 2);

    // B. `--strict --strict-vacuity`: escalates vacuity & fragment rules to Error -> exits 2!
    let vac_out = Command::new(obb_bin())
        .args([
            "lint",
            "--repo",
            repo.path().to_str().unwrap(),
            "--strict",
            "--strict-vacuity",
            "--json",
        ])
        .output()
        .expect("run obb lint --strict-vacuity");
    assert_eq!(vac_out.status.code(), Some(2));
    let vac_json: serde_json::Value = serde_json::from_slice(&vac_out.stdout).unwrap();
    assert_eq!(vac_json["errors"], 3);

    // C. `--strict --strict-wire`: escalates cross-lang wire drift to Error -> exits 2!
    let wire_out = Command::new(obb_bin())
        .args([
            "lint",
            "--repo",
            repo.path().to_str().unwrap(),
            "--strict",
            "--strict-wire",
            "--json",
        ])
        .output()
        .expect("run obb lint --strict-wire");
    assert_eq!(wire_out.status.code(), Some(2));
    let wire_json: serde_json::Value = serde_json::from_slice(&wire_out.stdout).unwrap();
    assert_eq!(wire_json["errors"], 2);
}

#[test]
fn broker_hbox_recipe_falls_back_when_default_seed_pool_unwritable_and_autodetects_home_repo() {
    let sandbox = tempfile::tempdir().unwrap();
    let fake_home = sandbox.path().join("home_hbox");
    let home_repo = fake_home.join("obend/repo");
    let work_root = sandbox.path().join("worktrees");
    let fake_bin = sandbox.path().join("bin");
    let unwritable_parent = sandbox.path().join("ro_othersys");

    fs::create_dir_all(home_repo.join("lean/Obend")).unwrap();
    fs::create_dir_all(&work_root).unwrap();
    fs::create_dir_all(&fake_bin).unwrap();
    fs::create_dir_all(&unwritable_parent).unwrap();
    // Make `ro_othersys` read-only (`0o555`) to simulate `/othersys` owned by `root:root` on `hbox`
    fs::set_permissions(&unwritable_parent, fs::Permissions::from_mode(0o555)).unwrap();

    // Initialize a real git repo at `$HOME/obend/repo` without setting `OBB_BASE_REPO`
    for args in [
        vec!["init"],
        vec!["config", "user.email", "test@obend.local"],
        vec!["config", "user.name", "Test"],
    ] {
        assert!(
            Command::new("git")
                .args(&args)
                .current_dir(&home_repo)
                .output()
                .unwrap()
                .status
                .success()
        );
    }
    fs::write(home_repo.join("lean/Obend/GpuCheck.lean"), "-- hbox ok\n").unwrap();
    assert!(
        Command::new("git")
            .args(["add", "."])
            .current_dir(&home_repo)
            .output()
            .unwrap()
            .status
            .success()
    );
    assert!(
        Command::new("git")
            .args(["commit", "-m", "init"])
            .current_dir(&home_repo)
            .output()
            .unwrap()
            .status
            .success()
    );

    let fake_lake = fake_bin.join("lake");
    fs::write(
        &fake_lake,
        "#!/usr/bin/env bash\nset -euo pipefail\ntest -f Obend/GpuCheck.lean\nmkdir -p .lake/build/lib\necho ok > .lake/build/lib/GpuCheck.olean\n",
    )
    .unwrap();
    fs::set_permissions(&fake_lake, fs::Permissions::from_mode(0o755)).unwrap();

    let mock = MockSshExecutor::new();
    let unwritable_seed = unwritable_parent.join("obb-seeds/obend");
    let plan = plan_build(
        &["Obend.GpuCheck".to_string()],
        &BuildPlanOptions {
            host_choice: HostChoice::Hbox,
            timeout_secs: 30,
            max_rss_gb: 8,
            dry_run: true,
            exec: false,
            repo_root: Some(home_repo.clone()),
            target_commit: None,
            remote_seed_root: Some(unwritable_seed.to_string_lossy().to_string()),
        },
        &mock,
    )
    .unwrap();

    let orig_path = std::env::var("PATH").unwrap_or_default();
    let test_path = format!("{}:{orig_path}", fake_bin.display());
    let out = Command::new("bash")
        .arg("-c")
        .arg(&plan.batches[0].remote_recipe)
        .env("HOME", &fake_home)
        .env("PATH", &test_path)
        .env("OBB_WORK_ROOT", &work_root)
        .env_remove("OBB_BASE_REPO")
        .output()
        .unwrap();

    // Restore permissions before assertions so tempdir cleanup always succeeds
    let _ = fs::set_permissions(&unwritable_parent, fs::Permissions::from_mode(0o755));

    assert!(
        out.status.success(),
        "hbox fallback recipe failed: stdout={}\nstderr={}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        fake_home.join("obend/obb-seeds/latest").exists() || Path::new("/othersys/lanes").exists(),
        "writable fallback seed pool must be populated cleanly"
    );
}

#[test]
fn stage2_fable_hardening_catches_bypasses_and_eliminates_false_positives() {
    let repo = tempfile::tempdir().unwrap();

    // 1. Adversarial bypass attempts that MUST be caught:
    // - `SilverWorkflow.toJudge` bound-variable checker (`w.verify`)
    // - `{ baseJudge with Fragment := ... (.isOk) }` struct-update + `.isOk`
    // - `(hRows : pp.rows > 0)` NOT silencing `ModuleSISHard`
    // - `variable (hSec : ModuleSISHard pp 999)` section variable
    // - `instance` with `assumptions := .hashCollision256 H maxBytes`
    // - `v1 = v2 ∨ (BoundedCollision treeHash verkleMaxPreimageBytes ∧ ¬ ModuleSISHard pp 131070)`
    write_rel(
        repo.path(),
        "lean/Obend/Crypto/AdversarialBypasses.lean",
        r#"module
public section
namespace Obend.Crypto

variable (hSecVar : ModuleSISHard globalPp 999)

def SilverWorkflow.toJudge (w : SilverWorkflow Q C) : Obend.Judge Q C where
  Clause := String
  Meaning := w.Spec
  check _ q c := w.verify q c
  sound h := w.sound h
  refutes _ := true
  refuted h hr c' hm := w.refuted h hr c' hm
  Fragment q := ∃ c, w.verify q c = .ok
  complete ⟨c, hc⟩ _ := ⟨c, 0, hc⟩
  mono _ _ := rfl

def cleanBaseJudge : Obend.Judge DomQ DomC where
  Clause := String
  Meaning := DomMeaning
  check _ q c := verifyDom q c
  sound h := verifyDom_sound h
  refutes _ := true
  refuted h hr c' hm := verifyDom_refuted h hr c' hm
  Fragment := DomWellFormed
  complete hWf hM := buildDom hWf hM
  mono _ _ := rfl

def bypassedStructUpdateJudge : Obend.Judge DomQ DomC :=
  { cleanBaseJudge with Fragment := fun q => ∃ c, (verifyDom q c).isOk }

theorem fake_rows_pos_guard (pp : AjtaiParams) (x y : Wit)
    (hRows : pp.rows > 0)
    (hSIS : ModuleSISHard pp 131070)
    (hEq : ajtaiCommit pp x = ajtaiCommit pp y) :
    x = y := by
  exact sis_step hRows hSIS hEq

instance badCompJudge (H : Hash) (maxBytes : Nat) : ComputationalJudge Stmt Cert where
  Clause := String
  Meaning := StmtMeaning
  Witness := StmtWit
  witnessSound w := w.sound
  assumptions := .hashCollision256 H maxBytes
  soundnessErr := (1, 2)
  den_pos := by decide
  verify _ s c := verifyStmt s c
  mono _ _ := rfl
  RewindBundle _ _ := Unit
  rewindValid _ _ _ _ := True
  extractOrBreak _ h _ := extractImpl h

theorem verkle_snapshot_disjunction_vacuous (v1 v2 : Val) (pp : AjtaiParams) :
    v1 = v2 ∨ (BoundedCollision treeHash verkleMaxPreimageBytes ∧ ¬ ModuleSISHard pp 131070) := by
  exact verkle_step v1 v2 pp

end Obend.Crypto
"#,
    );

    // 2. Clean patterns that MUST produce ZERO false positives:
    // - `Genealogy.lean`-style `wellFormed o.1 = .ok ()` (`Fragment` without `∃` calling domain checker != `succeed`)
    // - `∃ hdr, parseHeader q.raw = .ok hdr` (`Except.ok` domain parser where `hdr` is output, not cert input)
    // - `check` guarding on `if decide (WellFormed q) then ...` with `Fragment := WellFormed`
    // - Reversed `31 ≥ maxBytes` and parenthesized `BoundedCollision (H.eval) (16)`
    // - Relational `pp.cols ≤ pp.rows`
    write_rel(
        repo.path(),
        "lean/Obend/Crypto/HonestEdgeCases.lean",
        r#"module
public section
namespace Obend.Crypto

def InputWellFormed (q : Query) : Prop := q.bytes.size ≤ 1024

instance successionStyleJudge : Obend.Judge (Lineage × Lineage) CertPair where
  Clause := String
  Meaning o := ValidSuccession o.1 o.2
  check _ o c := succeed o.1 o.2 c.1 c.2
  sound h := succeed_sound h
  refutes _ := true
  refuted h hr c' hm := succeed_refuted h hr c' hm
  Fragment o := wellFormed o.1 = .ok () ∧ wellFormed o.2 = .ok ()
  complete hWf hM := buildSuccession hWf hM
  mono _ _ := rfl

instance headerDomainJudge : Obend.Judge RawPacket PacketCert where
  Clause := String
  Meaning p := PacketValid p
  check _ p c := if decide (InputWellFormed p.toQuery) then verifyPacket p c else .uncovered
  sound h := packet_sound h
  refutes _ := true
  refuted h hr c' hm := packet_refuted h hr c' hm
  Fragment p := InputWellFormed p.toQuery ∧ ∃ hdr, parseHeader p.raw = .ok hdr
  complete hWf hM := buildPacket hWf hM
  mono _ _ := rfl

theorem reversed_bound_honest (H : Hash32) (maxBytes : Nat)
    (hMax : 31 ≥ maxBytes) :
    ¬ BoundedCollision (H.eval) maxBytes := by
  exact inj_bound H maxBytes hMax

theorem small_paren_bound_honest (H : Hash32) :
    ¬ BoundedCollision (H.eval) (16) := by
  exact inj_16 H

theorem relational_non_compressing_sis (pp : AjtaiParams) (x y : Wit)
    (hRel : pp.cols ≤ pp.rows)
    (hSIS : ModuleSISHard pp 131070)
    (hEq : ajtaiCommit pp x = ajtaiCommit pp y) :
    x = y := by
  exact rel_inj hRel hSIS hEq

end Obend.Crypto
"#,
    );

    // 3. Non-crypto `Hardware/PlaceRoute.lean` with `checkPairNoCollision = true` and spatial `NoCollision`
    write_rel(
        repo.path(),
        "lean/Obend/Hardware/PlaceRoute.lean",
        r#"module
public section
namespace Obend.Hardware

def checkPairNoCollision (c1 c2 : PlacedCell) : Bool :=
  c1.x != c2.x || c1.y != c2.y

def NoCollision (cells : List PlacedCell) : Prop :=
  ∀ a b, a ≠ b → (a.x, a.y) ≠ (b.x, b.y)

theorem placement_injective_no_collision (c1 c2 : PlacedCell)
    (hOk : checkPairNoCollision c1 c2 = true) :
    (c1.x, c1.y) ≠ (c2.x, c2.y) := by
  exact place_sound c1 c2 hOk

end Obend.Hardware
"#,
    );

    let out = Command::new(obb_bin())
        .args(["lint", "--repo", repo.path().to_str().unwrap(), "--json"])
        .output()
        .expect("run obb lint");
    let json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    let findings = json["findings"].as_array().unwrap();

    let frag_hits: Vec<_> = findings
        .iter()
        .filter(|f| f["rule_id"] == "lean/judge-fragment-restates-check")
        .collect();
    assert_eq!(
        frag_hits.len(),
        2,
        "SilverWorkflow.toJudge + bypassedStructUpdateJudge must fire with 0 false positives on HonestEdgeCases: {frag_hits:#?}"
    );
    assert!(frag_hits.iter().all(|f| {
        f["path"]
            .as_str()
            .unwrap()
            .ends_with("AdversarialBypasses.lean")
    }));

    let vac_hits: Vec<_> = findings
        .iter()
        .filter(|f| f["rule_id"] == "lean/pigeonhole-vacuous-premise")
        .collect();
    assert_eq!(
        vac_hits.len(),
        4,
        "hSecVar + fake_rows_pos_guard + badCompJudge + verkle_snapshot_disjunction_vacuous must fire with 0 false positives on HonestEdgeCases or PlaceRoute: {vac_hits:#?}"
    );
    assert!(vac_hits.iter().all(|f| {
        f["path"]
            .as_str()
            .unwrap()
            .ends_with("AdversarialBypasses.lean")
    }));
}

#[test]
fn broker_rejects_malicious_targets_and_unsafe_seed_paths() {
    let mock = MockSshExecutor::new();
    let base_opts = BuildPlanOptions {
        host_choice: HostChoice::Bb2,
        timeout_secs: 60,
        max_rss_gb: 8,
        dry_run: true,
        exec: false,
        repo_root: None,
        target_commit: None,
        remote_seed_root: None,
    };

    for bad_target in [
        "-Kenv=evil",
        "--config=bad",
        "Obend.Mod; rm -rf /",
        "Obend.$(whoami)",
        "Obend\nmalicious",
    ] {
        let res = plan_build(&[bad_target.to_string()], &base_opts, &mock);
        assert!(
            res.is_err(),
            "malicious or option-smuggling target `{bad_target}` must be rejected"
        );
    }

    for bad_seed in [
        "relative/path",
        "/othersys/../etc/passwd",
        "/tmp/bad;rm",
        "/tmp/$(id)",
        "/tmp/seed pool",
        "/tmp/$UNSET_VAR/seeds",
        "$HOME/seeds/$OTHER",
    ] {
        let mut opts = base_opts.clone();
        opts.remote_seed_root = Some(bad_seed.to_string());
        let res = plan_build(&["Obend.Mod".to_string()], &opts, &mock);
        assert!(
            res.is_err(),
            "unsafe seed path `{bad_seed}` must be rejected"
        );
    }

    // Explicit `--commit` without `--repo` must emit a recipe that skips comparing `SEED_KEY` to `HEAD:lean`
    let mut commit_opts = base_opts.clone();
    commit_opts.target_commit = Some("a1531f8a00112233".to_string());
    let plan = plan_build(&["Obend.Mod".to_string()], &commit_opts, &mock)
        .expect("valid explicit commit plan");
    assert!(
        plan.batches[0]
            .remote_recipe
            .contains(r#"[ "$SEED_KEY" != "$TARGET_COMMIT" ]"#),
        "explicit commit without --repo must not compare commit SHA seed_key against HEAD:lean tree SHA"
    );
}

#[test]
fn stage3_astra_polarity_turbofish_nested_cfg_and_cycle_safety() {
    let repo = tempfile::tempdir().unwrap();

    // 1. Lean: cyclic struct updates, pure normalizer shared with `check`, double negation `¬ ¬ Collision`,
    //    `Not (ModuleSISHard ...)`, and arrow premise on `def` (`ModuleSISHard pp 999 → Nat`)
    write_rel(
        repo.path(),
        "lean/Obend/Crypto/AstraRegression.lean",
        r#"module
public section
namespace Obend.Crypto

def cycA := { cycB with Fragment := fun _ => True }
def cycB := { cycA with Fragment := fun _ => True }

def normalizeQuery (q : Query) : Query := q

instance normJudge : Obend.Judge Query Cert where
  Clause := String
  Meaning q := ValidNorm (normalizeQuery q)
  check _ q c := verifyNorm (normalizeQuery q) c
  sound h := verifyNorm_sound h
  refutes _ := true
  refuted h hr c' hm := verifyNorm_refuted h hr c' hm
  Fragment q := normalizeQuery q = q
  complete hWf hM := buildNorm hWf hM
  mono _ _ := rfl

theorem double_neg_collision_is_positive (H : Hash) (h : ¬ ¬ Collision H) : Collision H := by
  exact Classical.not_not.mp h

theorem negated_sis_hard_is_positive (pp : AjtaiParams) (h : Not (ModuleSISHard pp 999)) : True := by
  trivial

def arrow_premise_on_def (pp : AjtaiParams) : ModuleSISHard pp 999 → Nat :=
  fun _ => 42

theorem let_in_type_disjunction (H : Hash) (w : World) :
    let branched := cowBranch w
    branched = w ∨ BoundedCollision H 529 := by
  exact Or.inl rfl

structure CollisionPair (H : Hash) where
  left : List UInt8
  right : List UInt8

theorem CollisionPair.to_collision {H : Hash} (c : CollisionPair H) : Collision H := by
  exact witness_proj c

theorem toyLengthHash_collides : Collision toyLengthHash := by
  exact toy_counterexample

def dynamic_drop_frame (a b c : ByteArray) : ByteArray :=
  domainHash "OBEND.ASTRA.TURBO/v1" ([a, b, c].drop 1)

def spaced_decimal_tag (a b : ByteArray) : ByteArray :=
  domainHash [79 , 66 , 69 , 78 , 68 , 46 , 65 , 83 , 84 , 82 , 65 , 46 , 68 , 69 , 67 , 47 , 118 , 49] [a, b]

end Obend.Crypto
"#,
    );

    // 2. Rust: nested `mod tests { #![cfg(test)] ... }` followed by production code using turbofish `<u64, u32>`
    write_rel(
        repo.path(),
        "crates/obend-crypto-exec/src/astra_wire.rs",
        r#"
mod inner_tests {
    #![cfg(test)]
    fn ignored() {
        let _ = hash("OBEND.ASTRA.ONLY_IN_TEST/v1", &[b"x"]);
    }
}

pub fn prod_after_inner_cfg_test(a: &[u8], b: &[u8]) -> [u8; 32] {
    let _ = hash("OBEND.ASTRA.TURBO/v1", &[encode::<u64, u32>(a), b]);
    let _ = hash("OBEND.ASTRA.DEC/v1", &[a, b]);
    hash("OBEND.ASTRA.PROD_ORPHAN/v1", &[a, b])
}
"#,
    );

    let out = Command::new(obb_bin())
        .args(["lint", "--repo", repo.path().to_str().unwrap(), "--json"])
        .output()
        .expect("run obb lint");
    let json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    let findings = json["findings"].as_array().unwrap();

    // `normJudge` + `cycA`/`cycB` must emit 0 `lean/judge-fragment-restates-check`
    let frag_hits: Vec<_> = findings
        .iter()
        .filter(|f| f["rule_id"] == "lean/judge-fragment-restates-check")
        .collect();
    assert_eq!(
        frag_hits.len(),
        0,
        "unexpected fragment hits: {frag_hits:#?}"
    );

    // `arrow_premise_on_def` + `let_in_type_disjunction` should fire `lean/pigeonhole-vacuous-premise`
    // (NOT `¬ ¬ Collision`, `Not (ModuleSISHard ...)`, `CollisionPair.to_collision`, or `toyLengthHash_collides`)
    let vac_hits: Vec<_> = findings
        .iter()
        .filter(|f| f["rule_id"] == "lean/pigeonhole-vacuous-premise")
        .collect();
    assert_eq!(
        vac_hits.len(),
        2,
        "exact 2 vacuity hits expected on arrow_premise_on_def + let_in_type_disjunction: {vac_hits:#?}"
    );

    // Only `OBEND.ASTRA.PROD_ORPHAN/v1` should fire `cross-lang/domain-tag-drift`
    // (`ONLY_IN_TEST` is skipped; `TURBO` has dynamic `.drop 1` in Lean and 2-elem turbofish in Rust; `DEC` matches spaced `[79 , 66 , ...]`)
    let wire_hits: Vec<_> = findings
        .iter()
        .filter(|f| f["rule_id"] == "cross-lang/domain-tag-drift")
        .collect();
    assert_eq!(
        wire_hits.len(),
        1,
        "exact 1 wire hit expected on OBEND.ASTRA.PROD_ORPHAN/v1: {wire_hits:#?}"
    );
    assert_eq!(wire_hits[0]["symbol"], "OBEND.ASTRA.PROD_ORPHAN/v1");
}
