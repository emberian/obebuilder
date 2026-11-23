//! Planted-fault suite for obligation discovery, cosplay lints, broker recipe isolation and state-store isolation:
//! 1. `obb-judge::pipeline`: `*Obligations` + `extends HypothesisLedger` discovery; `UNDECLARED` on
//!    `0`-obligation repos (fails `--strict` / `--require-sealed`, never `STAGE_B_SEALED`);
//!    `(class_name, carrier_type)` discharge keying; `Unit`/`PUnit`/`Bool`/`Nat` trivial-carrier refusal.
//! 2. `obb-lint` (`lean/obligation-projection-cosplay`): catches 1–3 line `rfl`, `congrArg`,
//!    `Bool.and_eq_true`, `And.left`/`And.right`, `fun _ => trivial`, and `Fragment := fun _ => False`
//!    cosplay on `*Obligations` and `HypothesisLedger` instances while passing real theorem-backed instances.
//! 3. `obb-broker`: exact commit SHA sync (`git fetch` + `git checkout --detach <sha>`), `HEAD:lean`
//!    tree verification, `cp -R --reflink=auto` (zero `cp -al`), and whole-process-group PGID reaping.
//! 4. `obb-state`: zero `.obb/state.db` or `ledger/` pollution in audited git worktrees, and atomic
//!    SQLite rollback + surfaced `LedgerAppendFailed` refusal when JSONL append fails.

pub mod support;
use support::MockSshExecutor;

use obb_broker::{BuildPlanOptions, HostChoice, plan_build};
use obb_core::Severity;
use obb_judge::pipeline::{
    PipelineCheckOptions, PipelineStage, check_pipeline, check_pipeline_with_options,
};
use obb_lint::run_repo_lints;
use obb_state::{CampaignGuardEvidence, StateRefusal, StateStore};
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

fn obb_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_obb"))
}

fn write_rel(root: &Path, rel: &str, content: &str) {
    let full = root.join(rel);
    if let Some(parent) = full.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    fs::write(full, content).unwrap();
}

fn run_git(dir: &Path, args: &[&str]) -> String {
    let out = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .env("GIT_AUTHOR_NAME", "Test")
        .env("GIT_AUTHOR_EMAIL", "test@example.com")
        .env("GIT_COMMITTER_NAME", "Test")
        .env("GIT_COMMITTER_EMAIL", "test@example.com")
        .output()
        .expect("git command");
    assert!(
        out.status.success(),
        "git {:?} failed in {}: {}",
        args,
        dir.display(),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).trim().to_string()
}

#[test]
fn pipeline_matches_obligations_extends_ledger_never_seals_zero_classes_and_rejects_trivial_or_mismatched_carriers()
 {
    // 1. Zero obligation classes -> `UNDECLARED` (NEVER `STAGE_B_SEALED`), fails `--strict` & `--require-sealed`
    let zero_repo = tempfile::tempdir().unwrap();
    write_rel(
        zero_repo.path(),
        "lean/Obend/Core/Plain.lean",
        r#"module
public section
namespace Obend.Core
def addOne (n : Nat) : Nat := n + 1
theorem addOne_pos (n : Nat) : addOne n > 0 := Nat.succ_pos n
end Obend.Core
"#,
    );

    let rep_zero = check_pipeline(zero_repo.path()).unwrap();
    assert_eq!(rep_zero.stage, PipelineStage::Undeclared);
    assert_ne!(rep_zero.stage, PipelineStage::StageBSealed);
    assert!(!rep_zero.ready_for_claimed);
    assert!(!rep_zero.ready_for_parallel_swarm);

    let rep_zero_strict = check_pipeline_with_options(
        zero_repo.path(),
        PipelineCheckOptions {
            strict: true,
            allow_empty: false,
        },
    )
    .unwrap();
    assert_eq!(rep_zero_strict.stage, PipelineStage::Undeclared);
    assert!(!rep_zero_strict.passed);

    let cli_strict = Command::new(obb_bin())
        .args([
            "pipeline",
            "check",
            "--repo",
            zero_repo.path().to_str().unwrap(),
            "--strict",
        ])
        .output()
        .unwrap();
    assert_eq!(cli_strict.status.code(), Some(2));

    let cli_req_sealed = Command::new(obb_bin())
        .args([
            "pipeline",
            "check",
            "--repo",
            zero_repo.path().to_str().unwrap(),
            "--require-sealed",
        ])
        .output()
        .unwrap();
    assert_eq!(cli_req_sealed.status.code(), Some(2));

    // 2. Discover `class *Obligations` AND `extends HypothesisLedger`; verify `(class_name, carrier_type)` keying
    let carrier_repo = tempfile::tempdir().unwrap();
    write_rel(
        carrier_repo.path(),
        "lean/Obend/Crypto/Interface.lean",
        r#"module
public section
namespace Obend.Crypto

class HypothesisLedger : Prop

structure ProdPCS where
  commitment : Nat

structure ToyPCS where
  commitment : Nat

structure ProdConsensusState where
  view : Nat

class CanopyPCSObligations (C : Type) : Prop where
  binding_sound : ∀ (x y : C), x = y → x = y

class ConsensusSafety (S : Type) extends HypothesisLedger where
  view_monotone : ∀ (s : S), s = s

theorem apex_pcs_consumer [CanopyPCSObligations ProdPCS] [ConsensusSafety ProdConsensusState] :
    1 = 1 := rfl

end Obend.Crypto
"#,
    );

    let rep_stage_a = check_pipeline(carrier_repo.path()).unwrap();
    assert_eq!(rep_stage_a.stage, PipelineStage::StageALocked);
    assert_eq!(rep_stage_a.total_obligations, 2);
    assert_eq!(rep_stage_a.open_stage_a_obligations, 2);

    // 3. Cheating worker discharges `CanopyPCSObligations ToyPCS` while consumer requires `ProdPCS` -> MUST NOT SEAL!
    write_rel(
        carrier_repo.path(),
        "lean/Obend/Crypto/WrongCarrier.lean",
        r#"module
public import Obend.Crypto.Interface
public section
namespace Obend.Crypto

instance toyPcsSeal : CanopyPCSObligations ToyPCS where
  binding_sound := fun _ _ h => h

end Obend.Crypto
"#,
    );
    let rep_mismatch = check_pipeline(carrier_repo.path()).unwrap();
    assert_eq!(
        rep_mismatch.stage,
        PipelineStage::StageALocked,
        "ToyPCS instance must NOT seal ProdPCS consumer requirement: {rep_mismatch:#?}"
    );
    let pcs_ob = rep_mismatch
        .obligations
        .iter()
        .find(|o| o.class_name == "CanopyPCSObligations")
        .unwrap();
    assert!(!pcs_ob.discharged);
    assert_eq!(pcs_ob.unsealed_carriers, vec![vec!["ProdPCS".to_string()]]);

    // 4. Cheating worker tries `Unit`, `PUnit`, `Bool`, and `Nat` trivial carriers -> IMMEDIATE `FAILED`!
    for trivial_ty in ["Unit", "PUnit", "Bool", "Nat"] {
        let triv_repo = tempfile::tempdir().unwrap();
        write_rel(
            triv_repo.path(),
            "lean/Obend/Crypto/TrivialCarrier.lean",
            &format!(
                r#"module
public section
namespace Obend.Crypto

class CanopyPCSObligations (C : Type) : Prop where
  binding_sound : ∀ (x : C), x = x

instance badTrivialInst : CanopyPCSObligations {trivial_ty} where
  binding_sound := fun _ => Eq.refl _

end Obend.Crypto
"#
            ),
        );
        let rep_triv = check_pipeline(triv_repo.path()).unwrap();
        assert_eq!(
            rep_triv.stage,
            PipelineStage::Failed,
            "trivial carrier `{trivial_ty}` must fail pipeline check: {rep_triv:#?}"
        );
        assert!(
            rep_triv
                .violations
                .iter()
                .any(|v| v.kind == "trivial_carrier_instance"),
            "expected trivial_carrier_instance for `{trivial_ty}`, got {:?}",
            rep_triv.violations
        );
    }

    // 5. Discharging on the real `ProdPCS` and `ProdConsensusState` carriers seals Stage B cleanly!
    write_rel(
        carrier_repo.path(),
        "lean/Obend/Crypto/ProdSeal.lean",
        r#"module
public import Obend.Crypto.Interface
public section
namespace Obend.Crypto

instance prodPcsSeal : CanopyPCSObligations ProdPCS where
  binding_sound := fun _ _ h => h

instance prodConsensusSeal : ConsensusSafety ProdConsensusState where
  view_monotone := fun _ => Eq.refl _

end Obend.Crypto
"#,
    );
    let rep_sealed = check_pipeline(carrier_repo.path()).unwrap();
    assert_eq!(rep_sealed.stage, PipelineStage::StageBSealed);
    assert!(rep_sealed.passed);
    assert!(rep_sealed.ready_for_claimed);
    assert_eq!(rep_sealed.sealed_obligations, 2);
}

#[test]
fn lint_obligation_projection_cosplay_catches_all_six_cosplay_forms_and_allows_real_theorems() {
    let bad_repo = tempfile::tempdir().unwrap();
    write_rel(
        bad_repo.path(),
        "lean/Obend/Crypto/CosplayInstances.lean",
        r#"module
public section
namespace Obend.Crypto

class HypothesisLedger

structure ProdCarrier where
  tag : Nat

def commit (c : ProdCarrier) : Nat := c.tag
def checkPair (a b : Bool) : Bool := a && b

class CanopyPCSObligations (C : Type) where
  Fragment : C → Prop
  det_rfl : ∀ (c : C), commitProd c = commitProd c
  commit_det : ∀ (x y : ProdCarrier), x = y → commit x = commit y
  verify_unpack : ∀ (a b : Bool), checkPair a b = true → a = true
  proj_left : ∀ (P Q : Prop), P ∧ Q → P
  vacuous_true : C → True

class BridgeObligations (C : Type) extends HypothesisLedger where
  proj_right : ∀ (P Q : Prop), P ∧ Q → Q

instance cosplayCanopy : CanopyPCSObligations ProdCarrier where
  Fragment := fun _ => False
  det_rfl := fun _ => rfl
  commit_det := fun _ _ h => congrArg commit h
  verify_unpack := fun _ _ h => ((Bool.and_eq_true _ _).mp h).left
  proj_left := fun _ _ h => And.left h
  vacuous_true := fun _ => trivial

instance cosplayBridge : BridgeObligations ProdCarrier where
  proj_right _ _ h := h.right

end Obend.Crypto
"#,
    );

    let report = run_repo_lints(bad_repo.path()).unwrap();
    let cosplay_findings: Vec<_> = report
        .findings
        .iter()
        .filter(|f| f.rule_id == "lean/obligation-projection-cosplay")
        .collect();
    assert_eq!(
        cosplay_findings.len(),
        7,
        "expected all 7 cosplay fields (False, rfl, congrArg, Bool.and_eq_true, And.left, trivial, .right) to fire, got: {cosplay_findings:#?}"
    );
    assert!(
        cosplay_findings
            .iter()
            .all(|f| f.severity == Severity::Error)
    );

    // Positive control: genuine theorem-backed `*Obligations` instance passes with 0 cosplay findings
    let good_repo = tempfile::tempdir().unwrap();
    write_rel(
        good_repo.path(),
        "lean/Obend/Crypto/SubstantiveInstances.lean",
        r#"module
public section
namespace Obend.Crypto

structure Packet where
  epoch : Nat
  payload : Nat

def SupportedPacket (p : Packet) : Prop := p.epoch > 0

theorem packet_epoch_nonneg (p : Packet) : p.epoch >= 0 :=
  Nat.zero_le p.epoch

theorem packet_replay_sound (p : Packet) (h : SupportedPacket p) : p.epoch > 0 :=
  h

class VaultReplayObligations (P : Type) where
  Fragment : P → Prop
  epoch_nonneg : ∀ (p : Packet), p.epoch >= 0
  replay_sound : ∀ (p : Packet), SupportedPacket p → p.epoch > 0

instance substantiveVaultReplay : VaultReplayObligations Packet where
  Fragment := SupportedPacket
  epoch_nonneg p := packet_epoch_nonneg p
  replay_sound p h := packet_replay_sound p h

end Obend.Crypto
"#,
    );
    let good_report = run_repo_lints(good_repo.path()).unwrap();
    let good_cosplay: Vec<_> = good_report
        .findings
        .iter()
        .filter(|f| f.rule_id == "lean/obligation-projection-cosplay")
        .collect();
    assert!(
        good_cosplay.is_empty(),
        "substantive theorem-backed instance must produce 0 cosplay findings, got: {good_cosplay:#?}"
    );
}

#[test]
fn broker_recipe_fetches_detaches_exact_sha_verifies_tree_and_reaps_entire_process_group() {
    let sandbox = tempfile::tempdir().unwrap();
    let bare_origin = sandbox.path().join("origin.git");
    let author_repo = sandbox.path().join("author");
    let stale_remote_base = sandbox.path().join("remote_base");
    let work_root = sandbox.path().join("worktrees");
    let seed_pool = sandbox.path().join("seed_pool");
    let fake_bin = sandbox.path().join("bin");
    fs::create_dir_all(&bare_origin).unwrap();
    fs::create_dir_all(&author_repo).unwrap();
    fs::create_dir_all(&fake_bin).unwrap();

    run_git(&bare_origin, &["init", "--bare"]);
    run_git(&author_repo, &["init"]);
    run_git(
        &author_repo,
        &["remote", "add", "origin", bare_origin.to_str().unwrap()],
    );

    // Commit C1: initial stale version
    write_rel(&author_repo, "lean/Obend/Mod.lean", "-- version C1\n");
    run_git(&author_repo, &["add", "."]);
    run_git(&author_repo, &["commit", "-m", "commit C1"]);
    let c1_sha = run_git(&author_repo, &["rev-parse", "HEAD"]);
    run_git(&author_repo, &["push", "origin", "HEAD:refs/heads/dev"]);

    // Clone `stale_remote_base` at C1 (simulating a remote host whose local HEAD is stuck on C1!)
    let clone_out = Command::new("git")
        .args([
            "clone",
            "--quiet",
            bare_origin.to_str().unwrap(),
            stale_remote_base.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(clone_out.status.success());
    run_git(&stale_remote_base, &["checkout", "--detach", &c1_sha]);

    // Commit C2 in `author_repo` and push to `origin`, leaving `stale_remote_base` HEAD stale at C1!
    write_rel(&author_repo, "lean/Obend/Mod.lean", "-- version C2 EXACT\n");
    run_git(&author_repo, &["add", "."]);
    run_git(&author_repo, &["commit", "-m", "commit C2"]);
    let c2_sha = run_git(&author_repo, &["rev-parse", "HEAD"]);
    let c2_lean_tree = run_git(&author_repo, &["rev-parse", "HEAD:lean"]);
    run_git(&author_repo, &["push", "origin", "HEAD:refs/heads/dev"]);
    assert_ne!(c1_sha, c2_sha);

    let mock = MockSshExecutor::new();
    let plan = plan_build(
        &["Obend.Mod".to_string()],
        &BuildPlanOptions {
            host_choice: HostChoice::Bb2,
            timeout_secs: 30,
            max_rss_gb: 8,
            dry_run: true,
            exec: false,
            repo_root: Some(author_repo.clone()),
            target_commit: None,
            remote_seed_root: Some(seed_pool.to_string_lossy().to_string()),
        },
        &mock,
    )
    .unwrap();

    assert_eq!(plan.target_commit.as_deref(), Some(c2_sha.as_str()));
    assert_eq!(plan.seed_key, c2_lean_tree);
    let recipe = &plan.batches[0].remote_recipe;
    assert!(!recipe.contains("cp -al"));
    assert!(recipe.contains("cp -R --reflink=auto"));
    assert!(recipe.contains(&format!("TARGET_COMMIT=\"{c2_sha}\"")));

    // Part A: Execute `remote_recipe` with a fake `lake` that records checked-out `Obend/Mod.lean` and writes `.lake/build/lib`
    let observed_mod = sandbox.path().join("observed_mod.txt");
    let fake_lake = fake_bin.join("lake");
    fs::write(
        &fake_lake,
        format!(
            "#!/usr/bin/env bash\nset -euo pipefail\ncat Obend/Mod.lean > \"{}\"\nmkdir -p .lake/build/lib .lake/build/ir\necho olean-v2 > .lake/build/lib/Mod.olean\n",
            observed_mod.display()
        ),
    )
    .unwrap();
    fs::set_permissions(&fake_lake, fs::Permissions::from_mode(0o755)).unwrap();

    let orig_path = std::env::var("PATH").unwrap_or_default();
    let test_path = format!("{}:{orig_path}", fake_bin.display());
    let recipe_out = Command::new("bash")
        .arg("-c")
        .arg(recipe)
        .env("PATH", &test_path)
        .env("OBB_BASE_REPO", &stale_remote_base)
        .env("OBB_WORK_ROOT", &work_root)
        .output()
        .unwrap();
    assert!(
        recipe_out.status.success(),
        "remote recipe failed: stdout={}\nstderr={}",
        String::from_utf8_lossy(&recipe_out.stdout),
        String::from_utf8_lossy(&recipe_out.stderr)
    );
    let observed_text = fs::read_to_string(&observed_mod).unwrap();
    assert_eq!(
        observed_text.trim(),
        "-- version C2 EXACT",
        "recipe must fetch and detach-checkout exact C2 SHA, never stale C1 HEAD"
    );
    assert!(
        seed_pool
            .join(&c2_lean_tree)
            .join(".lake/build/lib/Mod.olean")
            .is_file(),
        "recipe must populate immutable tree-keyed seed cache"
    );

    // Part B: Plant a runaway grandchild process inside fake `lake` and verify negative-PGID reaping kills it!
    let grandchild_pid_file = sandbox.path().join("grandchild.pid");
    fs::write(
        &fake_lake,
        format!(
            "#!/usr/bin/env bash\n( sleep 60 ) &\necho $! > \"{}\"\nwait\n",
            grandchild_pid_file.display()
        ),
    )
    .unwrap();
    fs::set_permissions(&fake_lake, fs::Permissions::from_mode(0o755)).unwrap();

    let mut child = Command::new("bash")
        .arg("-c")
        .arg(recipe)
        .env("PATH", &test_path)
        .env("OBB_BASE_REPO", &stale_remote_base)
        .env("OBB_WORK_ROOT", &work_root)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();

    let start = Instant::now();
    while !grandchild_pid_file.is_file() && start.elapsed() < Duration::from_secs(5) {
        std::thread::sleep(Duration::from_millis(40));
    }
    let gc_pid: i32 = fs::read_to_string(&grandchild_pid_file)
        .expect("grandchild pid written")
        .trim()
        .parse()
        .unwrap();

    // Send SIGTERM to the recipe runner; `cleanup_obb_build` must reap the entire process group including `gc_pid`!
    let _ = Command::new("kill")
        .args(["-TERM", &child.id().to_string()])
        .status();
    let _ = child.wait();

    let wait_reap = Instant::now();
    let mut grandchild_alive = true;
    while wait_reap.elapsed() < Duration::from_secs(3) {
        let probe = Command::new("kill")
            .args(["-0", &gc_pid.to_string()])
            .stderr(Stdio::null())
            .status()
            .unwrap();
        if !probe.success() {
            grandchild_alive = false;
            break;
        }
        std::thread::sleep(Duration::from_millis(50));
    }
    if grandchild_alive {
        let _ = Command::new("kill")
            .args(["-KILL", &gc_pid.to_string()])
            .status();
    }
    assert!(
        !grandchild_alive,
        "grandchild process {gc_pid} survived recipe termination; whole-PGID reaping failed!"
    );
}

#[test]
fn state_store_never_pollutes_target_git_worktree_and_surfaces_jsonl_append_errors_with_rollback() {
    let sandbox = tempfile::tempdir().unwrap();
    let target_repo = sandbox.path().join("audited_target_repo");
    let xdg_state = sandbox.path().join("xdg_state");
    let explicit_state = sandbox.path().join("explicit_state");
    fs::create_dir_all(&target_repo).unwrap();
    fs::create_dir_all(&xdg_state).unwrap();

    // Initialize clean audited git repository
    run_git(&target_repo, &["init"]);
    write_rel(&target_repo, "README.md", "# Clean Target Repo\n");
    run_git(&target_repo, &["add", "."]);
    run_git(&target_repo, &["commit", "-m", "init clean repo"]);
    assert_eq!(run_git(&target_repo, &["status", "--porcelain"]), "");

    // Invoke `obb` state CLI against `target_repo` with `XDG_STATE_HOME`
    let cli_init = Command::new(obb_bin())
        .args([
            "--workspace",
            target_repo.to_str().unwrap(),
            "state",
            "init",
        ])
        .env("XDG_STATE_HOME", &xdg_state)
        .env_remove("OBB_STATE_DIR")
        .output()
        .unwrap();
    assert!(cli_init.status.success());

    let cli_camp = Command::new(obb_bin())
        .args([
            "--workspace",
            target_repo.to_str().unwrap(),
            "state",
            "campaign",
            "--id",
            "C-clean",
            "--title",
            "Zero Worktree Pollution",
            "--aim",
            "Never touch target git worktree",
        ])
        .env("XDG_STATE_HOME", &xdg_state)
        .env_remove("OBB_STATE_DIR")
        .output()
        .unwrap();
    assert!(
        cli_camp.status.success(),
        "cli_camp failed: {}",
        String::from_utf8_lossy(&cli_camp.stderr)
    );

    // Target audited git worktree MUST have ZERO untracked or modified files!
    assert_eq!(
        run_git(&target_repo, &["status", "--porcelain"]),
        "",
        "obb state polluted target git worktree!"
    );
    assert!(!target_repo.join(".obb").exists());
    assert!(!target_repo.join("ledger").exists());
    assert!(xdg_state.join("obb").is_dir());

    // Now test explicit `--state-dir` + planted JSONL append failure + atomic SQLite rollback
    let store =
        StateStore::open_with_state_dir(&target_repo, Some(explicit_state.as_path())).unwrap();
    store
        .create_campaign("C-atomic", "Atomic Ledger", "Aim", "/tmp")
        .unwrap();
    assert_eq!(store.verify_ledger_chain().unwrap(), 1);

    // Plant fault: replace `events.jsonl` with a directory so subsequent JSONL opens fail with EISDIR!
    let ledger_file = store.ledger_path().to_path_buf();
    fs::remove_file(&ledger_file).unwrap();
    fs::create_dir_all(&ledger_file).unwrap();

    let err = store
        .transition_campaign(
            "C-atomic",
            "Alone",
            CampaignGuardEvidence::Unconditional {
                note: "should fail JSONL append".into(),
            },
        )
        .expect_err("JSONL append failure must surface as Err, never swallowed!");
    assert!(
        matches!(err, StateRefusal::LedgerAppendFailed { .. }),
        "expected LedgerAppendFailed, got: {err:?}"
    );

    // Restore empty/valid ledger dir removal to inspect SQLite state: SQLite MUST have rolled back `C-atomic` to `"Aim"`!
    fs::remove_dir_all(&ledger_file).unwrap();
    let snap = store.snapshot().unwrap();
    assert_eq!(snap.campaigns.len(), 1);
    assert_eq!(
        snap.campaigns[0].state, "Aim",
        "SQLite transaction must roll back when JSONL append fails!"
    );
    assert_eq!(run_git(&target_repo, &["status", "--porcelain"]), "");
}
