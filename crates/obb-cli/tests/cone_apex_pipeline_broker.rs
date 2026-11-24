//! Unit, integration and CLI planted-fault tests for module cones, apex coverage, the pipeline and the broker:
//! 1. `LAW-M1` & `LAW-M2` Module-Cone Hygiene (`lean/file-wide-expose`, `lean/public-meta-import-leak`, `obb cone`, `obb cone plan`)
//! 2. `obb apex` Whole-System Compositional Assurance & Anti-Leaf-Island Engine (`quarry/obend-apex.toml`)
//! 3. `obb pipeline` Two-Stage `[HypothesisLedger]` Interface-Lock (`STAGE_A_LOCKED` -> `STAGE_B_SEALED`) & Smuggling Refusal,
//!    plus the ledger basis of repositories without obligation classes (verified Apex manifest,
//!    recorded `--allow-empty` override, zero theorem declarations, undeclared theorems)
//! 4. `obb broker` Remote `hbox` + `bb2` ZFS-ARC Health Prober, `.olean` Hardlink Seed Pool & Bounded `lake build` Batcher

pub mod support;
use support::MockSshExecutor;

use obb_broker::{
    BuildPlanOptions, HostChoice, RemoteCmdOutput, TargetWorkloadClass, plan_build, probe_hosts,
};
use obb_core::{Severity, Sink};
use obb_judge::pipeline::{
    PipelineCheckOptions, PipelineLedgerBasis, PipelineStage, check_pipeline,
    check_pipeline_with_options,
};
use obb_lint::apex::{ApexCheckOptions, ApexManifest, CANONICAL_SUBSYSTEMS, evaluate_apex};
use obb_lint::cone::{ProposedShard, plan_cone_shards, scan_repo_cone};
use obb_lint::{RepoLintOptions, run_repo_lints, run_repo_lints_with_options};
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn write_rel(root: &Path, rel: &str, content: &str) {
    let full = root.join(rel);
    if let Some(parent) = full.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    fs::write(full, content).unwrap();
}

fn obb_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_obb"))
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap()
}

#[test]
fn law_m1_file_wide_expose_flags_over_80_lines_and_escalates_under_strict_expose() {
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();

    // 1. Short file (<= 80 lines) with `@[expose] public section` -> ALLOWED (0 findings)
    let mut short_src =
        String::from("module\n\n@[expose] public section\n\nnamespace Obend.Small\n");
    for i in 0..20 {
        short_src.push_str(&format!("def proj{i} (x : Nat) : Nat := x + {i}\n"));
    }
    short_src.push_str("end Obend.Small\n");
    assert!(short_src.lines().count() <= 80);
    write_rel(
        root,
        "lean/Obend/Core/Small carrier.lean"
            .replace(' ', "")
            .as_str(),
        &short_src,
    );

    // 2. Large file (> 80 lines) with `@[expose] public section` -> FLAGGED (`lean/file-wide-expose`)
    let mut big_bad =
        String::from("module\n\n@[expose] public section\n\nnamespace Obend.Core.Giant\n");
    for i in 0..90 {
        big_bad.push_str(&format!("def heavyStep{i} (x : Nat) : Nat := x + {i}\n"));
    }
    big_bad.push_str("end Obend.Core.Giant\n");
    assert!(big_bad.lines().count() > 80);
    write_rel(root, "lean/Obend/Core/GiantExpose.lean", &big_bad);

    // 3. Large file (> 80 lines) using Lean 4.35 `public section` + selective `@[expose]` -> CLEAN
    let mut big_clean = String::from(
        "module\n\npublic section\n\nnamespace Obend.Core.Clean\n@[expose] def tinyProj (x : Nat) : Nat := x\n",
    );
    for i in 0..90 {
        big_clean.push_str(&format!("def hiddenBody{i} (x : Nat) : Nat := x + {i}\n"));
    }
    big_clean.push_str("end Obend.Core.Clean\n");
    assert!(big_clean.lines().count() > 80);
    write_rel(root, "lean/Obend/Core/CleanSection.lean", &big_clean);

    // Default run: `Severity::Warning`, `Sink::Slow`
    let rep_default = run_repo_lints(root).unwrap();
    let expose_findings: Vec<_> = rep_default
        .findings
        .iter()
        .filter(|f| f.rule_id == "lean/file-wide-expose")
        .collect();
    assert_eq!(
        expose_findings.len(),
        1,
        "expected exactly GiantExpose.lean to be flagged"
    );
    assert!(expose_findings[0].path.ends_with("GiantExpose.lean"));
    assert_eq!(expose_findings[0].severity, Severity::Warning);
    assert_eq!(expose_findings[0].sink, Some(Sink::Slow));
    assert!(
        expose_findings[0].remediation.contains("public section")
            && expose_findings[0].remediation.contains("@[expose]"),
        "remediation must explain Lean 4.35 `public section` + selective `@[expose]`"
    );
    assert_eq!(rep_default.modularity.file_wide_expose_modules, 1);

    // `--strict-expose` run: escalates to `Severity::Error`
    let rep_strict = run_repo_lints_with_options(
        root,
        RepoLintOptions {
            strict_expose: true,
            ..Default::default()
        },
    )
    .unwrap();
    let strict_finding = rep_strict
        .findings
        .iter()
        .find(|f| f.rule_id == "lean/file-wide-expose")
        .unwrap();
    assert_eq!(strict_finding.severity, Severity::Error);

    // CLI `--strict --strict-expose` exits non-zero (code 2)
    let cli_out = Command::new(obb_bin())
        .args([
            "lint",
            "--repo",
            root.to_str().unwrap(),
            "--strict",
            "--strict-expose",
            "--rule",
            "lean/file-wide-expose",
        ])
        .output()
        .unwrap();
    assert_eq!(cli_out.status.code(), Some(2));
}

#[test]
fn law_m2_public_meta_import_leak_allows_tactic_and_elab_and_blocks_other_modules() {
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();

    // Allowed: `Obend/Tactic/` and `Obend/Elab/`
    write_rel(
        root,
        "lean/Obend/Tactic/OmegaHelper.lean",
        "module\npublic meta import Lean\npublic section\ndef helper : Nat := 1\n",
    );
    write_rel(
        root,
        "lean/Obend/Elab/CustomMacro.lean",
        "module\npublic meta import Lean.Elab.Command\npublic section\ndef macroId : Nat := 2\n",
    );

    // Forbidden: `Obend/Hardware/` and `Obend/Lower/`
    write_rel(
        root,
        "lean/Obend/Hardware/UserspaceLeak.lean",
        "module\npublic meta import Lean\npublic section\ndef regWidth : Nat := 64\n",
    );
    write_rel(
        root,
        "lean/Obend/Lower/FabricLeak.lean",
        "module\npublic meta import Lean.Elab.Term\npublic section\ndef lowerWidth : Nat := 32\n",
    );

    // Clean private `meta import Lean` outside Tactic/Elab -> ALLOWED (`LAW-M2` remediation!)
    write_rel(
        root,
        "lean/Obend/Hardware/CleanPrivateMeta.lean",
        "module\nmeta import Lean\npublic section\ndef cleanWidth : Nat := 64\n",
    );

    let rep = run_repo_lints(root).unwrap();
    let leaks: Vec<_> = rep
        .findings
        .iter()
        .filter(|f| f.rule_id == "lean/public-meta-import-leak")
        .collect();
    assert_eq!(leaks.len(), 2);
    assert!(leaks.iter().all(|f| f.severity == Severity::Error));
    assert!(leaks.iter().all(|f| f.sink == Some(Sink::Slow)));
    let paths: BTreeSet<&str> = leaks.iter().map(|f| f.path.as_str()).collect();
    assert!(paths.contains("lean/Obend/Hardware/UserspaceLeak.lean"));
    assert!(paths.contains("lean/Obend/Lower/FabricLeak.lean"));

    let cone = scan_repo_cone(root, None).unwrap();
    assert_eq!(cone.public_meta_import_leaks.len(), 2);
}

#[test]
fn cone_blast_radius_depth_and_shard_planner_enforce_disjoint_slices_and_hub_barriers() {
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();

    // Central carrier hub `Obend.Core.Hub` publicly imported by 27 modules (`fan_in > 25`!)
    write_rel(
        root,
        "lean/Obend/Core/Hub.lean",
        "module\npublic section\nstructure HubState where\n  tick : Nat\n",
    );
    // Private implementation helper `Obend.Core.PrivImpl` privately imported by `Mid` -> its header
    // does NOT transitively leak through `Mid`!
    write_rel(
        root,
        "lean/Obend/Core/PrivImpl.lean",
        "module\npublic section\ndef internalConst : Nat := 42\n",
    );
    write_rel(
        root,
        "lean/Obend/Core/Mid.lean",
        "module\npublic import Obend.Core.Hub\nimport Obend.Core.PrivImpl\npublic section\ndef stepHub (s : HubState) : HubState := { tick := s.tick + internalConst }\n",
    );
    // Proof module leaked via `public import` in runtime module -> `proof_cone_leaks`
    write_rel(
        root,
        "lean/Obend/Core/Proofs/HubLemmas.lean",
        "module\nimport Obend.Core.Mid\npublic section\ntheorem step_eq (s : HubState) : s.tick = s.tick := rfl\n",
    );
    write_rel(
        root,
        "lean/Obend/Leaf/BadProofReexport.lean",
        "module\npublic import Obend.Core.Proofs.HubLemmas\npublic section\ndef leafVal : Nat := 0\n",
    );

    // 27 downstream consumer modules that `public import Obend.Core.Mid` (giving `Hub` and `Mid` `public_fan_in >= 27`)
    for i in 0..27 {
        write_rel(
            root,
            &format!("lean/Obend/Vault/Consumer{i:02}.lean"),
            &format!(
                "module\npublic import Obend.Core.Mid\npublic section\ndef useHub{i} (s : HubState) : Nat := (stepHub s).tick + {i}\n"
            ),
        );
    }

    let cone = scan_repo_cone(root, Some(2)).unwrap();
    assert!(
        cone.scan_ms < 50.0,
        "cone scan took {:.2}ms (expected <50ms)",
        cone.scan_ms
    );
    // Chain `Obend.Vault.Consumer00 -> Obend.Core.Mid -> Obend.Core.Hub` has outgoing depth 2,
    // let's check `Hub` vs `PrivImpl` blast radius!
    let hub_node = cone
        .modules
        .iter()
        .find(|m| m.module == "Obend.Core.Hub")
        .unwrap();
    let priv_node = cone
        .modules
        .iter()
        .find(|m| m.module == "Obend.Core.PrivImpl")
        .unwrap();
    assert_eq!(
        hub_node.public_fan_in, 28,
        "Mid + 27 Consumers transitively `public import` Hub"
    );
    assert_eq!(
        hub_node.blast_radius, 29,
        "Mid + 27 Consumers + Proofs/HubLemmas (which privately imports Mid) rebuild when Hub's header changes"
    );
    assert_eq!(
        priv_node.public_fan_in, 0,
        "PrivImpl is privately imported by Mid, so 0 modules publicly re-export it"
    );
    assert_eq!(
        priv_node.blast_radius, 1,
        "Only Mid directly rebuilds if PrivImpl's header changes"
    );
    assert_eq!(cone.proof_cone_leaks.len(), 1);
    assert_eq!(
        cone.proof_cone_leaks[0].importer_module,
        "Obend.Leaf.BadProofReexport"
    );

    // Depth violation test (`--max-depth 1` fails since Consumer -> Mid -> Hub has depth 2)
    let strict_cone = scan_repo_cone(root, Some(1)).unwrap();
    assert!(!strict_cone.depth_violations.is_empty());

    // 1. Auto-partition into 3 shards: `Hub` and `Mid` (`fan_in > 25`) are isolated into `barrier_hubs`
    // and worker shards are 100% disjoint!
    let auto_plan = plan_cone_shards(&cone, 3, &[]).unwrap();
    assert!(auto_plan.disjoint_write_slices);
    assert_eq!(auto_plan.shards.len(), 3);
    assert_eq!(auto_plan.barrier_hubs.len(), 2);
    let mut seen_files = BTreeSet::new();
    for sh in &auto_plan.shards {
        for f in &sh.files {
            assert!(
                seen_files.insert(f.clone()),
                "duplicate file `{f}` across auto-planned shards"
            );
            assert!(
                f != "lean/Obend/Core/Hub.lean" && f != "lean/Obend/Core/Mid.lean",
                "high-blast-radius hub `{f}` must stay in the barrier, not parallel worker shards"
            );
        }
    }

    // 2. Planted overlapping proposed shards -> REFUSED (`disjoint_write_slices == false`)
    let overlap_plan = plan_cone_shards(
        &cone,
        2,
        &[
            ProposedShard {
                name: "worker-a".into(),
                files: vec![
                    "lean/Obend/Vault/Consumer00.lean".into(),
                    "lean/Obend/Vault/Consumer01.lean".into(),
                ],
                barrier: false,
            },
            ProposedShard {
                name: "worker-b".into(),
                files: vec![
                    "lean/Obend/Vault/Consumer01.lean".into(),
                    "lean/Obend/Vault/Consumer02.lean".into(),
                ],
                barrier: false,
            },
        ],
    )
    .unwrap();
    assert!(!overlap_plan.disjoint_write_slices);
    assert_eq!(overlap_plan.overlapping_assignments.len(), 1);
    assert_eq!(
        overlap_plan.overlapping_assignments[0].path,
        "lean/Obend/Vault/Consumer01.lean"
    );

    // 3. Disjoint proposed shards where `worker-a` touches `Obend/Core/Hub.lean` (`fan_in = 28 > 25`)
    // outside a barrier slice -> emits `HubContentionWarning`!
    let hub_warn_plan = plan_cone_shards(
        &cone,
        2,
        &[
            ProposedShard {
                name: "worker-a".into(),
                files: vec!["lean/Obend/Core/Hub.lean".into()],
                barrier: false,
            },
            ProposedShard {
                name: "worker-b".into(),
                files: vec!["lean/Obend/Vault/Consumer00.lean".into()],
                barrier: false,
            },
        ],
    )
    .unwrap();
    assert!(hub_warn_plan.disjoint_write_slices);
    assert_eq!(hub_warn_plan.hub_warnings.len(), 1);
    assert_eq!(hub_warn_plan.hub_warnings[0].module, "Obend.Core.Hub");

    // Moving `Hub.lean` into a `barrier: true` slice clears the hub contention warning!
    let barrier_clean_plan = plan_cone_shards(
        &cone,
        2,
        &[
            ProposedShard {
                name: "barrier-interface".into(),
                files: vec!["lean/Obend/Core/Hub.lean".into()],
                barrier: true,
            },
            ProposedShard {
                name: "worker-a".into(),
                files: vec!["lean/Obend/Vault/Consumer00.lean".into()],
                barrier: false,
            },
            ProposedShard {
                name: "worker-b".into(),
                files: vec!["lean/Obend/Vault/Consumer01.lean".into()],
                barrier: false,
            },
        ],
    )
    .unwrap();
    assert!(barrier_clean_plan.disjoint_write_slices);
    assert!(barrier_clean_plan.hub_warnings.is_empty());

    // CLI overlap check exits with code 2
    let cli_overlap = Command::new(obb_bin())
        .args([
            "cone",
            "plan",
            "--repo",
            root.to_str().unwrap(),
            "--propose",
            "w1=lean/Obend/Vault/Consumer00.lean",
            "--propose",
            "w2=lean/Obend/Vault/Consumer00.lean",
        ])
        .output()
        .unwrap();
    assert_eq!(cli_overlap.status.code(), Some(2));
}

#[test]
fn apex_engine_verifies_theorems_catches_unwired_leaf_islands_and_planted_cone_faults() {
    // 1. Validate the shipped `quarry/obend-apex.toml` manifest structure
    let shipped_manifest_path = workspace_root().join("quarry/obend-apex.toml");
    let shipped = ApexManifest::load_from_path(&shipped_manifest_path).unwrap();
    assert!(
        shipped.apex.len() >= 30,
        "expected comprehensive Apex theorem coverage in quarry/obend-apex.toml"
    );
    assert!(!shipped.planned_apex.is_empty());
    let covered_subs: BTreeSet<&str> = shipped.apex.iter().map(|a| a.subsystem.as_str()).collect();
    for canonical in CANONICAL_SUBSYSTEMS {
        assert!(
            covered_subs.contains(canonical),
            "quarry/obend-apex.toml missing canonical subsystem `{canonical}`"
        );
    }

    // 2. Synthetic repo testing reverse cone coverage, umbrella-barrel non-masking, Teeth exclusion,
    // unwired leaf island detection, and `sorry`/`axiom` cone rejection
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();

    write_rel(
        root,
        "lean/Obend/Core/Step.lean",
        "module\npublic section\nnamespace Obend.Core\ndef evalStep (n : Nat) : Nat := n + 1\ntheorem evalStep_pos (n : Nat) : evalStep n > 0 := by omega\nend Obend.Core\n",
    );
    write_rel(
        root,
        "lean/Obend/Vault/Replay.lean",
        "module\npublic import Obend.Core.Step\npublic section\nnamespace Obend.Vault\ndef replayTick (n : Nat) : Nat := Obend.Core.evalStep n\ntheorem replay_sound (n : Nat) : replayTick n > 0 := Obend.Core.evalStep_pos n\nend Obend.Vault\n",
    );
    // Unwired leaf island: NOT imported by any Apex theorem or executable (`Main.lean`) — even though
    // umbrella `lean/Obend.lean` re-exports it!
    write_rel(
        root,
        "lean/Obend/Hardware/DisconnectedIsland.lean",
        "module\npublic section\nnamespace Obend.Hardware\ntheorem island_self_eq (x : Nat) : x = x := rfl\nend Obend.Hardware\n",
    );
    write_rel(
        root,
        "lean/Obend.lean",
        "module\npublic import Obend.Vault.Replay\npublic import Obend.Hardware.DisconnectedIsland\n",
    );
    write_rel(
        root,
        "lean/Obend/Main.lean",
        "module\nimport Obend.Vault.Replay\ndef main : IO Unit := pure ()\n",
    );
    // Excluded Teeth & Census modules must NOT count as unwired library islands
    write_rel(
        root,
        "lean/Obend/Teeth/SmokeTooth.lean",
        "module\ntheorem tooth_ok : 1 = 1 := rfl\n",
    );
    write_rel(
        root,
        "lean/Obend/Census.lean",
        "module\ndef censusCount : Nat := 1\n",
    );

    let manifest_toml = r#"
version = 1
target_name = "synthetic-obend"
subsystems = ["Core", "Vault", "Hardware"]
entry_points = ["lean/Obend/Main.lean", "lean/Obend.lean"]

[[apex]]
id = "vault-replay-e2e"
subsystem = "Vault"
module = "Obend.Vault.Replay"
theorem = "replay_sound"
description = "End-to-end Vault -> Core replay soundness"

[[planned_apex]]
id = "planned-hw-spine"
pillar = "Pillar 2"
subsystem = "Hardware"
target_module = "Obend.Hardware.Spine"
target_theorem = "hw_e2e_ok"
wave = "Wave 4"
description = "Upcoming hardware spine"
"#;
    let manifest_path = root.join("apex.toml");
    fs::write(&manifest_path, manifest_toml).unwrap();
    let manifest = ApexManifest::load_from_path(&manifest_path).unwrap();

    let rep = evaluate_apex(root, &manifest, ApexCheckOptions::default()).unwrap();
    assert!(rep.all_apex_valid);
    assert!(rep.check_passed);
    assert_eq!(
        rep.total_library_modules, 4,
        "Core/Step + Vault/Replay + Hardware/DisconnectedIsland + Main"
    );
    assert_eq!(
        rep.apex_covered_library_modules, 2,
        "Vault/Replay + Core/Step in Apex cone"
    );
    assert_eq!(rep.wired_library_modules, 3, "Apex cone + Main entry point");
    assert_eq!(rep.unwired_island_count, 1);
    assert_eq!(
        rep.unwired_leaf_islands[0].rel_path,
        "lean/Obend/Hardware/DisconnectedIsland.lean"
    );

    // `--strict-islands` fails while `DisconnectedIsland.lean` is unwired
    let strict_rep = evaluate_apex(
        root,
        &manifest,
        ApexCheckOptions {
            strict_islands: true,
            max_islands: None,
        },
    )
    .unwrap();
    assert!(!strict_rep.check_passed);

    // Plant a custom `axiom` inside `Core/Step.lean` (transitively inside `replay_sound`'s cone) -> MUST FAIL!
    write_rel(
        root,
        "lean/Obend/Core/Step.lean",
        "module\npublic section\nnamespace Obend.Core\naxiom magic_step_pos (n : Nat) : n + 1 > 0\ndef evalStep (n : Nat) : Nat := n + 1\ntheorem evalStep_pos (n : Nat) : evalStep n > 0 := magic_step_pos n\nend Obend.Core\n",
    );
    let poisoned_rep = evaluate_apex(root, &manifest, ApexCheckOptions::default()).unwrap();
    assert!(!poisoned_rep.all_apex_valid);
    assert!(!poisoned_rep.check_passed);
    assert_eq!(poisoned_rep.apex_theorems[0].custom_axiom_count, 1);
}

#[test]
fn pipeline_enforces_stage_a_locked_to_stage_b_sealed_and_rejects_sorry_axiom_cycles_and_vacuity() {
    // Case 1: Clean Stage-A interface lock (`[VaultSyncHypothesisLedger]`, 0 sorry, 0 axiom, no instance yet)
    let stage_a = tempfile::tempdir().unwrap();
    write_rel(
        stage_a.path(),
        "lean/Obend/Vault/Interface.lean",
        r#"module
public section
namespace Obend.Vault

structure SyncPacket where
  epoch : Nat
  digest : Nat

class VaultSyncHypothesisLedger (pkt : SyncPacket) : Prop where
  epoch_monotone : pkt.epoch >= 0

theorem consumer_replay_safe (pkt : SyncPacket) [VaultSyncHypothesisLedger pkt] :
    pkt.epoch >= 0 :=
  VaultSyncHypothesisLedger.epoch_monotone

end Obend.Vault
"#,
    );

    let rep_a = check_pipeline(stage_a.path()).unwrap();
    assert_eq!(rep_a.stage, PipelineStage::StageALocked);
    assert_eq!(rep_a.ledger_basis, PipelineLedgerBasis::ObligationClasses);
    assert!(!rep_a.allow_empty_override);
    assert_eq!(rep_a.theorem_declaration_count, 1);
    assert!(rep_a.passed);
    assert!(rep_a.ready_for_parallel_swarm);
    assert!(!rep_a.ready_for_claimed);
    assert_eq!(rep_a.total_obligations, 1);
    assert_eq!(rep_a.open_stage_a_obligations, 1);
    assert_eq!(rep_a.consumer_sites.len(), 1);

    // CLI: `obb pipeline check` succeeds (0), `obb pipeline check --require-sealed` fails (2)
    let cli_a_ok = Command::new(obb_bin())
        .args([
            "pipeline",
            "check",
            "--repo",
            stage_a.path().to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_eq!(cli_a_ok.status.code(), Some(0));

    let cli_a_req = Command::new(obb_bin())
        .args([
            "pipeline",
            "check",
            "--repo",
            stage_a.path().to_str().unwrap(),
            "--require-sealed",
        ])
        .output()
        .unwrap();
    assert_eq!(cli_a_req.status.code(), Some(2));

    // Case 2: Producer lands concrete discharging `instance` -> transitions to `STAGE_B_SEALED`!
    write_rel(
        stage_a.path(),
        "lean/Obend/Vault/ProducerProof.lean",
        r#"module
public import Obend.Vault.Interface
public section
namespace Obend.Vault

instance sealVaultSync (pkt : SyncPacket) : VaultSyncHypothesisLedger pkt where
  epoch_monotone := Nat.zero_le pkt.epoch

end Obend.Vault
"#,
    );
    let rep_b = check_pipeline(stage_a.path()).unwrap();
    assert_eq!(rep_b.stage, PipelineStage::StageBSealed);
    assert_eq!(rep_b.ledger_basis, PipelineLedgerBasis::ObligationClasses);
    assert!(!rep_b.allow_empty_override);
    assert!(rep_b.passed);
    assert!(rep_b.ready_for_claimed);
    assert_eq!(rep_b.sealed_obligations, 1);
    assert_eq!(rep_b.open_stage_a_obligations, 0);

    let cli_b_req = Command::new(obb_bin())
        .args([
            "pipeline",
            "check",
            "--repo",
            stage_a.path().to_str().unwrap(),
            "--require-sealed",
        ])
        .output()
        .unwrap();
    assert_eq!(cli_b_req.status.code(), Some(0));

    // Case 3: Worker smuggles `sorry` or `axiom` instead of `[HypothesisLedger]` -> IMMEDIATE `FAILED`
    let smuggled = tempfile::tempdir().unwrap();
    write_rel(
        smuggled.path(),
        "lean/Obend/Lower/Smuggled.lean",
        r#"module
public section
namespace Obend.Lower
axiom secret_shortcut : 1 = 1
theorem bad_worker_claim (x : Nat) : x = x := by
  sorry
end Obend.Lower
"#,
    );
    let rep_smug = check_pipeline(smuggled.path()).unwrap();
    assert_eq!(rep_smug.stage, PipelineStage::Failed);
    assert!(!rep_smug.passed);
    assert_eq!(rep_smug.smuggled_sorry_count, 1);
    assert_eq!(rep_smug.smuggled_axiom_count, 1);

    // Case 4: Cyclic `[HypothesisLedger]` instances (`[LedgerB] -> LedgerA` and `[LedgerA] -> LedgerB`) -> `FAILED`
    let cyclic = tempfile::tempdir().unwrap();
    write_rel(
        cyclic.path(),
        "lean/Obend/Consensus/CyclicLedgers.lean",
        r#"module
public section
namespace Obend.Consensus

@[obb_obligation]
class LedgerAlpha (n : Nat) : Prop where
  ok_a : n >= 0

@[obb_obligation]
class LedgerBeta (n : Nat) : Prop where
  ok_b : n >= 0

instance alphaFromBeta (n : Nat) [h : LedgerBeta n] : LedgerAlpha n where
  ok_a := h.ok_b

instance betaFromAlpha (n : Nat) [h : LedgerAlpha n] : LedgerBeta n where
  ok_b := h.ok_a

end Obend.Consensus
"#,
    );
    let rep_cyc = check_pipeline(cyclic.path()).unwrap();
    assert_eq!(rep_cyc.stage, PipelineStage::Failed);
    assert!(
        rep_cyc
            .violations
            .iter()
            .any(|v| v.kind == "cyclic_instance_dependency"),
        "expected cyclic_instance_dependency violation, got {:?}",
        rep_cyc.violations
    );

    // Case 5: Vacuous instance over uninhabited 0-constructor carrier -> `FAILED`
    let vacuous = tempfile::tempdir().unwrap();
    write_rel(
        vacuous.path(),
        "lean/Obend/Hardware/VacuousWitness.lean",
        r#"module
public section
namespace Obend.Hardware

inductive GhostDevice : Type

class GhostHypothesisLedger (d : GhostDevice) : Prop where
  impossible_claim : 0 = 1

instance vacuousGhostInst (d : GhostDevice) : GhostHypothesisLedger d where
  impossible_claim := nomatch d

end Obend.Hardware
"#,
    );
    let rep_vac = check_pipeline(vacuous.path()).unwrap();
    assert_eq!(rep_vac.stage, PipelineStage::Failed);
    assert!(
        rep_vac.violations.iter().any(|v| {
            v.kind == "vacuous_instance_witness" || v.kind == "uninhabited_ledger_witness"
        }),
        "expected vacuous/uninhabited witness violation, got {:?}",
        rep_vac.violations
    );
}

fn pipeline_cli(repo: &Path, flags: &[&str]) -> std::process::Output {
    Command::new(obb_bin())
        .args(["pipeline", "check", "--repo", repo.to_str().unwrap()])
        .args(flags)
        .output()
        .unwrap()
}

fn pipeline_cli_stdout(repo: &Path, flags: &[&str]) -> (Option<i32>, String) {
    let out = pipeline_cli(repo, flags);
    (
        out.status.code(),
        String::from_utf8_lossy(&out.stdout).into_owned(),
    )
}

/// Exit code and parsed report of `obb pipeline check ... --json`.
fn pipeline_cli_json(repo: &Path, flags: &[&str]) -> (Option<i32>, serde_json::Value) {
    let mut args = flags.to_vec();
    args.push("--json");
    let out = pipeline_cli(repo, &args);
    let report = serde_json::from_slice(&out.stdout).unwrap_or_else(|e| {
        panic!(
            "`obb pipeline check {args:?}` did not print JSON ({e}): {}",
            String::from_utf8_lossy(&out.stdout)
        )
    });
    (out.status.code(), report)
}

const STRICT: PipelineCheckOptions = PipelineCheckOptions {
    strict: true,
    allow_empty: false,
};

const ALLOW_EMPTY: PipelineCheckOptions = PipelineCheckOptions {
    strict: false,
    allow_empty: true,
};

const REPLAY_APEX_ENTRY: &str = r#"
[[apex]]
id = "vault-replay-e2e"
subsystem = "Vault"
module = "Obend.Vault.Replay"
theorem = "replay_sound"
description = "Vault replay soundness composed over Core evaluation"
"#;

/// Lean tree without obligation classes in which the `replay_sound` apex cone and the
/// `Main.lean` entry point together reach every library module.
fn write_wired_apex_tree(root: &Path) {
    write_rel(
        root,
        "lean/Obend/Core/Step.lean",
        "module\npublic section\nnamespace Obend.Core\ndef evalStep (n : Nat) : Nat := n + 1\ntheorem evalStep_pos (n : Nat) : evalStep n > 0 := by omega\nend Obend.Core\n",
    );
    write_rel(
        root,
        "lean/Obend/Vault/Replay.lean",
        "module\npublic import Obend.Core.Step\npublic section\nnamespace Obend.Vault\ndef replayTick (n : Nat) : Nat := Obend.Core.evalStep n\ntheorem replay_sound (n : Nat) : replayTick n > 0 := Obend.Core.evalStep_pos n\nend Obend.Vault\n",
    );
    write_rel(
        root,
        "lean/Obend/Main.lean",
        "module\nimport Obend.Vault.Replay\ndef main : IO Unit := pure ()\n",
    );
}

/// Apex manifest with top-level `settings` followed by `apex_entries` tables.
fn apex_manifest(settings: &str, apex_entries: &str) -> String {
    format!(
        "version = 1\ntarget_name = \"synthetic-apex\"\nsubsystems = [\"Core\", \"Vault\"]\nentry_points = [\"lean/Obend/Main.lean\"]\n{settings}\n{apex_entries}"
    )
}

fn has_unverified_apex_violation(
    rep: &obb_judge::pipeline::PipelineReport,
    message_part: &str,
) -> bool {
    rep.violations
        .iter()
        .any(|v| v.kind == "unverified_apex_manifest" && v.message.contains(message_part))
}

#[test]
fn pipeline_strict_separates_zero_theorem_declarations_from_undeclared_theorems() {
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();
    let (code, empty) = pipeline_cli_json(root, &["--strict"]);
    assert_eq!(code, Some(2));
    assert_eq!(empty["ledger_basis"]["kind"], "zero_declarations");
    assert!(check_pipeline_with_options(&root.join("nonexistent"), ALLOW_EMPTY).is_err());

    // Library definitions only; theorems under test-only paths are not counted
    write_rel(
        root,
        "lean/Obend/Teeth/Smoke.lean",
        "theorem smoke : True := True.intro\n",
    );
    write_rel(
        root,
        "lean/Obend/Core/Defs.lean",
        "module\npublic section\nnamespace Obend.Core\ndef idNat (n : Nat) : Nat := n\nexample : idNat 2 = 2 := rfl\nend Obend.Core\n",
    );
    write_rel(
        root,
        "lean/tests/CoreTest.lean",
        "import Obend.Core.Defs\ntheorem idNat_self (n : Nat) : Obend.Core.idNat n = n := rfl\n",
    );
    write_rel(
        root,
        "lean/Obend/Core/DefsTests.lean",
        "module\nimport Obend.Core.Defs\ntheorem idNat_two : Obend.Core.idNat 2 = 2 := rfl\n",
    );

    let rep_zero = check_pipeline_with_options(root, STRICT).unwrap();
    assert_eq!(rep_zero.ledger_basis, PipelineLedgerBasis::ZeroDeclarations);
    assert_eq!(rep_zero.theorem_declaration_count, 0);
    assert_eq!(rep_zero.stage, PipelineStage::Undeclared);
    assert!(!rep_zero.passed);
    assert!(!rep_zero.allow_empty_override);

    let (code, json) = pipeline_cli_json(root, &["--strict"]);
    assert_eq!(code, Some(2));
    assert_eq!(json["ledger_basis"]["kind"], "zero_declarations");
    assert_eq!(json["theorem_declaration_count"], 0);
    assert_eq!(json["allow_empty_override"], false);

    let (code, stdout) = pipeline_cli_stdout(root, &["--strict"]);
    assert_eq!(code, Some(2));
    assert!(
        stdout.contains("ledger_basis: zero_declarations | theorem_declarations=0"),
        "{stdout}"
    );
    assert!(
        stdout.contains("[FAIL] `--strict` is set, and 0 theorem declarations were found"),
        "{stdout}"
    );

    // One library theorem, with neither obligation classes nor an Apex manifest
    write_rel(
        root,
        "lean/Obend/Core/Lemma.lean",
        "module\npublic import Obend.Core.Defs\npublic section\nnamespace Obend.Core\nlemma idNat_eq (n : Nat) : idNat n = n := rfl\nend Obend.Core\n",
    );
    let rep_undeclared = check_pipeline_with_options(root, STRICT).unwrap();
    assert_eq!(
        rep_undeclared.ledger_basis,
        PipelineLedgerBasis::UndeclaredTheorems
    );
    assert_eq!(rep_undeclared.theorem_declaration_count, 1);
    assert_eq!(rep_undeclared.stage, PipelineStage::Undeclared);
    assert!(!rep_undeclared.passed);

    let (code, json) = pipeline_cli_json(root, &["--strict"]);
    assert_eq!(code, Some(2));
    assert_eq!(json["ledger_basis"]["kind"], "undeclared_theorems");
    assert_eq!(json["theorem_declaration_count"], 1);

    let (code, stdout) = pipeline_cli_stdout(root, &["--strict"]);
    assert_eq!(code, Some(2));
    assert!(
        stdout.contains(
            "[FAIL] `--strict` is set, and 1 theorem declaration(s) have neither obligation classes"
        ),
        "{stdout}"
    );
    let (code, stdout) = pipeline_cli_stdout(root, &["--require-sealed"]);
    assert_eq!(code, Some(2));
    assert!(
        stdout.contains(
            "[FAIL] `--require-sealed` is set, and 1 theorem declaration(s) have neither"
        ),
        "{stdout}"
    );
}

#[test]
fn pipeline_records_allow_empty_override_for_release_consumers() {
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();
    write_rel(
        root,
        "lean/Obend/Core/Plain.lean",
        "module\npublic section\nnamespace Obend.Core\ndef addOne (n : Nat) : Nat := n + 1\ntheorem addOne_pos (n : Nat) : addOne n > 0 := Nat.succ_pos n\nend Obend.Core\n",
    );

    let rep = check_pipeline_with_options(
        root,
        PipelineCheckOptions {
            strict: true,
            allow_empty: true,
        },
    )
    .unwrap();
    assert_eq!(rep.ledger_basis, PipelineLedgerBasis::AllowEmptyOverride);
    assert_eq!(rep.stage, PipelineStage::StageBSealed);
    assert!(rep.passed);
    assert!(rep.allow_empty_override);
    assert_eq!(rep.theorem_declaration_count, 1);

    let (code, json) = pipeline_cli_json(root, &["--allow-empty", "--require-sealed"]);
    assert_eq!(code, Some(0));
    assert_eq!(json["stage"], "STAGE_B_SEALED");
    assert_eq!(json["allow_empty_override"], true);
    assert_eq!(json["ledger_basis"]["kind"], rep.ledger_basis.as_str());

    let (code, stdout) = pipeline_cli_stdout(root, &["--allow-empty"]);
    assert_eq!(code, Some(0));
    assert!(
        stdout.contains("ledger_basis: allow_empty_override | theorem_declarations=1"),
        "{stdout}"
    );
    assert!(stdout.contains("[ALLOW-EMPTY OVERRIDE]"), "{stdout}");

    assert!(stdout.contains("allow_empty_override: true"), "{stdout}");

    // Without the flag the same tree is not sealed, and no override is claimed
    let plain = check_pipeline(root).unwrap();
    assert_eq!(plain.ledger_basis, PipelineLedgerBasis::UndeclaredTheorems);
    assert_eq!(plain.stage, PipelineStage::Undeclared);
    assert!(!plain.allow_empty_override);
    let (_, stdout) = pipeline_cli_stdout(root, &[]);
    assert!(!stdout.contains("[ALLOW-EMPTY OVERRIDE]"), "{stdout}");

    // A failed run is not an override seal, even with the flag
    write_rel(
        root,
        "lean/Obend/Core/Smuggled.lean",
        "module\npublic section\nnamespace Obend.Core\ntheorem shortcut (n : Nat) : n = n := by\n  sorry\nend Obend.Core\n",
    );
    let failed = check_pipeline_with_options(root, ALLOW_EMPTY).unwrap();
    assert_eq!(failed.stage, PipelineStage::Failed);
    assert_eq!(failed.ledger_basis, PipelineLedgerBasis::AllowEmptyOverride);
    assert!(!failed.allow_empty_override);
}

#[test]
fn pipeline_seals_verified_apex_manifest_without_obligation_classes() {
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();
    write_wired_apex_tree(root);
    write_rel(
        root,
        "quarry/obend-apex.toml",
        &apex_manifest("", REPLAY_APEX_ENTRY),
    );

    let rep = check_pipeline_with_options(root, STRICT).unwrap();
    assert!(rep.violations.is_empty(), "{:?}", rep.violations);
    assert_eq!(
        rep.ledger_basis,
        PipelineLedgerBasis::ApexManifest {
            manifest_path: "quarry/obend-apex.toml".to_string(),
            registered_apex_count: 1,
            valid_apex_count: 1,
            unwired_island_count: 0,
        }
    );
    assert_eq!(rep.total_obligations, 0);
    assert_eq!(rep.theorem_declaration_count, 2);
    assert_eq!(rep.stage, PipelineStage::StageBSealed);
    assert!(rep.passed && rep.ready_for_claimed);
    assert!(!rep.allow_empty_override);

    let expected_basis = serde_json::json!({
        "kind": "apex_manifest",
        "manifest_path": "quarry/obend-apex.toml",
        "registered_apex_count": 1,
        "valid_apex_count": 1,
        "unwired_island_count": 0,
    });
    for flags in [
        &["--strict", "--require-sealed"][..],
        &["--strict", "--require-sealed", "--allow-empty"],
    ] {
        let (code, json) = pipeline_cli_json(root, flags);
        assert_eq!(code, Some(0), "{flags:?}: {json}");
        assert_eq!(json["stage"], "STAGE_B_SEALED");
        assert_eq!(json["allow_empty_override"], false);
        assert_eq!(json["ledger_basis"], expected_basis);
    }
    let (code, stdout) = pipeline_cli_stdout(root, &["--strict", "--require-sealed"]);
    assert_eq!(code, Some(0));
    assert!(
        stdout.contains(
            "ledger_basis: apex_manifest quarry/obend-apex.toml (apex_valid=1/1 unwired_leaf_islands=0) | theorem_declarations=2"
        ),
        "{stdout}"
    );
    assert!(!stdout.contains("[ALLOW-EMPTY OVERRIDE]"), "{stdout}");

    // `quarry/obend-apex.toml` stays authoritative beside other `quarry/*-apex.toml` files ...
    let missing_theorem_entry = REPLAY_APEX_ENTRY.replace("replay_sound", "replay_complete");
    write_rel(
        root,
        "quarry/draft-apex.toml",
        &apex_manifest("", &missing_theorem_entry),
    );
    let rep_beside = check_pipeline_with_options(root, STRICT).unwrap();
    assert_eq!(rep_beside.stage, PipelineStage::StageBSealed);
    assert_eq!(rep_beside.ledger_basis, rep.ledger_basis);

    // ... and a root `obb-apex.toml` outranks both: the root manifest is the one verified
    write_rel(
        root,
        "obb-apex.toml",
        &apex_manifest("", &missing_theorem_entry),
    );
    let rep_root = check_pipeline_with_options(root, STRICT).unwrap();
    assert_eq!(rep_root.stage, PipelineStage::Failed);
    assert!(
        matches!(&rep_root.ledger_basis, PipelineLedgerBasis::ApexManifest { manifest_path, valid_apex_count: 0, .. } if manifest_path == "obb-apex.toml"),
        "{:?}",
        rep_root.ledger_basis
    );

    // A single `quarry/*-apex.toml` is found under any target name
    let named = tempfile::tempdir().unwrap();
    write_wired_apex_tree(named.path());
    write_rel(
        named.path(),
        "quarry/replay-apex.toml",
        &apex_manifest("", REPLAY_APEX_ENTRY),
    );
    let rep_named = check_pipeline_with_options(named.path(), STRICT).unwrap();
    assert_eq!(rep_named.stage, PipelineStage::StageBSealed);
    assert!(
        matches!(&rep_named.ledger_basis, PipelineLedgerBasis::ApexManifest { manifest_path, .. } if manifest_path == "quarry/replay-apex.toml"),
        "{:?}",
        rep_named.ledger_basis
    );
}

#[test]
fn pipeline_refuses_unverified_apex_manifest_even_under_allow_empty() {
    // 1. Planted unwired leaf island: counted without a cap, refused under `--strict`
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();
    write_wired_apex_tree(root);
    write_rel(
        root,
        "quarry/obend-apex.toml",
        &apex_manifest("", REPLAY_APEX_ENTRY),
    );
    write_rel(
        root,
        "lean/Obend/Vault/Orphan.lean",
        "module\npublic section\nnamespace Obend.Vault\ntheorem orphan_refl (n : Nat) : n = n := rfl\nend Obend.Vault\n",
    );

    let uncapped = check_pipeline(root).unwrap();
    assert_eq!(uncapped.stage, PipelineStage::StageBSealed);
    assert!(
        matches!(
            uncapped.ledger_basis,
            PipelineLedgerBasis::ApexManifest {
                unwired_island_count: 1,
                ..
            }
        ),
        "{:?}",
        uncapped.ledger_basis
    );

    let strict = check_pipeline_with_options(root, STRICT).unwrap();
    assert_eq!(strict.stage, PipelineStage::Failed);
    assert!(!strict.passed && !strict.allow_empty_override);
    assert!(
        has_unverified_apex_violation(&strict, "Unwired leaf islands (1) exceed allowed cap (0)"),
        "{:?}",
        strict.violations
    );

    for flags in [
        &["--strict"][..],
        &["--allow-empty"],
        &["--strict", "--allow-empty"],
    ] {
        let (code, json) = pipeline_cli_json(root, flags);
        assert_eq!(code, Some(2), "{flags:?}: {json}");
        assert_eq!(json["stage"], "FAILED");
        assert_eq!(json["allow_empty_override"], false);
        assert_eq!(json["ledger_basis"]["kind"], "apex_manifest");
        assert_eq!(json["ledger_basis"]["unwired_island_count"], 1);
        assert!(
            json["violations"]
                .as_array()
                .unwrap()
                .iter()
                .any(|v| v["kind"] == "unverified_apex_manifest"),
            "{json}"
        );
    }

    // 2. The manifest's own island cap also binds without either flag
    write_rel(
        root,
        "quarry/obend-apex.toml",
        &apex_manifest("max_unwired_islands = 0", REPLAY_APEX_ENTRY),
    );
    let (code, json) = pipeline_cli_json(root, &[]);
    assert_eq!(code, Some(2), "{json}");
    assert_eq!(json["stage"], "FAILED");
    assert_eq!(json["allow_empty_override"], false);

    // 3. Missing apex theorem: refused under `--strict` and under `--allow-empty`
    let missing = tempfile::tempdir().unwrap();
    write_wired_apex_tree(missing.path());
    write_rel(
        missing.path(),
        "quarry/obend-apex.toml",
        &apex_manifest(
            "",
            &REPLAY_APEX_ENTRY.replace("replay_sound", "replay_complete"),
        ),
    );
    for opts in [STRICT, ALLOW_EMPTY] {
        let rep = check_pipeline_with_options(missing.path(), opts).unwrap();
        assert_eq!(rep.stage, PipelineStage::Failed, "{opts:?}");
        assert!(!rep.passed && !rep.allow_empty_override, "{opts:?}");
        assert!(
            matches!(
                rep.ledger_basis,
                PipelineLedgerBasis::ApexManifest {
                    registered_apex_count: 1,
                    valid_apex_count: 0,
                    ..
                }
            ),
            "{:?}",
            rep.ledger_basis
        );
        assert!(
            has_unverified_apex_violation(&rep, "theorem `replay_complete` not found"),
            "{:?}",
            rep.violations
        );
    }
    let (code, stdout) = pipeline_cli_stdout(missing.path(), &["--allow-empty"]);
    assert_eq!(code, Some(2));
    assert!(
        stdout.contains("[FAIL][unverified_apex_manifest] quarry/obend-apex.toml"),
        "{stdout}"
    );
    assert!(!stdout.contains("[ALLOW-EMPTY OVERRIDE]"), "{stdout}");

    // 4. A manifest registering no `[[apex]]` theorem cannot seal anything
    write_rel(
        missing.path(),
        "quarry/obend-apex.toml",
        &apex_manifest("", ""),
    );
    let rep_unregistered = check_pipeline_with_options(missing.path(), ALLOW_EMPTY).unwrap();
    assert_eq!(rep_unregistered.stage, PipelineStage::Failed);
    assert!(
        matches!(
            rep_unregistered.ledger_basis,
            PipelineLedgerBasis::ApexManifest {
                registered_apex_count: 0,
                ..
            }
        ),
        "{:?}",
        rep_unregistered.ledger_basis
    );
    assert!(
        has_unverified_apex_violation(&rep_unregistered, "registers zero `[[apex]]` theorems"),
        "{:?}",
        rep_unregistered.violations
    );

    for invalid in ["", "this is not toml"] {
        write_rel(missing.path(), "quarry/obend-apex.toml", invalid);
        let (code, rep) = pipeline_cli_json(missing.path(), &["--allow-empty"]);
        assert_eq!(code, Some(2));
        assert_eq!(rep["stage"], "FAILED");
        assert_eq!(rep["allow_empty_override"], false);
        assert_eq!(rep["violations"][0]["kind"], "unverified_apex_manifest");
    }

    // 5. Several `quarry/*-apex.toml` without an authoritative name are refused, not guessed
    let ambiguous = tempfile::tempdir().unwrap();
    write_wired_apex_tree(ambiguous.path());
    for rel in ["quarry/core-apex.toml", "quarry/vault-apex.toml"] {
        write_rel(ambiguous.path(), rel, &apex_manifest("", REPLAY_APEX_ENTRY));
    }
    let rep_ambiguous = check_pipeline_with_options(ambiguous.path(), ALLOW_EMPTY).unwrap();
    assert_eq!(rep_ambiguous.stage, PipelineStage::Failed);
    assert!(
        matches!(&rep_ambiguous.ledger_basis, PipelineLedgerBasis::ApexManifest { manifest_path, .. } if manifest_path == "quarry/*-apex.toml"),
        "{:?}",
        rep_ambiguous.ledger_basis
    );
    assert!(
        has_unverified_apex_violation(
            &rep_ambiguous,
            "quarry/core-apex.toml, quarry/vault-apex.toml"
        ),
        "{:?}",
        rep_ambiguous.violations
    );
}

#[cfg(unix)]
#[test]
fn pipeline_rejects_unreadable_manifest_candidates_before_fallback() {
    use std::os::unix::fs::symlink;

    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();
    write_wired_apex_tree(root);
    for rel in [
        "quarry/project-apex.toml",
        "quarry/obend-apex.toml",
        "obb-apex.toml",
    ] {
        let path = root.join(rel);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        // Each broken higher-priority entry must also outrank the valid lower one.
        symlink("missing.toml", &path).unwrap();
        let (code, rep) = pipeline_cli_json(root, &["--allow-empty"]);
        assert_eq!(code, Some(2), "{rel}: {rep}");
        assert_eq!(rep["ledger_basis"]["manifest_path"], rel);
        assert_eq!(rep["violations"][0]["kind"], "unverified_apex_manifest");
        assert_eq!(rep["allow_empty_override"], false);
        fs::remove_file(path).unwrap();
        write_rel(root, rel, &apex_manifest("", REPLAY_APEX_ENTRY));
    }
}

#[test]
fn pipeline_checks_entire_apex_cone_for_sorry_and_custom_axioms() {
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();
    write_wired_apex_tree(root);
    write_rel(root, "obb-apex.toml", &apex_manifest("", REPLAY_APEX_ENTRY));
    for (source, diagnostic) in [
        (
            "theorem replay_sound (_ : (show Type from by sorry)) : True := True.intro",
            "1 sorry site(s)",
        ),
        (
            "-- fixture kept\ntheorem replay_sound : True := by sorry",
            "1 sorry site(s)",
        ),
        (
            "-- fixture kept\naxiom trusted : True\ntheorem replay_sound : True := trusted",
            "1 custom axiom(s)",
        ),
    ] {
        write_rel(
            root,
            "lean/Obend/Vault/Replay.lean",
            &format!(
                "module\npublic import Obend.Core.Step\npublic section\nnamespace Obend.Vault\n{source}\nend Obend.Vault\n"
            ),
        );
        let rep = check_pipeline_with_options(root, ALLOW_EMPTY).unwrap();
        assert_eq!(rep.stage, PipelineStage::Failed);
        assert!(
            has_unverified_apex_violation(&rep, diagnostic),
            "{:?}",
            rep.violations
        );
        assert!(!rep.allow_empty_override);
    }
}

#[test]
fn pipeline_verifies_apex_against_the_supplied_index() {
    use obb_judge::pipeline::check_pipeline_with_index_and_options;
    use obb_lint::lean_index::build_lean_index;

    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();
    write_wired_apex_tree(root);
    write_rel(root, "obb-apex.toml", &apex_manifest("", REPLAY_APEX_ENTRY));
    let index = build_lean_index(root);
    fs::remove_file(root.join("lean/Obend/Vault/Replay.lean")).unwrap();
    let snapshot = check_pipeline_with_index_and_options(root.to_str().unwrap(), &index, STRICT);
    assert_eq!(snapshot.stage, PipelineStage::StageBSealed);
    assert_eq!(snapshot.theorem_declaration_count, 2);
    let fresh = check_pipeline_with_options(root, STRICT).unwrap();
    assert_eq!(fresh.stage, PipelineStage::Failed);
    assert!(has_unverified_apex_violation(&fresh, "not found"));
}

#[test]
fn broker_mock_ssh_probes_zfs_arc_runaways_routes_targets_and_batches_seeded_lake_builds() {
    // `hbox` has ZFS ARC reclaimable memory (48 GiB ARC over c_min on top of 20 GiB MemAvailable -> ~68 GiB free),
    // PLUS a planted 45-minute (2,700s > 1,800s) runaway `lean` process and heavy load!
    // `bb2` is idle with 94 GiB free and 0 runaways -> `bb2` must win `recommended_general_host`!
    let zfs_48gib_bytes: u64 = 48 * 1024 * 1024 * 1024;
    let hbox_stdout = format!(
        "OBB_META|24|18.50 16.00 12.00|128974848 20971520|{zfs_48gib_bytes}|94371840|1\n\
         OBB_PROC|41230|2700|14680064|lean|lean --make Obend/Core/Proofs/Adequacy/Sound.lean\n\
         OBB_PROC|41999|120|1048576|lake|lake build Obend.Vault.Replay\n"
    );
    let bb2_stdout = "OBB_META|32|1.25 1.10 0.90|127926272 98566144|0|188743680|1\n".to_string();

    let mock = MockSshExecutor::new()
        .with_host_output(
            "hbox",
            RemoteCmdOutput {
                exit_code: 0,
                stdout: hbox_stdout,
                stderr: String::new(),
                duration_ms: 4,
            },
        )
        .with_host_output(
            "bb2",
            RemoteCmdOutput {
                exit_code: 0,
                stdout: bb2_stdout,
                stderr: String::new(),
                duration_ms: 3,
            },
        );

    let hosts = vec!["bb2".to_string(), "hbox".to_string()];
    let probe = probe_hosts(&hosts, &mock, false);
    assert_eq!(probe.recommended_general_host.as_deref(), Some("bb2"));

    let hbox = probe.hosts.iter().find(|h| h.host == "hbox").unwrap();
    assert!(hbox.reachable);
    assert_eq!(hbox.zfs_arc_reclaimable_gib, 48.0);
    assert!(
        (hbox.mem_free_gib - 68.0).abs() < 0.5,
        "hbox free GiB must credit ZFS ARC reclaimable memory, got {}",
        hbox.mem_free_gib
    );
    assert_eq!(hbox.active_lean_lake_procs, 2);
    assert_eq!(hbox.runaway_procs.len(), 1);
    assert_eq!(hbox.runaway_procs[0].pid, 41230);
    assert_eq!(hbox.runaway_procs[0].elapsed_secs, 2700);

    // Plan mixed targets:
    // - 2 GPU/RDNA2/Litmus targets -> batched onto `hbox`
    // - 2 Yosys/Verilator/FABulous targets -> batched onto `bb2`
    // - 2 General Lean targets -> routed to healthier host (`bb2`) and batched into the SAME `bb2` `lake build`!
    let targets = vec![
        "Obend.Hardware.Rdna2.Decode".to_string(),
        "litmus-check".to_string(),
        "Obend.Hardware.Fabulous.Fabric".to_string(),
        "emit-sv".to_string(),
        "lean/Obend/Vault/Replay.lean".to_string(),
        "Obend.Leaf.Emit".to_string(),
    ];
    let opts = BuildPlanOptions {
        host_choice: HostChoice::Auto,
        timeout_secs: 450,
        max_rss_gb: 14,
        dry_run: false,
        exec: true,
        repo_root: Some(workspace_root()),
        target_commit: None,
        remote_seed_root: None,
    };

    let plan = plan_build(&targets, &opts, &mock).unwrap();
    assert_eq!(plan.total_targets, 6);
    assert_eq!(
        plan.total_batches, 2,
        "must batch into 1 `bb2` batch + 1 `hbox` batch"
    );

    let route_map: std::collections::HashMap<_, _> = plan
        .routing
        .iter()
        .map(|r| {
            (
                r.lake_target.as_str(),
                (r.assigned_host.as_str(), r.workload_class),
            )
        })
        .collect();
    assert_eq!(
        route_map["Obend.Hardware.Rdna2.Decode"],
        ("hbox", TargetWorkloadClass::GpuRdna2Litmus)
    );
    assert_eq!(
        route_map["litmus-check"],
        ("hbox", TargetWorkloadClass::GpuRdna2Litmus)
    );
    assert_eq!(
        route_map["Obend.Hardware.Fabulous.Fabric"],
        ("bb2", TargetWorkloadClass::YosysVerilatorEda)
    );
    assert_eq!(
        route_map["emit-sv"],
        ("bb2", TargetWorkloadClass::YosysVerilatorEda)
    );
    assert_eq!(
        route_map["Obend.Vault.Replay"],
        ("bb2", TargetWorkloadClass::GeneralLean)
    );
    assert_eq!(
        route_map["Obend.Leaf.Emit"],
        ("bb2", TargetWorkloadClass::GeneralLean)
    );

    let bb2_batch = plan.batches.iter().find(|b| b.host == "bb2").unwrap();
    assert_eq!(
        bb2_batch.batched_lake_command,
        "lake build Obend.Hardware.Fabulous.Fabric emit-sv Obend.Vault.Replay Obend.Leaf.Emit"
    );
    assert!(bb2_batch.remote_recipe.contains("cp -R --reflink=auto"));
    assert!(!bb2_batch.remote_recipe.contains("cp -al"));
    assert!(
        bb2_batch
            .remote_recipe
            .contains("git -C \"$BASE_REPO\" fetch")
    );
    assert!(
        bb2_batch
            .remote_recipe
            .contains("checkout --detach --force")
    );
    assert!(
        bb2_batch
            .remote_recipe
            .contains("SWARM_MEM_MAX=\"14G\" exec swarm-build timeout --kill-after=10s 450s")
    );
    assert!(bb2_batch.remote_recipe.contains("ulimit -v"));
    assert!(
        bb2_batch
            .remote_recipe
            .contains("kill -TERM -- \"-$BUILD_PGID\"")
    );
    assert!(bb2_batch.remote_recipe.contains("pkill -TERM -P $$"));
    assert_eq!(bb2_batch.execution.as_ref().unwrap().exit_code, 0);

    let hbox_batch = plan.batches.iter().find(|b| b.host == "hbox").unwrap();
    assert_eq!(
        hbox_batch.batched_lake_command,
        "lake build Obend.Hardware.Rdna2.Decode litmus-check"
    );
    assert_eq!(hbox_batch.seed_pool_dir, "/othersys/obb-seeds/obend");

    // Verify CLI `--dry-run --json` works offline with zero SSH calls
    let cli_plan = Command::new(obb_bin())
        .args([
            "broker",
            "plan-build",
            "Obend.Vault.Replay",
            "Obend.Hardware.Rdna2.Decode",
            "--dry-run",
            "--json",
        ])
        .output()
        .unwrap();
    assert_eq!(cli_plan.status.code(), Some(0));
    let parsed_json: serde_json::Value = serde_json::from_slice(&cli_plan.stdout).unwrap();
    assert_eq!(parsed_json["total_targets"], 2);
}
