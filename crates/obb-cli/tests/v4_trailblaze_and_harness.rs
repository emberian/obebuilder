//! End-to-end CLI & library verification suite for `Obb-v4`:
//! 1. `lean/obligation-tautological-field`: catches Stage-A tautological field signatures inside
//!    `*Obligations`, `*Ledger`, and `@[obb_obligation]` classes (modeled on `Trailblaze` catches:
//!    `PolisObligations.darkBazaarSameOpeningZeroKnowledge`, `ClusterGovObligations.teeHardwareRootAttested`,
//!    `LeanFpgaObligations.siliconSimpKernelProofSound`, `ZkStripeObligations.sableKernelArithmeticSound`,
//!    unused quantified domain binders, and non-existential `*Extract` fields).
//! 2. `lean/judge-empty-fragment`: catches `Fragment := fun _ => False` and `refutes := fun _ => false`
//!    in `Judge` instances and builders (`SilverWorkflow.toJudge`).
//! 3. `lean/excessive-decl-expose`: flags `> 80`-line `module` files with `> 12` per-declaration
//!    `@[expose]` attributes (`Warning` by default, `Error` under `--strict-expose`).
//! 4. `obb harness {list, install, check}`: materializes and validates `AGENTS.md`, `GEMINI.md`,
//!    `CLAUDE.md`, `.agents/skills/*/SKILL.md`, and `.claude/skills/*/SKILL.md` with byte budgets,
//!    YAML frontmatter, SHA-256 markers, drift refusal (`exit 2`), and zero `obb lint` false positives.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

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

#[test]
fn cli_lint_catches_trailblaze_stage_a_cosplay_judge_evasion_and_excessive_expose() {
    let repo = tempfile::tempdir().unwrap();

    // Build a >80-line module with:
    // - Trailblaze-modeled Stage-A cosplay obligations
    // - Judge empty-fragment builder (`SilverWorkflow.toJudge`)
    // - >12 per-declaration `@[expose]` attributes
    let mut lean_src = String::from(
        r#"module

public section

namespace Obend.Trailblaze

@[expose] structure Opening where
  toNat : Nat

@[expose] structure TeeQuote where
  enclaveDigest : Nat
  pcrDigest : Nat

@[expose] structure SimpCert where
  lhsHash : UInt64
  rhsHash : UInt64

@[expose] structure SableParams where
  modulusP : Nat

@[expose] def checkSableNoWrap (b : SableParams) : Bool := b.modulusP > 0

@[expose] structure Judge (α : Type) where
  Fragment : α → Prop
  refutes : α → Bool

@[expose] structure SilverWorkflow (α : Type) where
  label : String

@[expose] def SilverWorkflow.toJudge (_wf : SilverWorkflow α) : Judge α where
  Fragment := fun _w => False
  refutes := fun _clause => false

class PolisObligations (Carrier : Type) where
  darkBazaarSameOpeningZeroKnowledge :
    ∀ (o1 o2 : Opening), o1 = o2 → o1.toNat = o2.toNat

class ClusterGovObligations (Carrier : Type) where
  teeHardwareRootAttested :
    ∀ (q : TeeQuote) (p : Bool) (r : Bool),
      p = true → r = true → (p = true ∧ r = true)

class LeanFpgaObligations (Carrier : Type) where
  siliconSimpKernelProofSound :
    ∀ (c : SimpCert), c.lhsHash = c.rhsHash → c.lhsHash == c.rhsHash = true
  cofibMeetSound :
    ∀ (φ ψ : SimpCert), (φ.meet ψ).implies φ = true
  unusedBinderObligation :
    ∀ (unusedGhost : SimpCert) (c : SimpCert), c.lhsHash = c.rhsHash → c.rhsHash = c.lhsHash
  knowledgeSoundnessExtract :
    ∀ (c : SimpCert), c.lhsHash = c.lhsHash

class ZkStripeObligations (Carrier : Type) where
  sableKernelArithmeticSoundGkr :
    ∀ (b : SableParams), checkSableNoWrap b = true → b.modulusP > 0

"#,
    );

    for i in 0..10 {
        lean_src.push_str(&format!(
            "@[expose] def helperExpose{i} (n : Nat) : Nat :=\n  let a := n + {i}\n  let b := a + 1\n  b\n\n"
        ));
    }
    lean_src.push_str("end Obend.Trailblaze\n");
    assert!(lean_src.lines().count() > 80);

    write_rel(repo.path(), "lean/Obend/Trailblaze/Cosplay.lean", &lean_src);

    // 1. Default `obb lint --json` (without `--strict-expose`):
    //    `obligation-tautological-field` = Error, `judge-empty-fragment` = Warning, `excessive-decl-expose` = Warning
    let out_default = Command::new(obb_bin())
        .args(["lint", "--repo", repo.path().to_str().unwrap(), "--json"])
        .output()
        .expect("obb lint default");
    assert!(out_default.status.success());
    let json_default: serde_json::Value =
        serde_json::from_slice(&out_default.stdout).expect("valid lint json");
    let findings = json_default["findings"].as_array().unwrap();

    let tauto_errors: Vec<_> = findings
        .iter()
        .filter(|f| f["rule_id"] == "lean/obligation-tautological-field")
        .collect();
    assert!(
        tauto_errors.len() >= 5,
        "expected >= 5 tautological obligation errors, got {}: {tauto_errors:#?}",
        tauto_errors.len()
    );
    assert!(tauto_errors.iter().all(|f| f["severity"] == "error"));

    let judge_warns: Vec<_> = findings
        .iter()
        .filter(|f| f["rule_id"] == "lean/judge-empty-fragment")
        .collect();
    assert_eq!(
        judge_warns.len(),
        2,
        "expected Fragment + refutes warnings: {judge_warns:#?}"
    );

    let expose_warns: Vec<_> = findings
        .iter()
        .filter(|f| f["rule_id"] == "lean/excessive-decl-expose")
        .collect();
    assert_eq!(expose_warns.len(), 1);
    assert_eq!(expose_warns[0]["severity"], "warning");

    // 2. With `--strict --strict-expose`, `excessive-decl-expose` escalates to `error` and CLI exits 2
    let out_strict = Command::new(obb_bin())
        .args([
            "lint",
            "--repo",
            repo.path().to_str().unwrap(),
            "--strict",
            "--strict-expose",
            "--json",
        ])
        .output()
        .expect("obb lint --strict --strict-expose");
    assert_eq!(out_strict.status.code(), Some(2));
    let json_strict: serde_json::Value =
        serde_json::from_slice(&out_strict.stdout).expect("valid strict lint json");
    let strict_expose_findings: Vec<_> = json_strict["findings"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|f| f["rule_id"] == "lean/excessive-decl-expose")
        .collect();
    assert_eq!(strict_expose_findings.len(), 1);
    assert_eq!(strict_expose_findings[0]["severity"], "error");
}

#[test]
fn cli_harness_install_check_list_and_clean_lint_coexistence() {
    let repo = tempfile::tempdir().unwrap();

    // Seed a clean genuine Stage-A Lean module so `obb lint` scans both Lean and root Markdown
    write_rel(
        repo.path(),
        "lean/Obend/Core/Spec.lean",
        r#"module

public section

namespace Obend.Core

structure HashFn where
  compress : ByteArray → ByteArray

def Collision (H : HashFn) : Prop :=
  ∃ x y : ByteArray, x ≠ y ∧ H.compress x = H.compress y

def VerifyCommitment (H : HashFn) (c m : ByteArray) : Bool :=
  decide (H.compress m == c)

class VaultObligations (Carrier : Type) where
  bindingUpToCollision :
    ∀ (H : HashFn) (c m1 m2 : ByteArray),
      VerifyCommitment H c m1 = true →
      VerifyCommitment H c m2 = true →
      m1 = m2 ∨ Collision H
  witnessExtract :
    ∀ (H : HashFn) (c : ByteArray),
      (∃ m, VerifyCommitment H c m = true) →
      ∃ w, VerifyCommitment H c w = true ∨ Collision H

end Obend.Core
"#,
    );

    // 1. `obb harness list --json`
    let list_out = Command::new(obb_bin())
        .args(["harness", "list", "--json"])
        .output()
        .expect("obb harness list");
    assert!(list_out.status.success());
    let list_json: serde_json::Value = serde_json::from_slice(&list_out.stdout).unwrap();
    assert_eq!(list_json["total_artifacts"], 11);
    assert_eq!(list_json["root_rules"], 3);
    assert_eq!(list_json["skills"], 8);

    // 2. `obb harness check` before install -> exit 2
    let pre_check = Command::new(obb_bin())
        .args(["harness", "check", "--repo", repo.path().to_str().unwrap()])
        .output()
        .expect("pre-install check");
    assert_eq!(pre_check.status.code(), Some(2));

    // 3. Unmanaged `AGENTS.md` refuses `install` without `--force`, succeeds with `--force`
    write_rel(repo.path(), "AGENTS.md", "# Hand-written unmanaged file\n");
    let refused_install = Command::new(obb_bin())
        .args([
            "harness",
            "install",
            "--repo",
            repo.path().to_str().unwrap(),
            "--json",
        ])
        .output()
        .expect("refused install");
    assert_eq!(refused_install.status.code(), Some(2));

    let forced_install = Command::new(obb_bin())
        .args([
            "harness",
            "install",
            "--repo",
            repo.path().to_str().unwrap(),
            "--force",
            "--json",
        ])
        .output()
        .expect("forced install");
    assert!(forced_install.status.success());
    let install_json: serde_json::Value = serde_json::from_slice(&forced_install.stdout).unwrap();
    assert_eq!(install_json["passed"], true);
    assert_eq!(install_json["files_written"], 11);

    // 4. `obb harness check --repo <tmp> --json` -> exit 0
    let ok_check = Command::new(obb_bin())
        .args([
            "harness",
            "check",
            "--repo",
            repo.path().to_str().unwrap(),
            "--json",
        ])
        .output()
        .expect("post-install check");
    assert!(
        ok_check.status.success(),
        "harness check failed: {}",
        String::from_utf8_lossy(&ok_check.stdout)
    );
    let check_json: serde_json::Value = serde_json::from_slice(&ok_check.stdout).unwrap();
    assert_eq!(check_json["passed"], true);
    assert_eq!(check_json["issues"].as_array().unwrap().len(), 0);

    // 5. `obb lint --repo <tmp> --strict --strict-expose` -> exit 0 (`0` errors, no markdown false positives!)
    let lint_out = Command::new(obb_bin())
        .args([
            "lint",
            "--repo",
            repo.path().to_str().unwrap(),
            "--strict",
            "--strict-expose",
            "--json",
        ])
        .output()
        .expect("obb lint with harness installed");
    assert!(
        lint_out.status.success(),
        "obb lint failed with harness installed: {}",
        String::from_utf8_lossy(&lint_out.stdout)
    );
    let lint_json: serde_json::Value = serde_json::from_slice(&lint_out.stdout).unwrap();
    assert_eq!(lint_json["errors"], 0);

    // 6. Tamper with `.claude/skills/obend-anti-cosplay/SKILL.md` -> `obb harness check` exits 2
    let claude_skill = repo
        .path()
        .join(".claude/skills/obend-anti-cosplay/SKILL.md");
    let mut tampered = fs::read_to_string(&claude_skill).unwrap();
    tampered.push_str("\n<!-- drifted -->\n");
    fs::write(&claude_skill, tampered).unwrap();

    let drift_check = Command::new(obb_bin())
        .args(["harness", "check", "--repo", repo.path().to_str().unwrap()])
        .output()
        .expect("drift check");
    assert_eq!(drift_check.status.code(), Some(2));
}

#[test]
fn cli_single_sequence_harness_warns_by_default_and_errors_under_strict_harnesses_and_apex_check() {
    let repo = tempfile::tempdir().unwrap();

    write_rel(
        repo.path(),
        "lean/Obend/Consensus/TurnOnly.lean",
        r#"module

public section

namespace Obend.Consensus

structure GovState where
  mandateBudget : Nat
  revokedCount : Nat

structure GovTurn where
  spend : Nat

def stepGov (s : GovState) (t : GovTurn) : Option GovState :=
  if t.spend <= s.mandateBudget then
    some { s with mandateBudget := s.mandateBudget - t.spend }
  else
    none

theorem apex_gov_turn_safe (s s' : GovState) (t : GovTurn)
    (h : stepGov s t = some s') :
    s'.mandateBudget <= s.mandateBudget := by
  omega

end Obend.Consensus
"#,
    );

    write_rel(
        repo.path(),
        "apex.toml",
        r#"version = 1
target_name = "obend"

[[apex]]
id = "gov-turn"
subsystem = "Consensus"
module = "Obend.Consensus.TurnOnly"
theorem = "apex_gov_turn_safe"
description = "Single-turn only planted test"
"#,
    );

    // 1. Default `obb lint --strict`: `lean/single-sequence-harness` is `warning`, so `--strict` exits 0
    let default_out = Command::new(obb_bin())
        .args([
            "lint",
            "--repo",
            repo.path().to_str().unwrap(),
            "--strict",
            "--json",
        ])
        .output()
        .expect("default lint");
    assert!(default_out.status.success());
    let default_json: serde_json::Value = serde_json::from_slice(&default_out.stdout).unwrap();
    let st_warns: Vec<_> = default_json["findings"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|f| f["rule_id"] == "lean/single-sequence-harness")
        .collect();
    assert_eq!(st_warns.len(), 1);
    assert_eq!(st_warns[0]["severity"], "warning");

    // 2. `obb lint --strict --strict-harnesses`: escalates to `error` and exits 2
    let strict_h_out = Command::new(obb_bin())
        .args([
            "lint",
            "--repo",
            repo.path().to_str().unwrap(),
            "--strict",
            "--strict-harnesses",
            "--json",
        ])
        .output()
        .expect("strict-harnesses lint");
    assert_eq!(strict_h_out.status.code(), Some(2));
    let strict_h_json: serde_json::Value = serde_json::from_slice(&strict_h_out.stdout).unwrap();
    let st_errs: Vec<_> = strict_h_json["findings"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|f| f["rule_id"] == "lean/single-sequence-harness")
        .collect();
    assert_eq!(st_errs.len(), 1);
    assert_eq!(st_errs[0]["severity"], "error");

    // 3. `obb apex check` ALSO flags single-turn-only `[apex]` theorems and exits 2!
    let apex_fail = Command::new(obb_bin())
        .args([
            "apex",
            "check",
            "--repo",
            repo.path().to_str().unwrap(),
            "--manifest",
            repo.path().join("apex.toml").to_str().unwrap(),
            "--json",
        ])
        .output()
        .expect("apex check single-turn fail");
    assert_eq!(apex_fail.status.code(), Some(2));
    let apex_fail_json: serde_json::Value = serde_json::from_slice(&apex_fail.stdout).unwrap();
    assert_eq!(apex_fail_json["check_passed"], false);

    // 4. Add a multi-turn `List GovTurn` / `ValidTrace` invariant theorem -> both `--strict-harnesses` and `apex check` pass!
    write_rel(
        repo.path(),
        "lean/Obend/Consensus/TurnOnly.lean",
        r#"module

public section

namespace Obend.Consensus

structure GovState where
  mandateBudget : Nat
  revokedCount : Nat

structure GovTurn where
  spend : Nat

def stepGov (s : GovState) (t : GovTurn) : Option GovState :=
  if t.spend <= s.mandateBudget then
    some { s with mandateBudget := s.mandateBudget - t.spend }
  else
    none

def ValidTrace (s : GovState) (ts : List GovTurn) : Prop :=
  ts.length >= 0 ∧ s.mandateBudget >= 0

theorem apex_gov_turn_safe (s s' : GovState) (t : GovTurn)
    (h : stepGov s t = some s') :
    s'.mandateBudget <= s.mandateBudget := by
  omega

theorem gov_multi_turn_trace_safe (s : GovState) (ts : List GovTurn)
    (h : ValidTrace s ts) :
    s.mandateBudget >= 0 := h.2

end Obend.Consensus
"#,
    );

    let strict_h_pass = Command::new(obb_bin())
        .args([
            "lint",
            "--repo",
            repo.path().to_str().unwrap(),
            "--strict",
            "--strict-harnesses",
        ])
        .output()
        .expect("strict-harnesses pass");
    assert!(strict_h_pass.status.success());

    let apex_pass = Command::new(obb_bin())
        .args([
            "apex",
            "check",
            "--repo",
            repo.path().to_str().unwrap(),
            "--manifest",
            repo.path().join("apex.toml").to_str().unwrap(),
        ])
        .output()
        .expect("apex check pass");
    assert!(apex_pass.status.success());
}
