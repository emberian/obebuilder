use obb_core::Severity;

use obb_lint::lean_index::build_lean_index;
use obb_lint::lean_rules::*;
use std::fs;

#[test]
fn obligation_projection_cosplay_unit_planted_faults_and_clean_control() {
    let dir = tempfile::tempdir().unwrap();
    let lean_dir = dir.path().join("lean/Obend/Crypto");
    fs::create_dir_all(&lean_dir).unwrap();
    fs::write(
        lean_dir.join("CanopyCosplay.lean"),
        r#"module
public section
namespace Obend.Crypto

class HypothesisLedger

structure PCS where
  digest : Nat

def hashPCS (p : PCS) : Nat := p.digest
def bothTrue (a b : Bool) : Bool := a && b

class CanopyPCSObligations (C : Type) where
  Fragment : C → Prop
  refl_cosplay : ∀ (x : C), x = x
  congr_cosplay : ∀ (a b : PCS), a = b → hashPCS a = hashPCS b
  bool_cosplay : ∀ (a b : Bool), bothTrue a b = true → a = true
  and_left_cosplay : ∀ (P Q : Prop), P ∧ Q → P
  and_right_tactic : ∀ (P Q : Prop), P ∧ Q → Q
  trivial_witness : C → True

class LedgerBridge (C : Type) extends HypothesisLedger where
  anon_rfl : ∀ (x : C), x = x

instance badCanopy : CanopyPCSObligations PCS where
  Fragment := fun _ => False
  refl_cosplay := fun _ => rfl
  congr_cosplay := fun _ _ h => congrArg hashPCS h
  bool_cosplay := by
    intro a b h
    exact ((Bool.and_eq_true _ _).mp h).1
  and_left_cosplay := fun _ _ h => And.left h
  and_right_tactic := by
    intro _ _ h
    exact And.right h
  trivial_witness := fun _ => trivial

instance badAnonBridge : LedgerBridge PCS := ⟨fun _ => rfl⟩

end Obend.Crypto
"#,
    )
    .unwrap();

    let idx = build_lean_index(dir.path());
    let (findings, _) = run_lean_lints(&idx);
    let cosplay: Vec<_> = findings
        .iter()
        .filter(|f| f.rule_id == "lean/obligation-projection-cosplay")
        .collect();
    assert_eq!(
        cosplay.len(),
        8,
        "all 8 planted cosplay fields (7 where-fields + 1 anonymous ⟨...⟩ field) must fire: {cosplay:#?}"
    );

    // Positive control: substantive theorem-backed instance
    let clean_dir = tempfile::tempdir().unwrap();
    let clean_lean = clean_dir.path().join("lean/Obend/Crypto");
    fs::create_dir_all(&clean_lean).unwrap();
    fs::write(
        clean_lean.join("CanopyReal.lean"),
        r#"module
public section
namespace Obend.Crypto

structure PCS where
  digest : Nat

def NonTrivialPCS (p : PCS) : Prop := p.digest > 0

theorem pcs_digest_nonneg (p : PCS) : p.digest >= 0 :=
  Nat.zero_le p.digest

class CanopyPCSObligations (C : Type) where
  Fragment : C → Prop
  digest_nonneg : ∀ (p : PCS), p.digest >= 0

instance goodCanopy : CanopyPCSObligations PCS where
  Fragment := NonTrivialPCS
  digest_nonneg p := pcs_digest_nonneg p

end Obend.Crypto
"#,
    )
    .unwrap();

    let clean_idx = build_lean_index(clean_dir.path());
    let (clean_findings, _) = run_lean_lints(&clean_idx);
    assert!(
        clean_findings
            .iter()
            .all(|f| f.rule_id != "lean/obligation-projection-cosplay"),
        "clean theorem-backed instance must produce 0 cosplay findings: {clean_findings:#?}"
    );
}

#[test]
fn stage_a_obligation_tautological_field_catches_trailblaze_cosplay_and_passes_real_obligations() {
    let dir = tempfile::tempdir().unwrap();
    let tb_dir = dir.path().join("lean/Obend/Trailblaze");
    fs::create_dir_all(&tb_dir).unwrap();
    fs::write(
        tb_dir.join("CosplayStageA.lean"),
        r#"module
public section
namespace Obend.Trailblaze

class PolisObligations : Prop where
  darkBazaarSameOpeningZeroKnowledge :
    ∀ (commitA commitB : BitVec 256),
      commitA = commitB → commitA.toNat = commitB.toNat
  regularCoveragePullbackStable :
    ∀ (P : PCA) (A B C : Assembly P) (f : TrackedMorphism A C) (g : TrackedMorphism B C),
      (∀ z : C.Carrier, ∃ x : A.Carrier, f.map x = z) →
      ∀ y : B.Carrier, ∃ x : A.Carrier, f.map x = g.map y

class ClusterGovObligations : Prop where
  qwenLogUpGkrSound :
    ∀ (b : IntTensorBound), checkSableNoWrap b = true → b.modulusP > 0
  teeHardwareRootAttested :
    ∀ (step : AriadneStep),
      step.flopsUsed ≤ step.flopsCap →
      step.batchCallTreeRoot ≠ 0 →
      step.flopsUsed ≤ step.flopsCap ∧ step.batchCallTreeRoot ≠ 0

class LeanFpgaObligations : Prop where
  siliconSimpKernelProofSound :
    ∀ (φ ψ : CofibLUT16), (φ.meet ψ).implies φ = true

class CustomAuditLedger : Prop where
  unusedDomainBinder :
    ∀ (salt : BitVec 256) (n : Nat), n > 0 → n >= 0
  trivialTrueTail :
    ∀ (x : Nat), x > 0 → True

@[obb_obligation]
class TaggedSoundnessGate : Prop where
  fnCongr : ∀ (x y : Nat), x = y → hashVal x = hashVal y

end Obend.Trailblaze
"#,
    )
    .unwrap();

    let idx = build_lean_index(dir.path());
    let (findings, _) = run_lean_lints(&idx);
    let tauto: Vec<_> = findings
        .iter()
        .filter(|f| f.rule_id == "lean/obligation-tautological-field")
        .collect();
    assert_eq!(
        tauto.len(),
        8,
        "all 8 planted Stage-A tautological obligation fields must fire: {tauto:#?}"
    );
    assert!(tauto.iter().all(|f| f.severity == Severity::Error));
    for expected_sym in [
        "Obend.Trailblaze.PolisObligations.darkBazaarSameOpeningZeroKnowledge",
        "Obend.Trailblaze.PolisObligations.regularCoveragePullbackStable",
        "Obend.Trailblaze.ClusterGovObligations.qwenLogUpGkrSound",
        "Obend.Trailblaze.ClusterGovObligations.teeHardwareRootAttested",
        "Obend.Trailblaze.LeanFpgaObligations.siliconSimpKernelProofSound",
        "Obend.Trailblaze.CustomAuditLedger.unusedDomainBinder",
        "Obend.Trailblaze.CustomAuditLedger.trivialTrueTail",
        "Obend.Trailblaze.TaggedSoundnessGate.fnCongr",
    ] {
        assert!(
            tauto
                .iter()
                .any(|f| f.symbol.as_deref() == Some(expected_sym)),
            "expected `{expected_sym}` to fire, got: {tauto:#?}"
        );
    }

    // Positive control: genuine commitment binding & completeness obligations produce 0 findings
    let clean_dir = tempfile::tempdir().unwrap();
    let clean_tb = clean_dir.path().join("lean/Obend/Trailblaze");
    fs::create_dir_all(&clean_tb).unwrap();
    fs::write(
        clean_tb.join("RealStageA.lean"),
        r#"module
public section
namespace Obend.Trailblaze

class RealTrailblazeObligations : Prop where
  tlsnAeadCommitmentBinding :
    ∀ (H : Hash) (t₁ t₂ : HttpsSessionNode),
      callTreeDigest H t₁ = callTreeDigest H t₂ →
      t₁ = t₂ ∨ Collision H
  blumPermutationComplete :
    ∀ (online : List MemOp),
      checkChronologicalLog online = true →
      (∀ op ∈ online, op.isWrite = true) →
      ∃ offline : List MemOp, verifyBlumMemory online offline = true
  dualPcsCallTreeExtract :
    ∀ (H : Hash) (pol : ZkStripePolicy) (rcpt : DualPcsCallTreeReceipt),
      verifyDualPcsReceipt H rcpt = true →
      ∃ tree : HttpsSessionNode,
        callTreeDigest H tree = rcpt.committedTreeRoot ∧
        verifyZkStripeCallTree pol tree = true

end Obend.Trailblaze
"#,
    )
    .unwrap();

    let clean_idx = build_lean_index(clean_dir.path());
    let (clean_findings, _) = run_lean_lints(&clean_idx);
    let clean_tauto: Vec<_> = clean_findings
        .iter()
        .filter(|f| f.rule_id == "lean/obligation-tautological-field")
        .collect();
    assert!(
        clean_tauto.is_empty(),
        "genuine Stage-A obligations must produce 0 findings: {clean_tauto:#?}"
    );
}

#[test]
fn judge_empty_fragment_catches_silver_workflow_to_judge_and_passes_inhabited_judge() {
    let dir = tempfile::tempdir().unwrap();
    let tb_dir = dir.path().join("lean/Obend/Trailblaze");
    fs::create_dir_all(&tb_dir).unwrap();
    fs::write(
            tb_dir.join("Obligations.lean"),
            r#"module
public section
namespace Obend.Trailblaze

@[instance_reducible] def SilverWorkflow.toJudge (W : Type) [wf : SilverWorkflow W] : Obend.Judge W Unit where
  Clause := String
  Meaning := fun w _cert => wf.Spec w
  check := fun _grade w _cert => .ok
  sound := by intro _ w _ _; exact wf.silverSound w rfl
  refutes := fun _clause => false
  refuted := by intro _ _ _ _ _ _ hRef; cases hRef
  Fragment := fun _w => False
  complete := by intro _w hFrag; cases hFrag
  mono := by intro _ _ _ _ _ _; rfl

end Obend.Trailblaze
"#,
        )
        .unwrap();

    let idx = build_lean_index(dir.path());
    let (findings, _) = run_lean_lints(&idx);
    let empty_frag: Vec<_> = findings
        .iter()
        .filter(|f| f.rule_id == "lean/judge-empty-fragment")
        .collect();
    assert_eq!(
        empty_frag.len(),
        2,
        "both `refutes := fun _ => false` and `Fragment := fun _ => False` must fire: {empty_frag:#?}"
    );
    assert!(empty_frag.iter().all(|f| f.severity == Severity::Warning));

    // Positive control: inhabited `Fragment` and `refutes := fun _ => true`
    let clean_dir = tempfile::tempdir().unwrap();
    let clean_tb = clean_dir.path().join("lean/Obend/Trailblaze");
    fs::create_dir_all(&clean_tb).unwrap();
    fs::write(
            clean_tb.join("CompleteJudge.lean"),
            r#"module
public section
namespace Obend.Trailblaze

@[instance_reducible] def CompleteSilverWorkflow.toJudge (W : Type) [wf : SilverWorkflow W] : Obend.Judge W Unit where
  Clause := String
  Meaning := fun w _cert => wf.Spec w
  check := fun _grade w _cert => .ok
  sound := by intro _ w _ _; exact wf.silverSound w rfl
  refutes := fun _clause => true
  refuted := by intro _ _ _ _ _ hCheck _; cases hCheck
  Fragment := wf.DecidableFragment
  complete := by intro w hFrag; exact wf.silverComplete w hFrag
  mono := by intro _ _ _ _ _ _; rfl

end Obend.Trailblaze
"#,
        )
        .unwrap();

    let clean_idx = build_lean_index(clean_dir.path());
    let (clean_findings, _) = run_lean_lints(&clean_idx);
    assert!(
        clean_findings
            .iter()
            .all(|f| f.rule_id != "lean/judge-empty-fragment"),
        "inhabited Judge must produce 0 `lean/judge-empty-fragment` findings: {clean_findings:#?}"
    );
}

#[test]
fn excessive_decl_expose_flags_over_12_in_module_and_escalates_with_strict_expose() {
    let dir = tempfile::tempdir().unwrap();
    let tb_dir = dir.path().join("lean/Obend/Trailblaze");
    fs::create_dir_all(&tb_dir).unwrap();

    let mut bad_src = String::from("module\npublic section\nnamespace Obend.Trailblaze\n");
    for i in 0..15 {
        bad_src.push_str(&format!(
            "@[expose] def exposedHelper{i} (x : Nat) : Nat := x + {i}\n"
        ));
    }
    for i in 0..75 {
        bad_src.push_str(&format!("def sealedHelper{i} (x : Nat) : Nat := x + {i}\n"));
    }
    bad_src.push_str("end Obend.Trailblaze\n");
    assert!(bad_src.lines().count() > 80);
    fs::write(tb_dir.join("ExposeSpam.lean"), &bad_src).unwrap();

    let mut clean_src = String::from("module\npublic section\nnamespace Obend.Trailblaze\n");
    for i in 0..8 {
        clean_src.push_str(&format!(
            "@[expose] def tinyCarrierProj{i} (x : Nat) : Nat := x + {i}\n"
        ));
    }
    for i in 0..85 {
        clean_src.push_str(&format!("def privateBody{i} (x : Nat) : Nat := x + {i}\n"));
    }
    clean_src.push_str("end Obend.Trailblaze\n");
    assert!(clean_src.lines().count() > 80);
    fs::write(tb_dir.join("CleanExpose.lean"), &clean_src).unwrap();

    let idx = build_lean_index(dir.path());
    let (warn_findings, _) = run_lean_lints_with_options(&idx, LeanLintOptions::default());
    let excessive_warn: Vec<_> = warn_findings
        .iter()
        .filter(|f| f.rule_id == "lean/excessive-decl-expose")
        .collect();
    assert_eq!(excessive_warn.len(), 1);
    assert!(excessive_warn[0].path.ends_with("ExposeSpam.lean"));
    assert_eq!(excessive_warn[0].severity, Severity::Warning);

    let (err_findings, _) = run_lean_lints_with_options(
        &idx,
        LeanLintOptions {
            strict_expose: true,
            ..Default::default()
        },
    );
    let excessive_err: Vec<_> = err_findings
        .iter()
        .filter(|f| f.rule_id == "lean/excessive-decl-expose")
        .collect();
    assert_eq!(excessive_err.len(), 1);
    assert_eq!(excessive_err[0].severity, Severity::Error);
}

#[test]
fn single_sequence_harness_flags_single_turn_apex_and_passes_with_multi_turn_invariant() {
    let dir = tempfile::tempdir().unwrap();
    let gov_dir = dir.path().join("lean/Obend/Consensus");
    fs::create_dir_all(&gov_dir).unwrap();

    fs::write(
        gov_dir.join("SingleTurnOnly.lean"),
        r#"module
public section
namespace Obend.Consensus

structure GovState where
  mandateBudget : Nat
  revokedCount : Nat

structure GovTurn where
  spend : Nat

def stepTurn (s : GovState) (t : GovTurn) : Option GovState :=
  if t.spend <= s.mandateBudget then
    some { s with mandateBudget := s.mandateBudget - t.spend }
  else
    none

theorem apex_gov_turn_safe (s s' : GovState) (t : GovTurn)
    (h : stepTurn s t = some s') :
    s'.mandateBudget <= s.mandateBudget := by
  omega

end Obend.Consensus
"#,
    )
    .unwrap();

    fs::write(
        gov_dir.join("MultiTurnComplete.lean"),
        r#"module
public section
namespace Obend.Consensus

structure SessionState where
  budget : Nat

structure SessionTurn where
  cost : Nat

def ValidTrace (s : SessionState) (ts : List SessionTurn) : Prop :=
  ts.length >= 0 ∧ s.budget >= 0

theorem apex_session_turn_sound (s : SessionState) (t : SessionTurn) :
    ValidTrace s [t] := by
  exact ⟨Nat.zero_le _, Nat.zero_le _⟩

theorem session_trace_invariant (s : SessionState) (ts : List SessionTurn)
    (h : ValidTrace s ts) :
    s.budget >= 0 := h.2

end Obend.Consensus
"#,
    )
    .unwrap();

    let idx = build_lean_index(dir.path());
    let (warn_findings, _) = run_lean_lints_with_options(&idx, LeanLintOptions::default());
    let st_warns: Vec<_> = warn_findings
        .iter()
        .filter(|f| f.rule_id == "lean/single-sequence-harness")
        .collect();
    assert_eq!(
        st_warns.len(),
        1,
        "expected 1 single-turn warning: {st_warns:#?}"
    );
    assert!(st_warns[0].path.ends_with("SingleTurnOnly.lean"));
    assert_eq!(st_warns[0].severity, Severity::Warning);

    let (err_findings, _) = run_lean_lints_with_options(
        &idx,
        LeanLintOptions {
            strict_harnesses: true,
            ..Default::default()
        },
    );
    let st_errs: Vec<_> = err_findings
        .iter()
        .filter(|f| f.rule_id == "lean/single-sequence-harness")
        .collect();
    assert_eq!(st_errs.len(), 1);
    assert_eq!(st_errs[0].severity, Severity::Error);
}

#[test]
fn judge_fragment_restates_check_catches_same_opening_and_passes_genuine_fragments() {
    let dir = tempfile::tempdir().unwrap();
    let crypto_dir = dir.path().join("lean/Obend/Crypto");
    fs::create_dir_all(&crypto_dir).unwrap();

    fs::write(
        crypto_dir.join("SameOpeningTautology.lean"),
        r#"module
public section
namespace Obend.Crypto

def aliasedFrag (q : SameOpeningInstance) : Prop :=
  ∃ c, verifySameOpening q c = .ok

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

def aliasedJudge : Obend.Judge SameOpeningInstance SameOpeningWitness where
  Clause := SameOpeningRefusal
  Meaning := SameOpeningMeaning
  check _ q c := verifySameOpening q c
  sound {_ _ _} h := verifySameOpening_sound h
  refutes := sameOpeningRefutes
  refuted {_ _ _ _ _} h hr c' hm := verifySameOpening_refuted h hr c' hm
  Fragment := aliasedFrag
  complete {q} ⟨c, hc⟩ _ := ⟨c, 0, hc⟩
  mono _ _ := rfl

end Obend.Crypto
"#,
    )
    .unwrap();

    fs::write(
        crypto_dir.join("HonestFragments.lean"),
        r#"module
public section
namespace Obend.Crypto

instance universalJudge : Obend.Judge Obj Cert where
  Clause := ClauseTy
  Meaning := SemanticMeaning
  check _ o c := verifySemantic o c
  sound {_ _ _} h := verifySemantic_sound h
  refutes _ := true
  refuted {_ _ _ _ _} h hr c' hm := verifySemantic_refuted h hr c' hm
  Fragment := fun _ => True
  complete {o} _ ⟨c, hm⟩ := buildCert_complete o c hm
  mono _ _ := rfl

instance syntacticDomainJudge : Obend.Judge TransportObj TransportCert where
  Clause := TransportClause
  Meaning := TransportMeaning
  check := transportCheck
  sound {_ _ _} h := transportCheck_sound h
  refutes _ := true
  refuted {_ _ _ _ _} h hr c' hm := transportCheck_refuted h hr c' hm
  Fragment o := nonEmptySplits o.decideExpr = true ∧ checkL [] o.decideExpr .boolean = true
  complete {o} hFrag _ := transport_complete o hFrag
  mono _ _ := rfl

instance wellFormedPredicateJudge : Obend.Judge HyperbolicSystem Cert where
  Clause := String
  Meaning := HyperbolicMeaning
  check _ s c := verifyHyperbolic s c
  sound {_ _ _} h := verifyHyperbolic_sound h
  refutes _ := true
  refuted {_ _ _ _ _} h hr c' hm := verifyHyperbolic_refuted h hr c' hm
  Fragment := HyperbolicSystem.WellFormed
  complete {s} hWf hMean := buildHyperbolicCert s hWf hMean
  mono _ _ := rfl

end Obend.Crypto
"#,
    )
    .unwrap();

    let idx = build_lean_index(dir.path());
    let (warn_findings, _) = run_lean_lints_with_options(&idx, LeanLintOptions::default());
    let frag_warns: Vec<_> = warn_findings
        .iter()
        .filter(|f| f.rule_id == "lean/judge-fragment-restates-check")
        .collect();
    assert_eq!(
        frag_warns.len(),
        2,
        "both inline `SameOpening` and 1-hop aliased `Fragment` must fire while all 3 honest judges pass: {frag_warns:#?}"
    );
    assert!(frag_warns.iter().all(|f| {
        f.path.ends_with("SameOpeningTautology.lean") && f.severity == Severity::Warning
    }));

    let (err_findings, _) = run_lean_lints_with_options(
        &idx,
        LeanLintOptions {
            strict_vacuity: true,
            ..Default::default()
        },
    );
    let frag_errs: Vec<_> = err_findings
        .iter()
        .filter(|f| f.rule_id == "lean/judge-fragment-restates-check")
        .collect();
    assert_eq!(frag_errs.len(), 2);
    assert!(frag_errs.iter().all(|f| f.severity == Severity::Error));
}

#[test]
fn pigeonhole_vacuous_premise_catches_compressing_sis_and_bounded_collision_and_passes_psum_and_games()
 {
    let dir = tempfile::tempdir().unwrap();
    let crypto_dir = dir.path().join("lean/Obend/Crypto");
    let hw_dir = dir.path().join("lean/Obend/Hardware");
    fs::create_dir_all(&crypto_dir).unwrap();
    fs::create_dir_all(&hw_dir).unwrap();

    fs::write(
        crypto_dir.join("VacuousHardness.lean"),
        r#"module
public section
namespace Obend.Crypto

def ModuleSISHard (pp : AjtaiParams) (B : Nat) : Prop :=
  ∀ v, nonZero v → ¬ (ajtaiEval pp v = 0 ∧ infNorm v ≤ B)

theorem binding_of_sis_hard (pp : AjtaiParams) (x y : Witness)
    (hSIS : ModuleSISHard pp 131070)
    (hEq : ajtaiCommit pp x = ajtaiCommit pp y) :
    x = y := by
  exact sis_inj hSIS hEq

theorem merkle_binding_of_bounded_collision_free (H : Hash32) (v : Nat) (t1 t2 : Tree)
    (hNoCol : ¬ BoundedCollision H.eval (merkleMaxPreimageBytes v))
    (hRoot : merkleRoot H t1 = merkleRoot H t2) :
    t1 = t2 := by
  exact merkle_inj hNoCol hRoot

theorem prop_only_fixed_cshake_disjunction (a b : Payload)
    (hEq : digest a = digest b) :
    a = b ∨ CshakeCollision := by
  exact Or.inr trivialCshakeCollision

end Obend.Crypto
"#,
    )
    .unwrap();

    fs::write(
        crypto_dir.join("HonestReductions.lean"),
        r#"module
public section
namespace Obend.Crypto

def extractDoubleOpenOrBreak (pp : AjtaiParams) (x y : Witness)
    (hEq : ajtaiCommit pp x = ajtaiCommit pp y) :
    PSum (x = y) (SISShortVecWitness pp.modulus 262140 pp.matrix) :=
  extractImpl pp x y hEq

theorem nonPigeonhole_sis_binding (pp : AjtaiParams) (x y : Witness)
    (hNP : NonPigeonholeSISParams pp)
    (hSIS : ModuleSISHard pp 131070)
    (hEq : ajtaiCommit pp x = ajtaiCommit pp y) :
    x = y := by
  exact np_inj hNP hSIS hEq

theorem toyInjectiveHash_no_boundedCollision (maxBytes : Nat)
    (hMax : maxBytes ≤ 31) :
    ¬ BoundedCollision toyHash.eval maxBytes := by
  exact toy_inj maxBytes hMax

theorem keyed_msis_game_sound (G : KeyedMSISGame) (adv : Adversary) (eps : RatSlack)
    (hSec : GameSecure G adv eps) :
    Advantage G adv ≤ eps := by
  exact hSec

theorem pair_collision_among_honest (H : Hash) (a b : List UInt8)
    (hEq : H a = H b) :
    a = b ∨ CollisionAmong H (fun m => m = a ∨ m = b) := by
  exact pair_binds H a b hEq

end Obend.Crypto
"#,
    )
    .unwrap();

    // Spatial placement `Bool` helper named `checkPairNoCollision` must NOT false-positive!
    fs::write(
        hw_dir.join("PlaceRoute.lean"),
        r#"module
public section
namespace Obend.Hardware

def checkPairNoCollision (c1 c2 : PlacedCell) : Bool :=
  c1.x != c2.x || c1.y != c2.y

end Obend.Hardware
"#,
    )
    .unwrap();

    let idx = build_lean_index(dir.path());
    let (warn_findings, _) = run_lean_lints_with_options(&idx, LeanLintOptions::default());
    let vac_warns: Vec<_> = warn_findings
        .iter()
        .filter(|f| f.rule_id == "lean/pigeonhole-vacuous-premise")
        .collect();
    assert_eq!(
        vac_warns.len(),
        4,
        "all 4 vacuous declarations in VacuousHardness.lean must fire with 0 false positives on HonestReductions.lean or PlaceRoute.lean: {vac_warns:#?}"
    );
    assert!(
        vac_warns.iter().all(|f| {
            f.path.ends_with("VacuousHardness.lean") && f.severity == Severity::Warning
        })
    );

    let (err_findings, _) = run_lean_lints_with_options(
        &idx,
        LeanLintOptions {
            strict_vacuity: true,
            ..Default::default()
        },
    );
    let vac_errs: Vec<_> = err_findings
        .iter()
        .filter(|f| f.rule_id == "lean/pigeonhole-vacuous-premise")
        .collect();
    assert_eq!(vac_errs.len(), 4);
    assert!(vac_errs.iter().all(|f| f.severity == Severity::Error));
}

#[test]
fn test_in_library_flags_tier1_guard_tooth_eval_guard_msgs_under_strict_tests_and_allows_teeth_tests_comments_strings()
 {
    let dir = tempfile::tempdir().unwrap();
    let obend_dir = dir.path().join("lean/Obend");
    let teeth_dir = dir.path().join("lean/Obend/Teeth");
    let tests_dir = dir.path().join("lean/tests");
    fs::create_dir_all(&obend_dir).unwrap();
    fs::create_dir_all(&teeth_dir).unwrap();
    fs::create_dir_all(&tests_dir).unwrap();

    // 1. Tier-1 library file `lean/Obend/Foo.lean`:
    //    - Has `#guard`, `#tooth`, `#eval`, and `#guard_msgs` (including indented inside `namespace`)
    //    - Also has `#guard`, `#tooth`, `#eval`, `#guard_msgs` inside line comments, nested block comments,
    //      docstrings, normal/interpolated/raw string literals, syntax quotes, and BitVec width suffixes
    fs::write(
        obend_dir.join("Foo.lean"),
        r###"module
public section
namespace Obend.Foo

-- Line comment: #guard true / #tooth foo / #eval 1 / #guard_msgs in #eval 2
/- Block comment:
   #guard false
   /- Nested block comment:
      #tooth nested_thm by mutation f := g
      #eval 999
   -/
   #guard_msgs in #check Nat
-/

/-- Docstring mentioning `#guard`, `#tooth`, `#eval`, and `#guard_msgs` must be ignored. -/
def describeCommands : String :=
  "#guard x && #tooth y && #eval z && #guard_msgs"

def interpolatedMsg (n : Nat) : String :=
  s!"interpolated: #guard {n} #tooth #eval #guard_msgs"

def rawMsg : String :=
  r##"raw string with "inner quotes" and
#guard true
#tooth fake_thm
#eval 123
#guard_msgs in #eval 456
"##

def bitvecSuffix (x eval : Nat) : BitVec eval :=
  x#eval

def quotedStx : Lean.MacroM Lean.Syntax := do
  `(command| #guard true)

def double (n : Nat) : Nat := n + n

theorem double_zero : double 0 = 0 := rfl

#guard double 2 == 4

  #tooth double_zero by mutation double := fun n => n + 1

#eval double 21

/-- info: 6 -/
#guard_msgs in
#check double

end Obend.Foo
"###,
    )
    .unwrap();

    // 2. Tier-2 mutation gate file `lean/Obend/Teeth/FooTeeth.lean` -> permitted!
    fs::write(
        teeth_dir.join("FooTeeth.lean"),
        r#"module
import Obend.Foo
namespace Obend.Teeth

#tooth Obend.Foo.double_zero by mutation Obend.Foo.double := fun n => n + 1
#guard true
#guard_msgs in
#eval 1 + 1

end Obend.Teeth
"#,
    )
    .unwrap();

    // 3. Compiled test suite file `lean/tests/FooTest.lean` -> permitted!
    fs::write(
        tests_dir.join("FooTest.lean"),
        r#"import Obend.Foo

#guard Obend.Foo.double 3 == 6
#tooth Obend.Foo.double_zero by mutation Obend.Foo.double := fun n => n + 1
#guard_msgs in
#eval Obend.Foo.double 5
"#,
    )
    .unwrap();

    let idx = build_lean_index(dir.path());

    // Summary counts are ALWAYS populated even when `strict_tests` is false:
    // `Foo.lean` has 1 `#guard` + 1 `#guard_msgs` (= 2 `tier1_guards`), 1 `#tooth` (= 1 `tier1_teeth`), 1 `#eval` (= 1 `tier1_evals`).
    let (tier1_guards, tier1_teeth, tier1_evals) = compute_tier1_test_counts(&idx);
    assert_eq!(tier1_guards, 2, "expected #guard + #guard_msgs in Foo.lean");
    assert_eq!(tier1_teeth, 1, "expected #tooth in Foo.lean");
    assert_eq!(tier1_evals, 1, "expected #eval in Foo.lean");

    // Without `--strict-tests`, `lean/test-in-library` emits 0 findings so Wave-7 lanes are unaffected
    let (default_findings, _) = run_lean_lints_with_options(&idx, LeanLintOptions::default());
    assert!(
        default_findings
            .iter()
            .all(|f| f.rule_id != "lean/test-in-library"),
        "default lint run must not emit lean/test-in-library findings: {default_findings:#?}"
    );

    // With `--strict-tests`, exactly the 4 real top-level commands in `lean/Obend/Foo.lean` fire as `Severity::Error`
    let (strict_findings, _) = run_lean_lints_with_options(
        &idx,
        LeanLintOptions {
            strict_tests: true,
            ..Default::default()
        },
    );
    let test_errs: Vec<_> = strict_findings
        .iter()
        .filter(|f| f.rule_id == "lean/test-in-library")
        .collect();
    assert_eq!(
        test_errs.len(),
        4,
        "expected exactly 4 lean/test-in-library errors in Foo.lean (0 in Teeth/ and tests/): {test_errs:#?}"
    );
    assert!(
        test_errs
            .iter()
            .all(|f| { f.path == "lean/Obend/Foo.lean" && f.severity == Severity::Error })
    );

    let symbols: Vec<&str> = test_errs
        .iter()
        .filter_map(|f| f.symbol.as_deref())
        .collect();
    assert_eq!(symbols, vec!["#guard", "#tooth", "#eval", "#guard_msgs"]);
    assert!(
        test_errs[0].remediation.contains("lean/tests/")
            && test_errs[0].remediation.contains("obend-test")
    );
    assert!(test_errs[1].remediation.contains("lean/Obend/Teeth/"));
    assert!(test_errs[2].remediation.contains("Remove `#eval`"));
    assert!(
        test_errs[3].remediation.contains("lean/tests/")
            || test_errs[3].remediation.contains("lean/Obend/Teeth/")
    );
}
