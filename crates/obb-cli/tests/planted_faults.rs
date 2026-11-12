//! Planted-fault & non-regression test suite (`Q4 Toothed`) proving every `obb` detector,
//! genealogy judge rule, git revert check, statechart guard, and HTTP endpoint bites.

use obb_cli::serve::{ServeConfig, build_router};
use obb_judge::{
    Floor, Gate, Method, MethodBinding, Refusal, TrustBase, check_revert_clean, check_succeed,
    check_well_formed, evaluate_gate,
};
use obb_lint::run_repo_lints;
use obb_lint::spec_check::parse_transport_census_json;
use obb_state::{MachineStatus, StateRefusal, StateStore};
use std::collections::BTreeSet;
use std::fs;
use std::path::Path;
use std::process::Command;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

fn write_rel(root: &Path, rel: &str, content: &str) {
    let full = root.join(rel);
    if let Some(parent) = full.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    fs::write(full, content).unwrap();
}

#[test]
fn planted_lean_vacuity_and_theater_faults_all_bite() {
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();

    // 1. Real Core inductive for cross-checking
    write_rel(
        root,
        "lean/Obend/Core/Term.lean",
        r#"
namespace Obend.Core

inductive Quantity where
  | erased
  | affine
  | linear
  | unrestricted

inductive Term where
  | var (idx : Nat)
  | lam (q : Quantity) (ty : Term) (body : Term)
  | app (fn : Term) (arg : Term)

end Obend.Core
"#,
    );

    // 2. Planted Lean vacuity, unused params, closed `_sound` claim, cosplay name, sorry
    write_rel(
        root,
        "lean/Obend/Lower/MockFabric.lean",
        r#"
namespace Obend.Lower

def stepCamDefEqNodeWord_refl_thm (_tag _h : Nat) : True ∧ (True → True) :=
  ⟨trivial, fun h => h⟩

theorem fake_iff_domain : (1 = 1) ↔ (1 = 1) := Iff.rfl

def runZone1Whnf (x : Nat) : Nat := x

theorem runZone1Whnf_sound : runZone1Whnf 0 = 0 := by decide

def goldenShowcasePole (x : Nat) : Nat := x + 1

theorem unfinished_claim (n : Nat) : n = n := by sorry

end Obend.Lower
"#,
    );

    // 3. Planted SiliconElab-style tactic computing `z1` and never splicing `$z1` into `evalTactic`
    write_rel(
        root,
        "lean/Obend/Tactic/BadElab.lean",
        r#"
import Lean

elab "silicon_fake" : tactic => do
  let z1 := computeHardwareState 42
  if z1.focusHandle >= 64 then
    throwError "hardware overflow"
  Lean.Elab.Tactic.evalTactic (← `(tactic| omega))
"#,
    );

    // 4. Planted tautological `Judge.Meaning` + hardcoded string-literal wire decoder
    write_rel(
        root,
        "lean/Obend/Analysis/BadJudge.lean",
        r#"
namespace Obend.Analysis

def verifyFlowpipe (p : Nat) (c : Nat) : Bool := p == c

instance : Obend.Judge Nat Nat where
  check p c := verifyFlowpipe p c
  Meaning p c := verifyFlowpipe p c = true
  sound p c h := h

def badFormat : Judge.Format Nat Nat where
  name := "flow@1"
  decodeObj s := match s with
    | "thermostat-default" => some 1
    | _ => none
  decodeCert s := match s with
    | "valid-cooling-switch" => some 1
    | _ => none

end Obend.Analysis
"#,
    );

    let report = run_repo_lints(root).unwrap();
    let rules: BTreeSet<&str> = report.findings.iter().map(|f| f.rule_id.as_str()).collect();

    for expected in [
        "lean/cosplay-naming",
        "lean/trivial-conclusion",
        "lean/unused-param",
        "lean/closed-soundness-claim",
        "lean/sorry-or-axiom",
        "lean/discarded-tactic-binding",
        "lean/tautological-judge-meaning",
        "lean/hardcoded-wire-decoder",
    ] {
        assert!(
            rules.contains(expected),
            "expected rule `{expected}` to fire, got rules: {rules:?}\nfindings: {:#?}",
            report.findings
        );
    }
}

#[test]
fn clean_lean_repo_produces_zero_findings() {
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();

    write_rel(
        root,
        "lean/Obend/Core/Term.lean",
        r#"
namespace Obend.Core

inductive Term where
  | var (k : Nat)
  | app (f : Term) (a : Term)

def evalStep (t : Term) : Term :=
  match t with
  | .var k => .var k
  | .app f a => .app f a

theorem evalStep_idempotent (t : Term) : evalStep (evalStep t) = evalStep t := by
  cases t <;> rfl

elab "use_computed_bound" : tactic => do
  let boundStx := Lean.Syntax.mkNumLit "0"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact $boundStx))

end Obend.Core
"#,
    );

    write_rel(
        root,
        "DESIGN.md",
        r#"# Clean Design

## Term Table (`Obend/Core/Term.lean`)

| Category | Constructors | Notes |
|---|---|---|
| Core | `var k`, `app f a` | Proved idempotent by `evalStep_idempotent` |
"#,
    );

    let report = run_repo_lints(root).unwrap();
    assert_eq!(
        report.total_findings, 0,
        "clean fixture must produce 0 findings, got: {:#?}",
        report.findings
    );
}

#[test]
fn planted_cross_language_mirrors_and_markdown_hallucinations_bite() {
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();

    // Lean ground truth with 2 constructors
    write_rel(
        root,
        "lean/Obend/Core/Term.lean",
        r#"
namespace Obend.Core

inductive Term where
  | bound (k : Nat)
  | app (f : Term) (a : Term)

end Obend.Core
"#,
    );

    // 1. Markdown with hallucinated constructors (`pi`, `brand`), missing `.lean` file, missing symbol, and Navel prose
    write_rel(
        root,
        "DESIGN.md",
        r#"# Architecture

### 1.1 Term Former Table (`Obend/Core/Term.lean`)

| Category | Constructors | Purpose |
|---|---|---|
| Core | `bound k`, `app f a`, `pi q A B`, `brand tag inner` | Kernel |

```lean
inductive Term where
  | bound (k : Nat)
  | hallucinatedCtor (x : Nat)
```

Hardware lowering lives in (RTL.lean, Verilog.lean) and proves `nonexistent_magic_sound`.
This legacy layer was deleted on 2026-11-04 and has 0 sorryAx!
"#,
    );

    // 2. `.obend` spec with claim restating method + tautological law
    write_rel(
        root,
        "apps/demo/Demo.obend",
        r#"
law trivial_law : state == state

spec SettlementSpec:
  def computeFee(amount: Nat) -> Nat := amount + 5
  claim fee_correct(amount: Nat) : computeFee(amount) == amount + 5
"#,
    );

    // 3. Python E2E self-mocking suite (`import subprocess` unused + `CAbiBridgeMock`)
    write_rel(
        root,
        "tests/e2e/test_fake_e2e.py",
        r#"
import subprocess

class CAbiBridgeMock:
    def run_obend(self, x):
        return x + 1

def test_end_to_end_pipeline():
    bridge = CAbiBridgeMock()
    assert bridge.run_obend(41) == 42
"#,
    );

    // 4. Rust `MockBackend` in `src/` + hardcoded `.obend` semantic mirror
    write_rel(
        root,
        "crates/demo-hal/src/sim_backend.rs",
        r#"
/// Evaluates `Demo.obend` circuit state transitions in Rust.
pub struct MockBackend {
    pub acc: u64,
}

pub struct DemoObendSpecEvaluation {
    pub fee: u64,
}

impl DemoObendSpecEvaluation {
    pub fn evaluate_obend_step(amount: u64) -> Self {
        let computed = (amount * 3) + 5;
        let next = computed ^ 0x55;
        Self { fee: next }
    }
}
"#,
    );

    let report = run_repo_lints(root).unwrap();
    let rules: BTreeSet<&str> = report.findings.iter().map(|f| f.rule_id.as_str()).collect();

    for expected in [
        "markdown/hallucinated-constructor",
        "markdown/missing-lean-file",
        "markdown/missing-lean-symbol",
        "markdown/navel-prose",
        "obend/tautological-law",
        "obend/claim-restates-method",
        "python/e2e-mock-bridge",
        "python/e2e-self-mock",
        "rust/mock-backend-in-src",
        "rust/obend-semantic-mirror",
    ] {
        assert!(
            rules.contains(expected),
            "expected cross-language rule `{expected}` to fire, got: {rules:?}\nfindings: {:#?}",
            report.findings
        );
    }
}

#[test]
fn spec_sensitivity_parser_flags_disconnected_proofs_and_accepts_broken_downstream() {
    let insensitive_json = r#"{
        "total": 14,
        "intact": 14,
        "broken": 0,
        "declarations": [
            {"file": "Obend/Lower/Foo.lean", "line": 20, "decl": "foo_sound", "status": "intact"}
        ]
    }"#;
    let res_bad = parse_transport_census_json(insensitive_json, "Obend/Core/Spec.lean").unwrap();
    assert!(!res_bad.spec_sensitive);
    assert_eq!(res_bad.findings.len(), 1);
    assert_eq!(res_bad.findings[0].rule_id, "lean/spec-insensitive-change");

    let sensitive_json = r#"{
        "total": 14,
        "intact": 11,
        "broken": 3,
        "declarations": [
            {"file": "Obend/Lower/Foo.lean", "line": 44, "decl": "foo_sound", "status": "broken", "error": "type mismatch"}
        ]
    }"#;
    let res_good = parse_transport_census_json(sensitive_json, "Obend/Core/Spec.lean").unwrap();
    assert!(res_good.spec_sensitive);
    assert_eq!(res_good.broken_decls, 3);
    assert!(res_good.findings.is_empty());
}

#[test]
fn judge_genealogy_refuses_every_g4_regression_and_records_lob_cost() {
    let judge_path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../judge.json");
    let baseline = Gate::load_from_path(&judge_path).unwrap();
    check_well_formed(&baseline).expect("root judge.json must be WellFormed");

    // Fault 1: Drop a floor (`no_discarded_tactic_result <= 0`)
    let mut dropped = baseline.clone();
    dropped.name = "bad-dropped-floor".into();
    dropped
        .floors
        .retain(|f| f.cell_key() != "no_discarded_tactic_result");
    dropped
        .methods
        .retain(|m| m.floor.cell_key() != "no_discarded_tactic_result");
    let err = check_succeed(&baseline, &dropped, &[]).unwrap_err();
    assert!(
        matches!(err, Refusal::DropsFloor(ref s) if s.contains("no_discarded_tactic_result")),
        "expected DropsFloor, got {err:?}"
    );

    // Fault 2: Loosen numeric cap (`tier1_module_sec_cap <= 60` -> `<= 600`)
    let mut loosened = baseline.clone();
    loosened.name = "bad-loosened-cap".into();
    for fl in &mut loosened.floors {
        if let Floor::Cap { cell, max } = fl {
            if cell == "tier1_module_sec_cap" {
                *max = 600;
            }
        }
    }
    for m in &mut loosened.methods {
        if let Floor::Cap { cell, max } = &mut m.floor {
            if cell == "tier1_module_sec_cap" {
                *max = 600;
            }
        }
    }
    let err = check_succeed(&baseline, &loosened, &[]).unwrap_err();
    assert!(
        matches!(err, Refusal::LoosensFloor { ref cell, .. } if cell == "tier1_module_sec_cap"),
        "expected LoosensFloor on tier1_module_sec_cap, got {err:?}"
    );

    // Fault 3: Drop `revert@1` format
    let mut no_revert = baseline.clone();
    no_revert.name = "bad-no-revert".into();
    no_revert.formats.retain(|f| f != "revert@1");
    no_revert.methods.retain(|m| m.format != "revert@1");
    let err = check_succeed(&baseline, &no_revert, &[]).unwrap_err();
    assert!(matches!(err, Refusal::RefusesRevert(_)), "got {err:?}");

    // Fault 4: Discharge `revert@1` via `eval:compiled` instead of `lemma`
    let mut eval_revert = baseline.clone();
    eval_revert.name = "bad-eval-revert".into();
    eval_revert.methods[0].method = Method::Eval(TrustBase::Compiled);
    let err = check_succeed(&baseline, &eval_revert, &[]).unwrap_err();
    assert!(matches!(err, Refusal::RevertUnproved { .. }), "got {err:?}");

    // Fault 5: Expand trust base (`external:lean-transport`) WITHOUT `--lob`
    let mut stronger = baseline.clone();
    stronger.name = "g1-with-transport".into();
    let new_tb = TrustBase::External("lean-transport".into());
    let new_floor = Floor::Cap {
        cell: "spec_insensitive_decls".into(),
        max: 0,
    };
    stronger.floors.push(new_floor.clone());
    stronger.basis.push(new_tb.clone());
    for fmt in &stronger.formats {
        let method = if fmt == "revert@1" || fmt == "judge-succession@1" || fmt == "markdown-spec@1"
        {
            Method::Lemma
        } else {
            Method::Eval(new_tb.clone())
        };
        stronger.methods.push(MethodBinding {
            format: fmt.clone(),
            floor: new_floor.clone(),
            method,
        });
    }
    let err = check_succeed(&baseline, &stronger, &[]).unwrap_err();
    assert!(
        matches!(err, Refusal::Stronger(ref tb) if tb == &new_tb),
        "expected Stronger refusal without --lob, got {err:?}"
    );

    // Valid succession WITH explicit `--lob external:lean-transport` + tightened cap `60 -> 45`
    for fl in &mut stronger.floors {
        if let Floor::Cap { cell, max } = fl {
            if cell == "tier1_module_sec_cap" {
                *max = 45;
            }
        }
    }
    for m in &mut stronger.methods {
        if let Floor::Cap { cell, max } = &mut m.floor {
            if cell == "tier1_module_sec_cap" {
                *max = 45;
            }
        }
    }
    let rec = check_succeed(&baseline, &stronger, &[new_tb.clone()])
        .expect("labelled non-regressing succession must succeed");
    assert_eq!(rec.lob_cost, vec![new_tb]);
    assert_eq!(rec.added_floors, vec!["spec_insensitive_decls <= 0"]);
    assert_eq!(
        rec.tightened_floors,
        vec!["tier1_module_sec_cap: <= 60 -> <= 45"]
    );

    // Persist `LobCost` into temporary StateStore ledger and verify hash chain
    let ws = tempfile::tempdir().unwrap();
    let store = StateStore::open(ws.path()).unwrap();
    store.record_lob_succession(&rec).unwrap();
    assert_eq!(store.verify_ledger_chain().unwrap(), 1);
}

#[test]
fn check_revert_detects_clean_and_conflicting_commits_without_touching_repo() {
    let tmp = tempfile::tempdir().unwrap();
    let repo = tmp.path();

    let git = |args: &[&str]| {
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
            "git {:?} failed: {}",
            args,
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8_lossy(&out.stdout).trim().to_string()
    };

    git(&["init", "-b", "main"]);
    fs::write(repo.join("shared.txt"), "line1\nline2\n").unwrap();
    fs::write(repo.join("independent.txt"), "alpha\n").unwrap();
    git(&["add", "shared.txt", "independent.txt"]);
    git(&["commit", "-m", "root"]);

    // Commit 1: modifies `shared.txt`
    fs::write(repo.join("shared.txt"), "line1-from-c1\nline2\n").unwrap();
    git(&["add", "shared.txt"]);
    git(&["commit", "-m", "c1 modifies shared"]);
    let c1 = git(&["rev-parse", "HEAD"]);

    // Commit 2: modifies `independent.txt` (cleanly revertible even after Commit 3!)
    fs::write(repo.join("independent.txt"), "beta\n").unwrap();
    git(&["add", "independent.txt"]);
    git(&["commit", "-m", "c2 modifies independent"]);
    let c2 = git(&["rev-parse", "HEAD"]);

    // Commit 3 (HEAD): overwrites `shared.txt` line 1 again -> reverting `c1` now conflicts!
    fs::write(repo.join("shared.txt"), "line1-overwritten-by-c3\nline2\n").unwrap();
    git(&["add", "shared.txt"]);
    git(&["commit", "-m", "c3 overwrites shared"]);
    let c3 = git(&["rev-parse", "HEAD"]);

    // Snapshot object count before `check_revert_clean`
    let before_status = git(&["status", "--porcelain"]);
    assert!(before_status.is_empty());

    let res_c2 = check_revert_clean(repo, &c2).unwrap();
    assert!(res_c2.clean, "independent commit c2 must revert cleanly");

    let res_c3 = check_revert_clean(repo, &c3).unwrap();
    assert!(res_c3.clean, "HEAD commit c3 must revert cleanly");

    let res_c1 = check_revert_clean(repo, &c1).unwrap();
    assert!(
        !res_c1.clean,
        "conflicting earlier commit c1 must fail check_revert_clean"
    );

    // Target repo working tree & index remain 100% untouched
    let after_status = git(&["status", "--porcelain"]);
    assert!(after_status.is_empty());
}

#[tokio::test]
async fn statechart_guards_disk_floor_segment_rules_and_http_serve_work() {
    let ws = tempfile::tempdir().unwrap();
    let root = ws.path();

    // Copy `judge.json` into temp workspace so `/api/judge` evaluates cleanly
    let repo_judge = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../judge.json");
    fs::copy(&repo_judge, root.join("judge.json")).unwrap();
    // Mark planted-fault witness path in temp workspace so `planted_fault_red <= 0` passes too
    write_rel(root, "crates/obb-cli/tests/planted_faults.rs", "// witness\n");

    let store = StateStore::open(root).unwrap();
    store
        .create_campaign("C1", "Test Campaign", "Aim", "/tmp")
        .unwrap();

    // Illegal campaign jump `Aim -> Running` (skipping `Grounded`) must be refused
    let bad_camp = store
        .transition_campaign("C1", "Running", true, "skip")
        .unwrap_err();
    assert!(matches!(bad_camp, StateRefusal::IllegalTransition { .. }));

    store.transition_campaign("C1", "Alone", true, "no ambition yet").unwrap();
    store.transition_campaign("C1", "Aim", true, "AMBITION.md written").unwrap();
    store
        .transition_campaign("C1", "Grounded", true, "G1 whole-read")
        .unwrap();
    store
        .transition_campaign("C1", "Running", true, "G2 briefs")
        .unwrap();

    // Quest lifecycle (`Grounded -> Scoped -> Built -> Wired -> Toothed -> Landed -> Claimed -> Recorded`) & sink exit rule
    store
        .create_quest("Q-1", "C1", "Prove soundness", "agent-alpha", "decided")
        .unwrap();
    // Jumping `Grounded -> Built` (skipping `Scoped`) must be refused
    assert!(matches!(
        store
            .transition_quest("Q-1", "Built", "agent-alpha", None, None, true)
            .unwrap_err(),
        StateRefusal::IllegalTransition { .. }
    ));

    // Step `Grounded -> Scoped -> Built`, enter `Theater` sink (`Built -> Theater` in `sink_edges`), then try to exit via wrong agent -> refused!
    store
        .transition_quest("Q-1", "Scoped", "agent-alpha", None, None, true)
        .unwrap();
    store
        .transition_quest("Q-1", "Built", "agent-alpha", None, None, true)
        .unwrap();
    store
        .transition_quest("Q-1", "Theater", "agent-alpha", None, None, true)
        .unwrap();
    assert!(matches!(
        store
            .transition_quest(
                "Q-1",
                "Built",
                "wrong-agent",
                Some("deleted tautology"),
                None,
                true
            )
            .unwrap_err(),
        StateRefusal::SinkExitViolation { .. }
    ));
    // Holder agent with remedial action exits sink cleanly back to `Built`, then wires to `Wired`
    store
        .transition_quest(
            "Q-1",
            "Built",
            "agent-alpha",
            Some("replaced tautological theorem with independent spec"),
            None,
            true,
        )
        .unwrap();
    store
        .transition_quest("Q-1", "Wired", "agent-alpha", None, None, true)
        .unwrap();
    // `Wired -> Toothed` WITHOUT `tooth_witness` must fail Q4!
    assert!(matches!(
        store
            .transition_quest("Q-1", "Toothed", "agent-alpha", None, None, true)
            .unwrap_err(),
        StateRefusal::GuardFailed { ref guard, .. } if guard == "Q4"
    ));
    store
        .transition_quest(
            "Q-1",
            "Toothed",
            "agent-alpha",
            None,
            Some("tests/planted_faults.rs"),
            true,
        )
        .unwrap();

    // Ember channel rejects status noise, accepts `decision`
    assert!(matches!(
        store
            .enqueue_ember_event("status_ping", "Q-1", "still compiling...")
            .unwrap_err(),
        StateRefusal::InvalidEmberEvent { .. }
    ));
    store
        .enqueue_ember_event("decision", "Q-1", "Accept external:cadical into judge basis?")
        .unwrap();

    // Disk headroom floor (< 20 GB) blocks dispatch on `hbox`
    store
        .record_machine_status(&MachineStatus {
            host: "hbox".into(),
            reachable: true,
            required_for_dispatch: true,
            avail_gb: 9.4,
            total_gb: 500.0,
            load_summary: "disk tight".into(),
            below_floor: true,
            checked_at: "2026-11-12T00:00:00Z".into(),
        })
        .unwrap();
    assert!(matches!(
        store
            .seg_new("seg-blocked", "Q-1", "pro", "hbox", "blocked")
            .unwrap_err(),
        StateRefusal::DiskHeadroomFloor { .. }
    ));

    // Healthy host (`local` with 120 GB free) allows segment creation, enforces S4 & S5
    store
        .record_machine_status(&MachineStatus {
            host: "local".into(),
            reachable: true,
            required_for_dispatch: true,
            avail_gb: 120.0,
            total_gb: 500.0,
            load_summary: "ok".into(),
            below_floor: false,
            checked_at: "2026-11-12T00:00:00Z".into(),
        })
        .unwrap();
    store
        .seg_new("seg-1", "Q-1", "pro", "local", "initial")
        .unwrap();
    store.seg_continue("seg-1", 80_000, "deep audit").unwrap();

    // S4: > 64k tokens without `Distilled` refuses `seg_fork`
    assert!(matches!(
        store
            .seg_fork("seg-1", "seg-2", "flash", "local", "downshift", "full")
            .unwrap_err(),
        StateRefusal::LargeContextFork { .. }
    ));

    // Distill `seg-1`, then test S5 handoff-tax direction violation (`escalate` with `full` refused!)
    store
        .seg_distill("seg-1", "Distilled proof obligations")
        .unwrap();
    assert!(matches!(
        store
            .seg_fork("seg-1", "seg-2", "pro", "local", "escalate", "full")
            .unwrap_err(),
        StateRefusal::HandoffDirectionViolation { .. }
    ));
    store
        .seg_fork("seg-1", "seg-2", "pro", "local", "escalate", "compacted")
        .unwrap();

    // Verify ledger hash chain across all recorded transitions
    assert!(store.verify_ledger_chain().unwrap() >= 8);

    // Evaluate judge on this clean workspace (non-git workspace skips git history window cleanly)
    let gate = Gate::load_from_path(&root.join("judge.json")).unwrap();
    let eval = evaluate_gate(&gate, root).unwrap();
    assert!(eval.all_passed, "clean workspace should pass judge floors: {eval:#?}");

    // Test `obb serve` HTTP endpoints over a real localhost ephemeral TCP socket
    let app = build_router(ServeConfig::new(
        root.to_path_buf(),
        root.to_path_buf(),
        root.join("judge.json"),
    ));
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();
    let srv = tokio::spawn(async move {
        let _ = axum::serve(listener, app).await;
    });

    for path in ["/", "/api/status", "/api/judge", "/api/lints"] {
        let mut stream = tokio::net::TcpStream::connect(addr).await.unwrap();
        let req = format!("GET {path} HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n");
        stream.write_all(req.as_bytes()).await.unwrap();
        let mut resp = String::new();
        stream.read_to_string(&mut resp).await.unwrap();
        assert!(
            resp.starts_with("HTTP/1.1 200 OK"),
            "endpoint {path} did not return 200 OK: {}",
            resp.lines().next().unwrap_or("")
        );
    }
    srv.abort();
}
