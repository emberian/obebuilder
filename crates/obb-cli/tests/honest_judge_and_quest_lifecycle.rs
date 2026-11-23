//! Honest judge, fail-closed floors, SHA-bound statechart receipts and unseeded end-to-end quest tests.
//!
//! Verifies five judge and state requirements:
//! 1. `#tooth` (`planted_fault_red`) executes real positive (`exit == 0`) + isolated mutated negative
//!    controls (`exit != 0`) in `/private/tmp`, distinguishing `BIT`, `VACUOUS`, `INVALID_TOOTH`,
//!    and `POSITIVE_FAILED` without touching the candidate working tree; static/index presence is
//!    typed strictly as `tooth_structural_presence` (`attested`, `eval:lexical`).
//! 2. Unknown named/cap floors (`UnknownFloor`) and missing timing/spec-census measurements
//!    (`MissingMeasurement`) fail closed; `no_sorry_ax` / lexical scanners report `eval:lexical`
//!    (`Regime::Attested`) and refuse `eval:kernel` (`Regime::Decided`) unless a `HEAD`-bound
//!    external `KernelReceipt` is verified (`StaleKernelReceipt` when `HEAD` advances).
//! 3. `obb-state` requires SHA-bound `JudgeReceipt`s on `(base_sha, head_sha, tree_oid)`, enforces
//!    non-overlapping footprint leases (`FootprintLeaseConflict`, `FootprintViolation`), rejects
//!    tampered receipts (`TamperedReceipt`) and stale trunk bases (`StaleBaseSha`), and records
//!    emergency bypasses truthfully as `effective_regime = "AttestedOverride"` + `merged_ungated = true`.
//! 4. Seeded demo fixtures (`seed_obend_campaign`) are tagged `origin = "demo_seed"` and never
//!    masquerade as live verified transitions (`live_transition_count == 0`, `verified_quest_count == 0`),
//!    and an unseeded mini-quest runs end-to-end (`init -> take -> commit -> judge -> propose -> land -> record`).

use obb_core::Regime;
use obb_judge::{
    Floor, FloorDiagnostic, Gate, JudgeClock, JudgeReceipt, KernelReceipt, Method, MethodBinding,
    ToothMutation, ToothSpec, ToothVerdict, TrustBase, check_succeed, evaluate_gate,
    evaluate_gate_on, evaluate_teeth, issue_judge_receipt, issue_judge_receipt_with_state_dir,
};
use obb_state::{
    CampaignGuardEvidence, ORIGIN_DEMO_SEED, ORIGIN_LIVE, QuestGuardEvidence,
    REGIME_ATTESTED_OVERRIDE, StateRefusal, StateStore,
};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn obb_bin() -> &'static str {
    env!("CARGO_BIN_EXE_obb")
}

fn temp_in_private_tmp(prefix: &str) -> tempfile::TempDir {
    let mut builder = tempfile::Builder::new();
    builder.prefix(prefix);
    if Path::new("/private/tmp").is_dir() {
        builder.tempdir_in("/private/tmp").unwrap()
    } else {
        builder.tempdir().unwrap()
    }
}

fn write_rel(root: &Path, rel: &str, content: &str) {
    let full = root.join(rel);
    if let Some(p) = full.parent() {
        fs::create_dir_all(p).unwrap();
    }
    fs::write(full, content).unwrap();
}

fn git_cmd(repo: &Path, args: &[&str]) -> String {
    let out = Command::new("git")
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("TMPDIR", std::env::temp_dir())
        .env("GIT_AUTHOR_NAME", "obb-test")
        .env("GIT_AUTHOR_EMAIL", "obb-test@localhost")
        .env("GIT_COMMITTER_NAME", "obb-test")
        .env("GIT_COMMITTER_EMAIL", "obb-test@localhost")
        .arg("-C")
        .arg(repo)
        .args(args)
        .output()
        .expect("git command failed to spawn");
    assert!(
        out.status.success(),
        "git {:?} failed in {}:\nstdout: {}\nstderr: {}",
        args,
        repo.display(),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).to_string()
}

fn init_git_repo_on_main(repo: &Path) {
    git_cmd(repo, &["init", "--quiet"]);
    git_cmd(repo, &["checkout", "-B", "main"]);
    write_rel(repo, ".gitignore", "/.obb/\n");
    git_cmd(repo, &["add", ".gitignore"]);
}

fn run_obb(args: &[&str]) -> Output {
    Command::new(obb_bin())
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("TMPDIR", std::env::temp_dir())
        .args(args)
        .output()
        .expect("obb binary failed to spawn")
}

fn build_gate(
    name: &str,
    floors: Vec<(Floor, Method)>,
    basis: Vec<TrustBase>,
    teeth: Vec<ToothSpec>,
) -> Gate {
    let mut floor_list = Vec::new();
    let mut methods = Vec::new();
    for (fl, m) in floors {
        methods.push(MethodBinding {
            format: "revert@1".into(),
            floor: fl.clone(),
            method: Method::Lemma,
        });
        methods.push(MethodBinding {
            format: "impact@1".into(),
            floor: fl.clone(),
            method: m,
        });
        floor_list.push(fl);
    }
    Gate {
        name: name.into(),
        formats: vec!["revert@1".into(), "impact@1".into()],
        floors: floor_list,
        methods,
        basis,
        teeth,
    }
}

// =============================================================================
// 1. Real `#tooth` Execution (`BIT` vs `VACUOUS` vs `INVALID_TOOTH` vs `POSITIVE_FAILED`)
// =============================================================================

#[test]
fn executed_tooth_distinguishes_bit_vacuous_invalid_and_positive_failed_without_dirtying_tree() {
    let tmp = temp_in_private_tmp("obb-teeth-");
    let repo = tmp.path().join("repo");
    fs::create_dir_all(&repo).unwrap();
    init_git_repo_on_main(&repo);

    write_rel(
        &repo,
        "src/calc.py",
        "def clamp_positive(x):\n    return x if x > 0 else 0\n\ndef unused_helper(x):\n    return x + 1\n",
    );
    write_rel(
        &repo,
        "tests/test_calc.py",
        "import sys\nsys.path.insert(0, 'src')\nfrom calc import clamp_positive\n\nassert clamp_positive(5) == 5, 'positive input preserved'\nassert clamp_positive(-3) == 0, 'negative input clamped to zero'\nprint('ran 2 behavioral assertions ok')\n",
    );
    git_cmd(&repo, &["add", "src/calc.py", "tests/test_calc.py"]);
    git_cmd(&repo, &["commit", "-m", "root commit"]);

    write_rel(&repo, "README.md", "# Calc\n");
    git_cmd(&repo, &["add", "README.md"]);
    git_cmd(&repo, &["commit", "-m", "second commit for home 1"]);

    // Case A: Biting tooth (`BIT`), vacuous tooth (`VACUOUS`), syntax-error tooth (`INVALID_TOOTH`),
    // zero-test-discovery tooth (`INVALID_TOOTH`), missing-substring tooth (`INVALID_TOOTH`),
    // missing-search-snippet tooth (`INVALID_TOOTH`), and failing positive check (`POSITIVE_FAILED`).
    let specs = vec![
        ToothSpec {
            inputs: Vec::new(),
            id: "tooth-bit".into(),
            description: "Flipping > 0 to >= -999 breaks negative clamping assertion".into(),
            build_cmd: Some("python3 -m py_compile src/calc.py tests/test_calc.py".into()),
            check_cmd: "python3 tests/test_calc.py".into(),
            mutation: ToothMutation::Replace {
                file: "src/calc.py".into(),
                search: "return x if x > 0 else 0".into(),
                replace: "return x if x >= -999 else 0".into(),
                replace_all: false,
            },
            expect_failure_substring: Some("negative input clamped to zero".into()),
            timeout_ms: 10_000,
        },
        ToothSpec {
            inputs: Vec::new(),
            id: "tooth-vacuous".into(),
            description: "Mutating untested `unused_helper` leaves test suite exiting 0".into(),
            build_cmd: Some("python3 -m py_compile src/calc.py tests/test_calc.py".into()),
            check_cmd: "python3 tests/test_calc.py".into(),
            mutation: ToothMutation::Replace {
                file: "src/calc.py".into(),
                search: "return x + 1".into(),
                replace: "return x + 999".into(),
                replace_all: false,
            },
            expect_failure_substring: None,
            timeout_ms: 10_000,
        },
        ToothSpec {
            inputs: Vec::new(),
            id: "tooth-invalid-syntax".into(),
            description:
                "Breaking Python syntax fails `build_cmd` / parser rather than behavioral check"
                    .into(),
            build_cmd: Some("python3 -m py_compile src/calc.py tests/test_calc.py".into()),
            check_cmd: "python3 tests/test_calc.py".into(),
            mutation: ToothMutation::Replace {
                file: "src/calc.py".into(),
                search: "return x if x > 0 else 0".into(),
                replace: "def broken_syntax(:::".into(),
                replace_all: false,
            },
            expect_failure_substring: None,
            timeout_ms: 10_000,
        },
        ToothSpec {
            inputs: Vec::new(),
            id: "tooth-invalid-zero-tests".into(),
            description: "Runner reporting `ran 0 tests` is rejected as INVALID_TOOTH".into(),
            build_cmd: None,
            check_cmd: "echo 'running 0 tests' && exit 0".into(),
            mutation: ToothMutation::Env {
                key: "FAULT".into(),
                value: "1".into(),
            },
            expect_failure_substring: None,
            timeout_ms: 10_000,
        },
        ToothSpec {
            inputs: Vec::new(),
            id: "tooth-invalid-wrong-assertion".into(),
            description: "Failing with wrong error message misses `expect_failure_substring`"
                .into(),
            build_cmd: None,
            check_cmd: "python3 tests/test_calc.py".into(),
            mutation: ToothMutation::Replace {
                file: "src/calc.py".into(),
                search: "return x if x > 0 else 0".into(),
                replace: "return x if x >= -999 else 0".into(),
                replace_all: false,
            },
            expect_failure_substring: Some("expected-marker-that-never-appears".into()),
            timeout_ms: 10_000,
        },
        ToothSpec {
            inputs: Vec::new(),
            id: "tooth-invalid-missing-search".into(),
            description: "Search string absent in target file".into(),
            build_cmd: None,
            check_cmd: "python3 tests/test_calc.py".into(),
            mutation: ToothMutation::Replace {
                file: "src/calc.py".into(),
                search: "nonexistent_snippet()".into(),
                replace: "boom()".into(),
                replace_all: false,
            },
            expect_failure_substring: None,
            timeout_ms: 10_000,
        },
        ToothSpec {
            inputs: Vec::new(),
            id: "tooth-positive-failed".into(),
            description: "Positive check already broken before mutation".into(),
            build_cmd: None,
            check_cmd: "exit 1".into(),
            mutation: ToothMutation::Env {
                key: "FAULT".into(),
                value: "1".into(),
            },
            expect_failure_substring: None,
            timeout_ms: 10_000,
        },
    ];

    let report = evaluate_teeth(&repo, &specs).unwrap();
    assert_eq!(report.total, 7);
    assert_eq!(report.bit_count, 1);
    assert_eq!(report.vacuous_count, 1);
    assert_eq!(report.invalid_count, 4);
    assert_eq!(report.positive_failed_count, 1);
    assert!(!report.all_bit);

    let by_id = |id: &str| report.results.iter().find(|r| r.id == id).unwrap().verdict;
    assert_eq!(by_id("tooth-bit"), ToothVerdict::Bit);
    assert_eq!(by_id("tooth-vacuous"), ToothVerdict::Vacuous);
    assert_eq!(by_id("tooth-invalid-syntax"), ToothVerdict::InvalidTooth);
    assert_eq!(
        by_id("tooth-invalid-zero-tests"),
        ToothVerdict::InvalidTooth
    );
    assert_eq!(
        by_id("tooth-invalid-wrong-assertion"),
        ToothVerdict::InvalidTooth
    );
    assert_eq!(
        by_id("tooth-invalid-missing-search"),
        ToothVerdict::InvalidTooth
    );
    assert_eq!(by_id("tooth-positive-failed"), ToothVerdict::PositiveFailed);

    // Working tree MUST remain 100% untouched after all 7 mutations!
    let porcelain = git_cmd(&repo, &["status", "--porcelain"]);
    assert!(
        porcelain.trim().is_empty(),
        "tooth execution dirtied candidate working tree: {porcelain}"
    );

    // Case B: Static file presence (`crates/obb-cli/tests/planted_faults.rs`) WITHOUT `teeth.json`
    // MUST fail `planted_fault_red` (`MissingToothExecution`) while `tooth_structural_presence`
    // passes strictly at `Regime::Attested` (`eval:lexical`).
    write_rel(
        &repo,
        "crates/obb-cli/tests/planted_faults.rs",
        "// structural placeholder without executable teeth.json\n",
    );
    git_cmd(&repo, &["add", "crates/obb-cli/tests/planted_faults.rs"]);
    git_cmd(&repo, &["commit", "-m", "add structural placeholder"]);

    let gate_static_vs_exec = build_gate(
        "g-tooth-split",
        vec![
            (
                Floor::Home(1),
                Method::Eval(TrustBase::External("git-merge-tree".into())),
            ),
            (
                Floor::Named("tooth_structural_presence".into()),
                Method::Eval(TrustBase::Lexical),
            ),
            (
                Floor::Named("planted_fault_red".into()),
                Method::Eval(TrustBase::Compiled),
            ),
        ],
        vec![
            TrustBase::Lexical,
            TrustBase::Compiled,
            TrustBase::External("git-merge-tree".into()),
        ],
        Vec::new(),
    );
    let rep_no_exec = evaluate_gate(&gate_static_vs_exec, &repo).unwrap();
    assert!(!rep_no_exec.all_passed);

    let struct_ev = rep_no_exec
        .evaluations
        .iter()
        .find(|e| e.cell == "tooth_structural_presence")
        .unwrap();
    assert!(struct_ev.passed);
    assert_eq!(struct_ev.regime, Regime::Attested);

    let pfr_ev = rep_no_exec
        .evaluations
        .iter()
        .find(|e| e.cell == "planted_fault_red")
        .unwrap();
    assert!(!pfr_ev.passed);
    assert!(matches!(
        pfr_ev.diagnostic,
        Some(FloorDiagnostic::MissingToothExecution { .. })
    ));

    // Case C: Adding an executable biting `teeth.json` makes `planted_fault_red` pass at `Regime::Decided`!
    let biting_only = vec![specs[0].clone()];
    write_rel(
        &repo,
        "teeth.json",
        &serde_json::to_string_pretty(&biting_only).unwrap(),
    );
    git_cmd(&repo, &["add", "teeth.json"]);
    git_cmd(&repo, &["commit", "-m", "add executable biting tooth"]);

    let rep_with_exec = evaluate_gate(&gate_static_vs_exec, &repo).unwrap();
    assert!(rep_with_exec.all_passed);
    assert_eq!(rep_with_exec.achieved_regime, Regime::Decided);
    let pfr_ok = rep_with_exec
        .evaluations
        .iter()
        .find(|e| e.cell == "planted_fault_red")
        .unwrap();
    assert!(pfr_ok.passed);
    assert_eq!(pfr_ok.regime, Regime::Decided);
}

// =============================================================================
// 2. Fail-Closed Unknown Floors, Missing Measurements & Honest `eval:lexical` vs `eval:kernel`
// =============================================================================

#[test]
fn fail_closed_unknown_floors_missing_measurements_and_honest_lexical_vs_kernel_regimes() {
    let tmp = temp_in_private_tmp("obb-floors-");
    let repo = tmp.path().join("repo");
    fs::create_dir_all(&repo).unwrap();
    init_git_repo_on_main(&repo);

    write_rel(
        &repo,
        "lean/Obend/Demo.lean",
        "namespace Obend.Demo\ndef double (n : Nat) : Nat := n + n\nend Obend.Demo\n",
    );
    git_cmd(&repo, &["add", "lean/Obend/Demo.lean"]);
    git_cmd(&repo, &["commit", "-m", "root lean file"]);
    write_rel(&repo, "README.md", "# Demo\n");
    git_cmd(&repo, &["add", "README.md"]);
    git_cmd(&repo, &["commit", "-m", "second commit"]);

    // 2a. Unknown named floor & unknown cap floor MUST fail closed (`UnknownFloor`), never defaulting to 0!
    let gate_unknown = build_gate(
        "g-unknown",
        vec![
            (
                Floor::Home(1),
                Method::Eval(TrustBase::External("git-merge-tree".into())),
            ),
            (
                Floor::Named("totally_unknown_lint_floor".into()),
                Method::Eval(TrustBase::Lexical),
            ),
            (
                Floor::Cap {
                    cell: "made_up_metric_cap".into(),
                    max: 0,
                },
                Method::Eval(TrustBase::Compiled),
            ),
        ],
        vec![
            TrustBase::Lexical,
            TrustBase::Compiled,
            TrustBase::External("git-merge-tree".into()),
        ],
        Vec::new(),
    );
    let rep_unknown = evaluate_gate(&gate_unknown, &repo).unwrap();
    assert!(!rep_unknown.all_passed);
    for cell_name in ["totally_unknown_lint_floor", "made_up_metric_cap"] {
        let ev = rep_unknown
            .evaluations
            .iter()
            .find(|e| e.cell == cell_name)
            .unwrap();
        assert!(!ev.passed, "`{cell_name}` must fail closed");
        assert_eq!(
            ev.diagnostic,
            Some(FloorDiagnostic::UnknownFloor {
                cell: cell_name.into()
            })
        );
    }

    // 2b. Missing timing (`tier1_module_sec_cap`) and missing spec-census (`spec_insensitive_decls`)
    // MUST fail closed with `MissingMeasurement` when their JSON measurement artifacts are absent!
    let gate_missing_meas = build_gate(
        "g-missing-meas",
        vec![
            (
                Floor::Home(1),
                Method::Eval(TrustBase::External("git-merge-tree".into())),
            ),
            (
                Floor::Cap {
                    cell: "tier1_module_sec_cap".into(),
                    max: 60,
                },
                Method::Eval(TrustBase::Compiled),
            ),
            (
                Floor::Cap {
                    cell: "spec_insensitive_decls".into(),
                    max: 0,
                },
                Method::Eval(TrustBase::External("lean-transport".into())),
            ),
        ],
        vec![
            TrustBase::Compiled,
            TrustBase::External("git-merge-tree".into()),
            TrustBase::External("lean-transport".into()),
        ],
        Vec::new(),
    );
    let rep_missing = evaluate_gate(&gate_missing_meas, &repo).unwrap();
    assert!(!rep_missing.all_passed);
    for cell_name in ["tier1_module_sec_cap", "spec_insensitive_decls"] {
        let ev = rep_missing
            .evaluations
            .iter()
            .find(|e| e.cell == cell_name)
            .unwrap();
        assert!(!ev.passed);
        assert!(matches!(
            ev.diagnostic,
            Some(FloorDiagnostic::MissingMeasurement { .. })
        ));
    }

    // Also verify `maxHeartbeats > 400_000` trips `tier1_module_sec_cap <= 60` even when `max_tier1_sec` is 5s!
    write_rel(&repo, ".obb/build-timings.json", r#"{"max_tier1_sec": 5}"#);
    write_rel(
        &repo,
        "lean/Obend/Heavy.lean",
        "set_option maxHeartbeats 900000\nnamespace Obend.Heavy\ndef h : Nat := 1\nend Obend.Heavy\n",
    );
    let gate_hb = build_gate(
        "g-hb",
        vec![
            (
                Floor::Home(1),
                Method::Eval(TrustBase::External("git-merge-tree".into())),
            ),
            (
                Floor::Cap {
                    cell: "tier1_module_sec_cap".into(),
                    max: 60,
                },
                Method::Eval(TrustBase::Compiled),
            ),
        ],
        vec![
            TrustBase::Compiled,
            TrustBase::External("git-merge-tree".into()),
        ],
        Vec::new(),
    );
    let rep_hb = evaluate_gate(&gate_hb, &repo).unwrap();
    let hb_ev = rep_hb
        .evaluations
        .iter()
        .find(|e| e.cell == "tier1_module_sec_cap")
        .unwrap();
    assert!(
        !hb_ev.passed,
        "maxHeartbeats > 400k must fail tier1_module_sec_cap"
    );
    fs::remove_file(repo.join("lean/Obend/Heavy.lean")).unwrap();
    fs::remove_file(repo.join(".obb/build-timings.json")).unwrap();

    // 2c. Honest epistemic regimes for `no_sorry_ax` and `no_declared_axiom`:
    // Under `eval:lexical`: passes ONLY at `Regime::Attested` (`evaluator_kind == "lexical"`).
    let gate_lexical = build_gate(
        "g-lexical",
        vec![
            (
                Floor::Home(1),
                Method::Eval(TrustBase::External("git-merge-tree".into())),
            ),
            (
                Floor::Named("no_sorry_ax".into()),
                Method::Eval(TrustBase::Lexical),
            ),
            (
                Floor::Named("no_declared_axiom".into()),
                Method::Eval(TrustBase::Lexical),
            ),
        ],
        vec![
            TrustBase::Lexical,
            TrustBase::External("git-merge-tree".into()),
        ],
        Vec::new(),
    );
    let rep_lex = evaluate_gate(&gate_lexical, &repo).unwrap();
    assert!(rep_lex.all_passed);
    assert!(!rep_lex.kernel_verified);
    let sorry_lex = rep_lex
        .evaluations
        .iter()
        .find(|e| e.cell == "no_sorry_ax")
        .unwrap();
    assert_eq!(sorry_lex.regime, Regime::Attested);
    assert_eq!(sorry_lex.evaluator_kind, "lexical");

    // Under `eval:kernel` WITHOUT `.obb/kernel-receipt.json`: MUST fail closed (`UnverifiedKernelClaim`)!
    let gate_kernel = build_gate(
        "g-kernel",
        vec![
            (
                Floor::Home(1),
                Method::Eval(TrustBase::External("git-merge-tree".into())),
            ),
            (
                Floor::Named("no_sorry_ax".into()),
                Method::Eval(TrustBase::Kernel),
            ),
            (
                Floor::Named("no_declared_axiom".into()),
                Method::Eval(TrustBase::Kernel),
            ),
        ],
        vec![
            TrustBase::Kernel,
            TrustBase::External("git-merge-tree".into()),
        ],
        Vec::new(),
    );
    let rep_kern_missing = evaluate_gate(&gate_kernel, &repo).unwrap();
    assert!(!rep_kern_missing.all_passed);
    let sorry_unver = rep_kern_missing
        .evaluations
        .iter()
        .find(|e| e.cell == "no_sorry_ax")
        .unwrap();
    assert!(!sorry_unver.passed);
    assert!(matches!(
        sorry_unver.diagnostic,
        Some(FloorDiagnostic::UnverifiedKernelClaim { .. })
    ));

    // Write a valid `HEAD`-bound `.obb/kernel-receipt.json` from `lean4checker` -> passes at `Regime::Decided`!
    let head_sha = git_cmd(&repo, &["rev-parse", "HEAD"]).trim().to_string();
    let kr = KernelReceipt {
        checker: "lean4checker".into(),
        head_sha: head_sha.clone(),
        exit_code: 0,
        sorry_ax_count: 0,
        user_axiom_count: 0,
        modules_checked: 1,
        checked_at: "2026-11-14T00:00:00Z".into(),
    };
    write_rel(
        &repo,
        ".obb/kernel-receipt.json",
        &serde_json::to_string_pretty(&kr).unwrap(),
    );
    let rep_kern_ok = evaluate_gate(&gate_kernel, &repo).unwrap();
    assert!(rep_kern_ok.all_passed);
    assert!(rep_kern_ok.kernel_verified);
    assert_eq!(rep_kern_ok.achieved_regime, Regime::Decided);
    let sorry_decided = rep_kern_ok
        .evaluations
        .iter()
        .find(|e| e.cell == "no_sorry_ax")
        .unwrap();
    assert_eq!(sorry_decided.regime, Regime::Decided);
    assert_eq!(sorry_decided.evaluator_kind, "kernel:lean4checker");

    // Advance `HEAD` without regenerating `.obb/kernel-receipt.json` -> MUST fail with `StaleKernelReceipt`!
    write_rel(&repo, "README.md", "# Demo v2\n");
    git_cmd(&repo, &["add", "README.md"]);
    git_cmd(&repo, &["commit", "-m", "advance HEAD past kernel receipt"]);

    let rep_kern_stale = evaluate_gate(&gate_kernel, &repo).unwrap();
    assert!(!rep_kern_stale.all_passed);
    let sorry_stale = rep_kern_stale
        .evaluations
        .iter()
        .find(|e| e.cell == "no_sorry_ax")
        .unwrap();
    assert!(!sorry_stale.passed);
    assert!(matches!(
        sorry_stale.diagnostic,
        Some(FloorDiagnostic::StaleKernelReceipt { .. })
    ));
}

// =============================================================================
// 3. True Unseeded End-to-End Quest Lifecycle (`init -> take -> commit -> judge -> propose -> land`)
// =============================================================================

#[test]
fn unseeded_end_to_end_quest_lifecycle_catches_footprint_vacuous_tampered_and_stale_base_sha() {
    let tmp = temp_in_private_tmp("obb-e2e-");
    let repo = tmp.path().join("repo");
    let state_dir = tmp.path().join("state");
    fs::create_dir_all(&repo).unwrap();
    init_git_repo_on_main(&repo);

    // Set up self-contained mini-repo with `judge.json`, `README.md`, `src/calc.py`, `tests/test_calc.py`
    let gate = build_gate(
        "g0-mini-e2e",
        vec![
            (
                Floor::Home(1),
                Method::Eval(TrustBase::External("git-merge-tree".into())),
            ),
            (
                Floor::Named("docs_symbols_exist".into()),
                Method::Eval(TrustBase::Lexical),
            ),
            (
                Floor::Named("planted_fault_red".into()),
                Method::Eval(TrustBase::Compiled),
            ),
        ],
        vec![
            TrustBase::Lexical,
            TrustBase::Compiled,
            TrustBase::External("git-merge-tree".into()),
        ],
        Vec::new(),
    );
    let judge_path = repo.join("judge.json");
    write_rel(
        &repo,
        "judge.json",
        &serde_json::to_string_pretty(&gate).unwrap(),
    );
    write_rel(
        &repo,
        "README.md",
        "# Mini Quest Repo\n\nClean reader docs.\n",
    );
    write_rel(
        &repo,
        "src/calc.py",
        "def safe_div(a, b):\n    if b == 0:\n        raise ValueError('division by zero')\n    return a // b\n",
    );
    write_rel(
        &repo,
        "tests/test_calc.py",
        "import sys\nsys.path.insert(0, 'src')\nfrom calc import safe_div\nassert safe_div(10, 2) == 5\nprint('baseline ok')\n",
    );
    git_cmd(&repo, &["add", "."]);
    git_cmd(&repo, &["commit", "-m", "initial baseline"]);

    write_rel(&repo, "NOTES.txt", "trunk rev 1\n");
    git_cmd(&repo, &["add", "NOTES.txt"]);
    git_cmd(&repo, &["commit", "-m", "trunk rev 1"]);
    let initial_main_sha = git_cmd(&repo, &["rev-parse", "main"]).trim().to_string();

    // 1. Initialize empty unseeded vault via `obb state init`
    let init_out = run_obb(&["state", "--state-dir", state_dir.to_str().unwrap(), "init"]);
    assert!(init_out.status.success());

    let store = StateStore::open_with_state_dir(&workspace_root(), Some(&state_dir)).unwrap();
    let snap0 = store.snapshot().unwrap();
    assert!(!snap0.contains_demo_seed);
    assert_eq!(snap0.demo_seed_event_count, 0);
    assert_eq!(snap0.live_transition_count, 0);
    assert_eq!(snap0.verified_quest_count, 0);

    // 2. Create live campaign `C-live` (`Aim -> Grounded -> Running`) & quests `Q-e2e` and `Q-overlap`
    for args in [
        vec![
            "state",
            "--state-dir",
            state_dir.to_str().unwrap(),
            "campaign",
            "--id",
            "C-live",
            "--title",
            "Live Mini Campaign",
            "--aim",
            "Harden safe_div zero-divisor guard with executed tooth",
            "--repo",
            repo.to_str().unwrap(),
        ],
        vec![
            "state",
            "--state-dir",
            state_dir.to_str().unwrap(),
            "campaign",
            "--id",
            "C-live",
            "--to",
            "Grounded",
            "--foundation-file",
            "README.md",
            "--foundation-file",
            "judge.json",
        ],
        vec![
            "state",
            "--state-dir",
            state_dir.to_str().unwrap(),
            "campaign",
            "--id",
            "C-live",
            "--to",
            "Running",
            "--judge",
            judge_path.to_str().unwrap(),
        ],
    ] {
        let out = run_obb(&args);
        assert!(
            out.status.success(),
            "campaign command {:?} failed: {}",
            args,
            String::from_utf8_lossy(&out.stderr)
        );
    }

    for (id, actor) in [("Q-e2e", "lane-alpha"), ("Q-overlap", "lane-beta")] {
        let out = run_obb(&[
            "state",
            "--state-dir",
            state_dir.to_str().unwrap(),
            "quest",
            "--id",
            id,
            "--campaign",
            "C-live",
            "--title",
            "Harden division",
            "--actor",
            actor,
        ]);
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
    }

    // 3. `obb state take Q-e2e` with exclusive footprint lease `["src/calc.py", "tests/", "teeth.json"]`
    let take_out = run_obb(&[
        "state",
        "--state-dir",
        state_dir.to_str().unwrap(),
        "take",
        "Q-e2e",
        "--actor",
        "lane-alpha",
        "--deliverable",
        "Zero-divisor check + executed tooth",
        "--footprint",
        "src/calc.py",
        "--footprint",
        "tests/",
        "--footprint",
        "teeth.json",
        "--repo",
        repo.to_str().unwrap(),
        "--trunk",
        "main",
    ]);
    assert!(
        take_out.status.success(),
        "obb state take failed: {}",
        String::from_utf8_lossy(&take_out.stderr)
    );
    let q_taken = store.get_quest("Q-e2e").unwrap().unwrap();
    assert_eq!(q_taken.state, "Scoped");
    assert_eq!(q_taken.origin, ORIGIN_LIVE);
    assert_eq!(q_taken.base_sha.as_deref(), Some(initial_main_sha.as_str()));

    // Verify overlapping footprint lease (`"src/"` overlaps `"src/calc.py"`) is refused!
    let overlap_err = store
        .take_quest(
            "Q-overlap",
            "lane-beta",
            "Touch src/ module",
            vec!["src/".into()],
            1.0,
            &repo,
            "main",
        )
        .unwrap_err();
    assert!(
        matches!(overlap_err, StateRefusal::FootprintLeaseConflict { .. }),
        "expected FootprintLeaseConflict, got {overlap_err:?}"
    );

    // 4. An out-of-lease edit is refused only when it collides with another active lease
    //    (`docs/rogue.md` lands inside `Q-docs`'s `docs/` lease).
    store
        .create_quest(
            "Q-docs",
            "C-live",
            "Own the docs tree",
            "lane-gamma",
            "attested",
        )
        .unwrap();
    store
        .take_quest(
            "Q-docs",
            "lane-gamma",
            "Docs sweep",
            vec!["docs/".into()],
            1.0,
            &repo,
            "main",
        )
        .unwrap();
    git_cmd(&repo, &["checkout", "-b", "quest/Q-e2e"]);
    write_rel(&repo, "docs/rogue.md", "# Out of footprint\n");
    write_rel(
        &repo,
        "tests/test_calc.py",
        "import sys\nsys.path.insert(0, 'src')\nfrom calc import safe_div\nassert safe_div(10, 2) == 5\ntry:\n    safe_div(1, 0)\n    raise SystemExit('expected ValueError')\nexcept ValueError:\n    pass\nprint('ran 2 tests ok')\n",
    );
    let biting_spec = vec![ToothSpec {
        inputs: Vec::new(),
        id: "div-zero-tooth".into(),
        description: "Removing b == 0 guard lets b=0 reach floor division or wrong path".into(),
        build_cmd: Some("python3 -m py_compile src/calc.py tests/test_calc.py".into()),
        check_cmd: "python3 tests/test_calc.py".into(),
        mutation: ToothMutation::Replace {
            file: "src/calc.py".into(),
            search: "if b == 0:\n        raise ValueError('division by zero')".into(),
            replace: "if b == 0:\n        return 0".into(),
            replace_all: false,
        },
        expect_failure_substring: Some("expected ValueError".into()),
        timeout_ms: 10_000,
    }];
    write_rel(
        &repo,
        "teeth.json",
        &serde_json::to_string_pretty(&biting_spec).unwrap(),
    );
    git_cmd(&repo, &["add", "."]);
    git_cmd(&repo, &["commit", "-m", "rogue out-of-footprint candidate"]);

    let rogue_receipt = issue_judge_receipt(&gate, &repo, "main").unwrap();
    assert!(rogue_receipt.all_passed);
    let fp_err = store
        .propose_quest("Q-e2e", "lane-alpha", &rogue_receipt, &repo, "main")
        .unwrap_err();
    assert!(
        matches!(fp_err, StateRefusal::FootprintLeaseConflict { ref requested, ref conflicting_quest, .. } if requested == "docs/rogue.md" && conflicting_quest == "Q-docs"),
        "expected FootprintLeaseConflict on docs/rogue.md against Q-docs, got {fp_err:?}"
    );
    let q_refused = store.get_quest("Q-e2e").unwrap().unwrap();
    assert_eq!(q_refused.state, "Scoped");
    assert!(
        !q_refused
            .footprint_lease
            .iter()
            .any(|p| p.starts_with("docs"))
    );

    // 5. Reset to `main` and commit an in-footprint candidate whose tooth is VACUOUS (`VACUOUS` caught!)
    git_cmd(&repo, &["reset", "--hard", "main"]);
    let vacuous_spec = vec![ToothSpec {
        inputs: Vec::new(),
        id: "div-zero-vacuous".into(),
        description: "Mutating safe_div(1, 0) when test never calls b=0 is VACUOUS".into(),
        build_cmd: Some("python3 -m py_compile src/calc.py tests/test_calc.py".into()),
        check_cmd: "python3 tests/test_calc.py".into(),
        mutation: ToothMutation::Replace {
            file: "src/calc.py".into(),
            search: "if b == 0:\n        raise ValueError('division by zero')".into(),
            replace: "if b == 0:\n        return 0".into(),
            replace_all: false,
        },
        expect_failure_substring: None,
        timeout_ms: 10_000,
    }];
    write_rel(
        &repo,
        "teeth.json",
        &serde_json::to_string_pretty(&vacuous_spec).unwrap(),
    );
    git_cmd(&repo, &["add", "teeth.json"]);
    git_cmd(&repo, &["commit", "-m", "candidate with vacuous tooth"]);

    let vac_receipt_path = tmp.path().join("vacuous-receipt.json");
    let vac_judge_out = run_obb(&[
        "judge",
        "check",
        "--strict-tests",
        "--judge",
        judge_path.to_str().unwrap(),
        "--repo",
        repo.to_str().unwrap(),
        "--base",
        "main",
        "--emit-receipt",
        vac_receipt_path.to_str().unwrap(),
        "--json",
    ]);
    assert!(
        !vac_judge_out.status.success(),
        "`obb judge check` must fail when `#tooth` is VACUOUS"
    );
    let vac_stdout = String::from_utf8_lossy(&vac_judge_out.stdout);
    assert!(
        vac_stdout.contains("VACUOUS"),
        "expected VACUOUS in judge output, got: {vac_stdout}"
    );

    let vac_receipt: JudgeReceipt =
        serde_json::from_str(&fs::read_to_string(&vac_receipt_path).unwrap()).unwrap();
    assert!(!vac_receipt.all_passed);
    assert_eq!(vac_receipt.teeth_report.vacuous_count, 1);
    let vac_prop_err = store
        .propose_quest("Q-e2e", "lane-alpha", &vac_receipt, &repo, "main")
        .unwrap_err();
    assert!(matches!(vac_prop_err, StateRefusal::GuardFailed { .. }));

    // Tampering with `vac_receipt` fields without recomputing valid oracle hash MUST trigger `TamperedReceipt`!
    let mut forged = vac_receipt.clone();
    forged.all_passed = true;
    forged.achieved_regime = Regime::Decided;
    forged.teeth_report.all_bit = true;
    let forge_err = store
        .propose_quest("Q-e2e", "lane-alpha", &forged, &repo, "main")
        .unwrap_err();
    assert!(
        matches!(forge_err, StateRefusal::TamperedReceipt { .. }),
        "expected TamperedReceipt, got {forge_err:?}"
    );

    // 6. Fix `tests/test_calc.py` + `teeth.json` so `#tooth` genuinely bites (`BIT`), emit receipt, and `propose`!
    write_rel(
        &repo,
        "tests/test_calc.py",
        "import sys\nsys.path.insert(0, 'src')\nfrom calc import safe_div\nassert safe_div(10, 2) == 5\ntry:\n    safe_div(1, 0)\n    raise SystemExit('expected ValueError')\nexcept ValueError:\n    pass\nprint('ran 2 tests ok')\n",
    );
    write_rel(
        &repo,
        "teeth.json",
        &serde_json::to_string_pretty(&biting_spec).unwrap(),
    );
    // `shared/util.txt` is outside the declared lease and held by nobody: the lease grows to
    // cover it instead of forcing the candidate to duplicate the shared file locally.
    write_rel(&repo, "shared/util.txt", "shared helper\n");
    git_cmd(
        &repo,
        &["add", "tests/test_calc.py", "teeth.json", "shared/util.txt"],
    );
    git_cmd(
        &repo,
        &[
            "commit",
            "-m",
            "add zero-divisor assertion and biting tooth",
        ],
    );

    let good_receipt_path = tmp.path().join("good-receipt.json");
    let ok_judge_out = run_obb(&[
        "judge",
        "check",
        "--strict-tests",
        "--judge",
        judge_path.to_str().unwrap(),
        "--repo",
        repo.to_str().unwrap(),
        "--base",
        "main",
        "--emit-receipt",
        good_receipt_path.to_str().unwrap(),
    ]);
    assert!(
        ok_judge_out.status.success(),
        "expected biting tooth judge check to exit 0:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&ok_judge_out.stdout),
        String::from_utf8_lossy(&ok_judge_out.stderr)
    );

    let prop_out = run_obb(&[
        "state",
        "--state-dir",
        state_dir.to_str().unwrap(),
        "propose",
        "Q-e2e",
        "--actor",
        "lane-alpha",
        "--receipt",
        good_receipt_path.to_str().unwrap(),
        "--repo",
        repo.to_str().unwrap(),
        "--trunk",
        "main",
    ]);
    assert!(
        prop_out.status.success(),
        "obb state propose failed: {}",
        String::from_utf8_lossy(&prop_out.stderr)
    );
    let q_toothed = store.get_quest("Q-e2e").unwrap().unwrap();
    assert_eq!(q_toothed.state, "Toothed");
    assert!(
        q_toothed
            .footprint_lease
            .iter()
            .any(|p| p == "shared/util.txt"),
        "uncontended out-of-lease path must extend the lease: {:?}",
        q_toothed.footprint_lease
    );
    assert!(store.read_ledger().unwrap().iter().any(|e| {
        e.event_type == "quest.footprint_extended"
            && e.entity_id == "Q-e2e"
            && e.payload["out_of_declared_footprint"] == serde_json::json!(["shared/util.txt"])
    }));

    // 7. Advance `main` with an independent commit so `good_receipt.base_sha` becomes STALE!
    git_cmd(&repo, &["checkout", "main"]);
    write_rel(
        &repo,
        "NOTES.txt",
        "trunk rev 2 (concurrent commit landed)\n",
    );
    git_cmd(&repo, &["add", "NOTES.txt"]);
    git_cmd(&repo, &["commit", "-m", "concurrent trunk commit"]);
    let advanced_main_sha = git_cmd(&repo, &["rev-parse", "main"]).trim().to_string();
    assert_ne!(initial_main_sha, advanced_main_sha);
    git_cmd(&repo, &["checkout", "quest/Q-e2e"]);

    let stale_receipt = JudgeReceipt::load_from_path(&good_receipt_path).unwrap();
    let stale_err = store
        .land_quest("Q-e2e", "lane-alpha", &stale_receipt, &repo, "main")
        .unwrap_err();
    assert!(
        matches!(
            stale_err,
            StateRefusal::StaleBaseSha {
                ref receipt_base_sha,
                ref current_trunk_sha,
                ..
            } if receipt_base_sha == &initial_main_sha && current_trunk_sha == &advanced_main_sha
        ),
        "expected StaleBaseSha when trunk moved, got {stale_err:?}"
    );

    let stale_cli_out = run_obb(&[
        "state",
        "--state-dir",
        state_dir.to_str().unwrap(),
        "land",
        "Q-e2e",
        "--actor",
        "lane-alpha",
        "--receipt",
        good_receipt_path.to_str().unwrap(),
        "--repo",
        repo.to_str().unwrap(),
        "--trunk",
        "main",
    ]);
    assert!(!stale_cli_out.status.success());
    assert!(
        String::from_utf8_lossy(&stale_cli_out.stderr).contains("StaleBaseSha"),
        "CLI stderr should report StaleBaseSha: {}",
        String::from_utf8_lossy(&stale_cli_out.stderr)
    );

    // 8. Rebase `quest/Q-e2e` onto new `main`, re-run `obb judge check`, re-propose, `land`, `Claimed`, `Recorded`!
    git_cmd(&repo, &["rebase", "main"]);
    let rebased_head_sha = git_cmd(&repo, &["rev-parse", "HEAD"]).trim().to_string();

    let rebased_receipt_path = tmp.path().join("rebased-receipt.json");
    let reb_judge_out = run_obb(&[
        "judge",
        "check",
        "--strict-tests",
        "--judge",
        judge_path.to_str().unwrap(),
        "--repo",
        repo.to_str().unwrap(),
        "--base",
        "main",
        "--emit-receipt",
        rebased_receipt_path.to_str().unwrap(),
    ]);
    assert!(reb_judge_out.status.success());

    let reprop_out = run_obb(&[
        "state",
        "--state-dir",
        state_dir.to_str().unwrap(),
        "propose",
        "Q-e2e",
        "--actor",
        "lane-alpha",
        "--receipt",
        rebased_receipt_path.to_str().unwrap(),
        "--repo",
        repo.to_str().unwrap(),
        "--trunk",
        "main",
    ]);
    assert!(reprop_out.status.success());

    let land_out = run_obb(&[
        "state",
        "--state-dir",
        state_dir.to_str().unwrap(),
        "land",
        "Q-e2e",
        "--actor",
        "lane-alpha",
        "--receipt",
        rebased_receipt_path.to_str().unwrap(),
        "--repo",
        repo.to_str().unwrap(),
        "--trunk",
        "main",
    ]);
    assert!(
        land_out.status.success(),
        "obb state land failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&land_out.stdout),
        String::from_utf8_lossy(&land_out.stderr)
    );

    // Verify `main` fast-forwarded to `rebased_head_sha` and side branch `quest/Q-e2e` was cleaned up (`Q5`)
    let post_land_main = git_cmd(&repo, &["rev-parse", "main"]).trim().to_string();
    assert_eq!(post_land_main, rebased_head_sha);
    let q5 = StateStore::probe_git_q5(&repo).unwrap();
    assert!(
        q5.q5_passed,
        "expected Q5 clean after land, got merged_side_branches={:?}",
        q5.merged_side_branches
    );

    // Advance `Landed -> Claimed -> Recorded` via CLI
    let claim_out = run_obb(&[
        "state",
        "--state-dir",
        state_dir.to_str().unwrap(),
        "quest",
        "--id",
        "Q-e2e",
        "--to",
        "Claimed",
        "--actor",
        "lane-alpha",
        "--receipt",
        rebased_receipt_path.to_str().unwrap(),
        "--repo",
        repo.to_str().unwrap(),
        "--trunk",
        "main",
    ]);
    assert!(
        claim_out.status.success(),
        "Claimed failed: {}",
        String::from_utf8_lossy(&claim_out.stderr)
    );

    let record_out = run_obb(&[
        "state",
        "--state-dir",
        state_dir.to_str().unwrap(),
        "quest",
        "--id",
        "Q-e2e",
        "--to",
        "Recorded",
        "--actor",
        "lane-alpha",
        "--repo",
        repo.to_str().unwrap(),
        "--summary",
        "Landed safe_div zero-divisor assertion with executed red tooth",
    ]);
    assert!(
        record_out.status.success(),
        "Recorded failed: {}",
        String::from_utf8_lossy(&record_out.stderr)
    );

    let verify_ledger_out = run_obb(&[
        "ledger",
        "--state-dir",
        state_dir.to_str().unwrap(),
        "verify",
    ]);
    assert!(verify_ledger_out.status.success());

    let snap_final = store.snapshot().unwrap();
    assert!(!snap_final.contains_demo_seed);
    assert_eq!(snap_final.demo_seed_event_count, 0);
    assert_eq!(snap_final.verified_quest_count, 1);
    assert_eq!(snap_final.ungated_override_count, 0);
    assert!(snap_final.live_transition_count >= 7);

    let final_q = store.get_quest("Q-e2e").unwrap().unwrap();
    assert_eq!(final_q.state, "Recorded");
    assert_eq!(final_q.effective_regime, "decided");
    assert!(!final_q.merged_ungated);
    assert_eq!(
        final_q.landed_sha.as_deref(),
        Some(rebased_head_sha.as_str())
    );

    // Second slice reuses the now-released footprint, rejects a faulty library test,
    // then converges a valid implementation refactor onto the first slice's trunk.
    let cli_ok = |args: &[&str]| {
        let output = run_obb(args);
        assert!(
            output.status.success(),
            "{args:?}: {}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    };
    let state = state_dir.to_str().unwrap();
    let repo_arg = repo.to_str().unwrap();
    cli_ok(&[
        "state",
        "--state-dir",
        state,
        "take",
        "Q-overlap",
        "--actor",
        "lane-beta",
        "--deliverable",
        "Equivalent division refactor",
        "--footprint",
        "src/",
        "--repo",
        repo_arg,
        "--trunk",
        "main",
    ]);
    git_cmd(&repo, &["checkout", "-b", "quest/Q-overlap", "main"]);
    let valid_source = fs::read_to_string(repo.join("src/calc.py"))
        .unwrap()
        .replace("return a // b", "return divmod(a, b)[0]");
    write_rel(
        &repo,
        "src/calc.py",
        &format!("{valid_source}\ndef test_embedded():\n    pass\n"),
    );
    git_cmd(&repo, &["add", "src/calc.py"]);
    git_cmd(
        &repo,
        &["commit", "-m", "faulty second slice with embedded test"],
    );
    let lint_bad = run_obb(&["lint", "--repo", repo_arg, "--strict", "--strict-tests"]);
    assert!(!lint_bad.status.success());
    let bad_receipt_path = tmp.path().join("second-bad.json");
    let bad_judge = run_obb(&[
        "judge",
        "check",
        "--strict-tests",
        "--judge",
        judge_path.to_str().unwrap(),
        "--repo",
        repo_arg,
        "--base",
        "main",
        "--emit-receipt",
        bad_receipt_path.to_str().unwrap(),
    ]);
    assert!(!bad_judge.status.success());
    let bad_propose = run_obb(&[
        "state",
        "--state-dir",
        state,
        "propose",
        "Q-overlap",
        "--actor",
        "lane-beta",
        "--repo",
        repo_arg,
        "--trunk",
        "main",
        "--receipt",
        bad_receipt_path.to_str().unwrap(),
    ]);
    assert!(!bad_propose.status.success());
    write_rel(&repo, "src/calc.py", &valid_source);
    git_cmd(&repo, &["add", "src/calc.py"]);
    git_cmd(&repo, &["commit", "-m", "keep tests outside the library"]);
    cli_ok(&["lint", "--repo", repo_arg, "--strict", "--strict-tests"]);
    let second_receipt = tmp.path().join("second-good.json");
    cli_ok(&[
        "judge",
        "check",
        "--strict-tests",
        "--judge",
        judge_path.to_str().unwrap(),
        "--repo",
        repo_arg,
        "--base",
        "main",
        "--emit-receipt",
        second_receipt.to_str().unwrap(),
    ]);
    for verb in ["propose", "land"] {
        cli_ok(&[
            "state",
            "--state-dir",
            state,
            verb,
            "Q-overlap",
            "--actor",
            "lane-beta",
            "--repo",
            repo_arg,
            "--trunk",
            "main",
            "--receipt",
            second_receipt.to_str().unwrap(),
        ]);
    }
    for stage in ["Claimed", "Recorded"] {
        cli_ok(&[
            "state",
            "--state-dir",
            state,
            "quest",
            "--id",
            "Q-overlap",
            "--to",
            stage,
            "--actor",
            "lane-beta",
            "--repo",
            repo_arg,
            "--receipt",
            second_receipt.to_str().unwrap(),
            "--summary",
            "Two slices converged with strict lint and executed mutation checks",
        ]);
    }
    let converged = store.snapshot().unwrap();
    assert_eq!(converged.verified_quest_count, 2);
    // `Q-docs` only exists to hold the contended `docs/` lease in step 4 and stays `Scoped`.
    assert!(
        converged
            .quests
            .iter()
            .filter(|q| q.id != "Q-docs")
            .all(|q| q.state == "Recorded")
    );
    assert_eq!(store.get_quest("Q-docs").unwrap().unwrap().state, "Scoped");
    assert!(StateStore::probe_git_q5(&repo).unwrap().q5_passed);
    assert!(git_cmd(&repo, &["status", "--porcelain"]).trim().is_empty());
    cli_ok(&["ledger", "--state-dir", state, "verify"]);
    let first_fold = run_obb(&["ledger", "--state-dir", state, "snapshot"]);
    let second_fold = run_obb(&["ledger", "--state-dir", state, "snapshot"]);
    assert!(first_fold.status.success() && second_fold.status.success());
    assert_eq!(first_fold.stdout, second_fold.stdout);
}

// =============================================================================
// 4. `AttestedOverride` (`merged_ungated`) Honesty & Demo-Seed Segregation
// =============================================================================

#[test]
fn emergency_override_records_attested_override_ungated_and_demo_seed_is_segregated() {
    let tmp = temp_in_private_tmp("obb-override-seed-");
    let repo = tmp.path().join("repo");
    let live_state_dir = tmp.path().join("live-state");
    let demo_state_dir = tmp.path().join("demo-state");
    fs::create_dir_all(&repo).unwrap();
    init_git_repo_on_main(&repo);

    write_rel(&repo, "README.md", "# Emergency Repo\n");
    git_cmd(&repo, &["add", "README.md"]);
    git_cmd(&repo, &["commit", "-m", "initial"]);

    let store = StateStore::open_with_state_dir(&workspace_root(), Some(&live_state_dir)).unwrap();
    store
        .create_campaign(
            "C-ops",
            "Ops Campaign",
            "Keep service alive",
            repo.to_str().unwrap(),
        )
        .unwrap();
    store
        .create_quest(
            "Q-emerg",
            "C-ops",
            "Emergency hotfix without tooth",
            "lane-ops",
            "decided",
        )
        .unwrap();

    git_cmd(&repo, &["checkout", "-b", "hotfix/Q-emerg"]);
    write_rel(&repo, "hotfix.txt", "mitigate production outage\n");
    git_cmd(&repo, &["add", "hotfix.txt"]);
    git_cmd(&repo, &["commit", "-m", "emergency hotfix"]);
    let hotfix_sha = git_cmd(&repo, &["rev-parse", "HEAD"]).trim().to_string();

    let override_out = run_obb(&[
        "state",
        "--state-dir",
        live_state_dir.to_str().unwrap(),
        "land",
        "Q-emerg",
        "--repo",
        repo.to_str().unwrap(),
        "--trunk",
        "main",
        "--head",
        "hotfix/Q-emerg",
        "--override-operator",
        "ember",
        "--override-reason",
        "urgent outage mitigation without tooth",
    ]);
    assert!(
        override_out.status.success(),
        "emergency override land should record reality and succeed: {}",
        String::from_utf8_lossy(&override_out.stderr)
    );

    let q_emerg = store.get_quest("Q-emerg").unwrap().unwrap();
    assert_eq!(q_emerg.state, "Landed");
    assert!(q_emerg.merged_ungated);
    assert_eq!(q_emerg.effective_regime, REGIME_ATTESTED_OVERRIDE);
    assert_eq!(q_emerg.landed_sha.as_deref(), Some(hotfix_sha.as_str()));

    let live_snap = store.snapshot().unwrap();
    assert_eq!(
        live_snap.verified_quest_count, 0,
        "ungated override must NEVER count as a verified (`decided`/`certified`) quest"
    );
    assert_eq!(live_snap.ungated_override_count, 1);

    let ledger = store.read_ledger().unwrap();
    assert!(
        ledger
            .iter()
            .any(|e| e.event_type == "quest.override_transition"),
        "expected quest.override_transition in ledger"
    );

    // Attempting to promote an ungated quest into `Recorded` MUST be refused!
    let rec_err = store
        .transition_quest(
            "Q-emerg",
            "Recorded",
            "ember",
            None,
            QuestGuardEvidence::RecordCheck {
                repo_root: repo.clone(),
                summary: "try to launder override".into(),
            },
        )
        .unwrap_err();
    assert!(matches!(
        rec_err,
        StateRefusal::IllegalTransition { .. } | StateRefusal::GuardFailed { .. }
    ));

    // Separate vault: verify 28-row `seed_obend_campaign` is strictly marked `demo_seed` and
    // reports `0` live transitions and `0` verified quests!
    let demo_store =
        StateStore::open_with_state_dir(&workspace_root(), Some(&demo_state_dir)).unwrap();
    let demo_snap = demo_store.seed_obend_campaign(&repo).unwrap();
    assert!(demo_snap.contains_demo_seed);
    assert_eq!(demo_snap.demo_seed_event_count, 28);
    assert_eq!(demo_snap.live_event_count, 0);
    assert_eq!(
        demo_snap.live_transition_count, 0,
        "28-row demo seed must NEVER masquerade as live operational transitions"
    );
    assert_eq!(demo_snap.verified_quest_count, 0);
    assert!(
        demo_snap
            .quests
            .iter()
            .all(|q| q.origin == ORIGIN_DEMO_SEED && q.effective_regime == ORIGIN_DEMO_SEED)
    );
}

#[test]
fn structural_scanner_tracks_lines_and_ignores_comments_literals_and_test_files() {
    use obb_lint::{RepoLintOptions, run_repo_lints_with_options};
    let tmp = temp_in_private_tmp("obb-scanner-");
    let fixtures = [
        (
            "src/lib.rs",
            r###"/// #[test]
/* outer #[cfg(test)] /* nested #[tokio::test] */ end */
pub const DOC: &str = r##"quoted " #[test]
#[cfg(test)]"##;
pub const BYTES: &[u8] = br#"#[test]"#;
pub const C: char = '"';
pub fn identity<'a>(x: &'a str) -> &'a str { x }
# [ cfg (
 test
) ]
mod suite {}
#[test]
fn actual() {}
#[tokio::test(flavor = "current_thread")]
async fn async_actual() {}
"###,
            vec![8, 12, 14],
        ),
        (
            "src/widget.ts",
            r#"/** test('ignored') */
const single = 'it("ignored")';
const template = `describe('ignored')
test('ignored')`;
const regex = /describe\(test\(/;
// it('ignored')
describe /* gap */ (
 'suite', () => { it('case', () => {}); test('case2', () => {}); });
"#,
            vec![7, 8, 8],
        ),
        (
            "src/library.py",
            r#"# def test_comment(): pass
text = r'''def test_string():
    unittest.TestCase'''
other = "def test_inline(): pass"
def test_actual():
    pass
class Actual(unittest.TestCase):
    pass
"#,
            vec![5, 7],
        ),
        (
            "src/nested/Library.lean",
            r##"/- #eval 1 /- #guard_msgs -/ -/
/-- #eval 1 -/
def text := r#"#eval 1 #guard_msgs"#
#eval 1
#guard_msgs in
#eval 2
"##,
            vec![4, 5, 6],
        ),
    ];
    for (path, source, _) in &fixtures {
        write_rel(tmp.path(), path, source);
    }
    for path in [
        "tests/lib.rs",
        "src/widget.test.ts",
        "src/widget.spec.js",
        "test_suite.py",
        "src/__tests__/widget.js",
    ] {
        write_rel(
            tmp.path(),
            path,
            "#[test]\ntest('allowed')\ndef test_allowed(): pass\n",
        );
    }
    let options = RepoLintOptions {
        strict_tests: true,
        ..Default::default()
    };
    let report = run_repo_lints_with_options(tmp.path(), options).unwrap();
    let findings: Vec<_> = report
        .findings
        .iter()
        .filter(|f| f.rule_id.ends_with("test-in-library"))
        .collect();
    assert_eq!(findings.len(), 11, "{findings:#?}");
    for (path, _, lines) in fixtures {
        assert_eq!(
            findings
                .iter()
                .filter(|f| f.path == path)
                .map(|f| f.line)
                .collect::<Vec<_>>(),
            lines,
            "{path}"
        );
    }
    let relaxed = run_repo_lints_with_options(tmp.path(), RepoLintOptions::default()).unwrap();
    assert!(
        !relaxed
            .findings
            .iter()
            .any(|f| f.rule_id.ends_with("test-in-library"))
    );
    let out = run_obb(&[
        "lint",
        "--repo",
        tmp.path().to_str().unwrap(),
        "--strict",
        "--strict-tests",
        "--json",
    ]);
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stdout).contains("rust/test-in-library"));
}

#[test]
fn structural_tooth_executes_real_positive_and_faulty_controls_without_lean() {
    let result = obb_judge::evaluate_with_planted_fault_tooth("tier1").unwrap();
    assert_eq!(result.verdict, ToothVerdict::Bit, "{result:#?}");
    assert_eq!(result.detail.matches(": BIT").count(), 5);
    assert_eq!(
        result.positive_exit, None,
        "built-in probes must not invent shell exit codes"
    );
}

#[tokio::test]
async fn serve_enforces_auth_methods_content_type_and_bounded_streaming_bodies() {
    use axum::{
        body::Body,
        http::{Request, StatusCode},
    };
    use obb_cli::serve::{MAX_BODY_BYTES, ServeConfig, build_router};
    use tower::ServiceExt;
    let tmp = temp_in_private_tmp("obb-http-");
    let cfg = ServeConfig::new(
        tmp.path().into(),
        tmp.path().into(),
        tmp.path().join("judge.json"),
    )
    .with_state_dir(Some(tmp.path().join("state")));
    let unconfigured = build_router(cfg.clone());
    assert_eq!(
        unconfigured
            .oneshot(
                Request::builder()
                    .uri("/api/status")
                    .body(Body::empty())
                    .unwrap()
            )
            .await
            .unwrap()
            .status(),
        StatusCode::SERVICE_UNAVAILABLE
    );
    let app = build_router(cfg.with_bearer_token("long-secret-token"));
    for (method, auth, content_type, body, expected) in [
        ("GET", "", "", "", StatusCode::UNAUTHORIZED),
        (
            "GET",
            "Bearer wrong-token",
            "",
            "",
            StatusCode::UNAUTHORIZED,
        ),
        (
            "GET",
            "Bearer long-secret-tokeN",
            "",
            "",
            StatusCode::UNAUTHORIZED,
        ),
        ("GET", "Bearer long-secret-token", "", "", StatusCode::OK),
        ("HEAD", "Bearer long-secret-token", "", "", StatusCode::OK),
        (
            "POST",
            "Bearer long-secret-token",
            "application/json",
            "{}",
            StatusCode::METHOD_NOT_ALLOWED,
        ),
        (
            "GET",
            "Bearer long-secret-token",
            "text/plain",
            "",
            StatusCode::UNSUPPORTED_MEDIA_TYPE,
        ),
        (
            "GET",
            "Bearer long-secret-token",
            "application/jsonp",
            "",
            StatusCode::UNSUPPORTED_MEDIA_TYPE,
        ),
        (
            "GET",
            "Bearer long-secret-token",
            "application/json",
            "{}",
            StatusCode::BAD_REQUEST,
        ),
    ] {
        let mut req = Request::builder().method(method).uri("/api/status");
        if !auth.is_empty() {
            req = req.header("authorization", auth);
        }
        if !content_type.is_empty() {
            req = req.header("content-type", content_type);
        }
        assert_eq!(
            app.clone()
                .oneshot(req.body(Body::from(body)).unwrap())
                .await
                .unwrap()
                .status(),
            expected
        );
    }
    // No Content-Length: the body collector must enforce the ceiling on chunks too.
    let chunks = tokio_stream::iter([
        Ok::<_, std::io::Error>(vec![b'x'; MAX_BODY_BYTES]),
        Ok(vec![b'x'; 1]),
    ]);
    let req = Request::builder()
        .uri("/api/status")
        .header("authorization", "Bearer long-secret-token")
        .body(Body::from_stream(chunks))
        .unwrap();
    assert_eq!(
        app.clone().oneshot(req).await.unwrap().status(),
        StatusCode::PAYLOAD_TOO_LARGE
    );
    let req = Request::builder()
        .uri("/api/status")
        .header("authorization", "Bearer long-secret-token")
        .header("authorization", "Bearer long-secret-token")
        .body(Body::empty())
        .unwrap();
    assert_eq!(
        app.oneshot(req).await.unwrap().status(),
        StatusCode::UNAUTHORIZED
    );
}

#[test]
fn local_ledger_serializes_concurrent_writers_and_migrates_with_deterministic_fold() {
    let tmp = temp_in_private_tmp("obb-ledger-");
    let state = tmp.path().join("state");
    let store = StateStore::open_with_state_dir(tmp.path(), Some(&state)).unwrap();
    std::thread::scope(|scope| {
        for writer in 0..8 {
            let store = &store;
            scope.spawn(move || {
                for row in 0..24 {
                    store
                        .append_ledger(
                            "test.event",
                            &format!("writer-{writer}"),
                            "concurrent",
                            serde_json::json!({"row": row}),
                        )
                        .unwrap();
                    store.verify_ledger_chain().unwrap();
                }
            });
        }
    });
    assert_eq!(store.verify_ledger_chain().unwrap(), 192);
    let snapshot = store.ledger_snapshot().unwrap();
    assert_eq!(snapshot, store.ledger_snapshot().unwrap());
    let migrated =
        StateStore::open_with_state_dir(tmp.path(), Some(&tmp.path().join("migrated"))).unwrap();
    assert_eq!(migrated.migrate_ledger(store.ledger_path()).unwrap(), 192);
    assert_eq!(migrated.migrate_ledger(store.ledger_path()).unwrap(), 192);
    assert_eq!(migrated.ledger_snapshot().unwrap(), snapshot);
    migrated
        .append_ledger(
            "test.other",
            "different",
            "divergence",
            serde_json::json!({}),
        )
        .unwrap();
    assert!(migrated.migrate_ledger(store.ledger_path()).is_err());
    let bad = tmp.path().join("bad.jsonl");
    let raw =
        fs::read_to_string(store.ledger_path())
            .unwrap()
            .replacen("concurrent", "tampered", 1);
    fs::write(&bad, raw).unwrap();
    assert!(migrated.migrate_ledger(&bad).is_err());
    assert!(!tmp.path().join("ledger/events.jsonl").exists());
}

#[test]
fn nested_javascript_templates_are_literals_and_unicode_ledger_tails_append_safely() {
    let tmp = temp_in_private_tmp("obb-lexical-edges-");
    write_rel(
        tmp.path(),
        "src/widget.js",
        r#"const nested = `outer ${`test('literal') ${"describe('literal')"}`} tail`;
const regex = /test(group)/;
const value = 9 / 3;
test('real', () => {});
"#,
    );
    let findings = obb_lint::test_in_library::scan_test_in_library(tmp.path()).unwrap();
    assert_eq!(findings.len(), 1, "{findings:#?}");
    assert_eq!(findings[0].line, 4);
    let store =
        StateStore::open_with_state_dir(tmp.path(), Some(&tmp.path().join("state"))).unwrap();
    for size in [40_000, 40_001, 40_002] {
        store
            .append_ledger(
                "unicode",
                "entity",
                "large record",
                serde_json::json!({"text": "é界".repeat(size)}),
            )
            .unwrap();
        store
            .append_ledger("small", "entity", "after unicode", serde_json::json!({}))
            .unwrap();
    }
    assert_eq!(store.verify_ledger_chain().unwrap(), 6);
    let mut raw = fs::read(store.ledger_path()).unwrap();
    raw.pop();
    fs::write(store.ledger_path(), raw).unwrap();
    assert!(
        store
            .append_ledger(
                "small",
                "entity",
                "torn append refused",
                serde_json::json!({})
            )
            .is_err()
    );
}

#[test]
fn scanner_skips_cfg_not_test_and_plain_calls_but_catches_inner_attrs_and_focused_tests() {
    let tmp = temp_in_private_tmp("obb-scanner-edges-");
    write_rel(
        tmp.path(),
        "src/lib.rs",
        r#"#[cfg(not(test))]
pub fn prod() {}
pub const X: char = '\x41';
pub const Q: char = '\'';
#[async_std::test]
async fn runtime_case() {}
"#,
    );
    write_rel(
        tmp.path(),
        "src/inner.rs",
        "#![cfg(test)]\nfn helper() {}\n",
    );
    write_rel(
        tmp.path(),
        "src/lib.ts",
        r#"export function check(value: string) { return test(value); }
class Probe { test(value: string) { return value; } }
it.only('focused', () => {});
"#,
    );
    let mut got: Vec<(String, usize)> = obb_lint::test_in_library::scan_test_in_library(tmp.path())
        .unwrap()
        .into_iter()
        .map(|f| (f.path, f.line))
        .collect();
    got.sort();
    assert_eq!(
        got,
        vec![
            ("src/inner.rs".to_string(), 1),
            ("src/lib.rs".to_string(), 5),
            ("src/lib.ts".to_string(), 3),
        ]
    );
}

#[test]
fn construction_clock_defers_teeth_and_revert_floors_and_never_exceeds_attested() {
    use obb_judge::{JudgeClock, evaluate_gate_on};
    let workspace = workspace_root();
    let gate = Gate::load_from_path(&workspace.join("judge.json")).unwrap();
    let report = evaluate_gate_on(&gate, &workspace, JudgeClock::Construction).unwrap();
    assert_eq!(report.clock, JudgeClock::Construction);
    assert_eq!(report.achieved_regime, Regime::Attested);
    assert_eq!(report.teeth_report.total, 0);
    assert!(
        report
            .deferred_floors
            .iter()
            .any(|f| f.starts_with("home "))
    );
    assert!(
        report
            .evaluations
            .iter()
            .all(|e| e.cell != "home_revert_clean" && e.cell != "planted_fault_red")
    );
}

// Authenticated evidence, input cones, exact proposals, deletion-only candidates.

fn receipt_gate_repo(root: &Path) -> (PathBuf, Gate) {
    let repo = root.join("repo");
    fs::create_dir_all(&repo).unwrap();
    init_git_repo_on_main(&repo);
    let command_floor: Floor = serde_json::from_value(serde_json::json!({
        "floor": "value_is_good",
        "inputs": ["src/**/*.txt"],
        "command": "test \"$(cat src/value.txt)\" = good"
    }))
    .unwrap();
    let tooth: ToothSpec = serde_json::from_value(serde_json::json!({
        "id": "value-tooth",
        "inputs": ["src/"],
        "check_cmd": "test \"$(cat src/value.txt)\" = good || { echo incorrect-value; exit 1; }",
        "mutation": {"kind": "replace", "file": "src/value.txt", "search": "good", "replace": "bad"},
        "expect_failure_substring": "incorrect-value"
    })).unwrap();
    let gate = build_gate(
        "receipt-gate",
        vec![
            (
                Floor::Home(1),
                Method::Eval(TrustBase::External("git-merge-tree".into())),
            ),
            (
                command_floor,
                Method::Eval(TrustBase::External("shell".into())),
            ),
            (
                Floor::Named("planted_fault_red".into()),
                Method::Eval(TrustBase::Compiled),
            ),
        ],
        vec![
            TrustBase::External("git-merge-tree".into()),
            TrustBase::External("shell".into()),
            TrustBase::Compiled,
        ],
        vec![tooth],
    );
    write_rel(&repo, "src/value.txt", "good\n");
    write_rel(&repo, "dead.txt", "obsolete\n");
    write_rel(
        &repo,
        "judge.json",
        &serde_json::to_string_pretty(&gate).unwrap(),
    );
    git_cmd(&repo, &["add", "."]);
    git_cmd(&repo, &["commit", "-m", "baseline"]);
    (repo, gate)
}

fn take_receipt_quest(repo: &Path, state: &Path) -> StateStore {
    let store = StateStore::open_with_state_dir(repo, Some(state)).unwrap();
    store
        .create_campaign(
            "C",
            "Receipt boundaries",
            "Exercise receipt boundaries",
            repo.to_str().unwrap(),
        )
        .unwrap();
    store
        .create_quest("Q", "C", "Candidate", "worker", "decided")
        .unwrap();
    store
        .take_quest(
            "Q",
            "worker",
            "Deliver candidate",
            vec!["src/".into(), "dead.txt".into(), "NOTES.txt".into()],
            1.0,
            repo,
            "main",
        )
        .unwrap();
    git_cmd(repo, &["checkout", "-b", "candidate"]);
    store
}

#[test]
fn hmac_vectors_and_recomputed_forgery_are_rejected() {
    use obb_judge::receipt_auth::hmac_sha256;
    let hex = |bytes: [u8; 32]| -> String {
        use std::fmt::Write;
        bytes
            .iter()
            .fold(String::with_capacity(64), |mut output, byte| {
                write!(output, "{byte:02x}").unwrap();
                output
            })
    };
    assert_eq!(
        hex(hmac_sha256(&[0x0b; 20], b"Hi There")),
        "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
    );
    assert_eq!(
        hex(hmac_sha256(b"Jefe", b"what do ya want for nothing?")),
        "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
    );
    assert_eq!(
        hex(hmac_sha256(
            &[0xaa; 131],
            b"Test Using Larger Than Block-Size Key - Hash Key First"
        )),
        "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"
    );

    let tmp = temp_in_private_tmp("obb-auth-");
    let (repo, gate) = receipt_gate_repo(tmp.path());
    let store = take_receipt_quest(&repo, &tmp.path().join("state"));
    write_rel(&repo, "NOTES.txt", "candidate\n");
    git_cmd(&repo, &["add", "NOTES.txt"]);
    git_cmd(&repo, &["commit", "-m", "candidate"]);
    let receipt = issue_judge_receipt(&gate, &repo, "main").unwrap();
    let key_path = repo.join(".obb/receipt.key");
    let key = fs::read(&key_path).unwrap();
    assert_eq!(key.len(), 32);
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        assert_eq!(
            fs::metadata(&key_path).unwrap().permissions().mode() & 0o777,
            0o600
        );
    }
    receipt.verify_authenticated(&key).unwrap();
    assert!(receipt.verify_authenticated(b"wrong-key").is_err());
    for remove_mac in [false, true] {
        let mut forged = receipt.clone();
        forged.evaluations[0].detail = "fabricated evidence".into();
        forged.receipt_hash = forged.compute_hash().unwrap();
        if remove_mac {
            forged.receipt_mac = None;
        }
        forged.verify_integrity().unwrap();
        let error = store
            .propose_quest("Q", "worker", &forged, &repo, "main")
            .unwrap_err();
        assert!(
            matches!(error, StateRefusal::TamperedReceipt { ref reason, .. } if reason.contains("receipt_mac")),
            "{error:?}"
        );
        assert_eq!(store.get_quest("Q").unwrap().unwrap().state, "Scoped");
    }
    store
        .propose_quest("Q", "worker", &receipt, &repo, "main")
        .unwrap();
    let mut forged = receipt.clone();
    forged.receipt_mac = Some("0".repeat(64));
    assert!(matches!(
        store.land_quest("Q", "worker", &forged, &repo, "main"),
        Err(StateRefusal::TamperedReceipt { .. })
    ));
    assert_eq!(
        git_cmd(&repo, &["rev-parse", "main"]).trim(),
        receipt.base_sha
    );
    store
        .land_quest("Q", "worker", &receipt, &repo, "main")
        .unwrap();
}

#[test]
fn cli_uses_selected_state_key_or_environment_key_for_receipts_and_cache() {
    for environment_key in [None, Some("external-signing-key")] {
        let tmp = temp_in_private_tmp("obb-cli-key-");
        let (repo, _gate) = receipt_gate_repo(tmp.path());
        let state = tmp.path().join("vault");
        let store = take_receipt_quest(&repo, &state);
        write_rel(&repo, "NOTES.txt", "candidate\n");
        git_cmd(&repo, &["add", "NOTES.txt"]);
        git_cmd(&repo, &["commit", "-m", "candidate"]);
        let output = tmp.path().join("receipt.json");
        let judge_args = [
            "--workspace",
            repo.to_str().unwrap(),
            "--state-dir",
            state.to_str().unwrap(),
            "judge",
            "check",
            "--repo",
            repo.to_str().unwrap(),
            "--base",
            "main",
            "--emit-receipt",
            output.to_str().unwrap(),
        ];
        let mut command = Command::new(obb_bin());
        command.args(judge_args).env_remove("OBB_RECEIPT_KEY");
        if let Some(key) = environment_key {
            command.env("OBB_RECEIPT_KEY", key);
        }
        let result = command.output().unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        let receipt = JudgeReceipt::load_from_path(&output).unwrap();
        let key = environment_key
            .map(|k| k.as_bytes().to_vec())
            .unwrap_or_else(|| fs::read(state.join(".obb/receipt.key")).unwrap());
        receipt.verify_authenticated(&key).unwrap();
        assert!(
            !repo.join(".obb/receipt.key").exists(),
            "receipt caching must use the selected signing key"
        );

        if environment_key.is_none() {
            // A repo-key-authenticated cache entry is not sufficient when signing with a vault key.
            write_rel(&repo, ".obb/receipt.key", "different-local-key");
            let local = Command::new(obb_bin())
                .args([
                    "--workspace",
                    repo.to_str().unwrap(),
                    "judge",
                    "check",
                    "--repo",
                    repo.to_str().unwrap(),
                    "--json",
                ])
                .env_remove("OBB_RECEIPT_KEY")
                .output()
                .unwrap();
            assert!(local.status.success());
            let local: obb_judge::JudgeCheckReport = serde_json::from_slice(&local.stdout).unwrap();
            assert!(!local.teeth_report.results[0].reused_from_cache);
            let result = command.output().unwrap();
            assert!(result.status.success());
            let vault_receipt = JudgeReceipt::load_from_path(&output).unwrap();
            assert!(!vault_receipt.teeth_report.results[0].reused_from_cache);
            vault_receipt.verify_authenticated(&key).unwrap();
        }
        let mut propose = Command::new(obb_bin());
        propose
            .args([
                "--workspace",
                repo.to_str().unwrap(),
                "--state-dir",
                state.to_str().unwrap(),
                "state",
                "propose",
                "Q",
                "--actor",
                "worker",
                "--repo",
                repo.to_str().unwrap(),
                "--trunk",
                "main",
                "--receipt",
                output.to_str().unwrap(),
            ])
            .env_remove("OBB_RECEIPT_KEY");
        if let Some(key) = environment_key {
            propose.env("OBB_RECEIPT_KEY", key);
        }
        let result = propose.output().unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(store.get_quest("Q").unwrap().unwrap().state, "Toothed");
        if environment_key.is_some() {
            let result = propose
                .env("OBB_RECEIPT_KEY", "wrong-key")
                .output()
                .unwrap();
            assert!(!result.status.success());
            assert!(String::from_utf8_lossy(&result.stderr).contains("receipt_mac"));
        }
    }
}

#[test]
fn cones_reuse_and_invalidate_on_inputs_commands_mutations_and_cache_tampering() {
    for definition in [
        serde_json::json!({"kind": "cap", "cell": "no_sorry_ax", "max": 0, "inputs": ["src/"]}),
        serde_json::json!({"kind": "home", "commits": 1, "inputs": ["src/"]}),
        serde_json::json!({"name": "no_sorry_ax", "inputs": ["src/"]}),
    ] {
        let floor: Floor = serde_json::from_value(definition).unwrap();
        assert_eq!(floor.inputs(), ["src/"]);
        assert_eq!(
            serde_json::from_value::<Floor>(serde_json::to_value(&floor).unwrap()).unwrap(),
            floor
        );
    }
    let tmp = temp_in_private_tmp("obb-cones-");
    let (repo, mut gate) = receipt_gate_repo(tmp.path());
    let floor = |report: &obb_judge::JudgeCheckReport| {
        report
            .evaluations
            .iter()
            .find(|e| e.cell == "value_is_good")
            .unwrap()
            .reused_from_cache
    };
    let first = evaluate_gate(&gate, &repo).unwrap();
    assert!(first.all_passed);
    assert!(!floor(&first));
    assert!(!first.teeth_report.results[0].reused_from_cache);
    let second = evaluate_gate(&gate, &repo).unwrap();
    assert!(floor(&second));
    assert!(second.teeth_report.results[0].reused_from_cache);
    assert_eq!(first.achieved_regime, second.achieved_regime);

    write_rel(&repo, "NOTES.txt", "outside both cones\n");
    git_cmd(&repo, &["add", "NOTES.txt"]);
    git_cmd(&repo, &["commit", "-m", "unrelated"]);
    let unrelated = evaluate_gate(&gate, &repo).unwrap();
    assert!(floor(&unrelated));
    assert!(unrelated.teeth_report.results[0].reused_from_cache);

    // Dirty input content must never be evaluated by looking only at HEAD's cached tree.
    write_rel(&repo, "src/value.txt", "bad\n");
    let dirty = evaluate_gate(&gate, &repo).unwrap();
    assert!(!dirty.all_passed);
    assert!(!floor(&dirty));
    assert!(!dirty.teeth_report.results[0].reused_from_cache);
    write_rel(&repo, "src/value.txt", "good\n\n");
    git_cmd(&repo, &["add", "src/value.txt"]);
    git_cmd(&repo, &["commit", "-m", "input edited"]);
    let changed = evaluate_gate(&gate, &repo).unwrap();
    assert!(changed.all_passed);
    assert!(!floor(&changed));
    assert!(!changed.teeth_report.results[0].reused_from_cache);

    // A glob must also notice additions nested below its literal directory prefix.
    write_rel(&repo, "src/nested/new.txt", "new input\n");
    git_cmd(&repo, &["add", "src/nested/new.txt"]);
    git_cmd(&repo, &["commit", "-m", "new input"]);
    let added = evaluate_gate(&gate, &repo).unwrap();
    assert!(!floor(&added));
    assert!(!added.teeth_report.results[0].reused_from_cache);

    for entry in fs::read_dir(repo.join(".obb/cache/cones")).unwrap() {
        let path = entry.unwrap().path();
        let mut cached: serde_json::Value =
            serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        cached["mac"] = serde_json::json!("0".repeat(64));
        fs::write(path, serde_json::to_vec(&cached).unwrap()).unwrap();
    }
    let tampered = evaluate_gate(&gate, &repo).unwrap();
    assert!(tampered.all_passed);
    assert!(!floor(&tampered));
    assert!(!tampered.teeth_report.results[0].reused_from_cache);

    if let Floor::Configured { command, .. } = &mut gate.floors[1] {
        *command = Some("exit 1".into());
    }
    if let ToothMutation::Replace { replace, .. } = &mut gate.teeth[0].mutation {
        *replace = "good".into();
    }
    let changed_checks = evaluate_gate(&gate, &repo).unwrap();
    assert!(!changed_checks.all_passed);
    assert!(!floor(&changed_checks));
    assert!(!changed_checks.teeth_report.results[0].reused_from_cache);
    assert_eq!(
        changed_checks.teeth_report.results[0].verdict,
        ToothVerdict::InvalidTooth
    );
    let failed_cached = evaluate_gate(&gate, &repo).unwrap();
    assert!(!failed_cached.all_passed);
    assert!(floor(&failed_cached));
    assert!(failed_cached.teeth_report.results[0].reused_from_cache);
}

#[test]
fn land_rejects_unproposed_receipt_and_candidate_before_moving_trunk() {
    let tmp = temp_in_private_tmp("obb-binding-");
    let (repo, gate) = receipt_gate_repo(tmp.path());
    let store = take_receipt_quest(&repo, &tmp.path().join("state"));
    write_rel(&repo, "NOTES.txt", "first\n");
    git_cmd(&repo, &["add", "NOTES.txt"]);
    git_cmd(&repo, &["commit", "-m", "first candidate"]);
    let proposed = issue_judge_receipt(&gate, &repo, "main").unwrap();
    let quest = store
        .propose_quest("Q", "worker", &proposed, &repo, "main")
        .unwrap();
    assert_eq!(
        quest.proposed_head_sha.as_deref(),
        Some(proposed.head_sha.as_str())
    );
    assert_eq!(
        quest.verified_receipt_hash.as_deref(),
        Some(proposed.receipt_hash.as_str())
    );
    for change_candidate in [false, true] {
        if change_candidate {
            write_rel(&repo, "NOTES.txt", "second\n");
            git_cmd(&repo, &["add", "NOTES.txt"]);
            git_cmd(&repo, &["commit", "-m", "unproposed candidate"]);
        }
        let swapped = issue_judge_receipt(&gate, &repo, "main").unwrap();
        assert_ne!(proposed.receipt_hash, swapped.receipt_hash);
        let error = store
            .land_quest("Q", "worker", &swapped, &repo, "main")
            .unwrap_err();
        assert!(
            matches!(error, StateRefusal::GuardFailed { ref reason, .. } if reason.contains("proposed")),
            "{error:?}"
        );
        // The direct state transition has the same guard as the composite land verb.
        let direct = store
            .transition_quest(
                "Q",
                "Landed",
                "worker",
                None,
                QuestGuardEvidence::Receipt {
                    receipt: Box::new(swapped),
                    repo_root: repo.clone(),
                    trunk_branch: "main".into(),
                },
            )
            .unwrap_err();
        assert!(
            matches!(direct, StateRefusal::GuardFailed { ref reason, .. } if reason.contains("proposed"))
        );
        assert_eq!(
            git_cmd(&repo, &["rev-parse", "main"]).trim(),
            proposed.base_sha
        );
        assert_eq!(store.get_quest("Q").unwrap().unwrap().state, "Toothed");
    }
    let updated = issue_judge_receipt(&gate, &repo, "main").unwrap();
    store
        .propose_quest("Q", "worker", &updated, &repo, "main")
        .unwrap();
    store
        .land_quest("Q", "worker", &updated, &repo, "main")
        .unwrap();

    // A later receipt for the landed commit is different evidence; only the landed one claims.
    let later = issue_judge_receipt(&gate, &repo, &updated.base_sha).unwrap();
    assert_eq!(later.head_sha, updated.head_sha);
    assert_ne!(later.receipt_hash, updated.receipt_hash);
    let claim = |receipt: &JudgeReceipt| {
        store.transition_quest(
            "Q",
            "Claimed",
            "worker",
            None,
            QuestGuardEvidence::Receipt {
                receipt: Box::new(receipt.clone()),
                repo_root: repo.clone(),
                trunk_branch: "main".into(),
            },
        )
    };
    let refused = claim(&later).unwrap_err();
    assert!(
        matches!(refused, StateRefusal::GuardFailed { ref reason, .. } if reason.contains("landed")),
        "{refused:?}"
    );
    assert_eq!(store.get_quest("Q").unwrap().unwrap().state, "Landed");
    claim(&updated).unwrap();
}

#[test]
fn cones_refuse_reuse_when_tree_entries_cannot_speak_for_the_inputs() {
    let tmp = temp_in_private_tmp("obb-cone-entries-");
    let (repo, gate) = receipt_gate_repo(tmp.path());
    // (all floors passed, command floor reused, tooth reused)
    let run = |gate: &Gate| {
        let report = evaluate_gate(gate, &repo).unwrap();
        let floor = report
            .evaluations
            .iter()
            .find(|e| e.cell == "value_is_good")
            .unwrap()
            .reused_from_cache;
        (
            report.all_passed,
            floor,
            report.teeth_report.results[0].reused_from_cache,
        )
    };
    assert_eq!(run(&gate), (true, false, false));
    assert_eq!(run(&gate), (true, true, true));

    // A pattern selecting no committed path leaves nothing to bind the verdict to: without a
    // refusal its digest would stay constant across every later edit.
    let mut unbound = gate.clone();
    unbound.teeth[0].inputs = vec!["no-such-dir/".into()];
    if let Floor::Configured { inputs, .. } = &mut unbound.floors[1] {
        *inputs = vec!["src/**/*.txt".into(), "typo/**".into()];
    }
    for _ in 0..2 {
        assert_eq!(run(&unbound), (true, false, false));
    }

    // An ignored file inside the cone reaches the sandbox copy but is in no tree entry, and
    // `git status` stays clean.
    write_rel(&repo, ".git/info/exclude", "src/local.txt\n");
    write_rel(
        &repo,
        "src/local.txt",
        "ignored, yet readable by the check\n",
    );
    for _ in 0..2 {
        assert_eq!(run(&gate), (true, false, false));
    }
    fs::remove_file(repo.join("src/local.txt")).unwrap();
    assert_eq!(run(&gate), (true, true, true));

    // `assume-unchanged` hides a tracked edit from `git status`; the tree is still not HEAD.
    git_cmd(
        &repo,
        &["update-index", "--assume-unchanged", "src/value.txt"],
    );
    write_rel(&repo, "src/value.txt", "bad\n");
    assert_eq!(run(&gate), (false, false, false));
    assert!(
        !issue_judge_receipt(&gate, &repo, "main")
            .unwrap()
            .clean_working_tree
    );
    assert!(!StateStore::probe_git_q5(&repo).unwrap().clean_working_tree);
}

#[test]
fn pure_deletion_quest_reaches_recorded_and_missing_files_are_not_evidence() {
    let tmp = temp_in_private_tmp("obb-deletion-");
    let (repo, gate) = receipt_gate_repo(tmp.path());
    let store = take_receipt_quest(&repo, &tmp.path().join("state"));
    for artifacts in [vec![], vec!["never-existed.txt".into()]] {
        assert!(
            store
                .transition_quest(
                    "Q",
                    "Built",
                    "worker",
                    None,
                    QuestGuardEvidence::RepoCheck {
                        repo_root: repo.clone(),
                        artifacts,
                    }
                )
                .is_err()
        );
    }
    // An existing file outside the repository is not an artifact, even when its spelling
    // starts inside the lease.
    write_rel(tmp.path(), "outside.txt", "not part of the candidate\n");
    let escape = store
        .transition_quest(
            "Q",
            "Built",
            "worker",
            None,
            QuestGuardEvidence::RepoCheck {
                repo_root: repo.clone(),
                artifacts: vec!["src/../../outside.txt".into()],
            },
        )
        .unwrap_err();
    assert!(
        matches!(escape, StateRefusal::GuardFailed { ref reason, .. } if reason.contains("inside")),
        "{escape:?}"
    );
    fs::remove_file(repo.join("dead.txt")).unwrap();
    assert!(
        store
            .transition_quest(
                "Q",
                "Built",
                "worker",
                None,
                QuestGuardEvidence::RepoCheck {
                    repo_root: repo.clone(),
                    artifacts: vec!["dead.txt".into()],
                }
            )
            .is_err(),
        "uncommitted disappearance is not a candidate deletion"
    );
    git_cmd(&repo, &["add", "-u"]);
    git_cmd(&repo, &["commit", "-m", "delete obsolete file"]);
    let receipt = issue_judge_receipt(&gate, &repo, "main").unwrap();
    assert_eq!(receipt.changed_paths, ["dead.txt"]);
    assert!(receipt.all_passed);
    store
        .propose_quest("Q", "worker", &receipt, &repo, "main")
        .unwrap();
    store
        .land_quest("Q", "worker", &receipt, &repo, "main")
        .unwrap();
    store
        .transition_quest(
            "Q",
            "Claimed",
            "worker",
            None,
            QuestGuardEvidence::Receipt {
                receipt: Box::new(receipt),
                repo_root: repo.clone(),
                trunk_branch: "main".into(),
            },
        )
        .unwrap();
    let recorded = store
        .transition_quest(
            "Q",
            "Recorded",
            "worker",
            None,
            QuestGuardEvidence::RecordCheck {
                repo_root: repo.clone(),
                summary: "Removed the obsolete file and checked retained behavior".into(),
            },
        )
        .unwrap();
    assert_eq!(recorded.state, "Recorded");
    assert!(!repo.join("dead.txt").exists());
    assert!(!recorded.merged_ungated);
    store.verify_ledger_chain().unwrap();
}

#[tokio::test]
async fn lints_scan_live_target_and_report_baseline_delta() {
    use axum::{
        body::{Body, to_bytes},
        http::Request,
    };
    use obb_cli::serve::{ServeConfig, build_router};
    use tower::ServiceExt;
    let tmp = temp_in_private_tmp("obb-live-lints-");
    let repo = tmp.path().join("live-repo");
    fs::create_dir_all(&repo).unwrap();
    let baseline = obb_lint::run_repo_lints(&repo).unwrap();
    write_rel(
        &repo,
        "reports/obend-baseline.json",
        &serde_json::to_string(&baseline).unwrap(),
    );
    let app = build_router(
        ServeConfig::new(tmp.path().into(), repo.clone(), repo.join("judge.json"))
            .with_bearer_token("secret"),
    );
    for add_fault in [false, true, false] {
        write_rel(
            &repo,
            "lean/Live.lean",
            if add_fault {
                "theorem live : True := by sorry\n"
            } else {
                "theorem live : True := by trivial\n"
            },
        );
        let response = app
            .clone()
            .oneshot(
                Request::builder()
                    .uri("/api/lints")
                    .header("authorization", "Bearer secret")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        let json: serde_json::Value =
            serde_json::from_slice(&to_bytes(response.into_body(), usize::MAX).await.unwrap())
                .unwrap();
        assert_eq!(json["source"], "live");
        assert!(json["scanned_at"].as_str().is_some());
        assert_eq!(json["scanned_at"], json["generated_at"]);
        assert_eq!(
            json["delta"]["baseline_generated_at"],
            baseline.generated_at
        );
        let count = json["by_rule"]["lean/sorry-or-axiom"].as_u64().unwrap_or(0);
        assert_eq!(count > 0, add_fault, "{json}");
        assert_eq!(json["delta"]["total_findings"], json["total_findings"]);
    }
}

#[test]
fn convergence_gate_sha256_binds_propose_land_succession_and_override() {
    let tmp = temp_in_private_tmp("obb-gate-bind-");
    let (repo, strong_gate) = receipt_gate_repo(tmp.path());
    let state = tmp.path().join("state");
    let store = take_receipt_quest(&repo, &state);

    let strong_sha = strong_gate.canonical_sha256().unwrap();
    let camp0 = store.get_campaign("C").unwrap().unwrap();
    assert_eq!(camp0.gate_sha256.as_deref(), Some(strong_sha.as_str()));

    // Construct a weaker gate (drops `value_is_good` floor) that still passes WellFormed + teeth.
    let mut weak_gate = strong_gate.clone();
    weak_gate.name = "receipt-gate-weakened".into();
    weak_gate
        .floors
        .retain(|fl| fl.cell_key() != "value_is_good");
    weak_gate
        .methods
        .retain(|m| m.floor.cell_key() != "value_is_good");
    let weak_judge_path = tmp.path().join("weak-judge.json");
    fs::write(
        &weak_judge_path,
        serde_json::to_string_pretty(&weak_gate).unwrap(),
    )
    .unwrap();

    // Even if `C` steps `Aim -> Grounded` (G1) and attempts `G2` (`Briefed`) with `weak-judge.json`,
    // `G2` MUST refuse weakening the campaign's configured gate!
    store
        .transition_campaign(
            "C",
            "Grounded",
            CampaignGuardEvidence::WholeRead {
                foundation_files: vec!["judge.json".into()],
                note: "G1 read".into(),
            },
        )
        .unwrap();
    let g2_weak_err = store
        .transition_campaign(
            "C",
            "Running",
            CampaignGuardEvidence::Briefed {
                judge_path: weak_judge_path.clone(),
                note: "try weaker judge".into(),
            },
        )
        .unwrap_err();
    assert!(
        matches!(g2_weak_err, StateRefusal::GuardFailed { ref guard, .. } if guard == "G2"),
        "expected G2 regression refusal, got: {g2_weak_err:?}"
    );
    store
        .transition_campaign(
            "C",
            "Running",
            CampaignGuardEvidence::Briefed {
                judge_path: repo.join("judge.json"),
                note: "brief configured strong gate".into(),
            },
        )
        .unwrap();

    // Candidate commit: earn a genuinely MAC-authenticated receipt under `weak_gate`.
    write_rel(&repo, "NOTES.txt", "candidate under weak gate\n");
    git_cmd(&repo, &["add", "NOTES.txt"]);
    git_cmd(&repo, &["commit", "-m", "candidate"]);

    let weak_receipt =
        issue_judge_receipt_with_state_dir(&weak_gate, &repo, "main", Some(&state)).unwrap();
    assert!(weak_receipt.all_passed);
    assert!(weak_receipt.receipt_mac.is_some());

    // `propose_quest` (and `obb state propose` CLI) MUST reject `weak_receipt` with `GateMismatch`!
    let prop_err = store
        .propose_quest("Q", "worker", &weak_receipt, &repo, "main")
        .unwrap_err();
    assert!(
        matches!(
            prop_err,
            StateRefusal::GateMismatch {
                ref quest_id,
                ref campaign_id,
                ref expected_gate_sha256,
                ref receipt_gate_sha256,
                ..
            } if quest_id == "Q"
                && campaign_id == "C"
                && expected_gate_sha256 == &strong_sha
                && receipt_gate_sha256 == &weak_receipt.gate_sha256
        ),
        "expected GateMismatch, got: {prop_err:?}"
    );
    assert_eq!(store.get_quest("Q").unwrap().unwrap().state, "Scoped");

    let weak_receipt_file = tmp.path().join("weak-receipt.json");
    fs::write(
        &weak_receipt_file,
        serde_json::to_string_pretty(&weak_receipt).unwrap(),
    )
    .unwrap();
    let cli_prop = run_obb(&[
        "--workspace",
        repo.to_str().unwrap(),
        "--state-dir",
        state.to_str().unwrap(),
        "state",
        "propose",
        "Q",
        "--actor",
        "worker",
        "--repo",
        repo.to_str().unwrap(),
        "--receipt",
        weak_receipt_file.to_str().unwrap(),
    ]);
    assert!(!cli_prop.status.success());
    assert!(
        String::from_utf8_lossy(&cli_prop.stderr).contains("GateMismatch"),
        "expected GateMismatch in stderr, got: {}",
        String::from_utf8_lossy(&cli_prop.stderr)
    );

    // Issue receipt under the campaign's configured `strong_gate` -> `propose_quest` succeeds.
    let strong_receipt =
        issue_judge_receipt_with_state_dir(&strong_gate, &repo, "main", Some(&state)).unwrap();
    store
        .propose_quest("Q", "worker", &strong_receipt, &repo, "main")
        .unwrap();
    assert_eq!(store.get_quest("Q").unwrap().unwrap().state, "Toothed");

    // Monotonically strengthen the campaign gate (`receipt-gate -> receipt-gate-stronger`, adding `no_sorry_ax`) BEFORE landing `Q`.
    let mut stronger_gate = strong_gate.clone();
    stronger_gate.name = "receipt-gate-stronger".into();
    stronger_gate
        .floors
        .push(Floor::Named("no_sorry_ax".into()));
    stronger_gate.basis.push(TrustBase::Lexical);
    for fmt in &stronger_gate.formats {
        stronger_gate.methods.push(MethodBinding {
            format: fmt.clone(),
            floor: Floor::Named("no_sorry_ax".into()),
            method: if fmt == "revert@1" {
                Method::Lemma
            } else {
                Method::Eval(TrustBase::Lexical)
            },
        });
    }
    let rec = check_succeed(&strong_gate, &stronger_gate, &[TrustBase::Lexical]).unwrap();
    store
        .record_lob_succession_with_gate(&rec, &stronger_gate)
        .unwrap();
    let stronger_sha = stronger_gate.canonical_sha256().unwrap();
    assert_eq!(
        store
            .get_campaign("C")
            .unwrap()
            .unwrap()
            .gate_sha256
            .as_deref(),
        Some(stronger_sha.as_str())
    );

    // Attempting to `land_quest` with the pre-succession `strong_receipt` MUST fail closed (`GateMismatch`)
    // without moving `main`!
    let stale_gate_land = store
        .land_quest("Q", "worker", &strong_receipt, &repo, "main")
        .unwrap_err();
    assert!(
        matches!(stale_gate_land, StateRefusal::GateMismatch { .. }),
        "expected GateMismatch on stale-gate land, got: {stale_gate_land:?}"
    );
    assert_eq!(
        git_cmd(&repo, &["rev-parse", "main"]).trim(),
        strong_receipt.base_sha
    );

    // Re-evaluate candidate under `stronger_gate`, re-propose `Q`, and land cleanly.
    let stronger_receipt =
        issue_judge_receipt_with_state_dir(&stronger_gate, &repo, "main", Some(&state)).unwrap();
    store
        .propose_quest("Q", "worker", &stronger_receipt, &repo, "main")
        .unwrap();
    store
        .land_quest("Q", "worker", &stronger_receipt, &repo, "main")
        .unwrap();
    assert_eq!(store.get_quest("Q").unwrap().unwrap().state, "Landed");

    // Strengthening the campaign gate AGAIN (`receipt-gate-strongest`) AFTER `Q` has already landed must NOT brick
    // claiming/recording `Q` on its landed evidence!
    let mut strongest_gate = stronger_gate.clone();
    strongest_gate.name = "receipt-gate-strongest".into();
    strongest_gate
        .floors
        .push(Floor::Named("no_declared_axiom".into()));
    for fmt in &strongest_gate.formats {
        strongest_gate.methods.push(MethodBinding {
            format: fmt.clone(),
            floor: Floor::Named("no_declared_axiom".into()),
            method: if fmt == "revert@1" {
                Method::Lemma
            } else {
                Method::Eval(TrustBase::Lexical)
            },
        });
    }
    let rec_strongest = check_succeed(&stronger_gate, &strongest_gate, &[]).unwrap();
    store
        .record_lob_succession_with_gate(&rec_strongest, &strongest_gate)
        .unwrap();

    store
        .transition_quest(
            "Q",
            "Claimed",
            "worker",
            None,
            QuestGuardEvidence::Receipt {
                receipt: Box::new(stronger_receipt),
                repo_root: repo.clone(),
                trunk_branch: "main".into(),
            },
        )
        .unwrap();
    let recorded = store
        .transition_quest(
            "Q",
            "Recorded",
            "worker",
            None,
            QuestGuardEvidence::RecordCheck {
                repo_root: repo.clone(),
                summary: "Landed under succeeded gate".into(),
            },
        )
        .unwrap();
    assert_eq!(recorded.state, "Recorded");

    // Emergency override (`land_quest_ungated`) remains available as an explicit, non-certifying escape hatch.
    store
        .create_quest("Q-emerg", "C", "Hotfix", "worker", "decided")
        .unwrap();
    git_cmd(&repo, &["checkout", "-b", "hotfix"]);
    write_rel(&repo, "NOTES.txt", "emergency hotfix\n");
    git_cmd(&repo, &["add", "NOTES.txt"]);
    git_cmd(&repo, &["commit", "-m", "emergency hotfix"]);
    let emerg = store
        .land_quest_ungated(
            "Q-emerg",
            "ember",
            "emergency production hotfix",
            &repo,
            "main",
            "hotfix",
        )
        .unwrap();
    assert_eq!(emerg.state, "Landed");
    assert!(emerg.merged_ungated);
    assert_eq!(emerg.effective_regime, REGIME_ATTESTED_OVERRIDE);
    store.verify_ledger_chain().unwrap();
}

#[test]
fn convergence_repo_identity_blocks_cross_checkout_transplants_and_allows_linked_worktrees() {
    fn copy_dir_all(src: &Path, dst: &Path) {
        fs::create_dir_all(dst).unwrap();
        for entry in fs::read_dir(src).unwrap() {
            let entry = entry.unwrap();
            let ty = entry.file_type().unwrap();
            let dest_path = dst.join(entry.file_name());
            if ty.is_dir() {
                copy_dir_all(&entry.path(), &dest_path);
            } else {
                fs::copy(entry.path(), dest_path).unwrap();
            }
        }
    }

    let tmp = temp_in_private_tmp("obb-repo-id-");
    let (repo_a, gate) = receipt_gate_repo(tmp.path());
    let state = tmp.path().join("state");
    let store = take_receipt_quest(&repo_a, &state);

    write_rel(&repo_a, "NOTES.txt", "candidate commit\n");
    git_cmd(&repo_a, &["add", "NOTES.txt"]);
    git_cmd(&repo_a, &["commit", "-m", "candidate"]);

    // 1. Virgin-vault forgery check: before ANY key exists in `state` or `repo_a`, a hand-crafted
    // receipt with `receipt_mac: None` MUST fail closed (`TamperedReceipt`), never bypass HMAC!
    let fake_id = obb_judge::resolve_git_repo_identity(&repo_a).unwrap();
    let head_sha = git_cmd(&repo_a, &["rev-parse", "HEAD"]).trim().to_string();
    let base_sha = git_cmd(&repo_a, &["rev-parse", "main"]).trim().to_string();
    let tree_oid = git_cmd(&repo_a, &["rev-parse", "HEAD^{tree}"])
        .trim()
        .to_string();
    let mut unkeyed_forged = JudgeReceipt {
        receipt_version: 1,
        transport: None,
        judge_name: gate.name.clone(),
        gate_sha256: gate.canonical_sha256().unwrap(),
        repo_root: fake_id.toplevel.to_string_lossy().to_string(),
        repo_git_common_dir: Some(fake_id.common_dir.to_string_lossy().to_string()),
        base_sha,
        head_sha,
        tree_oid,
        clean_working_tree: true,
        changed_paths: vec!["NOTES.txt".into()],
        checked_at: "2026-11-14T00:00:00Z".into(),
        all_passed: true,
        achieved_regime: Regime::Decided,
        kernel_verified: false,
        teeth_report: obb_judge::TeethReport {
            total: 1,
            bit_count: 1,
            vacuous_count: 0,
            invalid_count: 0,
            positive_failed_count: 0,
            all_bit: true,
            results: Vec::new(),
        },
        evaluations: Vec::new(),
        receipt_hash: String::new(),
        receipt_mac: None,
    };
    unkeyed_forged.receipt_hash = unkeyed_forged.compute_hash().unwrap();
    let virgin_err = store
        .propose_quest("Q", "worker", &unkeyed_forged, &repo_a, "main")
        .unwrap_err();
    assert!(
        matches!(virgin_err, StateRefusal::TamperedReceipt { .. }),
        "unauthenticated receipt on virgin vault must fail closed, got: {virgin_err:?}"
    );

    // 2. Create BOTH a separate `git clone` AND a byte-for-byte recursive copy (`cp -R`) of `repo_a`
    // sharing the exact same commits, branches, tree OIDs, `gate_sha256`, and vault HMAC key!
    let repo_clone = tmp.path().join("repo-clone");
    git_cmd(
        tmp.path(),
        &[
            "clone",
            "--no-local",
            repo_a.to_str().unwrap(),
            repo_clone.to_str().unwrap(),
        ],
    );
    git_cmd(&repo_clone, &["branch", "-f", "main", "origin/main"]);

    let repo_copy = tmp.path().join("repo-copy");
    copy_dir_all(&repo_a, &repo_copy);

    let clone_receipt =
        issue_judge_receipt_with_state_dir(&gate, &repo_clone, "main", Some(&state)).unwrap();
    let copy_receipt =
        issue_judge_receipt_with_state_dir(&gate, &repo_copy, "main", Some(&state)).unwrap();
    assert!(clone_receipt.all_passed && copy_receipt.all_passed);
    assert_eq!(clone_receipt.head_sha, copy_receipt.head_sha);

    // Transplanting either receipt onto `repo_a` MUST fail closed with `RepoMismatch`!
    for transplanted in [&clone_receipt, &copy_receipt] {
        let err = store
            .propose_quest("Q", "worker", transplanted, &repo_a, "main")
            .unwrap_err();
        assert!(
            matches!(err, StateRefusal::RepoMismatch { .. }),
            "expected RepoMismatch on cross-checkout receipt transplant, got: {err:?}"
        );
    }

    // Passing `--repo repo_clone` directly to `propose_quest` or `RepoCheck` on a quest whose
    // campaign targets `repo_a` MUST ALSO fail closed with `RepoMismatch`!
    let wrong_repo_prop = store
        .propose_quest("Q", "worker", &clone_receipt, &repo_clone, "main")
        .unwrap_err();
    assert!(
        matches!(wrong_repo_prop, StateRefusal::RepoMismatch { .. }),
        "expected RepoMismatch when passing clone `--repo`, got: {wrong_repo_prop:?}"
    );
    let wrong_repo_q2 = store
        .transition_quest(
            "Q",
            "Built",
            "worker",
            None,
            QuestGuardEvidence::RepoCheck {
                repo_root: repo_clone.clone(),
                artifacts: vec!["NOTES.txt".into()],
            },
        )
        .unwrap_err();
    assert!(
        matches!(wrong_repo_q2, StateRefusal::RepoMismatch { .. }),
        "expected RepoMismatch on Q2 RepoCheck against unrelated repo, got: {wrong_repo_q2:?}"
    );
    assert_eq!(store.get_quest("Q").unwrap().unwrap().state, "Scoped");

    // 3. Linked `git worktree` of `repo_a` (sharing canonical `git-common-dir` with `repo_a`):
    // proposing in the linked worktree and landing onto `main` in `repo_a` MUST succeed!
    git_cmd(&repo_a, &["checkout", "main"]);
    git_cmd(&repo_a, &["branch", "-D", "candidate"]);
    let wt = tmp.path().join("linked-wt");
    git_cmd(
        &repo_a,
        &["worktree", "add", "--detach", wt.to_str().unwrap(), "main"],
    );
    write_rel(&wt, "NOTES.txt", "worktree candidate\n");
    git_cmd(&wt, &["add", "NOTES.txt"]);
    git_cmd(&wt, &["commit", "-m", "worktree candidate"]);

    let wt_receipt = issue_judge_receipt_with_state_dir(&gate, &wt, "main", Some(&state)).unwrap();
    assert!(wt_receipt.all_passed);

    // Proposing with `--repo repo_a` while receipt was earned in `wt` is refused (wrong worktree at Q4),
    // while proposing with `--repo wt` succeeds!
    assert!(matches!(
        store.propose_quest("Q", "worker", &wt_receipt, &repo_a, "main"),
        Err(StateRefusal::RepoMismatch { .. })
    ));
    store
        .propose_quest("Q", "worker", &wt_receipt, &wt, "main")
        .unwrap();
    assert_eq!(store.get_quest("Q").unwrap().unwrap().state, "Toothed");

    git_cmd(&repo_a, &["worktree", "remove", wt.to_str().unwrap()]);
    let landed = store
        .land_quest("Q", "worker", &wt_receipt, &repo_a, "main")
        .unwrap();
    assert_eq!(landed.state, "Landed");
    assert_eq!(
        git_cmd(&repo_a, &["rev-parse", "main"]).trim(),
        wt_receipt.head_sha
    );
}

#[tokio::test]
async fn convergence_serve_api_judge_evaluates_target_repo_not_workspace_root() {
    use axum::{
        body::{Body, to_bytes},
        http::Request,
    };
    use obb_cli::serve::{ServeConfig, build_router};
    use tower::ServiceExt;

    let tmp = temp_in_private_tmp("obb-serve-judge-");
    let workspace = tmp.path().join("workspace");
    let target_repo = tmp.path().join("target-repo");
    fs::create_dir_all(&workspace).unwrap();
    fs::create_dir_all(&target_repo).unwrap();

    let gate = build_gate(
        "serve-target-gate",
        vec![
            (
                Floor::Home(1),
                Method::Eval(TrustBase::External("git-merge-tree".into())),
            ),
            (
                Floor::Named("no_sorry_ax".into()),
                Method::Eval(TrustBase::Lexical),
            ),
        ],
        vec![
            TrustBase::External("git-merge-tree".into()),
            TrustBase::Lexical,
        ],
        Vec::new(),
    );
    let judge_path = workspace.join("judge.json");
    write_rel(
        &workspace,
        "judge.json",
        &serde_json::to_string_pretty(&gate).unwrap(),
    );

    let app = build_router(
        ServeConfig::new(workspace.clone(), target_repo.clone(), judge_path.clone())
            .with_bearer_token("secret"),
    );

    // 1. Clean `workspace_root` + faulty `target_repo` -> `/api/judge` MUST report FAIL on `target_repo`!
    write_rel(
        &workspace,
        "lean/Clean.lean",
        "theorem ok : True := by trivial\n",
    );
    write_rel(
        &target_repo,
        "lean/Bad.lean",
        "theorem bad : True := by sorry\n",
    );

    let resp_fail = app
        .clone()
        .oneshot(
            Request::builder()
                .uri("/api/judge")
                .header("authorization", "Bearer secret")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    let json_fail: serde_json::Value =
        serde_json::from_slice(&to_bytes(resp_fail.into_body(), usize::MAX).await.unwrap())
            .unwrap();
    let canon_target = target_repo.canonicalize().unwrap();
    assert_eq!(
        json_fail["evaluation"]["repo_root"],
        canon_target.to_string_lossy().as_ref(),
        "{json_fail}"
    );
    assert_eq!(
        json_fail["evaluation"]["all_passed"],
        serde_json::json!(false),
        "fault in target_repo must fail /api/judge even when workspace_root is clean: {json_fail}"
    );

    // 2. Faulty `workspace_root` + clean `target_repo` -> `/api/judge` MUST report PASS on `target_repo`!
    write_rel(
        &workspace,
        "lean/Clean.lean",
        "theorem broken : True := by sorry\n",
    );
    write_rel(
        &target_repo,
        "lean/Bad.lean",
        "theorem fixed : True := by trivial\n",
    );

    let resp_pass = app
        .oneshot(
            Request::builder()
                .uri("/api/judge")
                .header("authorization", "Bearer secret")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    let json_pass: serde_json::Value =
        serde_json::from_slice(&to_bytes(resp_pass.into_body(), usize::MAX).await.unwrap())
            .unwrap();
    assert_eq!(
        json_pass["evaluation"]["repo_root"],
        canon_target.to_string_lossy().as_ref()
    );
    assert_eq!(
        json_pass["evaluation"]["all_passed"],
        serde_json::json!(true),
        "clean target_repo must pass /api/judge regardless of workspace_root contents: {json_pass}"
    );

    // 3. Nonexistent `target_repo` fails closed on both `evaluate_gate_on` and `/api/judge` (never vacuous pass).
    let missing_target = tmp.path().join("does-not-exist");
    assert!(evaluate_gate_on(&gate, &missing_target, JudgeClock::Construction).is_err());
    let missing_app = build_router(
        ServeConfig::new(workspace, missing_target, judge_path).with_bearer_token("secret"),
    );
    let resp_missing = missing_app
        .oneshot(
            Request::builder()
                .uri("/api/judge")
                .header("authorization", "Bearer secret")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    let json_missing: serde_json::Value = serde_json::from_slice(
        &to_bytes(resp_missing.into_body(), usize::MAX)
            .await
            .unwrap(),
    )
    .unwrap();
    assert!(
        json_missing["evaluation"].is_null() && json_missing["evaluation_error"].is_string(),
        "missing target_repo must report evaluation_error: {json_missing}"
    );
}

#[test]
fn land_preflight_refuses_dirty_checkout_before_changing_branch_or_trunk() {
    let tmp = temp_in_private_tmp("obb-land-preflight-");
    let (repo, gate) = receipt_gate_repo(tmp.path());
    let store = take_receipt_quest(&repo, &tmp.path().join("state"));
    write_rel(&repo, "NOTES.txt", "candidate\n");
    git_cmd(&repo, &["add", "NOTES.txt"]);
    git_cmd(&repo, &["commit", "-m", "candidate"]);
    let receipt = issue_judge_receipt(&gate, &repo, "main").unwrap();
    store
        .propose_quest("Q", "worker", &receipt, &repo, "main")
        .unwrap();
    // An unrelated tracked edit would survive checkout and the fast-forward, then fail Q5.
    write_rel(&repo, "dead.txt", "uncommitted work\n");
    let refused = store
        .land_quest("Q", "worker", &receipt, &repo, "main")
        .unwrap_err();
    assert!(matches!(refused, StateRefusal::GuardFailed { ref guard, .. } if guard == "Q5"));
    assert_eq!(
        git_cmd(&repo, &["rev-parse", "main"]).trim(),
        receipt.base_sha
    );
    assert_eq!(
        git_cmd(&repo, &["branch", "--show-current"]).trim(),
        "candidate"
    );
    assert_eq!(
        fs::read_to_string(repo.join("dead.txt")).unwrap(),
        "uncommitted work\n"
    );
    assert_eq!(store.get_quest("Q").unwrap().unwrap().state, "Toothed");
    write_rel(&repo, "dead.txt", "obsolete\n");
    store
        .land_quest("Q", "worker", &receipt, &repo, "main")
        .unwrap();
}

#[test]
fn candidate_receipts_and_leases_preserve_quoted_and_whitespace_paths() {
    let tmp = temp_in_private_tmp("obb-candidate-paths-");
    let (repo, gate) = receipt_gate_repo(tmp.path());
    let store = take_receipt_quest(&repo, &tmp.path().join("state"));
    let paths = [
        " spaced.txt ",
        "src/café.txt",
        "src/tab\tname.txt",
        "src/line\nbreak.txt",
    ];
    for path in paths {
        write_rel(&repo, path, "candidate\n");
    }
    git_cmd(&repo, &["add", "."]);
    git_cmd(&repo, &["commit", "-m", "candidate unusual paths"]);
    let receipt = issue_judge_receipt(&gate, &repo, "main").unwrap();
    let mut expected = paths.to_vec();
    expected.sort();
    assert_eq!(receipt.changed_paths, expected);
    let quest = store
        .propose_quest("Q", "worker", &receipt, &repo, "main")
        .unwrap();
    assert!(quest.footprint_lease.contains(&paths[0].to_string()));
    store
        .land_quest("Q", "worker", &receipt, &repo, "main")
        .unwrap();
}

#[test]
fn deeply_nested_javascript_templates_do_not_overflow_the_scanner_stack() {
    let tmp = temp_in_private_tmp("obb-deep-template-");
    let source = format!(
        "const value = {}0{};\ntest('real', () => {{}});\n",
        "`${".repeat(20_000),
        "}`".repeat(20_000)
    );
    write_rel(tmp.path(), "src/deep.js", &source);
    let findings = obb_lint::test_in_library::scan_test_in_library(tmp.path()).unwrap();
    assert_eq!(findings.len(), 1);
    assert_eq!(findings[0].line, 2);
}
