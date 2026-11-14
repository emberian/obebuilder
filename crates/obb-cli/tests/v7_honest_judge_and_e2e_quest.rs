//! `obb v7 (0.7.0)` Honest Judge, Fail-Closed Floors, SHA-Bound Statechart Receipts & Unseeded E2E Quest Tests.
//!
//! Verifies all five `obb v7` hardening requirements:
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
    Floor, FloorDiagnostic, Gate, JudgeReceipt, KernelReceipt, Method, MethodBinding,
    ToothMutation, ToothSpec, ToothVerdict, TrustBase, evaluate_gate, evaluate_teeth,
    issue_judge_receipt,
};
use obb_state::{
    ORIGIN_DEMO_SEED, ORIGIN_LIVE, QuestGuardEvidence, REGIME_ATTESTED_OVERRIDE, StateRefusal,
    StateStore,
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
        .env("TMPDIR", "/private/tmp")
        .env("GIT_AUTHOR_NAME", "obb-v7-test")
        .env("GIT_AUTHOR_EMAIL", "obb-v7@localhost")
        .env("GIT_COMMITTER_NAME", "obb-v7-test")
        .env("GIT_COMMITTER_EMAIL", "obb-v7@localhost")
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
}

fn run_obb(args: &[&str]) -> Output {
    Command::new(obb_bin())
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("TMPDIR", "/private/tmp")
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
    let tmp = temp_in_private_tmp("obb-v7-teeth-");
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
    let tmp = temp_in_private_tmp("obb-v7-floors-");
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
    let tmp = temp_in_private_tmp("obb-v7-e2e-");
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

    // 4. Test out-of-footprint violation (`docs/rogue.md` outside lease)
    git_cmd(&repo, &["checkout", "-b", "quest/Q-e2e"]);
    write_rel(&repo, "docs/rogue.md", "# Out of footprint\n");
    write_rel(
        &repo,
        "tests/test_calc.py",
        "import sys\nsys.path.insert(0, 'src')\nfrom calc import safe_div\nassert safe_div(10, 2) == 5\ntry:\n    safe_div(1, 0)\n    raise SystemExit('expected ValueError')\nexcept ValueError:\n    pass\nprint('ran 2 tests ok')\n",
    );
    let biting_spec = vec![ToothSpec {
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
        matches!(fp_err, StateRefusal::FootprintViolation { ref violating_paths, .. } if violating_paths == &vec!["docs/rogue.md".to_string()]),
        "expected FootprintViolation on docs/rogue.md, got {fp_err:?}"
    );

    // 5. Reset to `main` and commit an in-footprint candidate whose tooth is VACUOUS (`VACUOUS` caught!)
    git_cmd(&repo, &["reset", "--hard", "main"]);
    let vacuous_spec = vec![ToothSpec {
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
    git_cmd(&repo, &["add", "tests/test_calc.py", "teeth.json"]);
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
    assert!(converged.quests.iter().all(|q| q.state == "Recorded"));
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
    let tmp = temp_in_private_tmp("obb-v7-override-seed-");
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
    let tmp = temp_in_private_tmp("obb-v7-scanner-");
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
    let tmp = temp_in_private_tmp("obb-v7-http-");
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
    let tmp = temp_in_private_tmp("obb-v7-ledger-");
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
    let tmp = temp_in_private_tmp("obb-v7-lexical-edges-");
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
