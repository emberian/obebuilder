//! Mechanical anti-slop & vacuity detectors for Lean 4 (`DESIGN.md` §2.6, `JUDGE.md`).

use crate::lean_index::{
    BinderParam, DeclKind, LeanIndex, ParsedLeanDecl, ParsedLeanFile, TestCommandKind,
};
use crate::lean_lexer::{LeanToken, LeanTokenKind};
use obb_core::{ArtifactKind, DirectoryCensus, Finding, Regime, Severity, Sink};
use std::collections::{BTreeMap, HashMap, HashSet};

pub const FILE_WIDE_EXPOSE_LINE_THRESHOLD: usize = 80;
pub const EXCESSIVE_DECL_EXPOSE_THRESHOLD: usize = 12;

#[derive(Debug, Clone, Copy, Default)]
pub struct LeanLintOptions {
    /// Escalate `lean/file-wide-expose` and `lean/excessive-decl-expose` from `Severity::Warning` to `Severity::Error`.
    pub strict_expose: bool,
    /// Escalate `lean/single-sequence-harness` from `Severity::Warning` to `Severity::Error`.
    pub strict_harnesses: bool,
    /// Escalate `lean/judge-fragment-restates-check` and `lean/pigeonhole-vacuous-premise` from `Severity::Warning` to `Severity::Error`.
    pub strict_vacuity: bool,
    /// Enable `lean/test-in-library` (`Severity::Error` on `#guard`, `#guard_msgs`, `#tooth`, and `#eval` inside Tier-1 `lean/Obend/` library modules outside `lean/Obend/Teeth/`).
    pub strict_tests: bool,
}

/// Returns `true` when `rel_path` is a Tier-1 library `.lean` file under `lean/Obend/`
/// (or root `lean/Obend.lean`) excluding `lean/Obend/Teeth/`.
pub fn is_tier1_library_lean_path(rel_path: &str) -> bool {
    let norm = rel_path.strip_prefix("lean/").unwrap_or(rel_path);
    ((norm == "Obend.lean" || norm.starts_with("Obend/")) && !norm.starts_with("Obend/Teeth/"))
        || (rel_path.split('/').any(|p| p == "src")
            && !rel_path.split('/').any(|p| matches!(p, "tests" | "test")))
}

/// Tally `(tier1_guards, tier1_teeth, tier1_evals)` across all Tier-1 library `.lean` files
/// (`lean/Obend/` excluding `lean/Obend/Teeth/`), regardless of whether `--strict-tests` is active.
pub fn compute_tier1_test_counts(index: &LeanIndex) -> (usize, usize, usize) {
    let mut guards = 0usize;
    let mut teeth = 0usize;
    let mut evals = 0usize;
    for file in &index.files {
        if !is_tier1_library_lean_path(&file.rel_path) {
            continue;
        }
        for site in &file.test_commands {
            match site.kind {
                TestCommandKind::Guard | TestCommandKind::GuardMsgs => guards += 1,
                TestCommandKind::Tooth => teeth += 1,
                TestCommandKind::Eval => evals += 1,
            }
        }
    }
    (guards, teeth, evals)
}

pub fn is_allowed_public_meta_import_path(rel_path: &str) -> bool {
    let norm = rel_path.strip_prefix("lean/").unwrap_or(rel_path);
    norm.starts_with("Obend/Tactic/")
        || norm.starts_with("Obend/Elab/")
        || rel_path.contains("/Obend/Tactic/")
        || rel_path.contains("/Obend/Elab/")
}

pub fn run_lean_lints(index: &LeanIndex) -> (Vec<Finding>, Vec<DirectoryCensus>) {
    run_lean_lints_with_options(index, LeanLintOptions::default())
}

pub fn run_lean_lints_with_options(
    index: &LeanIndex,
    options: LeanLintOptions,
) -> (Vec<Finding>, Vec<DirectoryCensus>) {
    let mut findings = Vec::new();
    let mut dir_map: BTreeMap<String, DirectoryCensus> = BTreeMap::new();
    let (obligation_classes, obligation_class_fields) = collect_obligation_classes(index);

    for file in &index.files {
        let entry = dir_map
            .entry(file.directory_bucket.clone())
            .or_insert_with(|| DirectoryCensus {
                directory: file.directory_bucket.clone(),
                ..Default::default()
            });
        entry.files += 1;
        entry.teeth += file.tooth_targets.len();

        let is_teeth_or_test = is_teeth_or_test_path(&file.rel_path);
        let is_test_only = is_test_only_path(&file.rel_path);

        // 3-Way Proof / Test / Mutation Separation (`lean/test-in-library`, enabled by `--strict-tests`):
        // Ban `#guard`, `#guard_msgs`, `#tooth`, and `#eval` inside Tier-1 `lean/Obend/` library modules
        // (excluding `lean/Obend/Teeth/`).
        if options.strict_tests && is_tier1_library_lean_path(&file.rel_path) {
            for site in &file.test_commands {
                let (message, remediation) = match site.kind {
                    TestCommandKind::Guard => (
                        format!(
                            "Tier-1 library module `{}` executes top-level `#guard` during `lake build Obend`, mixing test execution with proof elaboration",
                            file.rel_path
                        ),
                        "Move `#guard` assertions out of `lean/Obend/` to `lean/tests/` compiled native `IO` test suites (`lake exe obend-test`).".to_string(),
                    ),
                    TestCommandKind::GuardMsgs => (
                        format!(
                            "Tier-1 library module `{}` executes top-level `#guard_msgs` during `lake build Obend`, mixing elaboration message tests with proof elaboration",
                            file.rel_path
                        ),
                        "Move `#guard_msgs` test assertions out of `lean/Obend/` to `lean/tests/` (`lake exe obend-test`) or `lean/Obend/Teeth/` (`lake build Teeth`).".to_string(),
                    ),
                    TestCommandKind::Tooth => {
                        let target_suffix = site
                            .target_hint
                            .as_deref()
                            .map(|t| format!(" (`{t}`)"))
                            .unwrap_or_default();
                        (
                            format!(
                                "Tier-1 library module `{}` executes top-level `#tooth`{target_suffix} during `lake build Obend`, running mutation replay inside pure library builds",
                                file.rel_path
                            ),
                            "Move `#tooth` mutation witnesses out of `lean/Obend/` to `lean/Obend/Teeth/` (`lake build Teeth` on-demand mutation gate).".to_string(),
                        )
                    }
                    TestCommandKind::Eval => (
                        format!(
                            "Tier-1 library module `{}` executes top-level `{}` during `lake build Obend`",
                            file.rel_path, site.raw_cmd
                        ),
                        "Remove `#eval` from Tier-1 `lean/Obend/` library modules (if checking executable output, assert it in `lean/tests/` compiled `obend-test`).".to_string(),
                    ),
                };
                findings.push(Finding {
                    rule_id: "lean/test-in-library".to_string(),
                    severity: Severity::Error,
                    artifact_kind: ArtifactKind::P,
                    max_regime: Regime::Decided,
                    sink: Some(Sink::Slow),
                    path: file.rel_path.clone(),
                    line: site.line,
                    column: site.col,
                    symbol: Some(site.kind.as_str().to_string()),
                    message,
                    remediation,
                });
            }
        }

        // LAW-M1: Ban top-level `@[expose] public section` in files > 80 lines
        if !is_test_only
            && file.line_count > FILE_WIDE_EXPOSE_LINE_THRESHOLD
            && !file.expose_public_sections.is_empty()
        {
            for &(eline, ecol) in &file.expose_public_sections {
                findings.push(Finding {
                    rule_id: "lean/file-wide-expose".to_string(),
                    severity: if options.strict_expose {
                        Severity::Error
                    } else {
                        Severity::Warning
                    },
                    artifact_kind: ArtifactKind::P,
                    max_regime: Regime::Decided,
                    sink: Some(Sink::Slow),
                    path: file.rel_path.clone(),
                    line: eline,
                    column: ecol,
                    symbol: None,
                    message: format!(
                        "Module `{}` ({} lines > {}-line cap) places `@[expose] public section` at top level, exporting all definition bodies into `.olean` public headers and kernel WHNF",
                        file.rel_path, file.line_count, FILE_WIDE_EXPOSE_LINE_THRESHOLD
                    ),
                    remediation: "Replace top-level `@[expose] public section` with Lean 4.35 `module` + `public section` so recursive bodies stay sealed in `.olean.private`, and attach selective `@[expose]` only on <= 10-line projections/types needed for definitional typechecking (use private `import all` inside `Proofs/`).".to_string(),
                });
            }
        }

        // LAW-M1b: Ban per-declaration `@[expose]` loophole (`> 12` `@[expose]` declarations in `module` files > 80 lines)
        if !is_test_only && file.has_module_kw && file.line_count > FILE_WIDE_EXPOSE_LINE_THRESHOLD
        {
            let exposed_decls: Vec<&ParsedLeanDecl> = file
                .declarations
                .iter()
                .filter(|d| !d.fixture_kept && d.attributes.iter().any(|a| a == "expose"))
                .collect();
            if exposed_decls.len() > EXCESSIVE_DECL_EXPOSE_THRESHOLD {
                let breach_decl = exposed_decls[EXCESSIVE_DECL_EXPOSE_THRESHOLD];
                let sample_names: Vec<&str> = exposed_decls
                    .iter()
                    .take(5)
                    .map(|d| d.name.as_str())
                    .collect();
                findings.push(Finding {
                    rule_id: "lean/excessive-decl-expose".to_string(),
                    severity: if options.strict_expose {
                        Severity::Error
                    } else {
                        Severity::Warning
                    },
                    artifact_kind: ArtifactKind::P,
                    max_regime: Regime::Decided,
                    sink: Some(Sink::Slow),
                    path: file.rel_path.clone(),
                    line: breach_decl.line,
                    column: breach_decl.col,
                    symbol: Some(breach_decl.fq_name.clone()),
                    message: format!(
                        "Module `{}` ({} lines) attaches `@[expose]` to {} declarations (>{} ceiling; e.g. `{}`), circumventing `LAW-M1` `.olean.private` encapsulation",
                        file.rel_path,
                        file.line_count,
                        exposed_decls.len(),
                        EXCESSIVE_DECL_EXPOSE_THRESHOLD,
                        sample_names.join("`, `")
                    ),
                    remediation: format!(
                        "Seal recursive and operational bodies inside `.olean.private` under `module` + `public section` (`LAW-M1`); restrict `@[expose]` to <= {} tiny carrier projections/constants per module and export behavioral contracts via theorems (`*_eq`, `*_sound`).",
                        EXCESSIVE_DECL_EXPOSE_THRESHOLD
                    ),
                });
            }
        }

        // LAW-M6: `public meta import Lean` leakage outside `Obend/Tactic/` or `Obend/Elab/`
        if !is_test_only && !is_allowed_public_meta_import_path(&file.rel_path) {
            for imp in &file.imports {
                if imp.is_public
                    && imp.is_meta
                    && (imp.module == "Lean" || imp.module.starts_with("Lean."))
                {
                    findings.push(Finding {
                        rule_id: "lean/public-meta-import-leak".to_string(),
                        severity: Severity::Error,
                        artifact_kind: ArtifactKind::P,
                        max_regime: Regime::Decided,
                        sink: Some(Sink::Slow),
                        path: file.rel_path.clone(),
                        line: imp.line,
                        column: imp.col,
                        symbol: Some(imp.module.clone()),
                        message: format!(
                            "Module `{}` declares `public meta import {}` outside `Obend/Tactic/` or `Obend/Elab/`, dragging `Lean.Elab` compiler internals into downstream `.olean` cones",
                            file.rel_path, imp.module
                        ),
                        remediation: "Move `CommandElabM`/`TacticM` metaprograms under `lean/Obend/Tactic/` or `lean/Obend/Elab/`, or downgrade to private `meta import` so downstream importers do not transitively load `Lean`.".to_string(),
                    });
                }
            }
        }

        // Module-level monolithic file budget check (> 1,500 lines risks RSS blowup)
        if !is_test_only && file.line_count > crate::modularity::MONOLITHIC_LINE_THRESHOLD {
            findings.push(Finding {
                rule_id: "lean/monolithic-module".to_string(),
                severity: Severity::Warning,
                artifact_kind: ArtifactKind::P,
                max_regime: Regime::Decided,
                sink: Some(Sink::Slow),
                path: file.rel_path.clone(),
                line: 1,
                column: 1,
                symbol: None,
                message: format!(
                    "Module `{}` spans {} lines (>{} line modularity cap across {} declarations), risking elaboration RSS blowups and slow incremental rebuilds",
                    file.rel_path,
                    file.line_count,
                    crate::modularity::MONOLITHIC_LINE_THRESHOLD,
                    file.declarations.len()
                ),
                remediation: "Split this module into focused submodules (<1,500 lines each) separating carrier types/specs (`Structure`/`Class`) from downstream soundness proofs.".to_string(),
            });
        }

        // Module-level cosplay naming check (`*Poles.lean`, `Mock*.lean`, `Golden*.lean`)
        if !is_teeth_or_test
            && file.rel_path.contains("Obend/")
            && let Some(stem) = std::path::Path::new(&file.rel_path)
                .file_stem()
                .and_then(|s| s.to_str())
            && let Some(pat) = cosplay_pattern(stem)
        {
            findings.push(Finding {
                        rule_id: "lean/cosplay-naming".to_string(),
                        severity: Severity::Warning,
                        artifact_kind: ArtifactKind::P,
                        max_regime: Regime::Attested,
                        sink: Some(Sink::Theater),
                        path: file.rel_path.clone(),
                        line: 1,
                        column: 1,
                        symbol: Some(stem.to_string()),
                        message: format!(
                            "Load-bearing library module `{stem}` uses showcase/cosplay naming (`{pat}`) outside `Obend/Teeth/`"
                        ),
                        remediation: "Rename module after the domain object it defines, or move pure fixture/pole checks under `lean/Obend/Teeth/`.".to_string(),
                    });
        }

        // Collect all functions wired as `decodeObj` / `decodeCert` in `Judge.Format` defs in this file
        let mut format_decoder_fns: HashSet<String> = HashSet::new();
        for decl in &file.declarations {
            if is_judge_format_decl(decl) {
                for wf in &decl.where_fields {
                    if wf.name == "decodeObj" || wf.name == "decodeCert" {
                        // Check inline string-literal match in `decodeObj` / `decodeCert`
                        if let Some(param_name) = wf.params.first() {
                            if let Some((lit, line, col)) =
                                find_preset_string_branch(&wf.rhs_tokens, param_name)
                            {
                                findings.push(Finding {
                                    rule_id: "lean/hardcoded-wire-decoder".to_string(),
                                    severity: Severity::Error,
                                    artifact_kind: ArtifactKind::P,
                                    max_regime: Regime::Attested,
                                    sink: Some(Sink::Theater),
                                    path: file.rel_path.clone(),
                                    line,
                                    column: col,
                                    symbol: Some(format!("{}.{}", decl.name, wf.name)),
                                    message: format!(
                                        "`{}.{}` short-circuits wire decoding on hardcoded preset string literal `\"{lit}\"`",
                                        decl.name, wf.name
                                    ),
                                    remediation: "Parse real wire bytes/JSON/Core.Data payloads structurally in `decodeObj`/`decodeCert`; remove preset string shortcuts.".to_string(),
                                });
                            }
                        } else if let Some((lit, line, col)) =
                            find_match_string_literal_arm(&wf.rhs_tokens)
                        {
                            findings.push(Finding {
                                rule_id: "lean/hardcoded-wire-decoder".to_string(),
                                severity: Severity::Error,
                                artifact_kind: ArtifactKind::P,
                                max_regime: Regime::Attested,
                                sink: Some(Sink::Theater),
                                path: file.rel_path.clone(),
                                line,
                                column: col,
                                symbol: Some(format!("{}.{}", decl.name, wf.name)),
                                message: format!(
                                    "`{}.{}` matches directly on hardcoded wire string literal `\"{lit}\"`",
                                    decl.name, wf.name
                                ),
                                remediation: "Replace hardcoded string-literal `match` arms with a structural wire format parser.".to_string(),
                            });
                        }

                        for tok in &wf.rhs_tokens {
                            if let LeanTokenKind::Ident(fn_id) = &tok.kind {
                                format_decoder_fns.insert(fn_id.clone());
                                if let Some(short) = fn_id.rsplit('.').next() {
                                    format_decoder_fns.insert(short.to_string());
                                }
                            }
                        }
                    }
                }
            }
        }

        // Collect `#assert_compiled <target>` names in this file for audited closed KAT pins
        let mut assert_compiled_set: HashSet<&str> = HashSet::new();
        for (target, _) in &file.assert_compiled_targets {
            assert_compiled_set.insert(target.as_str());
            if let Some(short) = target.rsplit('.').next() {
                assert_compiled_set.insert(short);
            }
        }

        // Map decl short & fully-qualified names -> decl for cross-checking `Judge.check` helper bodies and `Format` decoders
        let mut decl_by_name: HashMap<&str, &ParsedLeanDecl> = HashMap::new();
        for decl in &file.declarations {
            decl_by_name.insert(decl.name.as_str(), decl);
            decl_by_name.insert(decl.fq_name.as_str(), decl);
        }

        // Module-level HypothesisLedger / inhabited-premise index
        let module_witnessed_preds = collect_module_satisfiability_witnesses(file, &decl_by_name);

        // Pass 1 for `lean/pigeonhole-vacuous-premise`: collect file-local vacuous crypto defs/abbrevs
        // and check file-level `variable (...)` assumptions.
        let flagged_crypto_defs = if !is_teeth_or_test {
            collect_flagged_crypto_defs_and_check_section_vars(
                file,
                options.strict_vacuity,
                &mut findings,
            )
        } else {
            HashSet::new()
        };

        for decl in &file.declarations {
            // Check 2026 compiler-trust bypass (`native_decide` / `Lean.ofReduceBool`) in library modules
            if !is_test_only {
                check_native_decide_in_proof(
                    file,
                    decl,
                    is_teeth_or_test,
                    &assert_compiled_set,
                    &mut findings,
                );
            }

            // Check 2026 cryptographic narrow digest / 1-limb weld (`breadstuffs` 2^15.5-bit bug class)
            check_narrow_digest_weld(file, decl, &mut findings);

            match decl.kind {
                DeclKind::Example => {
                    entry.examples += 1;
                }
                DeclKind::Axiom => {
                    findings.push(Finding {
                        rule_id: "lean/sorry-or-axiom".to_string(),
                        severity: Severity::Error,
                        artifact_kind: ArtifactKind::S,
                        max_regime: Regime::Attested,
                        sink: Some(Sink::Label),
                        path: file.rel_path.clone(),
                        line: decl.line,
                        column: decl.col,
                        symbol: Some(decl.fq_name.clone()),
                        message: format!(
                            "Declared `axiom {}` violates the `no_declared_axiom` census floor",
                            decl.fq_name
                        ),
                        remediation: "Replace the `axiom` with a constructive proof or carry an explicit hypothesis parameter on the theorems that require it.".to_string(),
                    });
                    if !is_teeth_or_test && !decl.fixture_kept {
                        check_pigeonhole_vacuous_premise(
                            file,
                            decl,
                            &flagged_crypto_defs,
                            options.strict_vacuity,
                            &mut findings,
                        );
                    }
                }
                DeclKind::TacticElab => {
                    check_tactic_elab(file, decl, &mut findings);
                }
                DeclKind::Theorem | DeclKind::Def | DeclKind::Abbrev | DeclKind::Instance => {
                    // 1. Check `sorry` inside theorem/def/instance proof or type (excluding deliberate planted-sorry test fixtures)
                    if !is_planted_sorry_fixture_name(&decl.name) {
                        for tok in decl.type_tokens.iter().chain(decl.body_tokens.iter()) {
                            if let LeanTokenKind::Ident(id) = &tok.kind
                                && (id == "sorry" || id == "sorryAx")
                            {
                                findings.push(Finding {
                                        rule_id: "lean/sorry-or-axiom".to_string(),
                                        severity: Severity::Error,
                                        artifact_kind: ArtifactKind::P,
                                        max_regime: Regime::Attested,
                                        sink: Some(Sink::Theater),
                                        path: file.rel_path.clone(),
                                        line: tok.line,
                                        column: tok.col,
                                        symbol: Some(decl.fq_name.clone()),
                                        message: format!(
                                            "Declaration `{}` references `{id}`, violating `no_sorry_ax`",
                                            decl.fq_name
                                        ),
                                        remediation: "Discharge all proof obligations constructively without `sorry` or `sorryAx`.".to_string(),
                                    });
                                break;
                            }
                        }
                    }

                    // 2. Cosplay naming on load-bearing declarations
                    if !is_teeth_or_test
                        && file.rel_path.contains("Obend/")
                        && let Some(pat) = cosplay_pattern(&decl.name)
                    {
                        findings.push(Finding {
                                rule_id: "lean/cosplay-naming".to_string(),
                                severity: Severity::Warning,
                                artifact_kind: ArtifactKind::P,
                                max_regime: Regime::Attested,
                                sink: Some(Sink::Theater),
                                path: file.rel_path.clone(),
                                line: decl.line,
                                column: decl.col,
                                symbol: Some(decl.fq_name.clone()),
                                message: format!(
                                    "Declaration `{}` uses showcase/cosplay naming (`{pat}`) in load-bearing library module",
                                    decl.fq_name
                                ),
                                remediation: "Move concrete golden/showcase fixtures to `lean/Obend/Teeth/` or convert to unnamed `example`, and name library definitions after their mathematical object.".to_string(),
                            });
                    }

                    // 3. Trivial conclusions & unused decider parameters
                    check_trivial_conclusion_and_params(file, decl, &mut findings);

                    // 4. Theorem classification + closed concrete soundness claims
                    if decl.kind == DeclKind::Theorem {
                        let is_univ = is_universal_theorem(decl);
                        if is_univ {
                            entry.universal_theorems += 1;
                        } else {
                            entry.closed_theorems += 1;
                        }

                        let uses_native_decide =
                            tokens_contain_ident(&decl.body_tokens, "native_decide")
                                || tokens_contain_ident(&decl.body_tokens, "bv_decide");

                        if !is_univ {
                            entry.attested_claims += 1;
                            if claims_general_soundness(&decl.name)
                                && is_concrete_decision_proof(&decl.body_tokens)
                            {
                                findings.push(Finding {
                                    rule_id: "lean/closed-soundness-claim".to_string(),
                                    severity: Severity::Error,
                                    artifact_kind: ArtifactKind::S,
                                    max_regime: Regime::Attested,
                                    sink: Some(Sink::Theater),
                                    path: file.rel_path.clone(),
                                    line: decl.line,
                                    column: decl.col,
                                    symbol: Some(decl.fq_name.clone()),
                                    message: format!(
                                        "Closed concrete theorem `{}` has zero universal quantifiers (`∀` / binders) and reduces fixed inputs, yet its name claims general soundness/completeness",
                                        decl.fq_name
                                    ),
                                    remediation: "Quantify universally over arbitrary inputs/states (`∀ x, ...`), or downgrade this concrete test vector to `example` / move to `Obend/Teeth/` without `_sound` naming.".to_string(),
                                });
                            }
                        } else if uses_native_decide {
                            entry.certified_claims += 1;
                        } else {
                            entry.decided_claims += 1;
                        }

                        // 4b. HypothesisLedger uninhabited-premise check on universal `*_sound` theorems
                        if is_univ && !is_teeth_or_test {
                            check_uninhabited_premise_risk(
                                file,
                                decl,
                                &decl_by_name,
                                &module_witnessed_preds,
                                &mut findings,
                            );
                        }

                        // 4c. Single-sequence / single-turn apex harness check (`lean/single-sequence-harness`)
                        if !is_teeth_or_test
                            && !decl.fixture_kept
                            && let Some(st_msg) = single_turn_apex_violation(file, decl)
                        {
                            findings.push(Finding {
                                rule_id: "lean/single-sequence-harness".to_string(),
                                severity: if options.strict_harnesses {
                                    Severity::Error
                                } else {
                                    Severity::Warning
                                },
                                artifact_kind: ArtifactKind::S,
                                max_regime: Regime::Attested,
                                sink: Some(Sink::Theater),
                                path: file.rel_path.clone(),
                                line: decl.line,
                                column: decl.col,
                                symbol: Some(decl.fq_name.clone()),
                                message: st_msg,
                                remediation: "Pair single-turn step theorems with a multi-turn trace/reachability invariant (`List *Turn`, `Reach`, `SafeWP`, `ValidTrace`, or `MultiTurnHoare`) over arbitrary sequences, and prove environment completeness (`skip_implies_contract_violation` / multi-handle reachability) so state-accumulation bugs (`RevokedSet` growth, `Mandate` budget depletion, persistent `UMem`) cannot hide behind single-turn resets.".to_string(),
                            });
                        }
                    }

                    // 5. `Judge` instance tautological `Meaning`, empty `Fragment`/`refutes`, & `Fragment` restating `check`
                    if is_judge_instance_decl(decl, &decl_by_name) {
                        check_judge_meaning(file, decl, &decl_by_name, &mut findings);
                        if !is_test_only && !decl.fixture_kept {
                            check_judge_empty_fragment(file, decl, &decl_by_name, &mut findings);
                            check_judge_fragment_restates_check(
                                file,
                                decl,
                                &decl_by_name,
                                options.strict_vacuity,
                                &mut findings,
                            );
                        }
                    }

                    // 5a. Pigeonhole-vacuous cryptographic premises & unkeyed `Prop` collision disjunctions
                    if !is_teeth_or_test && !decl.fixture_kept {
                        check_pigeonhole_vacuous_premise(
                            file,
                            decl,
                            &flagged_crypto_defs,
                            options.strict_vacuity,
                            &mut findings,
                        );
                    }

                    // 5b. `*Obligations` / `HypothesisLedger` 1–3 line projection/determinism cosplay detector
                    if decl.kind == DeclKind::Instance && !is_test_only && !decl.fixture_kept {
                        check_obligation_projection_cosplay(
                            file,
                            decl,
                            &obligation_classes,
                            &obligation_class_fields,
                            &mut findings,
                        );
                    }

                    // 6. Hardcoded string-literal wire decoder detector
                    if decl.kind == DeclKind::Def
                        && (format_decoder_fns.contains(&decl.name)
                            || (decl.name.starts_with("decode") && !format_decoder_fns.is_empty()))
                    {
                        check_wire_decoder_def(file, decl, &mut findings);
                    }
                }
                DeclKind::Class | DeclKind::Structure if !is_test_only && !decl.fixture_kept => {
                    if decl.kind == DeclKind::Class {
                        check_obligation_class_tautological_fields(
                            file,
                            decl,
                            &obligation_classes,
                            &mut findings,
                        );
                    }
                    if !is_teeth_or_test {
                        check_pigeonhole_vacuous_premise(
                            file,
                            decl,
                            &flagged_crypto_defs,
                            options.strict_vacuity,
                            &mut findings,
                        );
                    }
                }
                _ => {}
            }
        }
    }

    // Tally findings into directory census buckets
    for f in &findings {
        let bucket = bucket_for_finding_path(&f.path);
        let entry = dir_map
            .entry(bucket.clone())
            .or_insert_with(|| DirectoryCensus {
                directory: bucket,
                ..Default::default()
            });
        entry.findings_count += 1;
        match f.severity {
            Severity::Error => entry.error_count += 1,
            Severity::Warning => entry.warning_count += 1,
            Severity::Info => {}
        }
    }

    (findings, dir_map.into_values().collect())
}

fn bucket_for_finding_path(rel_path: &str) -> String {
    let trimmed = rel_path.strip_prefix("lean/").unwrap_or(rel_path);
    let parts: Vec<&str> = trimmed.split('/').collect();
    if parts.first() == Some(&"Obend") && parts.len() >= 3 {
        format!("Obend/{}", parts[1])
    } else if parts.len() >= 2 {
        parts[0].to_string()
    } else {
        "root".to_string()
    }
}

fn is_teeth_or_test_path(rel_path: &str) -> bool {
    rel_path.contains("/Teeth/")
        || rel_path.starts_with("Obend/Teeth/")
        || rel_path.contains("/tests/")
        || rel_path.starts_with("tests/")
        || rel_path.ends_with("Test.lean")
        || rel_path.ends_with("Tests.lean")
}

fn is_planted_sorry_fixture_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower.contains("sorry")
        && (lower.contains("info") || lower.contains("fixture") || lower.contains("bad"))
}

fn cosplay_pattern(name: &str) -> Option<&'static str> {
    let lower = name.to_ascii_lowercase();
    if lower.starts_with("golden") {
        Some("golden*")
    } else if lower.starts_with("verified") {
        Some("verified*")
    } else if lower.contains("poles") {
        Some("*poles*")
    } else if lower.starts_with("mock") {
        Some("mock*")
    } else if lower.starts_with("dummy") {
        Some("dummy*")
    } else if lower.contains("showcase") {
        Some("*showcase*")
    } else {
        None
    }
}

fn is_universal_theorem(decl: &ParsedLeanDecl) -> bool {
    let has_value_binder = decl.binders.iter().any(|b| !b.is_instance_bracket);
    if has_value_binder {
        return true;
    }
    for tok in &decl.type_tokens {
        match &tok.kind {
            LeanTokenKind::Symbol(s) if s == "∀" => return true,
            LeanTokenKind::Ident(s) if s == "forall" => return true,
            _ => {}
        }
    }
    false
}

fn claims_general_soundness(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower.ends_with("_sound")
        || lower.ends_with("_complete")
        || lower.ends_with("_verified")
        || lower.ends_with("_conserved")
        || lower.ends_with("_safety")
}

fn is_concrete_decision_proof(body_tokens: &[LeanToken]) -> bool {
    if body_tokens.is_empty() {
        return false;
    }
    // Check if body relies solely on `rfl`, `decide`, `native_decide`, `bv_decide`, `simpa ... rfl`, `⟨rfl, ...⟩`
    // without induction or case-splitting (`induction`, `cases` on quantified vars)
    let has_induction = tokens_contain_ident(body_tokens, "induction");
    if has_induction {
        return false;
    }
    tokens_contain_ident(body_tokens, "rfl")
        || tokens_contain_ident(body_tokens, "decide")
        || tokens_contain_ident(body_tokens, "native_decide")
        || tokens_contain_ident(body_tokens, "bv_decide")
}

fn tokens_contain_ident(tokens: &[LeanToken], target: &str) -> bool {
    tokens.iter().any(|t| match &t.kind {
        LeanTokenKind::Ident(id) => id == target,
        _ => false,
    })
}

fn check_trivial_conclusion_and_params(
    file: &ParsedLeanFile,
    decl: &ParsedLeanDecl,
    findings: &mut Vec<Finding>,
) {
    if !matches!(decl.kind, DeclKind::Theorem | DeclKind::Def) {
        return;
    }

    // Check 1: Conclusion is trivially `True` / `True ∧ (True → True)` etc.
    if !decl.type_tokens.is_empty() && is_pure_true_proposition(&decl.type_tokens) {
        findings.push(Finding {
            rule_id: "lean/trivial-conclusion".to_string(),
            severity: Severity::Error,
            artifact_kind: ArtifactKind::S,
            max_regime: Regime::Attested,
            sink: Some(Sink::Theater),
            path: file.rel_path.clone(),
            line: decl.line,
            column: decl.col,
            symbol: Some(decl.fq_name.clone()),
            message: format!(
                "Declaration `{}` has a tautological `True` conclusion (`{}`)",
                decl.fq_name,
                render_tokens_compact(&decl.type_tokens)
            ),
            remediation: "State the actual domain equality or invariant in the return type instead of `True` / `True ∧ (True → True)`.".to_string(),
        });
    }

    // Check 2: `theorem ... : A ↔ B := Iff.rfl` disguised as a domain theorem
    if decl.kind == DeclKind::Theorem && is_iff_rfl_body(&decl.body_tokens) {
        findings.push(Finding {
            rule_id: "lean/trivial-conclusion".to_string(),
            severity: Severity::Warning,
            artifact_kind: ArtifactKind::S,
            max_regime: Regime::Attested,
            sink: Some(Sink::Label),
            path: file.rel_path.clone(),
            line: decl.line,
            column: decl.col,
            symbol: Some(decl.fq_name.clone()),
            message: format!(
                "Theorem `{}` is proved by `Iff.rfl` (definitional restatement disguised as a theorem)",
                decl.fq_name
            ),
            remediation: "Delete the definitional `Iff.rfl` wrapper and unfold the definition directly at use sites, or prove a non-definitional equivalence.".to_string(),
        });
    }

    // Check 3: Unused/discarded parameters in `theorem` or decider `def` (`*_thm`, `check*`, `verify*`)
    let non_inst_binders: Vec<_> = decl
        .binders
        .iter()
        .filter(|b| !b.is_instance_bracket)
        .collect();
    let is_thm_or_decider = decl.kind == DeclKind::Theorem
        || decl.name.ends_with("_thm")
        || decl.name.ends_with("Decider")
        || decl.name.starts_with("verify")
        || decl.name.starts_with("check");

    if is_thm_or_decider && !non_inst_binders.is_empty() {
        let discarded: Vec<&str> = non_inst_binders
            .iter()
            .filter(|b| {
                if b.name == "_inst" {
                    return false;
                }
                if b.is_underscore {
                    // Allow `_grade : Nat` on Judge `check` interface implementations when other params ARE used
                    if (b.name == "_grade" || b.name == "_" || b.name == "_r")
                        && non_inst_binders.len() > 1
                        && non_inst_binders.iter().any(|other| !other.is_underscore)
                    {
                        return false;
                    }
                    return true;
                }
                // Named parameter in `*_thm` or `verify*` never referenced in type OR body (when body has no pattern-match `|`)
                let has_top_pipe = decl
                    .body_tokens
                    .first()
                    .is_some_and(|t| matches!(&t.kind, LeanTokenKind::Symbol(s) if s == "|"));
                if !has_top_pipe
                    && (decl.name.ends_with("_thm") || decl.name.starts_with("verify"))
                    && !ident_referenced(&decl.type_tokens, &b.name)
                    && !ident_referenced(&decl.body_tokens, &b.name)
                {
                    return true;
                }
                false
            })
            .map(|b| b.name.as_str())
            .collect();

        if !discarded.is_empty() {
            findings.push(Finding {
                rule_id: "lean/unused-param".to_string(),
                severity: Severity::Error,
                artifact_kind: ArtifactKind::S,
                max_regime: Regime::Attested,
                sink: Some(Sink::Theater),
                path: file.rel_path.clone(),
                line: decl.line,
                column: decl.col,
                symbol: Some(decl.fq_name.clone()),
                message: format!(
                    "Declaration `{}` discards parameter(s) `{}` without constraining the conclusion or decision",
                    decl.fq_name,
                    discarded.join(", ")
                ),
                remediation: "Reference every quantified/input parameter in the theorem statement or decision procedure, or remove unused parameters.".to_string(),
            });
        }
    }
}

fn is_pure_true_proposition(type_tokens: &[LeanToken]) -> bool {
    let mut saw_true = false;
    for tok in type_tokens {
        match &tok.kind {
            LeanTokenKind::Ident(id) if id == "True" => {
                saw_true = true;
            }
            LeanTokenKind::Symbol(s)
                if matches!(s.as_str(), "∧" | "∨" | "→" | "->" | "↔" | "<->" | "(" | ")") =>
                {}
            _ => return false,
        }
    }
    saw_true
}

fn is_iff_rfl_body(body_tokens: &[LeanToken]) -> bool {
    if body_tokens.len() == 1
        && let LeanTokenKind::Ident(id) = &body_tokens[0].kind
    {
        return id == "Iff.rfl";
    }
    if body_tokens.len() == 2
        && matches!(&body_tokens[0].kind, LeanTokenKind::Ident(id) if id == "by")
        && matches!(&body_tokens[1].kind, LeanTokenKind::Ident(id) if id == "rfl")
    {
        return false;
    }
    false
}

fn ident_referenced(tokens: &[LeanToken], target: &str) -> bool {
    tokens.iter().any(|t| match &t.kind {
        LeanTokenKind::Ident(id) => {
            id == target || id.split('.').next().is_some_and(|head| head == target)
        }
        LeanTokenKind::AntiquoteIdent(id) => id == target,
        _ => false,
    })
}

fn check_tactic_elab(file: &ParsedLeanFile, decl: &ParsedLeanDecl, findings: &mut Vec<Finding>) {
    let toks = &decl.body_tokens;
    if toks.is_empty() {
        return;
    }

    // Locate `evalTactic` / `closeMainGoal` position if present
    let eval_pos = toks.iter().position(|t| {
        matches!(
            &t.kind,
            LeanTokenKind::Ident(id)
                if id == "evalTactic"
                    || id.ends_with(".evalTactic")
                    || id == "closeMainGoal"
                    || id.ends_with(".closeMainGoal")
        )
    });

    // Extract all `let` bindings before `eval_pos` (or across the whole tactic body)
    let limit = eval_pos.unwrap_or(toks.len());
    let mut bindings: Vec<(String, usize, usize, usize)> = Vec::new(); // (name, line, col, after_rhs_idx)

    let mut idx = 0usize;
    while idx < limit {
        if matches!(&toks[idx].kind, LeanTokenKind::Ident(s) if s == "let") {
            let let_line = toks[idx].line;
            let let_col = toks[idx].col;
            // Collect bound identifiers between `let` and `:=` / `←` / `<-`
            let mut j = idx + 1;
            let mut bound_names = Vec::new();
            while j < limit {
                match &toks[j].kind {
                    LeanTokenKind::Symbol(s) if s == ":=" || s == "<-" || s == "←" => {
                        j += 1;
                        break;
                    }
                    LeanTokenKind::Symbol(s) if s == ":" => {
                        // Skip type annotation until `:=` / `←`
                        while j < limit {
                            if matches!(
                                &toks[j].kind,
                                LeanTokenKind::Symbol(eq) if eq == ":=" || eq == "<-" || eq == "←"
                            ) {
                                j += 1;
                                break;
                            }
                            j += 1;
                        }
                        break;
                    }
                    LeanTokenKind::Ident(bname) if bname != "mut" && !bname.starts_with('_') => {
                        bound_names.push(bname.clone());
                    }
                    _ => {}
                }
                j += 1;
            }
            // Advance past the RHS expression (until next line-starting statement at <= `let_col`)
            let mut rhs_end = j;
            let mut depth = 0isize;
            while rhs_end < limit {
                if depth == 0
                    && rhs_end > j
                    && toks[rhs_end].first_on_line
                    && toks[rhs_end].col <= let_col
                {
                    break;
                }
                match &toks[rhs_end].kind {
                    LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{") => depth += 1,
                    LeanTokenKind::SyntaxQuoteOpen | LeanTokenKind::AntiquoteOpen => depth += 1,
                    LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}") => {
                        depth = (depth - 1).max(0);
                    }
                    _ => {}
                }
                rhs_end += 1;
            }
            for bname in bound_names {
                bindings.push((bname, let_line, let_col, rhs_end));
            }
            idx = rhs_end;
            continue;
        }
        idx += 1;
    }

    // 1. Check bindings never referenced anywhere after their RHS!
    for (bname, bline, bcol, after_rhs) in &bindings {
        if *after_rhs >= toks.len() || !ident_referenced(&toks[*after_rhs..], bname) {
            findings.push(Finding {
                rule_id: "lean/discarded-tactic-binding".to_string(),
                severity: Severity::Error,
                artifact_kind: ArtifactKind::P,
                max_regime: Regime::Attested,
                sink: Some(Sink::Theater),
                path: file.rel_path.clone(),
                line: *bline,
                column: *bcol,
                symbol: Some(format!("{} (let {bname})", decl.name)),
                message: format!(
                    "Tactic `{}` computes `let {bname} := ...` and never references `{bname}` before closing the goal",
                    decl.name
                ),
                remediation: "Splice the computed witness/term into the proof term (`$x` / `closeMainGoal`), or delete the theatrical `let` binding.".to_string(),
            });
        }
    }

    // 2. Check `evalTactic` slice: if the tactic computes local `let` bindings (beyond `target`/`goal`),
    // check whether ANY local binding is spliced into `evalTactic` (outside syntax-quote literal text)!
    if let Some(epos) = eval_pos {
        let eval_slice = &toks[epos + 1..];
        let spliced_idents = collect_meta_referenced_idents_in_eval(eval_slice);
        let domain_bindings: Vec<&(String, usize, usize, usize)> = bindings
            .iter()
            .filter(|(bname, _, _, after_rhs)| {
                !matches!(bname.as_str(), "target" | "goal" | "mvarId" | "env")
                    && *after_rhs < toks.len()
                    && ident_referenced(&toks[*after_rhs..], bname)
            })
            .collect();

        if !domain_bindings.is_empty()
            && domain_bindings
                .iter()
                .all(|(bname, _, _, _)| !spliced_idents.contains(bname.as_str()))
        {
            let (_, last_line, last_col, _) = domain_bindings.last().copied().unwrap();
            let names: Vec<&str> = domain_bindings.iter().map(|t| t.0.as_str()).collect();
            findings.push(Finding {
                rule_id: "lean/discarded-tactic-binding".to_string(),
                severity: Severity::Error,
                artifact_kind: ArtifactKind::P,
                max_regime: Regime::Attested,
                sink: Some(Sink::Theater),
                path: file.rel_path.clone(),
                line: *last_line,
                column: *last_col,
                symbol: Some(decl.name.clone()),
                message: format!(
                    "Tactic `{}` computes `{}` in MetaM, checks a side-condition, and then discards all computed data to run canned static `evalTactic` search",
                    decl.name,
                    names.join(", ")
                ),
                remediation: "Reconstruct a Lean proof term or certificate from the computed state and splice it via `$(...)` into `evalTactic` / `closeMainGoal`.".to_string(),
            });
        }
    }
}

/// Collect identifiers referenced at the Meta level in `evalTactic (...)`:
/// inside `` `(...) `` syntax quotes, ONLY `AntiquoteIdent($x)` or tokens inside `AntiquoteOpen $(...)`
/// reference local `let` bindings; outside `` `(...) ``, normal `Ident` tokens reference local bindings.
fn collect_meta_referenced_idents_in_eval(slice: &[LeanToken]) -> HashSet<String> {
    let mut out = HashSet::new();
    let mut quote_depth = 0usize;
    let mut antiquote_depth = 0usize;
    // Stack tracking what each `(` / `SyntaxQuoteOpen` / `AntiquoteOpen` opened:
    // 0 = normal paren, 1 = syntax quote, 2 = antiquote
    let mut stack: Vec<u8> = Vec::new();

    for tok in slice {
        match &tok.kind {
            LeanTokenKind::SyntaxQuoteOpen => {
                quote_depth += 1;
                stack.push(1);
            }
            LeanTokenKind::AntiquoteOpen => {
                antiquote_depth += 1;
                stack.push(2);
            }
            LeanTokenKind::AntiquoteIdent(id) => {
                out.insert(id.clone());
                if let Some(head) = id.split('.').next() {
                    out.insert(head.to_string());
                }
            }
            LeanTokenKind::Symbol(s) if s == "(" => {
                stack.push(0);
            }
            LeanTokenKind::Symbol(s) if s == ")" => match stack.pop() {
                Some(1) => quote_depth = quote_depth.saturating_sub(1),
                Some(2) => antiquote_depth = antiquote_depth.saturating_sub(1),
                _ => {}
            },
            LeanTokenKind::Ident(id) if (quote_depth == 0 || antiquote_depth > 0) => {
                out.insert(id.clone());
                if let Some(head) = id.split('.').next() {
                    out.insert(head.to_string());
                }
            }
            _ => {}
        }
    }

    out
}

fn resolves_to_judge_head(head: &str, decl_by_name: &HashMap<&str, &ParsedLeanDecl>) -> bool {
    if head == "Judge" || head == "Obend.Judge" {
        return true;
    }
    let short = head.rsplit('.').next().unwrap_or(head);
    if let Some(ab) = decl_by_name.get(short)
        && ab.kind == DeclKind::Abbrev
    {
        return ab.body_tokens.first().is_some_and(
            |t| matches!(&t.kind, LeanTokenKind::Ident(id) if id == "Judge" || id == "Obend.Judge"),
        );
    }
    false
}

fn strip_leading_at_and_parens(mut toks: &[LeanToken]) -> &[LeanToken] {
    loop {
        let stripped = strip_outer_parens_tokens(toks);
        if let Some(first) = stripped.first()
            && matches!(&first.kind, LeanTokenKind::Symbol(s) if s == "@")
        {
            toks = &stripped[1..];
            continue;
        }
        return stripped;
    }
}

fn struct_update_base_ident(body_tokens: &[LeanToken]) -> Option<&str> {
    let stripped = strip_outer_parens_tokens(body_tokens);
    if stripped.len() >= 4
        && matches!(&stripped[0].kind, LeanTokenKind::Symbol(s) if s == "{")
        && let LeanTokenKind::Ident(base_id) = &stripped[1].kind
        && matches!(&stripped[2].kind, LeanTokenKind::Ident(kw) if kw == "with")
    {
        return Some(base_id.as_str());
    }
    None
}

fn is_judge_instance_decl(
    decl: &ParsedLeanDecl,
    decl_by_name: &HashMap<&str, &ParsedLeanDecl>,
) -> bool {
    is_judge_instance_decl_bounded(decl, decl_by_name, 0)
}

fn is_judge_instance_decl_bounded(
    decl: &ParsedLeanDecl,
    decl_by_name: &HashMap<&str, &ParsedLeanDecl>,
    depth: usize,
) -> bool {
    if depth >= 6 || !matches!(decl.kind, DeclKind::Instance | DeclKind::Def) {
        return false;
    }
    if let Some(LeanToken {
        kind: LeanTokenKind::Ident(id),
        ..
    }) = decl.type_tokens.first()
        && resolves_to_judge_head(id, decl_by_name)
    {
        return true;
    }
    if let Some(head) = instance_target_head_class(&decl.type_tokens)
        && resolves_to_judge_head(&head, decl_by_name)
    {
        return true;
    }
    let body_core = strip_leading_at_and_parens(&decl.body_tokens);
    if body_core.first().is_some_and(|t| {
        matches!(
            &t.kind,
            LeanTokenKind::Ident(id) if id == "Judge.mk" || id == "Obend.Judge.mk"
        )
    }) {
        return true;
    }
    if let Some(base_id) = struct_update_base_ident(&decl.body_tokens) {
        let base_short = base_id.rsplit('.').next().unwrap_or(base_id);
        if let Some(base_decl) = decl_by_name
            .get(base_id)
            .or_else(|| decl_by_name.get(base_short))
            && base_decl.fq_name != decl.fq_name
            && is_judge_instance_decl_bounded(base_decl, decl_by_name, depth + 1)
        {
            return true;
        }
    }
    let has_check = decl.where_fields.iter().any(|f| f.name == "check");
    let has_fragment = decl.where_fields.iter().any(|f| f.name == "Fragment");
    let has_meaning = decl.where_fields.iter().any(|f| f.name == "Meaning");
    has_check && has_fragment && has_meaning
}

fn judge_canonical_field_names() -> Vec<String> {
    vec![
        "Clause".to_string(),
        "Meaning".to_string(),
        "check".to_string(),
        "sound".to_string(),
        "refutes".to_string(),
        "refuted".to_string(),
        "Fragment".to_string(),
        "complete".to_string(),
        "mono".to_string(),
    ]
}

fn extract_judge_fields<'a>(
    decl: &'a ParsedLeanDecl,
    decl_by_name: &'a HashMap<&'a str, &'a ParsedLeanDecl>,
) -> Vec<ExtractedInstanceField> {
    extract_judge_fields_inner(decl, decl_by_name, 0)
}

fn extract_judge_fields_inner(
    decl: &ParsedLeanDecl,
    decl_by_name: &HashMap<&str, &ParsedLeanDecl>,
    depth: usize,
) -> Vec<ExtractedInstanceField> {
    let fnames = judge_canonical_field_names();
    if decl.where_fields.is_empty() {
        let has_at = decl
            .body_tokens
            .first()
            .is_some_and(|t| matches!(&t.kind, LeanTokenKind::Symbol(s) if s == "@"));
        let body_core = strip_leading_at_and_parens(&decl.body_tokens);
        let is_mk = body_core.first().is_some_and(|t| {
            matches!(
                &t.kind,
                LeanTokenKind::Ident(id) if id == "Judge.mk" || id == "Obend.Judge.mk"
            ) || matches!(&t.kind, LeanTokenKind::Symbol(s) if s == ".mk")
        });
        if is_mk {
            let mut args_slice = &body_core[1..];
            if args_slice
                .first()
                .is_some_and(|t| matches!(&t.kind, LeanTokenKind::Symbol(s) if s == "<|"))
            {
                args_slice = &args_slice[1..];
            }
            let mut named_fields: Vec<ExtractedInstanceField> = Vec::new();
            let mut pos_args: Vec<Vec<LeanToken>> = Vec::new();
            let mut i = 0usize;
            while i < args_slice.len() {
                match &args_slice[i].kind {
                    LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "{" | "[" | "⟨") => {
                        let open = s.as_str();
                        let close = match open {
                            "(" => ")",
                            "{" => "}",
                            "[" => "]",
                            _ => "⟩",
                        };
                        let start = i;
                        let mut bdepth = 1usize;
                        i += 1;
                        while i < args_slice.len() && bdepth > 0 {
                            match &args_slice[i].kind {
                                LeanTokenKind::Symbol(o) if o == open => bdepth += 1,
                                LeanTokenKind::Symbol(c) if c == close => bdepth -= 1,
                                _ => {}
                            }
                            i += 1;
                        }
                        let end = i;
                        if open == "(" && end >= start + 3 {
                            let inner = &args_slice[start + 1..end - 1];
                            if let Some(f) = parse_field_assignment_chunk(inner) {
                                named_fields.push(f);
                                continue;
                            }
                        }
                        pos_args.push(args_slice[start..end].to_vec());
                    }
                    LeanTokenKind::Symbol(s) if s.starts_with('@') || s == "<|" => {
                        i += 1;
                    }
                    _ => {
                        pos_args.push(vec![args_slice[i].clone()]);
                        i += 1;
                    }
                }
            }
            //Under `@Judge.mk Obj Cert ...`, the first 2 positional args are `{Obj Cert : Type}`
            let pos_skip = if has_at && pos_args.len() >= 9 { 2 } else { 0 };
            let pos_slice = &pos_args[pos_skip.min(pos_args.len())..];
            let mut merged = Vec::new();
            let named_set: HashSet<String> =
                named_fields.iter().filter_map(|f| f.name.clone()).collect();
            if !pos_slice.is_empty() && (pos_slice.len() + named_fields.len() >= 7) {
                let mut fname_iter = fnames.iter().filter(|n| !named_set.contains(*n));
                for rhs in pos_slice {
                    if let Some(fname) = fname_iter.next() {
                        let first = &rhs[0];
                        let inner = strip_outer_parens_tokens(rhs).to_vec();
                        merged.push(ExtractedInstanceField {
                            name: Some(fname.clone()),
                            params: Vec::new(),
                            line: first.line,
                            col: first.col,
                            rhs_tokens: inner,
                        });
                    }
                }
            }
            merged.extend(named_fields);
            if !merged.is_empty() {
                return merged;
            }
        }
    }

    let mut fields = extract_instance_fields(decl, Some(&fnames));
    // Inherit un-overridden fields (such as `check`) from `{ baseJudge with Fragment := ... }`
    if depth < 4
        && let Some(base_id) = struct_update_base_ident(&decl.body_tokens)
    {
        let base_short = base_id.rsplit('.').next().unwrap_or(base_id);
        if let Some(base_decl) = decl_by_name
            .get(base_id)
            .or_else(|| decl_by_name.get(base_short))
            && base_decl.fq_name != decl.fq_name
        {
            let present: HashSet<String> = fields.iter().filter_map(|f| f.name.clone()).collect();
            for bf in extract_judge_fields_inner(base_decl, decl_by_name, depth + 1) {
                if let Some(ref bname) = bf.name
                    && !present.contains(bname)
                {
                    fields.push(bf);
                }
            }
        }
    }
    fields
}

fn check_judge_empty_fragment(
    file: &ParsedLeanFile,
    decl: &ParsedLeanDecl,
    decl_by_name: &HashMap<&str, &ParsedLeanDecl>,
    findings: &mut Vec<Finding>,
) {
    let extracted = extract_judge_fields(decl, decl_by_name);
    for ef in extracted {
        let Some(fname) = ef.name.as_deref() else {
            continue;
        };
        if fname != "Fragment" && fname != "refutes" {
            continue;
        }
        let mut bound = HashSet::new();
        for p in &ef.params {
            if p != "_" {
                bound.insert(p.clone());
            }
        }
        let core = strip_leading_lambdas(&ef.rhs_tokens, &mut bound);
        let core = strip_outer_parens_tokens(core);
        if core.len() != 1 {
            continue;
        }
        if let LeanTokenKind::Ident(id) = &core[0].kind {
            let short = id.rsplit('.').next().unwrap_or(id.as_str());
            if fname == "Fragment" && (short == "False" || short == "Empty") {
                findings.push(Finding {
                    rule_id: "lean/judge-empty-fragment".to_string(),
                    severity: Severity::Warning,
                    artifact_kind: ArtifactKind::S,
                    max_regime: Regime::Attested,
                    sink: Some(Sink::Theater),
                    path: file.rel_path.clone(),
                    line: ef.line,
                    column: ef.col,
                    symbol: Some(format!("{}.Fragment", decl.fq_name)),
                    message: format!(
                        "`{}` defines `Fragment := {}` (`{short}`), vacating completeness (`Judge.complete` holds vacuously on an empty fragment)",
                        decl.fq_name,
                        render_tokens_compact(&ef.rhs_tokens)
                    ),
                    remediation: "Define `Fragment` as the inhabited decidable domain predicate handled by `check` and prove `complete` constructively over that fragment.".to_string(),
                });
            } else if fname == "refutes" && (short == "false" || id == "Bool.false") {
                findings.push(Finding {
                    rule_id: "lean/judge-empty-fragment".to_string(),
                    severity: Severity::Warning,
                    artifact_kind: ArtifactKind::S,
                    max_regime: Regime::Attested,
                    sink: Some(Sink::Theater),
                    path: file.rel_path.clone(),
                    line: ef.line,
                    column: ef.col,
                    symbol: Some(format!("{}.refutes", decl.fq_name)),
                    message: format!(
                        "`{}` defines `refutes := {}` (`false`), vacating refusal soundness (`Judge.refuted` never certifies a negative verdict)",
                        decl.fq_name,
                        render_tokens_compact(&ef.rhs_tokens)
                    ),
                    remediation: "Set `refutes` to `true` on genuine counterexample/refusal clauses and prove `refuted` (`check = .refused c _ → ¬ Meaning`) from completeness or clause soundness.".to_string(),
                });
            }
        }
    }
}

fn is_ignored_check_combinator(short: &str) -> bool {
    matches!(
        short,
        "_" | "fun"
            | "λ"
            | "if"
            | "then"
            | "else"
            | "match"
            | "matches"
            | "with"
            | "let"
            | "in"
            | "do"
            | "by"
            | "true"
            | "false"
            | "True"
            | "False"
            | "some"
            | "none"
            | "ok"
            | "error"
            | "refused"
            | "uncovered"
            | "verified"
            | "isOk"
            | "isVerified"
            | "decide"
            | "ite"
            | "dite"
            | "not"
            | "deepen"
            | "map"
            | "mk"
            | "inl"
            | "inr"
            | "intro"
            | "Nat"
            | "Int"
            | "UInt8"
            | "UInt64"
            | "ByteArray"
            | "Unit"
            | "PUnit"
            | "Bool"
            | "Option"
            | "Except"
            | "Verdict"
            | "String"
            | "List"
            | "Array"
            | "Prod"
            | "And"
            | "Or"
            | "Exists"
            | "fst"
            | "snd"
    )
}

fn is_verdict_acceptance_token(tok: &LeanToken) -> bool {
    match &tok.kind {
        LeanTokenKind::Symbol(s) => {
            matches!(s.as_str(), ".ok" | ".verified" | ".isOk" | ".isVerified")
        }
        LeanTokenKind::Ident(id) => {
            let short = id.rsplit('.').next().unwrap_or(id.as_str());
            matches!(short, "ok" | "verified" | "isOk" | "isVerified")
                && (id == short || id.contains("Verdict") || id.starts_with("Except"))
        }
        _ => false,
    }
}

fn is_verdict_rejection_token(tok: &LeanToken) -> bool {
    match &tok.kind {
        LeanTokenKind::Symbol(s) => matches!(s.as_str(), ".refused" | ".uncovered" | ".error"),
        LeanTokenKind::Ident(id) => {
            let short = id.rsplit('.').next().unwrap_or(id.as_str());
            matches!(short, "refused" | "uncovered" | "error")
                && (id == short || id.contains("Verdict") || id.starts_with("Except"))
                || matches!(id.as_str(), "false" | "Bool.false" | "none" | "Option.none")
        }
        _ => false,
    }
}

fn is_bool_or_verdict_acceptance_token(tok: &LeanToken) -> bool {
    is_verdict_acceptance_token(tok)
        || matches!(
            &tok.kind,
            LeanTokenKind::Ident(id) if matches!(id.as_str(), "true" | "Bool.true" | "some" | "Option.some")
        )
}

fn has_prefix_word(s: &str, prefix: &str) -> bool {
    s.strip_prefix(prefix).is_some_and(|rest| {
        rest.chars()
            .next()
            .is_none_or(|c| c.is_ascii_uppercase() || c == '_' || c.is_ascii_digit())
    })
}

fn looks_like_operational_checker_ident(short: &str) -> bool {
    has_prefix_word(short, "check")
        || has_prefix_word(short, "verify")
        || has_prefix_word(short, "validate")
        || has_prefix_word(short, "judge")
        || short.ends_with("Check")
        || short.ends_with("Verify")
        || short.ends_with("Checker")
        || short.ends_with("Verifier")
}

/// Collect inner local binders (`fun x =>`, `let x :=`, `| pat =>`) inside a term slice so local
/// pattern variables never leak out as fake global checker identifiers.
fn collect_term_local_binders(tokens: &[LeanToken], bound: &mut HashSet<String>) {
    let mut i = 0usize;
    while i < tokens.len() {
        let is_lam_or_forall = matches!(
            &tokens[i].kind,
            LeanTokenKind::Ident(id) if id == "fun" || id == "λ"
        ) || matches!(&tokens[i].kind, LeanTokenKind::Symbol(s) if s == "∀" || s == "∃");
        if is_lam_or_forall {
            let mut j = i + 1;
            let mut depth = 0usize;
            while j < tokens.len() {
                match &tokens[j].kind {
                    LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "{" | "[") => depth += 1,
                    LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "}" | "]") => {
                        depth = depth.saturating_sub(1);
                    }
                    LeanTokenKind::Symbol(s) if (s == "=>" || s == ",") && depth == 0 => break,
                    LeanTokenKind::Symbol(s) if s == ":" && depth > 0 => {
                        // Skip type annotation inside `(x : T)` until matching `)`
                        while j + 1 < tokens.len()
                            && !matches!(&tokens[j + 1].kind, LeanTokenKind::Symbol(c) if matches!(c.as_str(), ")" | "}" | "]"))
                        {
                            j += 1;
                        }
                    }
                    LeanTokenKind::Ident(id) if id != "_" && !id.contains('.') => {
                        bound.insert(id.clone());
                    }
                    _ => {}
                }
                j += 1;
            }
            i = j;
            continue;
        }
        if matches!(&tokens[i].kind, LeanTokenKind::Ident(id) if id == "let")
            && let Some(LeanToken {
                kind: LeanTokenKind::Ident(var),
                ..
            }) = tokens.get(i + 1)
            && var != "_"
        {
            bound.insert(var.clone());
        }
        if matches!(&tokens[i].kind, LeanTokenKind::Symbol(s) if s == "|") {
            let mut j = i + 1;
            while j < tokens.len() {
                if matches!(&tokens[j].kind, LeanTokenKind::Symbol(s) if s == "=>") {
                    break;
                }
                if let LeanTokenKind::Ident(id) = &tokens[j].kind
                    && id != "_"
                    && !id.contains('.')
                    && id.chars().next().is_some_and(|c| c.is_ascii_lowercase())
                {
                    bound.insert(id.clone());
                }
                j += 1;
            }
        }
        i += 1;
    }
}

fn is_operational_check_callee_candidate(
    short: &str,
    is_head_of_check: bool,
    decl_by_name: &HashMap<&str, &ParsedLeanDecl>,
) -> bool {
    if short.len() < 2 || is_ignored_check_combinator(short) {
        return false;
    }
    if short.chars().next().is_some_and(|c| c.is_ascii_uppercase())
        && !looks_like_operational_checker_ident(short)
    {
        return false;
    }
    if let Some(d) = decl_by_name.get(short) {
        // Pure `: Prop` domain predicates (`WellFormed q : Prop`) are NOT operational checkers!
        if tokens_end_with_prop(&d.type_tokens) {
            return false;
        }
        if !is_head_of_check && !looks_like_operational_checker_ident(short) {
            // Non-head helpers called inside `check` (e.g. `normalize q`) only count if their
            // declared return type is an acceptance/verdict/boolean carrier (`Bool`, `Verdict`, `Except`, `Option`).
            let (_, ret_concl) = split_top_level_arrows(&d.type_tokens);
            let returns_verdict_like = ret_concl.iter().any(|t| {
                matches!(
                    &t.kind,
                    LeanTokenKind::Ident(id)
                        if matches!(
                            id.rsplit('.').next().unwrap_or(id.as_str()),
                            "Bool" | "Verdict" | "CheckVerdict" | "CheckResult" | "Except" | "Option"
                        )
                )
            });
            if !returns_verdict_like {
                return false;
            }
        }
    } else if !is_head_of_check && !looks_like_operational_checker_ident(short) {
        // Unknown non-head helper (e.g. imported pure projection/normalizer `normalize`) is NOT assumed to be a checker
        return false;
    }
    true
}

/// Extract the application sub-slice immediately to the left of `op_idx` up to the nearest
/// logical connective / quantifier comma / enclosing paren.
fn comparand_slice_before(slice: &[LeanToken], op_idx: usize) -> &[LeanToken] {
    let mut k = op_idx;
    let mut depth = 0i32;
    while k > 0 {
        let prev = &slice[k - 1];
        match &prev.kind {
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}") => depth += 1,
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{") => {
                if depth == 0 {
                    break;
                }
                depth -= 1;
            }
            LeanTokenKind::Symbol(s)
                if depth == 0
                    && matches!(
                        s.as_str(),
                        "∧" | "∨" | "," | "→" | "->" | "↔" | "=>" | ";" | ":=" | "|" | "¬"
                    ) =>
            {
                break;
            }
            LeanTokenKind::Ident(id)
                if depth == 0 && matches!(id.as_str(), "if" | "then" | "else" | "in" | "with") =>
            {
                break;
            }
            _ => {}
        }
        k -= 1;
    }
    strip_outer_parens_tokens(&slice[k..op_idx])
}

/// Extract the application sub-slice immediately to the right of `op_idx`.
fn comparand_slice_after(slice: &[LeanToken], op_idx: usize) -> &[LeanToken] {
    let start = op_idx + 1;
    if start >= slice.len() {
        return &[];
    }
    let mut k = start;
    let mut depth = 0i32;
    while k < slice.len() {
        let cur = &slice[k];
        match &cur.kind {
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{") => depth += 1,
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}") => {
                if depth == 0 {
                    break;
                }
                depth -= 1;
            }
            LeanTokenKind::Symbol(s)
                if depth == 0
                    && matches!(
                        s.as_str(),
                        "∧" | "∨" | "," | "→" | "->" | "↔" | "=>" | ";" | "|"
                    ) =>
            {
                break;
            }
            LeanTokenKind::Ident(id)
                if depth == 0 && matches!(id.as_str(), "then" | "else" | "in" | "with") =>
            {
                break;
            }
            _ => {}
        }
        k += 1;
    }
    strip_outer_parens_tokens(&slice[start..k])
}

fn extract_call_head_ident<'a>(
    expr: &'a [LeanToken],
    local_bound: &HashSet<String>,
    bound_check_heads: &HashSet<String>,
) -> Option<&'a str> {
    let stripped = strip_outer_parens_tokens(expr);
    for tok in stripped {
        if let LeanTokenKind::Ident(id) = &tok.kind {
            let root = id.split('.').next().unwrap_or(id.as_str());
            let short = id.rsplit('.').next().unwrap_or(id.as_str());
            if bound_check_heads.contains(id.as_str()) {
                return Some(id.as_str());
            }
            if local_bound.contains(id.as_str())
                || local_bound.contains(root)
                || is_ignored_check_combinator(short)
            {
                continue;
            }
            return Some(id.as_str());
        }
    }
    None
}

/// 2026 Soundness Rule (`lean/judge-fragment-restates-check`):
/// Flags `Judge` instances / builders whose `Fragment` field restates the operational `check` /
/// `verify*` verdict function (e.g. `Fragment q := ∃ c, verifySameOpening q c = .ok`), collapsing
/// `Judge.complete` into a 1-line projection tautology.
fn check_judge_fragment_restates_check(
    file: &ParsedLeanFile,
    decl: &ParsedLeanDecl,
    decl_by_name: &HashMap<&str, &ParsedLeanDecl>,
    strict_vacuity: bool,
    findings: &mut Vec<Finding>,
) {
    let extracted = extract_judge_fields(decl, decl_by_name);
    let Some(frag_field) = extracted
        .iter()
        .find(|ef| ef.name.as_deref() == Some("Fragment"))
    else {
        return;
    };

    let mut base_bound: HashSet<String> = HashSet::new();
    for sv in &file.section_variables {
        if !sv.is_underscore && sv.name != "_" {
            base_bound.insert(sv.name.clone());
        }
    }
    for b in &decl.binders {
        if !b.is_underscore && b.name != "_" {
            base_bound.insert(b.name.clone());
        }
    }

    // Collect operational callees from `check` + bound-variable checker heads (`w.verify`, `chk`)
    let mut direct_check_callees: HashSet<String> = HashSet::new();
    let mut bound_check_heads: HashSet<String> = HashSet::new();
    if let Some(check_field) = extracted
        .iter()
        .find(|ef| ef.name.as_deref() == Some("check"))
    {
        let mut check_param_bound: HashSet<String> = HashSet::new();
        for p in &check_field.params {
            if p != "_" {
                check_param_bound.insert(p.clone());
            }
        }
        let mut check_bound = base_bound.clone();
        check_bound.extend(check_param_bound.iter().cloned());
        let check_core = strip_leading_lambdas(&check_field.rhs_tokens, &mut check_bound);
        for b in check_bound.difference(&base_bound) {
            check_param_bound.insert(b.clone());
        }
        collect_term_local_binders(check_core, &mut check_bound);

        let check_head_short: Option<&str> =
            extract_call_head_ident(check_core, &check_bound, &bound_check_heads)
                .map(|h| h.rsplit('.').next().unwrap_or(h));

        for (tidx, tok) in check_core.iter().enumerate() {
            if let LeanTokenKind::Ident(id) = &tok.kind {
                let root = id.split('.').next().unwrap_or(id.as_str());
                let short = id.rsplit('.').next().unwrap_or(id.as_str());
                // Bound workflow/checker parameter (`w.verify q c` or `chk q c` where `w`/`chk` is in `base_bound`)
                if base_bound.contains(root) && !check_param_bound.contains(root) {
                    if id.contains('.') || tidx == 0 {
                        bound_check_heads.insert(id.clone());
                    }
                    continue;
                }
                let is_head = check_head_short == Some(short);
                if check_bound.contains(id.as_str())
                    || check_bound.contains(root)
                    || !is_operational_check_callee_candidate(short, is_head, decl_by_name)
                {
                    continue;
                }
                direct_check_callees.insert(short.to_string());
                if let Some(helper) = decl_by_name.get(short)
                    && matches!(helper.kind, DeclKind::Def | DeclKind::Abbrev)
                    && helper.body_tokens.len() <= 18
                {
                    let mut hbound: HashSet<String> = helper
                        .binders
                        .iter()
                        .filter(|b| !b.is_underscore && b.name != "_")
                        .map(|b| b.name.clone())
                        .collect();
                    let hcore = strip_leading_lambdas(&helper.body_tokens, &mut hbound);
                    collect_term_local_binders(hcore, &mut hbound);
                    let empty_heads = HashSet::new();
                    let h_head_short = extract_call_head_ident(hcore, &hbound, &empty_heads)
                        .map(|h| h.rsplit('.').next().unwrap_or(h));
                    for htok in hcore {
                        if let LeanTokenKind::Ident(hid) = &htok.kind {
                            let hroot = hid.split('.').next().unwrap_or(hid.as_str());
                            let hshort = hid.rsplit('.').next().unwrap_or(hid.as_str());
                            let h_is_head = is_head && h_head_short == Some(hshort);
                            if !hbound.contains(hid.as_str())
                                && !hbound.contains(hroot)
                                && is_operational_check_callee_candidate(
                                    hshort,
                                    h_is_head,
                                    decl_by_name,
                                )
                            {
                                direct_check_callees.insert(hshort.to_string());
                            }
                        }
                    }
                }
            }
        }
    }

    // Build candidate slices via up to 3-hop BFS over helper `Def | Abbrev | Inductive | Structure` decls
    let mut frag_bound = base_bound.clone();
    for p in &frag_field.params {
        if p != "_" {
            frag_bound.insert(p.clone());
        }
    }
    let frag_core = strip_outer_parens_tokens(strip_leading_lambdas(
        &frag_field.rhs_tokens,
        &mut frag_bound,
    ));

    // `(tokens, bound_vars, implicit_existential_from_inductive_or_struct)`
    let mut slices_to_check: Vec<(Vec<LeanToken>, HashSet<String>, HashSet<String>)> =
        vec![(frag_core.to_vec(), frag_bound.clone(), HashSet::new())];
    let mut visited_helpers: HashSet<String> = HashSet::new();
    let mut queue_idx = 0usize;

    while queue_idx < slices_to_check.len() && slices_to_check.len() < 8 {
        let (cur_slice, cur_bound, _) = slices_to_check[queue_idx].clone();
        queue_idx += 1;
        for tok in &cur_slice {
            if slices_to_check.len() >= 8 {
                break;
            }
            if let LeanTokenKind::Ident(id) = &tok.kind {
                let root = id.split('.').next().unwrap_or(id.as_str());
                let short = id.rsplit('.').next().unwrap_or(id.as_str());
                if cur_bound.contains(id.as_str())
                    || cur_bound.contains(root)
                    || direct_check_callees.contains(short)
                    || !visited_helpers.insert(short.to_string())
                {
                    continue;
                }
                if let Some(helper) = decl_by_name
                    .get(id.as_str())
                    .or_else(|| decl_by_name.get(short))
                {
                    match helper.kind {
                        DeclKind::Def | DeclKind::Abbrev
                            if tokens_end_with_prop(&helper.type_tokens)
                                || helper.type_tokens.is_empty() =>
                        {
                            let mut hbound: HashSet<String> = base_bound.clone();
                            for b in &helper.binders {
                                if !b.is_underscore && b.name != "_" {
                                    hbound.insert(b.name.clone());
                                }
                            }
                            let hcore = strip_outer_parens_tokens(strip_leading_lambdas(
                                &helper.body_tokens,
                                &mut hbound,
                            ));
                            let capped = &hcore[..hcore.len().min(512)];
                            slices_to_check.push((capped.to_vec(), hbound, HashSet::new()));
                        }
                        DeclKind::Inductive | DeclKind::Structure => {
                            let mut hbound: HashSet<String> = base_bound.clone();
                            for b in &helper.binders {
                                if !b.is_underscore && b.name != "_" {
                                    hbound.insert(b.name.clone());
                                }
                            }
                            let mut witness_fields = HashSet::new();
                            let mut combined = Vec::new();
                            for sf in &helper.struct_fields {
                                if sf.name != "_" {
                                    witness_fields.insert(sf.name.clone());
                                }
                                for sb in &sf.binders {
                                    if !sb.is_underscore && sb.name != "_" {
                                        witness_fields.insert(sb.name.clone());
                                    }
                                    combined.extend(sb.type_tokens.iter().cloned());
                                }
                                combined.extend(sf.type_tokens.iter().cloned());
                            }
                            combined.extend(helper.body_tokens.iter().cloned());
                            if combined.len() > 512 {
                                combined.truncate(512);
                            }
                            if !combined.is_empty() {
                                slices_to_check.push((combined, hbound, witness_fields));
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    let mut culprit_fn: Option<String> = None;

    for (slice, bound_vars, extra_ex_vars) in &slices_to_check {
        let mut local_bound = bound_vars.clone();
        let mut ex_vars = extra_ex_vars.clone();
        let mut has_existential = !ex_vars.is_empty();

        // Collect `∃ c r, ...` and `Exists (fun c => ...)` existential witnesses, plus `∀` / `fun` / `let` local vars
        let mut i = 0usize;
        while i < slice.len() {
            if matches!(&slice[i].kind, LeanTokenKind::Symbol(s) if s == "∃") {
                has_existential = true;
                let mut j = i + 1;
                let mut depth = 0usize;
                while j < slice.len() {
                    match &slice[j].kind {
                        LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "{" | "[") => {
                            depth += 1;
                        }
                        LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "}" | "]") => {
                            depth = depth.saturating_sub(1);
                        }
                        LeanTokenKind::Symbol(s) if s == "," && depth == 0 => break,
                        LeanTokenKind::Symbol(s) if s == ":" && depth > 0 => {
                            while j + 1 < slice.len()
                                && !matches!(&slice[j + 1].kind, LeanTokenKind::Symbol(c) if matches!(c.as_str(), ")" | "}" | "]"))
                            {
                                j += 1;
                            }
                        }
                        LeanTokenKind::Ident(id) if id != "_" && !id.contains('.') => {
                            local_bound.insert(id.clone());
                            ex_vars.insert(id.clone());
                        }
                        _ => {}
                    }
                    j += 1;
                }
            } else if matches!(&slice[i].kind, LeanTokenKind::Ident(id) if id == "Exists") {
                has_existential = true;
                // `Exists (fun c => ...)`
                let mut j = i + 1;
                while j < slice.len() && j < i + 6 {
                    if matches!(&slice[j].kind, LeanTokenKind::Ident(kw) if kw == "fun" || kw == "λ")
                        && let Some(LeanToken {
                            kind: LeanTokenKind::Ident(v),
                            ..
                        }) = slice.get(j + 1)
                        && v != "_"
                    {
                        local_bound.insert(v.clone());
                        ex_vars.insert(v.clone());
                        break;
                    }
                    j += 1;
                }
            }
            i += 1;
        }
        collect_term_local_binders(slice, &mut local_bound);

        // Pattern A: `Fragment` directly invokes an operational callee from `check` (including bound `w.verify`)
        for tok in slice {
            if let LeanTokenKind::Ident(id) = &tok.kind {
                if bound_check_heads.contains(id.as_str()) {
                    culprit_fn = Some(id.clone());
                    break;
                }
                let root = id.split('.').next().unwrap_or(id.as_str());
                let short = id.rsplit('.').next().unwrap_or(id.as_str());
                if local_bound.contains(id.as_str()) || local_bound.contains(root) {
                    continue;
                }
                if direct_check_callees.contains(short) {
                    culprit_fn = Some(short.to_string());
                    break;
                }
            }
        }
        if culprit_fn.is_some() {
            break;
        }

        // Pattern B & C: Existentially quantified operational verdict / checker acceptance
        // (`∃ c, verifyFoo q c = .ok`, `∃ c, (verifyFoo q c).isOk`, `∃ c, verifyFoo q c ≠ .refused r`, `∃ c, checkFoo q c = true`)
        if has_existential {
            let mut candidate_exprs: Vec<(&[LeanToken], bool)> = Vec::new();
            for (idx, tok) in slice.iter().enumerate() {
                match &tok.kind {
                    LeanTokenKind::Symbol(s) if s == "=" || s == "==" => {
                        let lhs = comparand_slice_before(slice, idx);
                        let rhs = comparand_slice_after(slice, idx);
                        let rhs_verdict = rhs.iter().any(is_verdict_acceptance_token);
                        let lhs_verdict = lhs.iter().any(is_verdict_acceptance_token);
                        let rhs_bool = rhs.iter().any(is_bool_or_verdict_acceptance_token);
                        let lhs_bool = lhs.iter().any(is_bool_or_verdict_acceptance_token);
                        if rhs_verdict && !lhs.is_empty() {
                            candidate_exprs.push((lhs, true));
                        } else if lhs_verdict && !rhs.is_empty() {
                            candidate_exprs.push((rhs, true));
                        } else if rhs_bool && !lhs.is_empty() {
                            candidate_exprs.push((lhs, false));
                        } else if lhs_bool && !rhs.is_empty() {
                            candidate_exprs.push((rhs, false));
                        }
                    }
                    LeanTokenKind::Symbol(s) if s == "≠" || s == "!=" => {
                        let lhs = comparand_slice_before(slice, idx);
                        let rhs = comparand_slice_after(slice, idx);
                        if rhs.iter().any(is_verdict_rejection_token) && !lhs.is_empty() {
                            candidate_exprs.push((lhs, true));
                        } else if lhs.iter().any(is_verdict_rejection_token) && !rhs.is_empty() {
                            candidate_exprs.push((rhs, true));
                        }
                    }
                    LeanTokenKind::Symbol(s) if s == ".isOk" || s == ".isVerified" => {
                        let lhs = comparand_slice_before(slice, idx);
                        if !lhs.is_empty() {
                            candidate_exprs.push((lhs, true));
                        }
                    }
                    LeanTokenKind::Ident(id)
                        if id == "matches"
                            && slice.get(idx + 1).is_some_and(is_verdict_acceptance_token) =>
                    {
                        let lhs = comparand_slice_before(slice, idx);
                        if !lhs.is_empty() {
                            candidate_exprs.push((lhs, true));
                        }
                    }
                    LeanTokenKind::Ident(id)
                        if id.ends_with(".isOk") || id.ends_with(".isVerified") =>
                    {
                        let rhs = comparand_slice_after(slice, idx);
                        if !rhs.is_empty() {
                            candidate_exprs.push((rhs, true));
                        }
                    }
                    _ => {}
                }
            }

            for (expr, is_verdict) in candidate_exprs {
                let passes_ex_witness = expr.iter().any(|t| {
                    if let LeanTokenKind::Ident(id) = &t.kind {
                        let root = id.split('.').next().unwrap_or(id.as_str());
                        ex_vars.contains(id.as_str()) || ex_vars.contains(root)
                    } else {
                        false
                    }
                });
                if let Some(head_id) =
                    extract_call_head_ident(expr, &local_bound, &bound_check_heads)
                {
                    let head_short = head_id.rsplit('.').next().unwrap_or(head_id);
                    if bound_check_heads.contains(head_id)
                        || looks_like_operational_checker_ident(head_short)
                        || (is_verdict && passes_ex_witness)
                    {
                        culprit_fn = Some(if bound_check_heads.contains(head_id) {
                            head_id.to_string()
                        } else {
                            head_short.to_string()
                        });
                        break;
                    }
                }
            }
        }
        if culprit_fn.is_some() {
            break;
        }
    }

    if let Some(fn_name) = culprit_fn {
        findings.push(Finding {
            rule_id: "lean/judge-fragment-restates-check".to_string(),
            severity: if strict_vacuity {
                Severity::Error
            } else {
                Severity::Warning
            },
            artifact_kind: ArtifactKind::S,
            max_regime: Regime::Attested,
            sink: Some(Sink::Theater),
            path: file.rel_path.clone(),
            line: frag_field.line,
            column: frag_field.col,
            symbol: Some(format!("{}.Fragment", decl.fq_name)),
            message: format!(
                "`{}` defines `Fragment` via operational checker `{fn_name}` (`{}`), making `Judge.complete` a tautological projection instead of proving completeness over an independent input fragment",
                decl.fq_name,
                render_tokens_compact(&frag_field.rhs_tokens)
            ),
            remediation: format!(
                "Define `Fragment` as a purely semantic/syntactic input-domain predicate independent of `{fn_name}` (e.g. structural well-formedness or valid domain parameters), and prove in `complete` that an honest prover constructs an accepted certificate whenever `Meaning` holds."
            ),
        });
    }
}

fn is_crypto_pigeonhole_def_name(name: &str) -> bool {
    let short = name.rsplit('.').next().unwrap_or(name);
    let lower = short.to_ascii_lowercase();
    lower.contains("sishard")
        || lower.contains("msisassumption")
        || lower.contains("sisassumption")
        || lower.contains("collisionfree")
        || lower.contains("nocollision")
        || lower.contains("hashinjective")
        || lower.contains("digestinjective")
        || lower.contains("commitinjective")
        || lower.contains("ajtaiinjective")
}

fn name_is_intrinsically_crypto(short: &str) -> bool {
    let l = short.to_ascii_lowercase();
    l.contains("sis")
        || l.contains("hash")
        || l.contains("digest")
        || l.contains("commit")
        || l.contains("ajtai")
        || l.contains("merkle")
        || l.contains("cshake")
}

fn has_crypto_carrier(file: &ParsedLeanFile, tokens: &[LeanToken]) -> bool {
    let p = &file.rel_path;
    if p.contains("/Crypto/")
        || p.starts_with("Obend/Crypto/")
        || p.contains("/Trailblaze/")
        || p.starts_with("Obend/Trailblaze/")
        || p.contains("/Polis/")
        || p.starts_with("Obend/Polis/")
        || p.contains("/Vault/")
        || p.starts_with("Obend/Vault/")
        || p.contains("/Bridge/")
        || p.starts_with("Obend/Bridge/")
        || p.contains("/Judge/")
        || p.starts_with("Obend/Judge/")
    {
        return true;
    }
    tokens.iter().any(|t| {
        if let LeanTokenKind::Ident(id) = &t.kind {
            let l = id.to_ascii_lowercase();
            [
                "hash",
                "digest",
                "ajtai",
                "sis",
                "commit",
                "merkle",
                "verkle",
                "cshake",
                "keccak",
                "sha256",
                "sha3",
                "blake",
                "poseidon",
                "lattice",
                "preimage",
                "collision256",
            ]
            .iter()
            .any(|kw| l.contains(kw))
        } else {
            false
        }
    })
}

fn tokens_end_with_prop(type_tokens: &[LeanToken]) -> bool {
    let stripped = strip_outer_parens_tokens(type_tokens);
    stripped
        .last()
        .is_some_and(|t| matches!(&t.kind, LeanTokenKind::Ident(id) if id == "Prop"))
}

fn parse_small_nat_token(tok: &LeanToken) -> Option<u64> {
    if let LeanTokenKind::NatLit(s) = &tok.kind {
        let cleaned: String = s.chars().filter(|&c| c != '_').collect();
        if let Some(hex) = cleaned
            .strip_prefix("0x")
            .or_else(|| cleaned.strip_prefix("0X"))
        {
            u64::from_str_radix(hex, 16).ok()
        } else {
            cleaned.parse::<u64>().ok()
        }
    } else {
        None
    }
}

fn token_short_lower(tok: &LeanToken) -> Option<String> {
    if let LeanTokenKind::Ident(id) = &tok.kind {
        Some(
            id.rsplit('.')
                .next()
                .unwrap_or(id.as_str())
                .to_ascii_lowercase(),
        )
    } else {
        None
    }
}

/// Extract balanced application argument slices following `tokens[head_idx]`, stopping at
/// depth-0 logical/relational/structural delimiters.
fn extract_app_args(tokens: &[LeanToken], head_idx: usize) -> Vec<&[LeanToken]> {
    let mut args: Vec<&[LeanToken]> = Vec::new();
    let mut i = head_idx + 1;
    while i < tokens.len() {
        match &tokens[i].kind {
            LeanTokenKind::Symbol(s)
                if matches!(
                    s.as_str(),
                    "∧" | "∨"
                        | "→"
                        | "->"
                        | "↔"
                        | "="
                        | "=="
                        | "≠"
                        | "!="
                        | "≤"
                        | "<="
                        | "<"
                        | "≥"
                        | ">="
                        | ">"
                        | ","
                        | ";"
                        | ":="
                        | "|"
                        | ")"
                        | "]"
                        | "}"
                        | "⟩"
                ) =>
            {
                break;
            }
            LeanTokenKind::Ident(kw)
                if matches!(
                    kw.as_str(),
                    "where" | "by" | "with" | "then" | "else" | "in"
                ) =>
            {
                break;
            }
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{" | "⟨") => {
                let open = s.as_str();
                let close = match open {
                    "(" => ")",
                    "[" => "]",
                    "{" => "}",
                    _ => "⟩",
                };
                let start = i;
                let mut depth = 1usize;
                i += 1;
                while i < tokens.len() && depth > 0 {
                    match &tokens[i].kind {
                        LeanTokenKind::Symbol(o) if o == open => depth += 1,
                        LeanTokenKind::Symbol(c) if c == close => depth -= 1,
                        _ => {}
                    }
                    i += 1;
                }
                while i < tokens.len()
                    && matches!(&tokens[i].kind, LeanTokenKind::Symbol(p) if p.starts_with('.'))
                {
                    i += 1;
                }
                args.push(strip_outer_parens_tokens(&tokens[start..i]));
            }
            _ => {
                let start = i;
                i += 1;
                while i < tokens.len()
                    && matches!(&tokens[i].kind, LeanTokenKind::Symbol(p) if p.starts_with('.'))
                {
                    i += 1;
                }
                args.push(&tokens[start..i]);
            }
        }
    }
    args
}

fn is_safe_preimage_byte_bound_arg(arg: &[LeanToken]) -> bool {
    let core = strip_outer_parens_tokens(arg);
    if core.len() == 1
        && let Some(n) = parse_small_nat_token(&core[0])
    {
        return n <= 32;
    }
    if core.len() >= 2
        && matches!(&core[0].kind, LeanTokenKind::Ident(fn_id) if fn_id.ends_with("merkleMaxPreimageBytes"))
    {
        let inner = strip_outer_parens_tokens(&core[1..]);
        if inner.len() == 1
            && let Some(v) = parse_small_nat_token(&inner[0])
        {
            return v == 0;
        }
    }
    false
}

/// Returns `true` when `type_or_body_tokens` (excluding binder variable names!) carry an explicit
/// non-compressing dimension guard (`NonPigeonhole*`, relational `cols ≤ rows` / `rows ≥ cols`,
/// `maxBytes ≤ 32` / `32 ≥ maxBytes`) OR reference a distributional cryptographic game (`LazyRO`,
/// `MSISGame`, `GameSoundness`, `CRHFGame`, `EUFCMAGame`, etc.).
fn has_dimension_or_game_guard(tokens: &[LeanToken]) -> bool {
    let is_cols = |s: &str| matches!(s, "cols" | "numcols" | "inputbits" | "domainbits");
    let is_rows = |s: &str| matches!(s, "rows" | "numrows" | "outputbits" | "codomainbits");
    let is_maxbytes = |s: &str| s.contains("maxbytes") || s.contains("maxpreimage");

    for (idx, tok) in tokens.iter().enumerate() {
        if let LeanTokenKind::Ident(id) = &tok.kind {
            let short = id.rsplit('.').next().unwrap_or(id.as_str());
            let lower = short.to_ascii_lowercase();
            if lower.contains("nonpigeonhole")
                || lower.contains("noncompressing")
                || lower.contains("injectivedomain")
                || matches!(
                    short,
                    "LazyRO"
                        | "GameSoundness"
                        | "GameSecure"
                        | "KeyedGame"
                        | "FiniteGame"
                        | "MSISGame"
                        | "KeyedMSISGame"
                        | "SISGame"
                        | "CollisionGame"
                        | "CRHFGame"
                        | "EUFCMAGame"
                        | "Advantage"
                        | "AdvBound"
                        | "GameAdv"
                        | "RatSlack"
                )
            {
                return true;
            }
        }

        if let LeanTokenKind::Symbol(op) = &tok.kind {
            let prev_tok = idx.checked_sub(1).and_then(|k| tokens.get(k));
            let next_tok = tokens.get(idx + 1);
            let lhs_id = prev_tok.and_then(token_short_lower);
            let rhs_id = next_tok.and_then(token_short_lower);

            if matches!(op.as_str(), "≤" | "<=" | "<") {
                // Relational `cols ≤ rows` / `pp.cols ≤ pp.rows` (never `cols ≤ 10^9`!)
                if lhs_id.as_deref().is_some_and(is_cols) && rhs_id.as_deref().is_some_and(is_rows)
                {
                    return true;
                }
                // `maxBytes ≤ 32` or `maxBytes < 33`
                if lhs_id.as_deref().is_some_and(is_maxbytes)
                    && let Some(rt) = next_tok
                    && let Some(bound_val) = parse_small_nat_token(rt)
                {
                    let limit = if op == "<" { 33 } else { 32 };
                    if bound_val <= limit {
                        return true;
                    }
                }
            } else if matches!(op.as_str(), "≥" | ">=" | ">") {
                // Relational `rows ≥ cols` (never `pp.rows > 0`!)
                if lhs_id.as_deref().is_some_and(is_rows) && rhs_id.as_deref().is_some_and(is_cols)
                {
                    return true;
                }
                // Reversed `32 ≥ maxBytes` or `33 > maxBytes`
                if rhs_id.as_deref().is_some_and(is_maxbytes)
                    && let Some(lt) = prev_tok
                    && let Some(bound_val) = parse_small_nat_token(lt)
                {
                    let limit = if op == ">" { 33 } else { 32 };
                    if bound_val <= limit {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// Returns `true` when the return/conclusion type constructs a `Type`-valued `PSum` or `Except`
/// witness extractor (`0 Classical`). Checked strictly on conclusions so an unrelated `(h : Except ...)`
/// hypothesis never silences vacuous premises!
fn conclusion_returns_psum_or_except(concl_tokens: &[LeanToken]) -> bool {
    let core = strip_outer_parens_tokens(concl_tokens);
    core.first().is_some_and(|t| {
        if let LeanTokenKind::Ident(id) = &t.kind {
            let short = id.rsplit('.').next().unwrap_or(id.as_str());
            matches!(short, "PSum" | "Except")
        } else {
            false
        }
    })
}

fn has_negated_existential_hardness_shape(tokens: &[LeanToken], is_crypto_named: bool) -> bool {
    let mut has_forall = false;
    let mut has_arrow = false;

    for (idx, tok) in tokens.iter().enumerate() {
        match &tok.kind {
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "¬" | "≠" | "∄") => return true,
            LeanTokenKind::Symbol(s) if s == "∀" => has_forall = true,
            LeanTokenKind::Symbol(s) if s == "→" || s == "->" => has_arrow = true,
            LeanTokenKind::Symbol(s) if s == "=" => {
                // `= []` empty kernel/collision list assertion
                if tokens
                    .get(idx + 1)
                    .is_some_and(|t| matches!(&t.kind, LeanTokenKind::Symbol(b) if b == "["))
                    && tokens
                        .get(idx + 2)
                        .is_some_and(|t| matches!(&t.kind, LeanTokenKind::Symbol(b) if b == "]"))
                {
                    return true;
                }
            }
            LeanTokenKind::Ident(id) => {
                let short = id.rsplit('.').next().unwrap_or(id.as_str());
                if matches!(
                    short,
                    "Not"
                        | "False"
                        | "PEmpty"
                        | "Empty"
                        | "IsEmpty"
                        | "Subsingleton"
                        | "Injective"
                        | "InjOn"
                        | "Unbroken"
                ) {
                    return true;
                }
            }
            _ => {}
        }
    }
    is_crypto_named && has_forall && has_arrow
}

fn hyp_is_bool_equality_check(hyp: &[LeanToken]) -> bool {
    hyp.iter().enumerate().any(|(i, t)| {
        matches!(&t.kind, LeanTokenKind::Symbol(s) if s == "=" || s == "==")
            && (hyp.get(i + 1).is_some_and(|r| {
                matches!(&r.kind, LeanTokenKind::Ident(id) if matches!(id.as_str(), "true" | "false" | "Bool.true" | "Bool.false"))
            }) || i
                .checked_sub(1)
                .and_then(|k| hyp.get(k))
                .is_some_and(|l| {
                    matches!(&l.kind, LeanTokenKind::Ident(id) if matches!(id.as_str(), "true" | "false" | "Bool.true" | "Bool.false"))
                }))
    })
}

/// Count enclosing prefix negations (`¬`, `Not`) immediately governing `slice[idx]` across
/// opening parentheses `(`. Also returns `true` when `slice` ends with `→ False` / `-> False`
/// without an intervening negation around `idx`.
fn negation_polarity_at(slice: &[LeanToken], idx: usize) -> usize {
    let mut negs = 0usize;
    let mut k = idx;
    while k > 0 {
        let prev = &slice[k - 1];
        match &prev.kind {
            LeanTokenKind::Symbol(s) if s == "(" => {
                k -= 1;
            }
            LeanTokenKind::Symbol(s) if s == "¬" => {
                negs += 1;
                k -= 1;
            }
            LeanTokenKind::Ident(id)
                if id == "Not" || id == "IsEmpty" || id.ends_with(".IsEmpty") =>
            {
                negs += 1;
                k -= 1;
            }
            _ => break,
        }
    }
    // Check trailing `→ False` / `-> PEmpty` / `-> Empty`
    if slice.len() >= 2
        && idx + 2 <= slice.len()
        && matches!(
            &slice[slice.len() - 2].kind,
            LeanTokenKind::Symbol(s) if s == "→" || s == "->"
        )
        && matches!(
            &slice[slice.len() - 1].kind,
            LeanTokenKind::Ident(id) if matches!(id.as_str(), "False" | "PEmpty" | "Empty")
        )
    {
        negs += 1;
    }
    negs
}

/// Inspect a hypothesis slice for unguarded negated-existential / Pigeonhole-vacuous premises:
/// - `*SISHard*`, `*CollisionFree*`, `*NoCollision*`, `*HashInjective*`, or file-local flagged crypto defs
/// - `Unbroken ...`
/// - `Function.Injective H` / `IsEmpty (Collision ...)` in crypto context
/// - `¬ Collision ...` / `Collision ... → False` (odd negation polarity only — `¬ ¬ Collision` is positive!)
/// - `¬ BoundedCollision H maxBytes` where `maxBytes > 32`, `merkleMaxPreimageBytes ...`, or unguarded
fn find_vacuous_premise_in_hyp(
    hyp: &[LeanToken],
    crypto_ctx: bool,
    flagged_crypto_defs: &HashSet<String>,
) -> Option<String> {
    let is_bool_eq = hyp_is_bool_equality_check(hyp);

    for (idx, tok) in hyp.iter().enumerate() {
        if let LeanTokenKind::Ident(id) = &tok.kind {
            let short = id.rsplit('.').next().unwrap_or(id.as_str());
            let negs = negation_polarity_at(hyp, idx);
            let is_positive_polarity = negs.is_multiple_of(2);
            let is_negated_polarity = !is_positive_polarity;

            if is_positive_polarity
                && !is_bool_eq
                && (flagged_crypto_defs.contains(short)
                    || (is_crypto_pigeonhole_def_name(short)
                        && (crypto_ctx || name_is_intrinsically_crypto(short))))
            {
                return Some(format!(
                    "premise assumes deterministic hardness `{short}` without a `NonPigeonhole` / `cols ≤ rows` dimension guard or `PSum` / `LazyRO` / `MSISGame` reduction (vacuously `False` by Pigeonhole/Minkowski on compressing parameters)"
                ));
            }
            if is_positive_polarity && short == "Unbroken" {
                return Some(
                    "premise assumes set-theoretic `Unbroken` (`¬ Broken`) without a non-compressing domain bound or distributional game reduction (vacuously `False` by Pigeonhole on compressing hashes/lattices)".to_string(),
                );
            }
            if is_positive_polarity
                && crypto_ctx
                && (short == "Injective" || short == "InjOn")
                && extract_app_args(hyp, idx).iter().any(|arg| {
                    arg.iter().any(|at| {
                        matches!(&at.kind, LeanTokenKind::Ident(aid) if {
                            let al = aid.to_ascii_lowercase();
                            al == "h"
                                || al.starts_with("h.")
                                || al.contains("hash")
                                || al.contains("digest")
                                || al.contains("commit")
                                || al.contains("cshake")
                                || al.contains("ajtai")
                        })
                    })
                })
            {
                return Some(format!(
                    "premise assumes global `{id}` on a compressing hash/commitment (identically `False` by Pigeonhole)"
                ));
            }

            if is_negated_polarity {
                if short == "Collision" || short == "CshakeCollision" || short == "MsisBreak" {
                    return Some(format!(
                        "premise assumes unbounded `¬ {short}` on a compressing function (identically `False` by Pigeonhole since `256^33 > 2^256`)"
                    ));
                }
                if short == "BoundedCollision" {
                    let is_at = idx > 0
                        && matches!(&hyp[idx - 1].kind, LeanTokenKind::Symbol(s) if s == "@");
                    let args = extract_app_args(hyp, idx);
                    let bound_arg = if is_at {
                        args.get(2).or_else(|| args.last())
                    } else {
                        args.get(1)
                    };
                    if let Some(barg) = bound_arg
                        && is_safe_preimage_byte_bound_arg(barg)
                    {
                        continue;
                    }
                    return Some(
                        "premise assumes `¬ BoundedCollision` with preimage bound `> 32` bytes (or unguarded `maxBytes` / `merkleMaxPreimageBytes`), which is `False` by Pigeonhole for any 32-byte digest"
                            .to_string(),
                    );
                }
            }
        }
    }

    None
}

/// Inspect a `Theorem`'s conclusion for unkeyed `Prop`-only disjunctions (`P ∨ Collision H`,
/// `P ∨ CshakeCollision`, `P ∨ MsisBreak pp`, `P ∨ BoundedCollision H 529`, `P ∨ (... ∧ ¬ ModuleSISHard ...)`)
/// or unguarded implication conclusions (`¬ P → Collision H`) that are classically trivial by Pigeonhole.
fn find_vacuous_prop_collision_disjunction(
    concl: &[LeanToken],
    has_any_hyp: bool,
    premise_mentions_collision: bool,
    flagged_crypto_defs: &HashSet<String>,
) -> Option<String> {
    let core = strip_outer_parens_tokens(concl);
    let has_or = core.iter().any(|t| {
        matches!(&t.kind, LeanTokenKind::Symbol(s) if s == "∨")
            || matches!(&t.kind, LeanTokenKind::Ident(id) if id == "Or")
    });

    // Direct unguarded implication conclusion `... → Collision H` / `... → CshakeCollision` / `... → MsisBreak`
    // (skip premise-free toy-hash counterexamples like `theorem lengthHash_collides : Collision lengthHash`
    // and witness-forgetting projections like `CollisionPair.hashBytes_collision` / `HashCollisionWitness.toCollision`).
    if !has_or {
        if has_any_hyp
            && !premise_mentions_collision
            && let Some(LeanToken {
                kind: LeanTokenKind::Ident(head_id),
                ..
            }) = core.first()
        {
            let head_short = head_id.rsplit('.').next().unwrap_or(head_id.as_str());
            if matches!(head_short, "Collision" | "CshakeCollision" | "MsisBreak") {
                return Some(format!(
                    "conclusion derives unkeyed `Prop` existence `{head_short}` (unconditionally `True` in `Prop` by Pigeonhole on compressing inputs; extract a `Type`-valued witness via `PSum` instead)"
                ));
            }
        }
        return None;
    }

    for (idx, tok) in concl.iter().enumerate() {
        if let LeanTokenKind::Ident(id) = &tok.kind {
            let short = id.rsplit('.').next().unwrap_or(id.as_str());
            let negs = negation_polarity_at(concl, idx);
            if !negs.is_multiple_of(2) {
                // `P ∨ ¬ ModuleSISHard pp B`, `P ∨ Not (ModuleSISHard pp B)`, or `P ∨ ¬ Unbroken A`
                if short == "Unbroken"
                    || is_crypto_pigeonhole_def_name(short)
                    || flagged_crypto_defs.contains(short)
                {
                    return Some(format!(
                        "conclusion states a `Prop` disjunction `... ∨ ¬ {short} ...` (`¬ {short}` is unconditionally `True` on compressing parameters, making the disjunction vacuously `True`)"
                    ));
                }
                continue;
            }
            if short == "Collision" {
                return Some(
                    "conclusion states an unkeyed `Prop` disjunction `... ∨ Collision ...` (unbounded `Collision` on a 32-byte hash is unconditionally `True` in `Prop` by Pigeonhole, making `P ∨ Collision H` classically trivial)"
                        .to_string(),
                );
            }
            if short == "CshakeCollision" {
                return Some(
                    "conclusion states an unkeyed `Prop` disjunction `... ∨ CshakeCollision` (`CshakeCollision` over infinite `List UInt8` is unconditionally `True` in `Prop` by Pigeonhole)"
                        .to_string(),
                );
            }
            if short == "MsisBreak" {
                return Some(
                    "conclusion states an unkeyed `Prop` disjunction `... ∨ MsisBreak ...` (set-theoretically `True` in `Prop` on compressing lattice parameters without a `PSum` extractor or CRS game)"
                        .to_string(),
                );
            }
            if short == "BoundedCollision" {
                let is_at =
                    idx > 0 && matches!(&concl[idx - 1].kind, LeanTokenKind::Symbol(s) if s == "@");
                let args = extract_app_args(concl, idx);
                let bound_arg = if is_at {
                    args.get(2).or_else(|| args.last())
                } else {
                    args.get(1)
                };
                if let Some(barg) = bound_arg
                    && !is_safe_preimage_byte_bound_arg(barg)
                {
                    let rendered = render_tokens_compact(barg);
                    return Some(format!(
                        "conclusion states a `Prop` disjunction `... ∨ BoundedCollision _ {rendered}` (`> 32` bytes or unguarded preimage bound guarantees a collision exists in `Prop` by Pigeonhole)"
                    ));
                }
            }
        }
    }

    None
}

/// Pass 1 per Lean module: collect file-local vacuous `: Prop` cryptographic hardness definitions
/// (`Def`/`Abbrev`/`Structure`/`Class`) and emit findings on offending `variable (...)` declarations.
fn collect_flagged_crypto_defs_and_check_section_vars(
    file: &ParsedLeanFile,
    strict_vacuity: bool,
    findings: &mut Vec<Finding>,
) -> HashSet<String> {
    let mut flagged = HashSet::new();
    for decl in &file.declarations {
        if decl.fixture_kept {
            continue;
        }
        match decl.kind {
            DeclKind::Def | DeclKind::Abbrev => {
                let mut type_sig = Vec::new();
                for b in &decl.binders {
                    type_sig.extend(b.type_tokens.iter().cloned());
                }
                type_sig.extend(decl.type_tokens.iter().cloned());
                if has_dimension_or_game_guard(&type_sig)
                    || has_dimension_or_game_guard(&decl.body_tokens)
                {
                    continue;
                }
                let is_prop_or_unascribed =
                    tokens_end_with_prop(&decl.type_tokens) || decl.type_tokens.is_empty();
                if is_prop_or_unascribed {
                    let crypto_ctx = has_crypto_carrier(file, &type_sig)
                        || has_crypto_carrier(file, &decl.body_tokens);
                    let named_ok = decl.name == "Unbroken"
                        || (is_crypto_pigeonhole_def_name(&decl.name)
                            && (crypto_ctx || name_is_intrinsically_crypto(&decl.name)));
                    if named_ok
                        && (decl.name == "Unbroken"
                            || has_negated_existential_hardness_shape(&decl.body_tokens, true))
                    {
                        flagged.insert(decl.name.clone());
                    } else if decl.kind == DeclKind::Abbrev
                        && let Some(LeanToken {
                            kind: LeanTokenKind::Ident(rhs_id),
                            ..
                        }) = strip_outer_parens_tokens(&decl.body_tokens).first()
                    {
                        let rhs_short = rhs_id.rsplit('.').next().unwrap_or(rhs_id.as_str());
                        if rhs_short == "Unbroken"
                            || is_crypto_pigeonhole_def_name(rhs_short)
                            || flagged.contains(rhs_short)
                        {
                            flagged.insert(decl.name.clone());
                        }
                    }
                }
            }
            DeclKind::Structure | DeclKind::Class if is_crypto_pigeonhole_def_name(&decl.name) => {
                let mut all_field_tokens = Vec::new();
                for sf in &decl.struct_fields {
                    all_field_tokens.extend(sf.type_tokens.iter().cloned());
                }
                let crypto_ctx = has_crypto_carrier(file, &all_field_tokens)
                    || name_is_intrinsically_crypto(&decl.name);
                if crypto_ctx
                    && !has_dimension_or_game_guard(&all_field_tokens)
                    && has_negated_existential_hardness_shape(&all_field_tokens, true)
                {
                    flagged.insert(decl.name.clone());
                }
            }
            _ => {}
        }
    }

    // Check file-level `variable (hSIS : ModuleSISHard pp 131070)` assumptions
    let all_sv_types: Vec<LeanToken> = file
        .section_variables
        .iter()
        .flat_map(|sv| sv.type_tokens.iter().cloned())
        .collect();
    if !has_dimension_or_game_guard(&all_sv_types) {
        let severity = if strict_vacuity {
            Severity::Error
        } else {
            Severity::Warning
        };
        for sv in &file.section_variables {
            let sv_crypto = has_crypto_carrier(file, &sv.type_tokens);
            if let Some(why) = find_vacuous_premise_in_hyp(&sv.type_tokens, sv_crypto, &flagged) {
                findings.push(Finding {
                    rule_id: "lean/pigeonhole-vacuous-premise".to_string(),
                    severity,
                    artifact_kind: ArtifactKind::S,
                    max_regime: Regime::Attested,
                    sink: Some(Sink::Theater),
                    path: file.rel_path.clone(),
                    line: sv.line,
                    column: sv.col,
                    symbol: Some(sv.name.clone()),
                    message: format!("Section `variable ({})`: {why}", sv.name),
                    remediation: "Remove section-wide deterministic hardness assumptions (`ModuleSISHard`, `Unbroken`, `¬ BoundedCollision`) or guard them with an explicit `NonPigeonhole` / `cols ≤ rows` / `maxBytes ≤ 32` bound.".to_string(),
                });
            }
        }
    }

    flagged
}

fn check_hash_collision256_assumptions_in_decl(
    file: &ParsedLeanFile,
    decl: &ParsedLeanDecl,
    severity: Severity,
    findings: &mut Vec<Finding>,
) -> bool {
    // 1. `where` fields (`assumptions := .hashCollision256 H maxBytes`)
    for wf in &decl.where_fields {
        if wf.name == "assumptions" {
            for (idx, tok) in wf.rhs_tokens.iter().enumerate() {
                if matches!(&tok.kind, LeanTokenKind::Symbol(s) if s == ".hashCollision256")
                    || matches!(&tok.kind, LeanTokenKind::Ident(id) if id.ends_with("hashCollision256"))
                {
                    let args = extract_app_args(&wf.rhs_tokens, idx);
                    let bound_ok = args
                        .get(1)
                        .is_some_and(|barg| is_safe_preimage_byte_bound_arg(barg));
                    if !bound_ok {
                        findings.push(Finding {
                            rule_id: "lean/pigeonhole-vacuous-premise".to_string(),
                            severity,
                            artifact_kind: ArtifactKind::S,
                            max_regime: Regime::Attested,
                            sink: Some(Sink::Theater),
                            path: file.rel_path.clone(),
                            line: wf.line,
                            column: wf.col,
                            symbol: Some(format!("{}.assumptions", decl.fq_name)),
                            message: format!(
                                "`{}` sets `assumptions := {}` with preimage bound `> 32` bytes (or unguarded `maxBytes`), making `Unbroken J.assumptions` identically `False` by Pigeonhole on 32-byte digests",
                                decl.fq_name,
                                render_tokens_compact(&wf.rhs_tokens)
                            ),
                            remediation: "Wire `extractOrBreak` (`PSum`) to a keyed `CRHFGame` / `EUFCMAGame` / `LazyRO` advantage predicate instead of set-theoretic `.hashCollision256` with `maxBytes > 32`.".to_string(),
                        });
                        return true;
                    }
                }
            }
        }
    }

    // 2. Struct literal `{ ... assumptions := .hashCollision256 H maxBytes ... }` in `decl.body_tokens`
    if decl.where_fields.is_empty() {
        for (idx, tok) in decl.body_tokens.iter().enumerate() {
            if matches!(&tok.kind, LeanTokenKind::Ident(id) if id == "assumptions")
                && decl
                    .body_tokens
                    .get(idx + 1)
                    .is_some_and(|t| matches!(&t.kind, LeanTokenKind::Symbol(s) if s == ":="))
            {
                let rhs = &decl.body_tokens[idx + 2..];
                for (ridx, rtok) in rhs.iter().take(12).enumerate() {
                    if matches!(&rtok.kind, LeanTokenKind::Symbol(s) if s == ".hashCollision256")
                        || matches!(&rtok.kind, LeanTokenKind::Ident(id) if id.ends_with("hashCollision256"))
                    {
                        let args = extract_app_args(rhs, ridx);
                        let bound_ok = args
                            .get(1)
                            .is_some_and(|barg| is_safe_preimage_byte_bound_arg(barg));
                        if !bound_ok {
                            findings.push(Finding {
                                rule_id: "lean/pigeonhole-vacuous-premise".to_string(),
                                severity,
                                artifact_kind: ArtifactKind::S,
                                max_regime: Regime::Attested,
                                sink: Some(Sink::Theater),
                                path: file.rel_path.clone(),
                                line: tok.line,
                                column: tok.col,
                                symbol: Some(format!("{}.assumptions", decl.fq_name)),
                                message: format!(
                                    "`{}` sets `assumptions := .hashCollision256 ...` with preimage bound `> 32` bytes (or unguarded `maxBytes`), making `Unbroken J.assumptions` identically `False` by Pigeonhole on 32-byte digests",
                                    decl.fq_name
                                ),
                                remediation: "Wire `extractOrBreak` (`PSum`) to a keyed `CRHFGame` / `EUFCMAGame` / `LazyRO` advantage predicate instead of set-theoretic `.hashCollision256` with `maxBytes > 32`.".to_string(),
                            });
                            return true;
                        }
                    }
                }
            }
        }
    }

    false
}

/// 2026 Cryptographic Anti-Vacuity Rule (`lean/pigeonhole-vacuous-premise`):
/// Flags Pigeonhole-False cryptographic hardness definitions/premises (`*SISHard*`, `*CollisionFree*`,
/// `*NoCollision*`, `*HashInjective*`, `Unbroken`, `¬ BoundedCollision H maxBytes` for `maxBytes > 32`)
/// and unkeyed `Prop`-only `∨ Collision` / `∨ CshakeCollision` disjunctions unless guarded by an
/// explicit non-compressing domain bound (`NonPigeonhole`, `cols ≤ rows`, `maxBytes ≤ 32`) or expressed
/// via constructive `PSum`/`Except` witness extraction or `LazyRO`/`GameSoundness` advantage bounds.
fn check_pigeonhole_vacuous_premise(
    file: &ParsedLeanFile,
    decl: &ParsedLeanDecl,
    flagged_crypto_defs: &HashSet<String>,
    strict_vacuity: bool,
    findings: &mut Vec<Finding>,
) {
    let severity = if strict_vacuity {
        Severity::Error
    } else {
        Severity::Warning
    };

    // Collect referenced identifiers in `decl` so only active `section_variables` participate
    let mut decl_ref_idents: HashSet<&str> = HashSet::new();
    for b in &decl.binders {
        for t in &b.type_tokens {
            if let LeanTokenKind::Ident(id) = &t.kind {
                decl_ref_idents.insert(id.split('.').next().unwrap_or(id.as_str()));
            }
        }
    }
    for t in decl.type_tokens.iter().chain(decl.body_tokens.iter()) {
        if let LeanTokenKind::Ident(id) = &t.kind {
            decl_ref_idents.insert(id.split('.').next().unwrap_or(id.as_str()));
        }
    }

    // Gather type tokens ONLY (never binder names!) from referenced `section_variables`, `decl.binders`, and `decl.type_tokens`
    let mut sig_type_tokens: Vec<LeanToken> = Vec::new();
    for sv in &file.section_variables {
        if decl_ref_idents.contains(sv.name.as_str()) {
            sig_type_tokens.extend(sv.type_tokens.iter().cloned());
        }
    }
    for b in &decl.binders {
        sig_type_tokens.extend(b.type_tokens.iter().cloned());
    }
    sig_type_tokens.extend(decl.type_tokens.iter().cloned());

    if has_dimension_or_game_guard(&sig_type_tokens) {
        return;
    }

    let crypto_ctx =
        has_crypto_carrier(file, &sig_type_tokens) || has_crypto_carrier(file, &decl.body_tokens);

    // Check `assumptions := .hashCollision256 H maxBytes` across `Def`, `Abbrev`, and `Instance`
    if matches!(
        decl.kind,
        DeclKind::Def | DeclKind::Abbrev | DeclKind::Instance
    ) && check_hash_collision256_assumptions_in_decl(file, decl, severity, findings)
    {
        return;
    }

    match decl.kind {
        DeclKind::Def | DeclKind::Abbrev => {
            // 2A. Vacuous `: Prop` cryptographic hardness definitions (`ModuleSISHard`, `Unbroken`, `*CollisionFree*`, `*HashInjective*`)
            let is_prop_or_unascribed =
                tokens_end_with_prop(&decl.type_tokens) || decl.type_tokens.is_empty();
            if is_prop_or_unascribed
                && flagged_crypto_defs.contains(&decl.name)
                && !has_dimension_or_game_guard(&decl.body_tokens)
            {
                findings.push(Finding {
                    rule_id: "lean/pigeonhole-vacuous-premise".to_string(),
                    severity,
                    artifact_kind: ArtifactKind::S,
                    max_regime: Regime::Attested,
                    sink: Some(Sink::Theater),
                    path: file.rel_path.clone(),
                    line: decl.line,
                    column: decl.col,
                    symbol: Some(decl.fq_name.clone()),
                    message: format!(
                        "Cryptographic `Prop` predicate `{}` asserts negated-existential / universal non-existence hardness (`{}`) without a `NonPigeonhole` / `cols ≤ rows` / `maxBytes ≤ 32` guard or distributional game bound (mathematically `False` by Pigeonhole/Minkowski on compressing parameters)",
                        decl.fq_name,
                        render_tokens_compact(&decl.body_tokens)
                    ),
                    remediation: "Replace set-theoretic non-existence (`Unbroken` / `¬ ∃` / `= []`) with a constructive `PSum` witness extractor (`0 Classical`) paired with a keyed CRS / `LazyRO` / `MSISGame` advantage bound, or add an explicit `NonPigeonhole` dimension guard.".to_string(),
                });
                return;
            }

            // Also check binders, quantified binders, and arrow hypotheses on `Def` / `Abbrev`
            // (`def foo : ModuleSISHard pp B → Nat := ...`) unless returning `PSum`/`Except`
            let mut qbinders = Vec::new();
            let mut hyps = Vec::new();
            let concl = peel_forall_and_arrows(&decl.type_tokens, &mut qbinders, &mut hyps);
            if conclusion_returns_psum_or_except(concl) {
                return;
            }
            let mut def_premise: Option<(String, usize, usize)> = None;
            for b in &decl.binders {
                if let Some(why) =
                    find_vacuous_premise_in_hyp(&b.type_tokens, crypto_ctx, flagged_crypto_defs)
                {
                    def_premise = Some((why, b.line, b.col));
                    break;
                }
            }
            if def_premise.is_none() {
                for qb in &qbinders {
                    if let Some(why) = find_vacuous_premise_in_hyp(
                        &qb.type_tokens,
                        crypto_ctx,
                        flagged_crypto_defs,
                    ) {
                        let (ln, cl) = qb
                            .type_tokens
                            .first()
                            .map_or((decl.line, decl.col), |t| (t.line, t.col));
                        def_premise = Some((why, ln, cl));
                        break;
                    }
                }
            }
            if def_premise.is_none() {
                for h in &hyps {
                    if let Some(why) =
                        find_vacuous_premise_in_hyp(h, crypto_ctx, flagged_crypto_defs)
                    {
                        let (ln, cl) = h.first().map_or((decl.line, decl.col), |t| (t.line, t.col));
                        def_premise = Some((why, ln, cl));
                        break;
                    }
                }
            }
            if let Some((why, ln, cl)) = def_premise {
                findings.push(Finding {
                    rule_id: "lean/pigeonhole-vacuous-premise".to_string(),
                    severity,
                    artifact_kind: ArtifactKind::S,
                    max_regime: Regime::Attested,
                    sink: Some(Sink::Theater),
                    path: file.rel_path.clone(),
                    line: ln,
                    column: cl,
                    symbol: Some(decl.fq_name.clone()),
                    message: format!("Definition `{}`: {why}", decl.fq_name),
                    remediation: "Remove the Pigeonhole-False hypothesis or return a constructive `PSum` witness-extraction sum.".to_string(),
                });
            }
        }

        DeclKind::Structure | DeclKind::Class => {
            if flagged_crypto_defs.contains(&decl.name) {
                findings.push(Finding {
                    rule_id: "lean/pigeonhole-vacuous-premise".to_string(),
                    severity,
                    artifact_kind: ArtifactKind::S,
                    max_regime: Regime::Attested,
                    sink: Some(Sink::Theater),
                    path: file.rel_path.clone(),
                    line: decl.line,
                    column: decl.col,
                    symbol: Some(decl.fq_name.clone()),
                    message: format!(
                        "Cryptographic structure/class `{}` encodes negated-existential hardness without a `NonPigeonhole` / `cols ≤ rows` dimension guard or distributional game bound",
                        decl.fq_name
                    ),
                    remediation: "Formulate cryptographic hardness via a keyed game (`MSISGame` / `LazyRO`) or constructive `PSum` witness reduction, or include an explicit non-compressing dimension guard.".to_string(),
                });
                return;
            }

            // Check fields of both `Structure` and `Class` for vacuous premises or direct `ModuleSISHard` field types
            for sf in &decl.struct_fields {
                let mut f_sig: Vec<LeanToken> = Vec::new();
                for b in &sf.binders {
                    f_sig.extend(b.type_tokens.iter().cloned());
                }
                f_sig.extend(sf.type_tokens.iter().cloned());
                if has_dimension_or_game_guard(&f_sig) {
                    continue;
                }
                let f_crypto = crypto_ctx || has_crypto_carrier(file, &f_sig);
                let mut qbinders = Vec::new();
                let mut hyps = Vec::new();
                let concl = peel_forall_and_arrows(&sf.type_tokens, &mut qbinders, &mut hyps);
                if conclusion_returns_psum_or_except(concl) {
                    continue;
                }
                let mut reason: Option<String> = None;
                for b in &sf.binders {
                    if let Some(r) =
                        find_vacuous_premise_in_hyp(&b.type_tokens, f_crypto, flagged_crypto_defs)
                    {
                        reason = Some(r);
                        break;
                    }
                }
                if reason.is_none() {
                    for qb in &qbinders {
                        if let Some(r) = find_vacuous_premise_in_hyp(
                            &qb.type_tokens,
                            f_crypto,
                            flagged_crypto_defs,
                        ) {
                            reason = Some(r);
                            break;
                        }
                    }
                }
                if reason.is_none() {
                    for h in &hyps {
                        if let Some(r) =
                            find_vacuous_premise_in_hyp(h, f_crypto, flagged_crypto_defs)
                        {
                            reason = Some(r);
                            break;
                        }
                    }
                }
                // Direct field type `hard : ModuleSISHard pp B` or `noCol : ¬ BoundedCollision H 64`
                if reason.is_none() {
                    reason = find_vacuous_premise_in_hyp(concl, f_crypto, flagged_crypto_defs);
                }
                if let Some(why) = reason {
                    findings.push(Finding {
                        rule_id: "lean/pigeonhole-vacuous-premise".to_string(),
                        severity,
                        artifact_kind: ArtifactKind::S,
                        max_regime: Regime::Attested,
                        sink: Some(Sink::Theater),
                        path: file.rel_path.clone(),
                        line: sf.line,
                        column: sf.col,
                        symbol: Some(format!("{}.{}", decl.fq_name, sf.name)),
                        message: format!("Field `{}.{}`: {why}", decl.fq_name, sf.name),
                        remediation: "Replace negated-existential fields/premises (`ModuleSISHard`, `Unbroken`, `¬ BoundedCollision`) with a `0 Classical` `PSum` witness extractor or keyed `MSISGame` / `LazyRO` advantage bound.".to_string(),
                    });
                }
            }
        }

        DeclKind::Theorem | DeclKind::Instance | DeclKind::Axiom => {
            let mut qbinders = Vec::new();
            let mut hyps = Vec::new();
            let concl = peel_forall_and_arrows(&decl.type_tokens, &mut qbinders, &mut hyps);
            if conclusion_returns_psum_or_except(concl) {
                return;
            }

            let concl_head_is_unbroken = strip_outer_parens_tokens(concl)
                .first()
                .is_some_and(|t| matches!(&t.kind, LeanTokenKind::Ident(id) if id == "Unbroken"));

            // 2B. Hypotheses assuming Pigeonhole-False premises
            let mut premise_reason: Option<(String, usize, usize)> = None;
            for b in &decl.binders {
                if let Some(r) =
                    find_vacuous_premise_in_hyp(&b.type_tokens, crypto_ctx, flagged_crypto_defs)
                {
                    if concl_head_is_unbroken && r.contains("`Unbroken`") {
                        continue;
                    }
                    premise_reason = Some((r, b.line, b.col));
                    break;
                }
            }
            if premise_reason.is_none() {
                for qb in &qbinders {
                    if let Some(r) = find_vacuous_premise_in_hyp(
                        &qb.type_tokens,
                        crypto_ctx,
                        flagged_crypto_defs,
                    ) {
                        if concl_head_is_unbroken && r.contains("`Unbroken`") {
                            continue;
                        }
                        let (ln, cl) = qb
                            .type_tokens
                            .first()
                            .map(|t| (t.line, t.col))
                            .unwrap_or((decl.line, decl.col));
                        premise_reason = Some((r, ln, cl));
                        break;
                    }
                }
            }
            if premise_reason.is_none() {
                for h in &hyps {
                    if let Some(r) = find_vacuous_premise_in_hyp(h, crypto_ctx, flagged_crypto_defs)
                    {
                        if concl_head_is_unbroken && r.contains("`Unbroken`") {
                            continue;
                        }
                        let (ln, cl) = h
                            .first()
                            .map(|t| (t.line, t.col))
                            .unwrap_or((decl.line, decl.col));
                        premise_reason = Some((r, ln, cl));
                        break;
                    }
                }
            }
            if premise_reason.is_none()
                && decl.kind == DeclKind::Axiom
                && let Some(r) = find_vacuous_premise_in_hyp(concl, crypto_ctx, flagged_crypto_defs)
            {
                premise_reason = Some((r, decl.line, decl.col));
            }

            if let Some((why, ln, cl)) = premise_reason {
                let kind_label = match decl.kind {
                    DeclKind::Instance => "Instance",
                    DeclKind::Axiom => "Axiom",
                    _ => "Theorem",
                };
                findings.push(Finding {
                    rule_id: "lean/pigeonhole-vacuous-premise".to_string(),
                    severity,
                    artifact_kind: ArtifactKind::S,
                    max_regime: Regime::Attested,
                    sink: Some(Sink::Theater),
                    path: file.rel_path.clone(),
                    line: ln,
                    column: cl,
                    symbol: Some(decl.fq_name.clone()),
                    message: format!("{kind_label} `{}`: {why}", decl.fq_name),
                    remediation: "Remove the Pigeonhole-False hypothesis (`False → P` vacuity) and prove either a `Type`-valued `PSum` witness-extraction reduction (`0 Classical`) or a distributional `LazyRO` / `MSISGame` advantage bound.".to_string(),
                });
                return;
            }

            if decl.kind != DeclKind::Theorem || concl_head_is_unbroken {
                return;
            }

            let premise_mentions_collision = decl
                .binders
                .iter()
                .flat_map(|b| b.type_tokens.iter())
                .chain(qbinders.iter().flat_map(|b| b.type_tokens.iter()))
                .chain(hyps.iter().flat_map(|h| h.iter()))
                .any(|t| {
                    matches!(
                        &t.kind,
                        LeanTokenKind::Ident(id) if {
                            let s = id.rsplit('.').next().unwrap_or(id.as_str());
                            s.contains("Collision")
                                || s.contains("MsisBreak")
                                || s.contains("SISShortVec")
                        }
                    )
                });
            let has_any_hyp = !hyps.is_empty() || !decl.binders.is_empty() || !qbinders.is_empty();

            // 2C. Unkeyed `Prop`-only `∨ Collision H` / `∨ CshakeCollision` / `∨ MsisBreak` / `∨ ¬ ModuleSISHard` conclusions
            if let Some(or_why) = find_vacuous_prop_collision_disjunction(
                concl,
                has_any_hyp,
                premise_mentions_collision,
                flagged_crypto_defs,
            ) {
                let (ln, cl) = concl
                    .first()
                    .map(|t| (t.line, t.col))
                    .unwrap_or((decl.line, decl.col));
                findings.push(Finding {
                    rule_id: "lean/pigeonhole-vacuous-premise".to_string(),
                    severity,
                    artifact_kind: ArtifactKind::S,
                    max_regime: Regime::Attested,
                    sink: Some(Sink::Theater),
                    path: file.rel_path.clone(),
                    line: ln,
                    column: cl,
                    symbol: Some(decl.fq_name.clone()),
                    message: format!("Theorem `{}`: {or_why}", decl.fq_name),
                    remediation: "Promote `Prop`-level `∨ Collision` / `∨ CshakeCollision` to a constructive `Type`-valued `PSum` witness extractor (`ExactCollisionPair` / `HashCollisionWitness`) or finite-pair `CollisionAmong H (fun x => x = m₁ ∨ x = m₂)` lifted into a keyed CRHF / `LazyRO` game.".to_string(),
                });
            }
        }

        _ => {}
    }
}

fn is_judge_format_decl(decl: &ParsedLeanDecl) -> bool {
    if !matches!(decl.kind, DeclKind::Def | DeclKind::Abbrev) {
        return false;
    }
    decl.type_tokens.iter().any(|t| {
        matches!(
            &t.kind,
            LeanTokenKind::Ident(id)
                if id == "Judge.Format" || id == "Obend.Judge.Format" || id == "Format"
        )
    })
}

fn check_judge_meaning(
    file: &ParsedLeanFile,
    decl: &ParsedLeanDecl,
    decl_by_name: &HashMap<&str, &ParsedLeanDecl>,
    findings: &mut Vec<Finding>,
) {
    let Some(meaning_field) = decl.where_fields.iter().find(|f| f.name == "Meaning") else {
        return;
    };

    // Collect identifiers called by `check` field (and one hop into a helper def `checkFoo`)
    let mut check_callees: HashSet<String> = HashSet::new();
    if let Some(check_field) = decl.where_fields.iter().find(|f| f.name == "check") {
        for tok in &check_field.rhs_tokens {
            if let LeanTokenKind::Ident(id) = &tok.kind {
                let short = id.rsplit('.').next().unwrap_or(id);
                check_callees.insert(short.to_string());
                if let Some(helper) = decl_by_name.get(short) {
                    for htok in &helper.body_tokens {
                        if let LeanTokenKind::Ident(hid) = &htok.kind {
                            let hshort = hid.rsplit('.').next().unwrap_or(hid);
                            check_callees.insert(hshort.to_string());
                        }
                    }
                }
            }
        }
    }

    let rhs = &meaning_field.rhs_tokens;
    let compares_to_bool_or_ok = rhs.windows(2).any(|w| {
        let eq = matches!(&w[0].kind, LeanTokenKind::Symbol(s) if s == "=" || s == "==");
        let ok_rhs = matches!(
            &w[1].kind,
            LeanTokenKind::Ident(id)
                if id == "true"
                    || id == "Bool.true"
                    || id == "Except.ok"
                    || id == "Verdict.ok"
                    || id == "Judge.Verdict.ok"
        ) || matches!(&w[1].kind, LeanTokenKind::Symbol(s) if s == ".ok");
        eq && ok_rhs
    });

    if !compares_to_bool_or_ok {
        return;
    }

    // Find the checker function identifier inside `Meaning`'s RHS
    let mut tautological_fn: Option<String> = None;
    for tok in rhs {
        if let LeanTokenKind::Ident(id) = &tok.kind {
            let short = id.rsplit('.').next().unwrap_or(id);
            if matches!(
                short,
                "true" | "false" | "decide" | "Except.ok" | "Verdict.ok" | "Judge.Verdict.ok"
            ) {
                continue;
            }
            if meaning_field.params.iter().any(|p| p == short) {
                continue;
            }
            let looks_like_checker = short.starts_with("check")
                || short.starts_with("verify")
                || short.starts_with("validate")
                || short.ends_with("Check")
                || short.ends_with("Valid")
                || check_callees.contains(short);
            if looks_like_checker {
                tautological_fn = Some(short.to_string());
                break;
            }
        }
    }

    if let Some(fn_name) = tautological_fn {
        findings.push(Finding {
            rule_id: "lean/tautological-judge-meaning".to_string(),
            severity: Severity::Error,
            artifact_kind: ArtifactKind::S,
            max_regime: Regime::Attested,
            sink: Some(Sink::Label),
            path: file.rel_path.clone(),
            line: meaning_field.line,
            column: meaning_field.col,
            symbol: Some(format!("{}.Meaning", decl.fq_name)),
            message: format!(
                "`{}` defines `Meaning` as `{fn_name} ... = true/.ok` (tautologically restating its own executable checker)",
                decl.fq_name
            ),
            remediation: format!(
                "Define `Meaning` as an independent declarative `Prop` over the problem domain (e.g. trajectory enclosure, unsatisfiability, derivation) and prove `{fn_name}` implies it in `sound`."
            ),
        });
    }
}

fn check_wire_decoder_def(
    file: &ParsedLeanFile,
    decl: &ParsedLeanDecl,
    findings: &mut Vec<Finding>,
) {
    let str_param = decl.binders.first().map(|b| b.name.as_str()).unwrap_or("s");

    if let Some((lit, line, col)) = find_preset_string_branch(&decl.body_tokens, str_param) {
        findings.push(Finding {
            rule_id: "lean/hardcoded-wire-decoder".to_string(),
            severity: Severity::Error,
            artifact_kind: ArtifactKind::P,
            max_regime: Regime::Attested,
            sink: Some(Sink::Theater),
            path: file.rel_path.clone(),
            line,
            column: col,
            symbol: Some(decl.fq_name.clone()),
            message: format!(
                "Wire decoder `{}` branches on hardcoded preset string literal `\"{lit}\"` instead of parsing wire data",
                decl.fq_name
            ),
            remediation: "Remove preset string aliases (`\"good\"`, `\"bad\"`, `\"default\"`, etc.) from `Judge.Format` wire decoders; parse only canonical serialized wire representations.".to_string(),
        });
    }
}

fn find_preset_string_branch(
    tokens: &[LeanToken],
    param_name: &str,
) -> Option<(String, usize, usize)> {
    // Pattern A: `param == "preset"` or `param = "preset"`
    for w in tokens.windows(3) {
        let lhs_is_param = matches!(&w[0].kind, LeanTokenKind::Ident(id) if id == param_name);
        let is_eq = matches!(&w[1].kind, LeanTokenKind::Symbol(s) if s == "==" || s == "=");
        if lhs_is_param
            && is_eq
            && let LeanTokenKind::StrLit(lit) = &w[2].kind
            && !lit.is_empty()
        {
            return Some((lit.clone(), w[2].line, w[2].col));
        }
    }
    // Pattern B: `match param with | "preset" => ...`
    find_match_string_literal_arm(tokens)
}

fn find_match_string_literal_arm(tokens: &[LeanToken]) -> Option<(String, usize, usize)> {
    for w in tokens.windows(3) {
        let is_pipe = matches!(&w[0].kind, LeanTokenKind::Symbol(s) if s == "|");
        let is_arrow = matches!(&w[2].kind, LeanTokenKind::Symbol(s) if s == "=>");
        if is_pipe
            && is_arrow
            && let LeanTokenKind::StrLit(lit) = &w[1].kind
            && !lit.is_empty()
        {
            return Some((lit.clone(), w[1].line, w[1].col));
        }
    }
    None
}

fn render_tokens_compact(tokens: &[LeanToken]) -> String {
    let mut parts = Vec::new();
    for t in tokens.iter().take(16) {
        match &t.kind {
            LeanTokenKind::Ident(s) | LeanTokenKind::Symbol(s) | LeanTokenKind::NatLit(s) => {
                parts.push(s.as_str());
            }
            _ => {}
        }
    }
    parts.join(" ")
}

fn is_test_only_path(rel_path: &str) -> bool {
    rel_path.contains("/tests/")
        || rel_path.starts_with("tests/")
        || rel_path.starts_with("lean/tests/")
        || rel_path.ends_with("Test.lean")
        || rel_path.ends_with("Tests.lean")
}

/// 2026 Soundness Rule 1 (`lean/native-decide-in-proof`):
/// Flags `native_decide` or `Lean.ofReduceBool` / `Lean.ofReduceNat` / `Lean.trustCompiler`
/// inside library modules (`arXiv:2606.29493` compiler-trust bypass in kernel theorems).
fn check_native_decide_in_proof(
    file: &ParsedLeanFile,
    decl: &ParsedLeanDecl,
    is_teeth_or_test: bool,
    assert_compiled_set: &HashSet<&str>,
    findings: &mut Vec<Finding>,
) {
    if !matches!(
        decl.kind,
        DeclKind::Theorem
            | DeclKind::Def
            | DeclKind::Abbrev
            | DeclKind::Instance
            | DeclKind::Example
            | DeclKind::Opaque
    ) {
        return;
    }

    let is_audited_kat = assert_compiled_set.contains(decl.name.as_str())
        || assert_compiled_set.contains(decl.fq_name.as_str())
        || (is_teeth_or_test && decl.kind == DeclKind::Example);

    let mut slices: Vec<&[LeanToken]> = vec![&decl.type_tokens, &decl.body_tokens];
    for wf in &decl.where_fields {
        slices.push(&wf.rhs_tokens);
    }

    for slice in slices {
        let mut quote_depth = 0usize;
        let mut antiquote_depth = 0usize;
        let mut stack: Vec<u8> = Vec::new();

        for tok in slice {
            match &tok.kind {
                LeanTokenKind::SyntaxQuoteOpen => {
                    quote_depth += 1;
                    stack.push(1);
                }
                LeanTokenKind::AntiquoteOpen => {
                    antiquote_depth += 1;
                    stack.push(2);
                }
                LeanTokenKind::Symbol(s) if s == "(" => {
                    stack.push(0);
                }
                LeanTokenKind::Symbol(s) if s == ")" => match stack.pop() {
                    Some(1) => quote_depth = quote_depth.saturating_sub(1),
                    Some(2) => antiquote_depth = antiquote_depth.saturating_sub(1),
                    _ => {}
                },
                LeanTokenKind::Ident(id) if quote_depth == 0 || antiquote_depth > 0 => {
                    let is_reduce_axiom = matches!(
                        id.as_str(),
                        "Lean.ofReduceBool"
                            | "ofReduceBool"
                            | "Lean.ofReduceNat"
                            | "ofReduceNat"
                            | "Lean.trustCompiler"
                    );
                    let is_native_decide =
                        id == "native_decide" || id == "Lean.Elab.Tactic.evalNativeDecide";

                    if is_reduce_axiom || (is_native_decide && !is_audited_kat) {
                        findings.push(Finding {
                            rule_id: "lean/native-decide-in-proof".to_string(),
                            severity: Severity::Error,
                            artifact_kind: ArtifactKind::P,
                            max_regime: Regime::Certified,
                            sink: Some(Sink::Label),
                            path: file.rel_path.clone(),
                            line: tok.line,
                            column: tok.col,
                            symbol: Some(decl.fq_name.clone()),
                            message: format!(
                                "Declaration `{}` invokes `{id}` in a library module, bypassing the Lean kernel with unverified native code generation (`arXiv:2606.29493`)",
                                decl.fq_name
                            ),
                            remediation: "Replace `native_decide`/`Lean.ofReduceBool` with kernel-checked `decide`, `omega`, `simp`, or constructive proof terms (or move pure smoke tests under `tests/`).".to_string(),
                        });
                        return;
                    }
                }
                _ => {}
            }
        }
    }
}

fn has_explicit_narrow_width_suffix(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower.ends_with('8')
        || lower.ends_with("16")
        || lower.ends_with("32")
        || lower.ends_with("64")
        || lower.ends_with("tag")
        || lower.ends_with("seed")
        || lower.ends_with("salt")
        || lower.ends_with("idx")
        || lower.ends_with("index")
        || lower.ends_with("len")
        || lower.ends_with("length")
        || lower.ends_with("count")
        || lower.ends_with("offset")
        || lower.ends_with("word")
        || lower.ends_with("limb")
        || lower.ends_with("lane")
        || lower.ends_with("lo")
        || lower.ends_with("hi")
}

fn is_crypto_digest_type_name(name: &str) -> bool {
    let short = name.rsplit('.').next().unwrap_or(name);
    if has_explicit_narrow_width_suffix(short) {
        return false;
    }
    let lower = short.to_ascii_lowercase();
    lower == "digest"
        || lower.ends_with("digest")
        || lower == "hashdigest"
        || lower == "merkleroot"
        || lower.ends_with("merkleroot")
        || lower == "stateroot"
        || lower.ends_with("stateroot")
        || lower == "commitroot"
        || lower.ends_with("commitroot")
        || lower == "transcriptroot"
        || lower.ends_with("transcriptroot")
}

fn is_crypto_digest_field_name(name: &str) -> bool {
    let short = name.rsplit('.').next().unwrap_or(name);
    if has_explicit_narrow_width_suffix(short) {
        return false;
    }
    let lower = short.to_ascii_lowercase();
    if lower.starts_with("hashcons") || lower == "hash" {
        // Bare `hash : UInt64` is Lean's `Hashable.hash` non-crypto hash table method!
        return false;
    }
    lower == "digest"
        || lower.ends_with("digest")
        || lower == "merkleroot"
        || lower.ends_with("merkleroot")
        || lower == "stateroot"
        || lower.ends_with("stateroot")
        || lower == "commitroot"
        || lower.ends_with("commitroot")
        || lower == "transcriptroot"
        || lower.ends_with("transcriptroot")
        || lower == "txroot"
        || lower.ends_with("txroot")
        || lower == "iroot"
        || lower == "blockhash"
        || lower.ends_with("blockhash")
        || lower == "paymenthash"
        || lower.ends_with("paymenthash")
        || lower == "leafhash"
        || lower.ends_with("leafhash")
        || lower == "roothash"
        || lower.ends_with("roothash")
}

fn is_crypto_digest_var_name(raw: &str) -> bool {
    let seg = raw.rsplit('.').next().unwrap_or(raw);
    let clean = seg.trim_end_matches('\'');
    if has_explicit_narrow_width_suffix(clean) {
        return false;
    }
    let lower = clean.to_ascii_lowercase();
    lower == "digest"
        || lower.ends_with("digest")
        || lower.starts_with("digest")
        || lower == "hash"
        || lower.ends_with("hash")
        || lower == "merkleroot"
        || lower.ends_with("merkleroot")
        || lower == "stateroot"
        || lower.ends_with("stateroot")
        || lower == "commitroot"
        || lower.ends_with("commitroot")
        || lower == "transcriptroot"
        || lower.ends_with("transcriptroot")
        || lower == "newroot"
        || lower == "oldroot"
        || lower == "iroot"
        || (lower == "root" && raw.contains('.'))
}

fn is_scalar_narrow_word_type(tokens: &[LeanToken]) -> bool {
    if tokens.is_empty() {
        return false;
    }
    // Reject tuple/product or function or container types (`Array`, `List`, `Vector`, `×`, `→`)
    for tok in tokens {
        match &tok.kind {
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "×" | "→" | "->") => return false,
            LeanTokenKind::Ident(id)
                if matches!(
                    id.as_str(),
                    "Array" | "ByteArray" | "List" | "Vector" | "Subarray" | "Option"
                ) =>
            {
                return false;
            }
            _ => {}
        }
    }
    match &tokens[0].kind {
        LeanTokenKind::Ident(id)
            if matches!(
                id.as_str(),
                "UInt8"
                    | "UInt16"
                    | "UInt32"
                    | "UInt64"
                    | "USize"
                    | "Felt"
                    | "Goldilocks"
                    | "BabyBear"
                    | "KoalaBear"
                    | "Mersenne31"
            ) =>
        {
            tokens.len() == 1
        }
        LeanTokenKind::Ident(id) if id == "BitVec" && tokens.len() == 2 => {
            if let LeanTokenKind::NatLit(n_str) = &tokens[1].kind
                && let Ok(bits) = n_str.replace('_', "").parse::<u64>()
            {
                return bits <= 64;
            }
            false
        }
        _ => false,
    }
}

fn find_single_limb_digest_weld(tokens: &[LeanToken]) -> Option<(String, usize, usize)> {
    let has_eq = tokens.iter().any(|t| {
        matches!(&t.kind, LeanTokenKind::Symbol(s) if s == "=" || s == "==")
            || matches!(&t.kind, LeanTokenKind::Ident(id) if id == "beq" || id.ends_with(".beq"))
    });
    if !has_eq {
        return None;
    }

    // Check if nonzero limbs (`1`, `2`, `3`) are also accessed in the same declaration (multi-limb comparison)
    let mut accesses_higher_limb = false;
    for i in 0..tokens.len() {
        match &tokens[i].kind {
            // `[1]`, `[2]`, `[3]`
            LeanTokenKind::Symbol(s) if s == "[" => {
                if let Some(LeanToken {
                    kind: LeanTokenKind::NatLit(n),
                    ..
                }) = tokens.get(i + 1)
                    && matches!(n.as_str(), "1" | "2" | "3") {
                        accesses_higher_limb = true;
                    }
            }
            // `x.get! 1`, `x.newRoot 1`
            LeanTokenKind::Ident(id) => {
                if (id.ends_with(".get!")
                    || id.ends_with(".getD")
                    || id.ends_with(".get?")
                    || id.ends_with(".get")
                    || is_crypto_digest_var_name(id))
                    && tokens.get(i + 1).is_some_and(|t| {
                        matches!(&t.kind, LeanTokenKind::NatLit(n) if matches!(n.as_str(), "1" | "2" | "3"))
                    })
                {
                    accesses_higher_limb = true;
                }
                if id.ends_with(".snd") || id.ends_with(".2") {
                    accesses_higher_limb = true;
                }
            }
            LeanTokenKind::Symbol(s)
                if matches!(s.as_str(), ".get!" | ".getD" | ".get?" | ".get") =>
            {
                if tokens.get(i + 1).is_some_and(|t| {
                    matches!(&t.kind, LeanTokenKind::NatLit(n) if matches!(n.as_str(), "1" | "2" | "3"))
                }) {
                    accesses_higher_limb = true;
                }
            }
            LeanTokenKind::Symbol(s) if s == "."
                && tokens.get(i + 1).is_some_and(|t| {
                    matches!(&t.kind, LeanTokenKind::NatLit(n) if matches!(n.as_str(), "2" | "3" | "4"))
                }) => {
                    accesses_higher_limb = true;
                }
            _ => {}
        }
    }

    if accesses_higher_limb {
        return None;
    }

    for i in 0..tokens.len() {
        // Pattern 1: `digest[0]` / `digest[0]!`
        if let LeanTokenKind::Ident(id) = &tokens[i].kind
            && is_crypto_digest_var_name(id)
            && tokens
                .get(i + 1)
                .is_some_and(|t| matches!(&t.kind, LeanTokenKind::Symbol(s) if s == "["))
            && tokens
                .get(i + 2)
                .is_some_and(|t| matches!(&t.kind, LeanTokenKind::NatLit(n) if n == "0"))
            && tokens
                .get(i + 3)
                .is_some_and(|t| matches!(&t.kind, LeanTokenKind::Symbol(s) if s == "]"))
        {
            return Some((format!("{id}[0]"), tokens[i].line, tokens[i].col));
        }

        // Pattern 2: `digest.get! 0` / `digest.getD 0` / `digest.get? 0` / `digest.get 0`
        if let LeanTokenKind::Ident(id) = &tokens[i].kind
            && let Some((base, getter)) = id.rsplit_once('.')
            && matches!(getter, "get!" | "getD" | "get?" | "get")
            && is_crypto_digest_var_name(base)
            && tokens
                .get(i + 1)
                .is_some_and(|t| matches!(&t.kind, LeanTokenKind::NatLit(n) if n == "0"))
        {
            return Some((format!("{id} 0"), tokens[i].line, tokens[i].col));
        }

        // Pattern 3: `(hash ...).get! 0` or `(hash ...)[0]`
        if matches!(&tokens[i].kind, LeanTokenKind::Symbol(s) if s == ")") {
            let is_dot_get0 = tokens.get(i + 1).is_some_and(|t| {
                matches!(
                    &t.kind,
                    LeanTokenKind::Symbol(s)
                        if matches!(s.as_str(), ".get!" | ".getD" | ".get?" | ".get")
                )
            }) && tokens
                .get(i + 2)
                .is_some_and(|t| matches!(&t.kind, LeanTokenKind::NatLit(n) if n == "0"));

            let is_idx0 = tokens
                .get(i + 1)
                .is_some_and(|t| matches!(&t.kind, LeanTokenKind::Symbol(s) if s == "["))
                && tokens
                    .get(i + 2)
                    .is_some_and(|t| matches!(&t.kind, LeanTokenKind::NatLit(n) if n == "0"))
                && tokens
                    .get(i + 3)
                    .is_some_and(|t| matches!(&t.kind, LeanTokenKind::Symbol(s) if s == "]"));

            if is_dot_get0 || is_idx0 {
                // Find matching `(` and check if its head callee is a digest/hash function
                let mut d = 1usize;
                let mut k = i;
                while k > 0 && d > 0 {
                    k -= 1;
                    match &tokens[k].kind {
                        LeanTokenKind::Symbol(s) if s == ")" => d += 1,
                        LeanTokenKind::Symbol(s) if s == "(" => d -= 1,
                        _ => {}
                    }
                }
                if d == 0
                    && let Some(LeanToken {
                        kind: LeanTokenKind::Ident(callee),
                        line,
                        col,
                        ..
                    }) = tokens.get(k + 1)
                    && is_crypto_digest_var_name(callee)
                {
                    let suffix = if is_idx0 { "[0]" } else { ".get! 0" };
                    return Some((format!("({callee} ...){suffix}"), *line, *col));
                }
            }
        }

        // Pattern 4: `Array.get! digest 0` / `List.get! digest 0`
        if let LeanTokenKind::Ident(id) = &tokens[i].kind
            && matches!(
                id.as_str(),
                "Array.get!" | "Array.getD" | "List.get!" | "List.getD"
            )
            && let (
                Some(LeanToken {
                    kind: LeanTokenKind::Ident(arg),
                    ..
                }),
                Some(LeanToken {
                    kind: LeanTokenKind::NatLit(n),
                    ..
                }),
            ) = (tokens.get(i + 1), tokens.get(i + 2))
            && n == "0"
            && is_crypto_digest_var_name(arg)
        {
            return Some((format!("{id} {arg} 0"), tokens[i].line, tokens[i].col));
        }

        // Pattern 5: `DescriptorIR2` function-limb projection `(m.newRoot 0)` / `(m.root 0)` / `(m.iroot 0)`
        if let LeanTokenKind::Ident(id) = &tokens[i].kind
            && id.contains('.')
            && is_crypto_digest_var_name(id)
            && tokens
                .get(i + 1)
                .is_some_and(|t| matches!(&t.kind, LeanTokenKind::NatLit(n) if n == "0"))
        {
            return Some((format!("{id} 0"), tokens[i].line, tokens[i].col));
        }
    }

    None
}

/// 2026 Crypto-Landmine Rule 2 (`lean/narrow-digest-weld`):
/// Detects 1-limb / single-`UInt32`/`UInt64` / single-felt cryptographic digest or Merkle-root
/// stand-in types, fields, and lane-0 equality welds (`breadstuffs` 2^15.5-bit binding bug class).
fn check_narrow_digest_weld(
    file: &ParsedLeanFile,
    decl: &ParsedLeanDecl,
    findings: &mut Vec<Finding>,
) {
    // (a) Type alias (`abbrev Digest := UInt64`, `def MerkleRoot := UInt32`, etc.)
    if matches!(decl.kind, DeclKind::Abbrev | DeclKind::Def)
        && decl.binders.is_empty()
        && is_crypto_digest_type_name(&decl.name)
        && is_scalar_narrow_word_type(&decl.body_tokens)
    {
        findings.push(Finding {
            rule_id: "lean/narrow-digest-weld".to_string(),
            severity: Severity::Error,
            artifact_kind: ArtifactKind::S,
            max_regime: Regime::Attested,
            sink: Some(Sink::Theater),
            path: file.rel_path.clone(),
            line: decl.line,
            column: decl.col,
            symbol: Some(decl.fq_name.clone()),
            message: format!(
                "Cryptographic commitment/digest alias `{}` is defined as narrow scalar `{}` (<=64-bit collision resistance, birthday bound <=2^32)",
                decl.fq_name,
                render_tokens_compact(&decl.body_tokens)
            ),
            remediation: "Use a full >=256-bit commitment carrier (e.g. `ByteArray` of length 32, `Vector UInt64 4`, `Digest256`, or parameterize over `Obend.Digest.Hash` with explicit `Bounded H`).".to_string(),
        });
        return;
    }

    // (b) Narrow scalar `Digest` / `*Root` field on `structure` or `class`
    if matches!(decl.kind, DeclKind::Structure | DeclKind::Class) {
        for sf in &decl.struct_fields {
            if is_crypto_digest_field_name(&sf.name) && is_scalar_narrow_word_type(&sf.type_tokens)
            {
                findings.push(Finding {
                    rule_id: "lean/narrow-digest-weld".to_string(),
                    severity: Severity::Error,
                    artifact_kind: ArtifactKind::S,
                    max_regime: Regime::Attested,
                    sink: Some(Sink::Theater),
                    path: file.rel_path.clone(),
                    line: sf.line,
                    column: sf.col,
                    symbol: Some(format!("{}.{}", decl.fq_name, sf.name)),
                    message: format!(
                        "Field `{}.{}` stores cryptographic digest/root as narrow scalar `{}` (<=64-bit stand-in)",
                        decl.fq_name,
                        sf.name,
                        render_tokens_compact(&sf.type_tokens)
                    ),
                    remediation: "Widen digest/root field to full 256-bit width (`ByteArray`, 4x`UInt64`, or 8xGoldilocks/KoalaBear limbs) or rename with an explicit `*Tag64` width suffix if non-cryptographic.".to_string(),
                });
            }
        }
    }

    // (c) 1-limb / lane-0 digest equality weld (`digest[0] == ...`, `digest.get! 0 = ...`, `(m.newRoot 0) = ...`)
    let mut combined: Vec<LeanToken> = Vec::new();
    for b in &decl.binders {
        combined.extend(b.type_tokens.iter().cloned());
    }
    combined.extend(decl.type_tokens.iter().cloned());
    combined.extend(decl.body_tokens.iter().cloned());
    for wf in &decl.where_fields {
        combined.extend(wf.rhs_tokens.iter().cloned());
    }

    if let Some((expr_pat, line, col)) = find_single_limb_digest_weld(&combined) {
        findings.push(Finding {
            rule_id: "lean/narrow-digest-weld".to_string(),
            severity: Severity::Error,
            artifact_kind: ArtifactKind::P,
            max_regime: Regime::Attested,
            sink: Some(Sink::Theater),
            path: file.rel_path.clone(),
            line,
            column: col,
            symbol: Some(decl.fq_name.clone()),
            message: format!(
                "Declaration `{}` compares only limb 0 (`{expr_pat}`) of a cryptographic digest/root without binding the remaining limbs (`breadstuffs` 1-felt weld class)",
                decl.fq_name
            ),
            remediation: "Compare the entire 256-bit digest/root value (`d1 == d2` over all limbs/bytes) rather than truncating equality to lane 0.".to_string(),
        });
    }
}

/// Split `type_tokens` at top-level `→` / `->` arrows into `(antecedents, conclusion)`.
fn split_top_level_arrows(tokens: &[LeanToken]) -> (Vec<&[LeanToken]>, &[LeanToken]) {
    let mut antecedents = Vec::new();
    let mut depth = 0isize;
    let mut seg_start = 0usize;
    for (idx, tok) in tokens.iter().enumerate() {
        match &tok.kind {
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{" | "⟨") => depth += 1,
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}" | "⟩") => {
                depth = (depth - 1).max(0);
            }
            LeanTokenKind::Symbol(s) if (s == "→" || s == "->") && depth == 0 => {
                if seg_start < idx {
                    antecedents.push(&tokens[seg_start..idx]);
                }
                seg_start = idx + 1;
            }
            _ => {}
        }
    }
    (antecedents, &tokens[seg_start..])
}

fn decl_defines_prop_predicate(decl: &ParsedLeanDecl) -> bool {
    match decl.kind {
        DeclKind::Def | DeclKind::Abbrev | DeclKind::Inductive | DeclKind::Structure => {
            let (_, concl) = split_top_level_arrows(&decl.type_tokens);
            concl
                .last()
                .is_some_and(|t| matches!(&t.kind, LeanTokenKind::Ident(id) if id == "Prop"))
        }
        _ => false,
    }
}

/// Collect identifiers in `file` that have at least one positive satisfiability/inhabitedness
/// witness in the same module (`#guard`, `example`, `*_complete`, `*_sat`, `*_inhabited`,
/// `∃`, `Judge.complete`, or positive conclusion not resting on the same unproved premise).
fn collect_module_satisfiability_witnesses(
    file: &ParsedLeanFile,
    decl_by_name: &HashMap<&str, &ParsedLeanDecl>,
) -> HashSet<String> {
    let mut witnessed = HashSet::new();

    // 1. `#guard` / `#silicon_check` positive checks
    for (_, gtoks) in &file.guard_tokens {
        let negated_check = gtoks.windows(2).any(|w| {
            matches!(&w[0].kind, LeanTokenKind::Symbol(s) if s == "==" || s == "=")
                && (matches!(
                    &w[1].kind,
                    LeanTokenKind::Ident(id)
                        if matches!(id.as_str(), "false" | "Bool.false" | "none" | "Option.none")
                ) || matches!(&w[1].kind, LeanTokenKind::Symbol(s) if s == ".error" || s == ".refused"))
        }) || gtoks
            .first()
            .is_some_and(|t| matches!(&t.kind, LeanTokenKind::Symbol(s) if s == "!" || s == "¬"));

        if !negated_check {
            for tok in gtoks {
                if let LeanTokenKind::Ident(id) = &tok.kind {
                    witnessed.insert(id.clone());
                    if let Some(short) = id.rsplit('.').next() {
                        witnessed.insert(short.to_string());
                    }
                }
            }
        }
    }

    // 2. `Judge` instance `complete` fields and constructive `Example` / completeness / inhabitedness theorems
    for decl in &file.declarations {
        if is_judge_instance_decl(decl, decl_by_name)
            && decl.where_fields.iter().any(|wf| wf.name == "complete")
        {
            for wf in &decl.where_fields {
                if wf.name == "check" || wf.name == "Meaning" || wf.name == "complete" {
                    for tok in &wf.rhs_tokens {
                        if let LeanTokenKind::Ident(id) = &tok.kind {
                            let short = id.rsplit('.').next().unwrap_or(id);
                            witnessed.insert(short.to_string());
                        }
                    }
                }
            }
        }

        if matches!(
            decl.kind,
            DeclKind::Theorem | DeclKind::Example | DeclKind::Instance
        ) {
            let lower = decl.name.to_ascii_lowercase();
            if lower.ends_with("_sound")
                || lower.contains("refuse")
                || lower.contains("reject")
                || lower.contains("invalid")
                || lower.contains("not_")
            {
                continue;
            }

            let is_named_witness = decl.kind == DeclKind::Example
                || lower.ends_with("_complete")
                || lower.contains("_iff")
                || lower.contains("inhabited")
                || lower.ends_with("_sat")
                || lower.contains("satisfiable")
                || lower.contains("nonempty")
                || lower.contains("witness")
                || lower.ends_with("_accepted")
                || lower.contains("accepts")
                || lower.ends_with("_ok")
                || lower.ends_with("_valid")
                || lower.ends_with("_true");

            let (_, concl) = split_top_level_arrows(&decl.type_tokens);
            let concl_is_refusal = concl.windows(2).any(|w| {
                matches!(&w[0].kind, LeanTokenKind::Symbol(s) if s == "=" || s == "==")
                    && (matches!(
                        &w[1].kind,
                        LeanTokenKind::Ident(id)
                            if matches!(id.as_str(), "false" | "Bool.false" | "none" | "Option.none")
                    ) || matches!(
                        &w[1].kind,
                        LeanTokenKind::Symbol(s) if s == ".error" || s == ".refused"
                    ))
            }) || concl.iter().any(|t| {
                matches!(&t.kind, LeanTokenKind::Symbol(s) if s == "≠" || s == "!=")
                    || matches!(&t.kind, LeanTokenKind::Ident(id) if id == "False")
            }) || concl
                .first()
                .is_some_and(|t| matches!(&t.kind, LeanTokenKind::Symbol(s) if s == "¬"));

            if concl_is_refusal {
                continue;
            }

            let has_existential = decl.type_tokens.iter().any(|t| {
                matches!(&t.kind, LeanTokenKind::Symbol(s) if s == "∃")
                    || matches!(
                        &t.kind,
                        LeanTokenKind::Ident(id)
                            if matches!(id.as_str(), "Exists" | "Nonempty" | "Inhabited")
                    )
            });

            // Collect identifiers assumed in binders/antecedents so `P x → P y` doesn't self-witness `P`
            let mut assumed_idents = HashSet::new();
            let (ants, _) = split_top_level_arrows(&decl.type_tokens);
            for b in &decl.binders {
                for tok in &b.type_tokens {
                    if let LeanTokenKind::Ident(id) = &tok.kind {
                        assumed_idents.insert(id.rsplit('.').next().unwrap_or(id).to_string());
                    }
                }
            }
            for ant in ants {
                for tok in ant {
                    if let LeanTokenKind::Ident(id) = &tok.kind {
                        assumed_idents.insert(id.rsplit('.').next().unwrap_or(id).to_string());
                    }
                }
            }

            if is_named_witness || has_existential {
                for tok in &decl.type_tokens {
                    if let LeanTokenKind::Ident(id) = &tok.kind {
                        let short = id.rsplit('.').next().unwrap_or(id);
                        if !assumed_idents.contains(short) || lower.contains("_iff") {
                            witnessed.insert(short.to_string());
                        }
                    }
                }
            } else {
                // Any unconditional positive theorem conclusion (`f ... = .ok` / `P ...`) witnesses `f`/`P`
                for tok in concl {
                    if let LeanTokenKind::Ident(id) = &tok.kind {
                        let short = id.rsplit('.').next().unwrap_or(id);
                        if !assumed_idents.contains(short) {
                            witnessed.insert(short.to_string());
                        }
                    }
                }
            }
        }
    }

    witnessed
}

fn extract_premise_target(
    hyp_tokens: &[LeanToken],
    decl_by_name: &HashMap<&str, &ParsedLeanDecl>,
) -> Option<(String, String)> {
    if hyp_tokens.is_empty() {
        return None;
    }

    // Case A: Equality `f ... = .ok` / `= Verdict.ok` / `= Except.ok ...` / `= true` / `= some ...`
    for (idx, tok) in hyp_tokens.iter().enumerate() {
        if matches!(&tok.kind, LeanTokenKind::Symbol(s) if s == "=" || s == "==") {
            let rhs = &hyp_tokens[idx + 1..];
            let is_positive_verdict = rhs.first().is_some_and(|r| {
                matches!(&r.kind, LeanTokenKind::Symbol(s) if s == ".ok")
                    || matches!(
                        &r.kind,
                        LeanTokenKind::Ident(id)
                            if matches!(
                                id.as_str(),
                                "true"
                                    | "Bool.true"
                                    | "Verdict.ok"
                                    | "Judge.Verdict.ok"
                                    | "Obend.Judge.Verdict.ok"
                                    | "Except.ok"
                                    | "some"
                                    | "Option.some"
                            )
                    )
            });
            if is_positive_verdict {
                let lhs = &hyp_tokens[..idx];
                for ltok in lhs {
                    if let LeanTokenKind::Ident(id) = &ltok.kind {
                        let short = id.rsplit('.').next().unwrap_or(id);
                        if let Some(target_decl) = decl_by_name.get(short)
                            && matches!(target_decl.kind, DeclKind::Def | DeclKind::Abbrev)
                        {
                            return Some((short.to_string(), render_tokens_compact(hyp_tokens)));
                        }
                    }
                }
            }
        }
    }

    // Case B: Module-local custom `: Prop` predicate `P ...`
    for tok in hyp_tokens {
        if let LeanTokenKind::Ident(id) = &tok.kind {
            let short = id.rsplit('.').next().unwrap_or(id);
            if let Some(target_decl) = decl_by_name.get(short)
                && decl_defines_prop_predicate(target_decl)
            {
                return Some((short.to_string(), render_tokens_compact(hyp_tokens)));
            }
        }
    }

    None
}

/// 2026 Compositional Anti-Vacuity Rule 3 (`lean/uninhabited-premise-risk`):
/// Detects `theorem ..._sound` whose hypotheses assume `check x = .ok` / `= true` or a
/// module-local custom predicate with no companion satisfiability/inhabitedness witness in
/// the same module (`HypothesisLedger` tracking).
fn check_uninhabited_premise_risk(
    file: &ParsedLeanFile,
    decl: &ParsedLeanDecl,
    decl_by_name: &HashMap<&str, &ParsedLeanDecl>,
    module_witnessed_preds: &HashSet<String>,
    findings: &mut Vec<Finding>,
) {
    if !decl.name.ends_with("_sound") {
        return;
    }

    let mut candidate_hyps: Vec<(&[LeanToken], usize, usize)> = Vec::new();
    for b in &decl.binders {
        if !b.is_instance_bracket && !b.type_tokens.is_empty() {
            candidate_hyps.push((&b.type_tokens, b.line, b.col));
        }
    }
    let (ants, _) = split_top_level_arrows(&decl.type_tokens);
    for ant in ants {
        if let Some(first) = ant.first() {
            candidate_hyps.push((ant, first.line, first.col));
        }
    }

    let mut reported_targets = HashSet::new();
    for (hyp_toks, line, col) in candidate_hyps {
        if let Some((target_sym, rendered_hyp)) = extract_premise_target(hyp_toks, decl_by_name)
            && !module_witnessed_preds.contains(&target_sym)
            && reported_targets.insert(target_sym.clone())
        {
            findings.push(Finding {
                    rule_id: "lean/uninhabited-premise-risk".to_string(),
                    severity: Severity::Warning,
                    artifact_kind: ArtifactKind::S,
                    max_regime: Regime::Decided,
                    sink: Some(Sink::Theater),
                    path: file.rel_path.clone(),
                    line,
                    column: col,
                    symbol: Some(decl.fq_name.clone()),
                    message: format!(
                        "Soundness theorem `{}` rests on premise `{}` (`{target_sym}`), which has no companion satisfiability/inhabitedness witness in `{}` (`HypothesisLedger` anti-vacuity risk)",
                        decl.fq_name,
                        rendered_hyp,
                        file.rel_path
                    ),
                    remediation: format!(
                        "Add a constructive inhabitedness/completeness theorem (`∃ x, ...`, `*_complete`, `*_inhabited`), `example`, or `#guard` in `{}` proving `{target_sym}` is satisfiable on non-trivial inputs.",
                        file.rel_path
                    ),
                });
        }
    }
}

fn is_obligation_class_name(name: &str) -> bool {
    let short = name.rsplit('.').next().unwrap_or(name);
    short == "HypothesisLedger"
        || short.contains("HypothesisLedger")
        || short == "Ledger"
        || short.ends_with("Ledger")
        || short == "Obligations"
        || short.ends_with("Obligations")
}

fn extract_class_parents_for_lint(type_tokens: &[LeanToken]) -> Vec<String> {
    let mut parents = Vec::new();
    let mut after_extends = false;
    let mut depth = 0isize;
    let mut expect_head = false;
    for tok in type_tokens {
        match &tok.kind {
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{") => depth += 1,
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}") => {
                depth = (depth - 1).max(0);
            }
            LeanTokenKind::Ident(s) if depth == 0 && s == "extends" => {
                after_extends = true;
                expect_head = true;
            }
            LeanTokenKind::Symbol(s) if after_extends && depth == 0 && s == "," => {
                expect_head = true;
            }
            LeanTokenKind::Symbol(s) if after_extends && depth == 0 && s == ":" => break,
            LeanTokenKind::Ident(s) if after_extends && depth == 0 && s == "where" => break,
            LeanTokenKind::Ident(id) if after_extends && depth == 0 && expect_head => {
                parents.push(id.clone());
                expect_head = false;
            }
            _ => {}
        }
    }
    parents
}

fn collect_obligation_classes(
    index: &LeanIndex,
) -> (HashSet<String>, HashMap<String, Vec<String>>) {
    let mut classes = HashSet::new();
    let mut class_fields: HashMap<String, Vec<String>> = HashMap::new();
    let mut candidates: Vec<(&ParsedLeanDecl, Vec<String>)> = Vec::new();

    for file in &index.files {
        if is_test_only_path(&file.rel_path) {
            continue;
        }
        for decl in &file.declarations {
            if decl.kind != DeclKind::Class {
                continue;
            }
            let parents = extract_class_parents_for_lint(&decl.type_tokens);
            let has_attr = decl.attributes.iter().any(|a| a == "obb_obligation");
            let extends_named = parents.iter().any(|p| is_obligation_class_name(p));
            if is_obligation_class_name(&decl.name) || has_attr || extends_named {
                let fnames: Vec<String> =
                    decl.struct_fields.iter().map(|f| f.name.clone()).collect();
                classes.insert(decl.name.clone());
                classes.insert(decl.fq_name.clone());
                class_fields.insert(decl.name.clone(), fnames.clone());
                class_fields.insert(decl.fq_name.clone(), fnames);
            } else if !parents.is_empty() {
                candidates.push((decl, parents));
            }
        }
    }

    loop {
        let mut added = false;
        for (decl, parents) in &candidates {
            if classes.contains(&decl.fq_name) {
                continue;
            }
            let matched = parents.iter().any(|p| {
                let short = p.rsplit('.').next().unwrap_or(p.as_str());
                classes.contains(p.as_str()) || classes.contains(short)
            });
            if matched {
                let fnames: Vec<String> =
                    decl.struct_fields.iter().map(|f| f.name.clone()).collect();
                classes.insert(decl.name.clone());
                classes.insert(decl.fq_name.clone());
                class_fields.insert(decl.name.clone(), fnames.clone());
                class_fields.insert(decl.fq_name.clone(), fnames);
                added = true;
            }
        }
        if !added {
            break;
        }
    }

    (classes, class_fields)
}

fn instance_target_head_class(type_tokens: &[LeanToken]) -> Option<String> {
    let mut start = 0usize;
    let mut depth = 0isize;
    for (idx, tok) in type_tokens.iter().enumerate() {
        match &tok.kind {
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{") => depth += 1,
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}") => {
                depth = (depth - 1).max(0);
            }
            LeanTokenKind::Symbol(s) if (s == "→" || s == "->" || s == ",") && depth == 0 => {
                start = idx + 1;
            }
            _ => {}
        }
    }
    for tok in &type_tokens[start..] {
        match &tok.kind {
            LeanTokenKind::Ident(id)
                if matches!(id.as_str(), "∀" | "forall" | "outParam" | "semiOutParam") =>
            {
                continue;
            }
            LeanTokenKind::Ident(id) if id == "where" => break,
            LeanTokenKind::Symbol(s) if s == ":=" => break,
            LeanTokenKind::Ident(id) => return Some(id.clone()),
            _ => {}
        }
    }
    None
}

struct ExtractedInstanceField {
    name: Option<String>,
    params: Vec<String>,
    rhs_tokens: Vec<LeanToken>,
    line: usize,
    col: usize,
}

fn split_top_level_delim(tokens: &[LeanToken], delims: &[&str]) -> Vec<Vec<LeanToken>> {
    let mut out = Vec::new();
    let mut cur = Vec::new();
    let mut depth = 0isize;
    for tok in tokens {
        match &tok.kind {
            LeanTokenKind::Symbol(s) if depth == 0 && delims.contains(&s.as_str()) => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
                continue;
            }
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{" | "⟨") => {
                depth += 1;
            }
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}" | "⟩") => {
                depth = (depth - 1).max(0);
            }
            _ => {}
        }
        cur.push(tok.clone());
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

fn parse_field_assignment_chunk(chunk: &[LeanToken]) -> Option<ExtractedInstanceField> {
    if chunk.is_empty() {
        return None;
    }
    let mut depth = 0isize;
    let mut assign_idx = None;
    for (idx, tok) in chunk.iter().enumerate() {
        match &tok.kind {
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{" | "⟨") => {
                depth += 1;
            }
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}" | "⟩") => {
                depth = (depth - 1).max(0);
            }
            LeanTokenKind::Symbol(s) if s == ":=" && depth == 0 => {
                assign_idx = Some(idx);
                break;
            }
            _ => {}
        }
    }
    let a_idx = assign_idx?;
    let head_tok = chunk.first()?;
    let LeanTokenKind::Ident(fname) = &head_tok.kind else {
        return None;
    };
    let mut params = Vec::new();
    for t in &chunk[1..a_idx] {
        if let LeanTokenKind::Ident(p) = &t.kind {
            params.push(p.clone());
        }
    }
    let rhs = chunk[a_idx + 1..].to_vec();
    if rhs.is_empty() {
        return None;
    }
    Some(ExtractedInstanceField {
        name: Some(fname.clone()),
        params,
        rhs_tokens: rhs,
        line: head_tok.line,
        col: head_tok.col,
    })
}

fn extract_instance_fields(
    decl: &ParsedLeanDecl,
    class_field_names: Option<&Vec<String>>,
) -> Vec<ExtractedInstanceField> {
    if !decl.where_fields.is_empty() {
        return decl
            .where_fields
            .iter()
            .filter(|wf| !wf.rhs_tokens.is_empty())
            .map(|wf| ExtractedInstanceField {
                name: Some(wf.name.clone()),
                params: wf.params.clone(),
                rhs_tokens: wf.rhs_tokens.clone(),
                line: wf.line,
                col: wf.col,
            })
            .collect();
    }

    let body = &decl.body_tokens;
    if body.is_empty() {
        return Vec::new();
    }

    // Struct literal `{ f := ..., g := ... }` or struct update `{ base with f := ..., g := ... }`
    if matches!(&body.first().unwrap().kind, LeanTokenKind::Symbol(s) if s == "{")
        && matches!(&body.last().unwrap().kind, LeanTokenKind::Symbol(s) if s == "}")
        && body.len() >= 2
    {
        let mut inner = &body[1..body.len() - 1];
        let mut d = 0usize;
        for (idx, tok) in inner.iter().enumerate() {
            match &tok.kind {
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{" | "⟨") => d += 1,
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}" | "⟩") => {
                    d = d.saturating_sub(1);
                }
                LeanTokenKind::Ident(kw) if d == 0 && kw == "with" => {
                    inner = &inner[idx + 1..];
                    break;
                }
                LeanTokenKind::Symbol(s) if d == 0 && (s == ":=" || s == "," || s == ";") => {
                    break;
                }
                _ => {}
            }
        }
        let raw_chunks = split_top_level_delim(inner, &[",", ";"]);
        // Re-join comma-continuations (such as `∃ c, ...` or `∀ x, ...`) that do not start a new `field :=` assignment
        let mut merged_chunks: Vec<Vec<LeanToken>> = Vec::new();
        for ch in raw_chunks {
            if parse_field_assignment_chunk(&ch).is_some() || merged_chunks.is_empty() {
                merged_chunks.push(ch);
            } else if let Some(prev) = merged_chunks.last_mut() {
                let (ln, cl) = ch.first().map_or((1, 1), |t| (t.line, t.col));
                prev.push(LeanToken {
                    kind: LeanTokenKind::Symbol(",".to_string()),
                    line: ln,
                    col: cl,
                    first_on_line: false,
                });
                prev.extend(ch);
            }
        }
        let mut parsed = Vec::new();
        for ch in &merged_chunks {
            if let Some(f) = parse_field_assignment_chunk(ch) {
                parsed.push(f);
            }
        }
        if !parsed.is_empty() {
            return parsed;
        }
    }

    // Anonymous constructor `⟨e1, e2, ...⟩`
    if matches!(&body.first().unwrap().kind, LeanTokenKind::Symbol(s) if s == "⟨")
        && matches!(&body.last().unwrap().kind, LeanTokenKind::Symbol(s) if s == "⟩")
        && body.len() >= 2
    {
        let inner = &body[1..body.len() - 1];
        let chunks = split_top_level_delim(inner, &[","]);
        return chunks
            .into_iter()
            .enumerate()
            .filter(|(_, ch)| !ch.is_empty())
            .map(|(i, ch)| {
                let first = &ch[0];
                let fname = class_field_names.and_then(|v| v.get(i).cloned());
                ExtractedInstanceField {
                    name: fname,
                    params: Vec::new(),
                    line: first.line,
                    col: first.col,
                    rhs_tokens: ch,
                }
            })
            .collect();
    }

    // Inline `where f := ...; g := ...`
    let semi_chunks = split_top_level_delim(body, &[";"]);
    let mut inline_fields = Vec::new();
    for ch in &semi_chunks {
        if let Some(f) = parse_field_assignment_chunk(ch) {
            inline_fields.push(f);
        }
    }
    if !inline_fields.is_empty() {
        return inline_fields;
    }

    let first = &body[0];
    vec![ExtractedInstanceField {
        name: class_field_names.and_then(|v| v.first().cloned()),
        params: Vec::new(),
        rhs_tokens: body.clone(),
        line: first.line,
        col: first.col,
    }]
}

/// Strip leading `fun x y =>` / `λ x y =>` binders and collect introduced parameter names.
fn strip_leading_lambdas<'a>(
    tokens: &'a [LeanToken],
    bound_params: &mut HashSet<String>,
) -> &'a [LeanToken] {
    let mut slice = tokens;
    loop {
        let is_fun = slice.first().is_some_and(|t| {
            matches!(&t.kind, LeanTokenKind::Ident(s) if s == "fun" || s == "λ")
                || matches!(&t.kind, LeanTokenKind::Symbol(s) if s == "λ")
        });
        if !is_fun {
            break;
        }
        let mut depth = 0isize;
        let mut arrow_pos = None;
        for (idx, tok) in slice.iter().enumerate().skip(1) {
            match &tok.kind {
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{") => depth += 1,
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}") => {
                    depth = (depth - 1).max(0);
                }
                LeanTokenKind::Symbol(s) if (s == "=>" || s == "↦") && depth == 0 => {
                    arrow_pos = Some(idx);
                    break;
                }
                _ => {}
            }
        }
        let Some(ap) = arrow_pos else {
            break;
        };
        // Collect bound identifiers before `:` inside binder groups or bare identifiers
        let mut i = 1usize;
        while i < ap {
            match &slice[i].kind {
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{") => {
                    let open = s.as_str();
                    let close = match open {
                        "(" => ")",
                        "[" => "]",
                        _ => "}",
                    };
                    let mut d = 1usize;
                    i += 1;
                    let mut seen_colon = false;
                    while i < ap && d > 0 {
                        match &slice[i].kind {
                            LeanTokenKind::Symbol(o) if o == open => d += 1,
                            LeanTokenKind::Symbol(c) if c == close => d -= 1,
                            LeanTokenKind::Symbol(col) if col == ":" && d == 1 => {
                                seen_colon = true;
                            }
                            LeanTokenKind::Ident(id) if d == 1 && !seen_colon && id != "_" => {
                                bound_params.insert(id.clone());
                            }
                            _ => {}
                        }
                        i += 1;
                    }
                    continue;
                }
                LeanTokenKind::Ident(id) if id != "_" => {
                    bound_params.insert(id.clone());
                }
                _ => {}
            }
            i += 1;
        }
        if ap + 1 >= slice.len() {
            break;
        }
        slice = &slice[ap + 1..];
    }
    slice
}

/// Strip leading `by`, `intro ...;`, `intros ...;`, `exact` so tactic-wrapped 1–3 line cosplay
/// is inspected on equal footing with term-mode cosplay.
fn strip_leading_trivial_tactics<'a>(
    tokens: &'a [LeanToken],
    bound_params: &mut HashSet<String>,
) -> &'a [LeanToken] {
    let mut slice = tokens;
    if slice
        .first()
        .is_some_and(|t| matches!(&t.kind, LeanTokenKind::Ident(s) if s == "by"))
    {
        slice = &slice[1..];
    }
    while let Some(first) = slice.first() {
        match &first.kind {
            LeanTokenKind::Ident(s) if s == "intro" || s == "intros" => {
                let intro_line = first.line;
                let mut i = 1usize;
                while i < slice.len() {
                    if matches!(&slice[i].kind, LeanTokenKind::Symbol(sym) if sym == ";") {
                        i += 1;
                        break;
                    }
                    if slice[i].first_on_line && slice[i].line > intro_line {
                        break;
                    }
                    if let LeanTokenKind::Ident(id) = &slice[i].kind
                        && id != "_"
                    {
                        bound_params.insert(id.clone());
                    }
                    i += 1;
                }
                slice = &slice[i..];
            }
            LeanTokenKind::Ident(s) if s == "exact" || s == "apply" => {
                slice = &slice[1..];
            }
            LeanTokenKind::Symbol(s) if s == ";" => {
                slice = &slice[1..];
            }
            _ => break,
        }
    }
    slice
}

fn classify_obligation_field_cosplay(
    field_name: Option<&str>,
    rhs_tokens: &[LeanToken],
    initial_bound: &HashSet<String>,
) -> Option<&'static str> {
    if rhs_tokens.is_empty() {
        return None;
    }
    let first_line = rhs_tokens.first()?.line;
    let last_line = rhs_tokens.last()?.line;
    let line_span = last_line.saturating_sub(first_line) + 1;
    if line_span > 3 {
        return None;
    }

    let mut bound = initial_bound.clone();
    let after_lam = strip_leading_lambdas(rhs_tokens, &mut bound);
    let core = strip_leading_trivial_tactics(after_lam, &mut bound);
    let core = strip_leading_lambdas(core, &mut bound);
    if core.is_empty() {
        return None;
    }

    // 1. Vacuous `False` predicate (`Fragment := fun _ => False` or `:= False`)
    if core.len() == 1
        && let LeanTokenKind::Ident(id) = &core[0].kind
    {
        let short = id.rsplit('.').next().unwrap_or(id.as_str());
        if short == "False" {
            return Some("vacuous `False` predicate (`fun _ => False`)");
        }
        if matches!(short, "false")
            && !std::ptr::eq(after_lam, rhs_tokens)
            && field_name.is_some_and(|n| {
                let l = n.to_ascii_lowercase();
                l.contains("fragment")
                    || l.contains("valid")
                    || l.contains("supported")
                    || l.contains("pred")
            })
        {
            return Some("vacuous `false` fragment predicate (`fun _ => false`)");
        }
    }

    // 2. Trivial `True` witness (`fun _ => trivial`, `trivial`, `True.intro`)
    if core.iter().all(|t| match &t.kind {
        LeanTokenKind::Ident(id) => matches!(id.as_str(), "trivial" | "True.intro"),
        LeanTokenKind::Symbol(s) => matches!(s.as_str(), "(" | ")" | "⟨" | "⟩"),
        _ => false,
    }) && core.iter().any(|t| {
        matches!(&t.kind, LeanTokenKind::Ident(id) if matches!(id.as_str(), "trivial" | "True.intro"))
    }) {
        return Some("trivial `True` witness (`fun _ => trivial` / `True.intro`)");
    }

    // 3. 1–3 line definitional reflexivity cosplay (`rfl`, `Eq.refl`, `Eq.rfl`, `Iff.rfl`, `HEq.rfl`)
    let is_refl_ident = |id: &str| {
        matches!(
            id,
            "rfl" | "Eq.refl" | "Eq.rfl" | "Iff.rfl" | "Iff.refl" | "HEq.rfl" | "HEq.refl"
        )
    };
    let has_refl = core
        .iter()
        .any(|t| matches!(&t.kind, LeanTokenKind::Ident(id) if is_refl_ident(id)));
    if has_refl {
        let only_refl_and_args = core.iter().all(|t| match &t.kind {
            LeanTokenKind::Ident(id) => {
                if is_refl_ident(id) || id == "_" {
                    true
                } else {
                    let root = id.split('.').next().unwrap_or(id.as_str());
                    bound.contains(id.as_str()) || bound.contains(root)
                }
            }
            LeanTokenKind::Symbol(_) => true,
            _ => false,
        });
        if only_refl_and_args {
            return Some("1–3 line reflexivity cosplay (`rfl` / `Eq.refl`)");
        }
    }

    // Helper: detect substantive domain theorem calls (anything outside bound vars, projections, and shallow rewriting tactics)
    let is_shallow_helper_or_tactic = |id: &str| -> bool {
        matches!(
            id,
            "_" | "by"
                | "intro"
                | "intros"
                | "exact"
                | "apply"
                | "rw"
                | "simp"
                | "simpa"
                | "dsimp"
                | "unfold"
                | "at"
                | "using"
                | "only"
                | "fun"
                | "congr"
                | "congrArg"
                | "congrFun"
                | "congrArg₂"
                | "Bool.and_eq_true"
                | "Bool.and_eq_true_iff"
                | "and_eq_true"
                | "And.left"
                | "And.right"
                | "Prod.fst"
                | "Prod.snd"
                | "PProd.fst"
                | "PProd.snd"
                | "Subtype.property"
                | "Subtype.val"
                | "Iff.mp"
                | "Iff.mpr"
                | "Eq.mp"
                | "Eq.mpr"
                | "Eq.symm"
                | "Eq.trans"
                | "id"
        )
    };
    let is_domain_theorem_ident = |id: &str| -> bool {
        let short = id.rsplit('.').next().unwrap_or(id);
        let lower = short.to_ascii_lowercase();
        lower.ends_with("_sound")
            || lower.ends_with("_complete")
            || lower.ends_with("_correct")
            || lower.ends_with("_verified")
            || lower.ends_with("_injective")
            || lower.ends_with("_binding")
            || lower.ends_with("_preserves")
            || id == "induction"
            || id == "omega"
    };

    // 4. 1–3 line `congrArg` / `congrFun` / `congr` determinism cosplay
    let has_congr = core.iter().any(|t| {
        matches!(
            &t.kind,
            LeanTokenKind::Ident(id)
                if matches!(id.as_str(), "congrArg" | "congrFun" | "congrArg₂" | "congr")
        )
    });
    if has_congr
        && !core
            .iter()
            .any(|t| matches!(&t.kind, LeanTokenKind::Ident(id) if is_domain_theorem_ident(id)))
    {
        return Some("1–3 line `congrArg`/`congr` determinism cosplay");
    }

    // 5. 1–3 line `Bool.and_eq_true` boolean-arm unpacking cosplay
    let has_bool_and_unpack = rhs_tokens.iter().any(|t| {
        matches!(&t.kind, LeanTokenKind::Ident(id) if id == "Bool.and_eq_true"
            || id == "Bool.and_eq_true_iff"
            || id.starts_with("Bool.and_eq_true."))
    });
    if has_bool_and_unpack
        && !core
            .iter()
            .any(|t| matches!(&t.kind, LeanTokenKind::Ident(id) if is_domain_theorem_ident(id)))
    {
        return Some("1–3 line `Bool.and_eq_true` boolean-conjunction projection cosplay");
    }

    // 6. 1–3 line `And.left` / `And.right` / `.left` / `.right` / `.1` / `.2` / `Prod.fst` / `Prod.snd` projection cosplay
    let mut has_proj_op = false;
    let mut has_external_call = false;
    for (idx, tok) in core.iter().enumerate() {
        match &tok.kind {
            LeanTokenKind::Ident(id) => {
                if matches!(
                    id.as_str(),
                    "And.left" | "And.right" | "Prod.fst" | "Prod.snd" | "PProd.fst" | "PProd.snd"
                ) || id.ends_with(".left")
                    || id.ends_with(".right")
                    || id.ends_with(".fst")
                    || id.ends_with(".snd")
                {
                    has_proj_op = true;
                }
                let root = id.split('.').next().unwrap_or(id.as_str());
                if !bound.contains(id.as_str())
                    && !bound.contains(root)
                    && !is_shallow_helper_or_tactic(id.as_str())
                {
                    // Note: `(expr).mp` where `id` is `Bool.and_eq_true.mp` already handled above;
                    // any other unbound identifier is an external lemma/theorem call!
                    has_external_call = true;
                }
            }
            LeanTokenKind::Symbol(s)
                if matches!(s.as_str(), ".left" | ".right" | ".fst" | ".snd") =>
            {
                has_proj_op = true;
            }
            LeanTokenKind::Symbol(s) if s == "." => {
                if let Some(LeanToken {
                    kind: LeanTokenKind::NatLit(n),
                    ..
                }) = core.get(idx + 1)
                    && (n == "1" || n == "2")
                {
                    has_proj_op = true;
                }
            }
            _ => {}
        }
    }

    if has_proj_op && !has_external_call {
        return Some("1–3 line `And.left`/`And.right` projection cosplay");
    }

    None
}

/// 2026 Obligation Instance Anti-Cosplay Rule (`lean/obligation-projection-cosplay`):
/// Flags `instance ... *Obligations` or `HypothesisLedger` (or `@[obb_obligation]` / `extends HypothesisLedger`)
/// fields whose bodies are 1–3 line projection/determinism/vacuity cosplay (`rfl`, `congrArg`,
/// `Bool.and_eq_true`, `And.left`/`And.right`, `fun _ => trivial`, `Fragment := fun _ => False`).
fn check_obligation_projection_cosplay(
    file: &ParsedLeanFile,
    decl: &ParsedLeanDecl,
    obligation_classes: &HashSet<String>,
    obligation_class_fields: &HashMap<String, Vec<String>>,
    findings: &mut Vec<Finding>,
) {
    let Some(target_head) = instance_target_head_class(&decl.type_tokens) else {
        return;
    };
    let short_head = target_head
        .rsplit('.')
        .next()
        .unwrap_or(target_head.as_str());
    let is_obl_instance = obligation_classes.contains(&target_head)
        || obligation_classes.contains(short_head)
        || is_obligation_class_name(&target_head)
        || decl.attributes.iter().any(|a| a == "obb_obligation");
    if !is_obl_instance {
        return;
    }

    let class_fnames = obligation_class_fields
        .get(&target_head)
        .or_else(|| obligation_class_fields.get(short_head));
    let extracted_fields = extract_instance_fields(decl, class_fnames);

    let mut base_bound: HashSet<String> = HashSet::new();
    for sv in &file.section_variables {
        if !sv.is_underscore && sv.name != "_" {
            base_bound.insert(sv.name.clone());
        }
    }
    for b in &decl.binders {
        if !b.is_underscore && b.name != "_" {
            base_bound.insert(b.name.clone());
        }
    }

    for ef in extracted_fields {
        let mut field_bound = base_bound.clone();
        for p in &ef.params {
            if p != "_" {
                field_bound.insert(p.clone());
            }
        }
        if let Some(reason) =
            classify_obligation_field_cosplay(ef.name.as_deref(), &ef.rhs_tokens, &field_bound)
        {
            let field_label = ef.name.as_deref().unwrap_or("<body_witness>");
            findings.push(Finding {
                rule_id: "lean/obligation-projection-cosplay".to_string(),
                severity: Severity::Error,
                artifact_kind: ArtifactKind::P,
                max_regime: Regime::Attested,
                sink: Some(Sink::Theater),
                path: file.rel_path.clone(),
                line: ef.line,
                column: ef.col,
                symbol: Some(format!("{}.{}", decl.fq_name, field_label)),
                message: format!(
                    "Obligation instance `{}` (`{target_head}`) discharges field `{field_label}` via {reason} (`{}`)",
                    decl.fq_name,
                    render_tokens_compact(&ef.rhs_tokens)
                ),
                remediation: "Replace 1–3 line projection/determinism/vacuity cosplay (`rfl`, `congrArg`, `Bool.and_eq_true`, `And.left`/`And.right`, `fun _ => trivial`, `Fragment := fun _ => False`) with a substantive domain soundness theorem over a non-empty fragment.".to_string(),
            });
        }
    }
}

fn strip_outer_parens_tokens(mut slice: &[LeanToken]) -> &[LeanToken] {
    let mut layers = 0usize;
    while layers < 8
        && slice.len() >= 2
        && matches!(&slice[0].kind, LeanTokenKind::Symbol(s) if s == "(")
        && matches!(&slice[slice.len() - 1].kind, LeanTokenKind::Symbol(s) if s == ")")
    {
        layers += 1;
        let mut depth = 0isize;
        let mut wraps_all = true;
        for (idx, tok) in slice.iter().enumerate() {
            match &tok.kind {
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{" | "⟨") => {
                    depth += 1;
                }
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}" | "⟩") => {
                    depth -= 1;
                    if depth == 0 && idx + 1 < slice.len() {
                        wraps_all = false;
                        break;
                    }
                }
                _ => {}
            }
        }
        if wraps_all && depth == 0 {
            slice = &slice[1..slice.len() - 1];
        } else {
            break;
        }
    }
    slice
}

#[derive(Debug, Clone)]
struct QuantBinder {
    name: String,
    is_underscore: bool,
    is_instance_bracket: bool,
    type_tokens: Vec<LeanToken>,
}

fn parse_forall_binder_tokens(slice: &[LeanToken], out: &mut Vec<QuantBinder>) {
    let mut i = 0usize;
    while i < slice.len() {
        match &slice[i].kind {
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "{" | "[") => {
                let open = s.as_str();
                let close = match open {
                    "(" => ")",
                    "{" => "}",
                    _ => "]",
                };
                let gstart = i + 1;
                let mut d = 1usize;
                i += 1;
                while i < slice.len() && d > 0 {
                    match &slice[i].kind {
                        LeanTokenKind::Symbol(o) if o == open => d += 1,
                        LeanTokenKind::Symbol(c) if c == close => d -= 1,
                        _ => {}
                    }
                    i += 1;
                }
                let gend = i.saturating_sub(1);
                if gstart <= gend && gend <= slice.len() {
                    let group = &slice[gstart..gend];
                    let is_inst = open == "[";
                    let mut depth = 0isize;
                    let mut colon_pos = None;
                    for (k, t) in group.iter().enumerate() {
                        match &t.kind {
                            LeanTokenKind::Symbol(sym)
                                if matches!(sym.as_str(), "(" | "[" | "{") =>
                            {
                                depth += 1;
                            }
                            LeanTokenKind::Symbol(sym)
                                if matches!(sym.as_str(), ")" | "]" | "}") =>
                            {
                                depth = (depth - 1).max(0);
                            }
                            LeanTokenKind::Symbol(sym) if sym == ":" && depth == 0 => {
                                colon_pos = Some(k);
                                break;
                            }
                            _ => {}
                        }
                    }
                    if is_inst && colon_pos.is_none() {
                        continue;
                    }
                    let (lhs, rhs_ty) = match colon_pos {
                        Some(c) => (&group[..c], group[c + 1..].to_vec()),
                        None => (group, Vec::new()),
                    };
                    for t in lhs {
                        if let LeanTokenKind::Ident(id) = &t.kind {
                            out.push(QuantBinder {
                                name: id.clone(),
                                is_underscore: id.starts_with('_'),
                                is_instance_bracket: is_inst,
                                type_tokens: rhs_ty.clone(),
                            });
                        }
                    }
                }
            }
            LeanTokenKind::Symbol(s) if s == ":" => {
                // Unparenthesized typed binder `∀ x y : T, ...`
                let rhs_ty = slice[i + 1..].to_vec();
                for qb in out.iter_mut().rev() {
                    if qb.type_tokens.is_empty() {
                        qb.type_tokens = rhs_ty.clone();
                    } else {
                        break;
                    }
                }
                break;
            }
            LeanTokenKind::Ident(id) => {
                out.push(QuantBinder {
                    name: id.clone(),
                    is_underscore: id.starts_with('_'),
                    is_instance_bracket: false,
                    type_tokens: Vec::new(),
                });
                i += 1;
            }
            _ => {
                i += 1;
            }
        }
    }
}

fn peel_forall_and_arrows<'a>(
    tokens: &'a [LeanToken],
    binders: &mut Vec<QuantBinder>,
    hyps: &mut Vec<&'a [LeanToken]>,
) -> &'a [LeanToken] {
    let mut slice = strip_outer_parens_tokens(tokens);
    loop {
        slice = strip_outer_parens_tokens(slice);
        if slice.is_empty() {
            return slice;
        }

        let starts_forall = matches!(
            &slice[0].kind,
            LeanTokenKind::Symbol(s) if s == "∀"
        ) || matches!(
            &slice[0].kind,
            LeanTokenKind::Ident(id) if id == "forall"
        );

        if starts_forall {
            let mut depth = 0isize;
            let mut comma_idx = None;
            for (idx, tok) in slice.iter().enumerate().skip(1) {
                match &tok.kind {
                    LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{" | "⟨") => {
                        depth += 1;
                    }
                    LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}" | "⟩") => {
                        depth = (depth - 1).max(0);
                    }
                    LeanTokenKind::Symbol(s) if s == "," && depth == 0 => {
                        comma_idx = Some(idx);
                        break;
                    }
                    _ => {}
                }
            }
            if let Some(cidx) = comma_idx {
                parse_forall_binder_tokens(&slice[1..cidx], binders);
                slice = &slice[cidx + 1..];
                continue;
            }
        }

        // Otherwise split at the first top-level `→` / `->`
        let mut depth = 0isize;
        let mut arrow_idx = None;
        for (idx, tok) in slice.iter().enumerate() {
            match &tok.kind {
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{" | "⟨") => {
                    depth += 1;
                }
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}" | "⟩") => {
                    depth = (depth - 1).max(0);
                }
                LeanTokenKind::Symbol(s) if (s == "→" || s == "->") && depth == 0 => {
                    arrow_idx = Some(idx);
                    break;
                }
                _ => {}
            }
        }

        if let Some(aidx) = arrow_idx {
            let ant = strip_outer_parens_tokens(&slice[..aidx]);
            if !ant.is_empty() {
                hyps.push(ant);
            }
            slice = &slice[aidx + 1..];
            continue;
        }

        return slice;
    }
}

fn is_non_obligation_sort_or_data_concl(concl: &[LeanToken]) -> bool {
    let c = strip_outer_parens_tokens(concl);
    let Some(first) = c.first() else {
        return true;
    };
    if let LeanTokenKind::Ident(id) = &first.kind {
        let short = id.rsplit('.').next().unwrap_or(id.as_str());
        if matches!(
            short,
            "Prop"
                | "Type"
                | "Sort"
                | "Bool"
                | "Nat"
                | "Int"
                | "String"
                | "Unit"
                | "PUnit"
                | "ByteArray"
                | "UInt8"
                | "UInt16"
                | "UInt32"
                | "UInt64"
                | "USize"
                | "Float"
                | "Option"
                | "List"
                | "Array"
                | "BitVec"
                | "Fin"
                | "Except"
        ) {
            // Ensure it's not an equality/comparison starting with `Nat.ble ... = true` etc.
            let has_rel = c.iter().any(|t| {
                matches!(
                    &t.kind,
                    LeanTokenKind::Symbol(s)
                        if matches!(
                            s.as_str(),
                            "=" | "==" | "≠" | "!=" | "<" | ">" | "≤" | "<=" | "≥" | ">=" | "↔" | "<->" | "∧" | "∨"
                        )
                )
            });
            if !has_rel {
                return true;
            }
        }
    }
    false
}

fn is_sort_binder_type(type_tokens: &[LeanToken]) -> bool {
    let t = strip_outer_parens_tokens(type_tokens);
    let (_, concl) = split_top_level_arrows(t);
    let concl = strip_outer_parens_tokens(concl);
    concl.first().is_some_and(|tok| {
        matches!(
            &tok.kind,
            LeanTokenKind::Ident(id) if matches!(id.as_str(), "Type" | "Sort" | "Prop")
        )
    })
}

fn normalize_prop_tokens(tokens: &[LeanToken]) -> Vec<String> {
    let clean = strip_outer_parens_tokens(tokens);
    clean
        .iter()
        .filter_map(|t| match &t.kind {
            LeanTokenKind::Ident(s) | LeanTokenKind::Symbol(s) | LeanTokenKind::NatLit(s) => {
                Some(s.clone())
            }
            LeanTokenKind::StrLit(s) => Some(format!("\"{s}\"")),
            _ => None,
        })
        .collect()
}

fn split_top_level_op<'a>(tokens: &'a [LeanToken], ops: &[&str]) -> Vec<&'a [LeanToken]> {
    let clean = strip_outer_parens_tokens(tokens);
    let mut parts = Vec::new();
    let mut depth = 0isize;
    let mut start = 0usize;
    for (idx, tok) in clean.iter().enumerate() {
        match &tok.kind {
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{" | "⟨") => depth += 1,
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}" | "⟩") => {
                depth = (depth - 1).max(0);
            }
            LeanTokenKind::Symbol(s) if depth == 0 && ops.contains(&s.as_str()) => {
                if start < idx {
                    parts.push(strip_outer_parens_tokens(&clean[start..idx]));
                }
                start = idx + 1;
            }
            _ => {}
        }
    }
    if start < clean.len() {
        parts.push(strip_outer_parens_tokens(&clean[start..]));
    }
    parts
}

fn split_top_level_binary<'a>(
    tokens: &'a [LeanToken],
    ops: &[&str],
) -> Option<(&'a [LeanToken], &'a str, &'a [LeanToken])> {
    let clean = strip_outer_parens_tokens(tokens);
    let mut depth = 0isize;
    for (idx, tok) in clean.iter().enumerate() {
        match &tok.kind {
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{" | "⟨") => depth += 1,
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}" | "⟩") => {
                depth = (depth - 1).max(0);
            }
            LeanTokenKind::Symbol(s)
                if depth == 0 && ops.contains(&s.as_str()) && idx > 0 && idx + 1 < clean.len() =>
            {
                return Some((
                    strip_outer_parens_tokens(&clean[..idx]),
                    s.as_str(),
                    strip_outer_parens_tokens(&clean[idx + 1..]),
                ));
            }
            _ => {}
        }
    }
    None
}

fn substitute_ident_in_norm(norm: &[String], from: &str, to: &str) -> Vec<String> {
    let prefix = format!("{from}.");
    norm.iter()
        .map(|tok| {
            if tok == from {
                to.to_string()
            } else if let Some(rest) = tok.strip_prefix(&prefix) {
                format!("{to}.{rest}")
            } else {
                tok.clone()
            }
        })
        .collect()
}

fn is_lattice_meet_implies_tautology(concl: &[LeanToken]) -> bool {
    let Some((lhs, _, rhs)) = split_top_level_binary(concl, &["=", "=="]) else {
        return false;
    };
    if rhs.len() != 1
        || !matches!(&rhs[0].kind, LeanTokenKind::Ident(id) if id == "true" || id == "Bool.true")
    {
        return false;
    }

    // Pattern 1: `φ.implies φ`
    if lhs.len() == 2
        && let (LeanTokenKind::Ident(a_imp), LeanTokenKind::Ident(b)) = (&lhs[0].kind, &lhs[1].kind)
        && let Some(a) = a_imp.strip_suffix(".implies")
        && a == b
    {
        return true;
    }

    // Pattern 2: `(φ.meet ψ).implies φ` or `(φ.meet ψ).implies ψ`
    if lhs.len() == 6
        && matches!(&lhs[0].kind, LeanTokenKind::Symbol(s) if s == "(")
        && matches!(&lhs[3].kind, LeanTokenKind::Symbol(s) if s == ")")
        && matches!(&lhs[4].kind, LeanTokenKind::Symbol(s) if s == ".implies")
        && let (LeanTokenKind::Ident(a_meet), LeanTokenKind::Ident(b), LeanTokenKind::Ident(target)) =
            (&lhs[1].kind, &lhs[2].kind, &lhs[5].kind)
        && let Some(a) = a_meet.strip_suffix(".meet")
        && (target == a || target == b)
    {
        return true;
    }

    // Pattern 3: `φ.implies (φ.join ψ)` or `ψ.implies (φ.join ψ)`
    if lhs.len() == 5
        && matches!(&lhs[1].kind, LeanTokenKind::Symbol(s) if s == "(")
        && matches!(&lhs[4].kind, LeanTokenKind::Symbol(s) if s == ")")
        && let (LeanTokenKind::Ident(t_imp), LeanTokenKind::Ident(a_join), LeanTokenKind::Ident(b)) =
            (&lhs[0].kind, &lhs[2].kind, &lhs[3].kind)
        && let (Some(target), Some(a)) =
            (t_imp.strip_suffix(".implies"), a_join.strip_suffix(".join"))
        && (target == a || target == b)
    {
        return true;
    }

    false
}

fn is_forall_instantiation_tautology(hyp: &[LeanToken], concl: &[LeanToken]) -> bool {
    let mut h_binders = Vec::new();
    let mut h_inner_hyps = Vec::new();
    let h_body = peel_forall_and_arrows(hyp, &mut h_binders, &mut h_inner_hyps);
    if h_binders.len() != 1 || !h_inner_hyps.is_empty() {
        return false;
    }
    let var = &h_binders[0].name;
    let body_norm = normalize_prop_tokens(h_body);
    let concl_norm = normalize_prop_tokens(concl);
    let var_positions: Vec<usize> = body_norm
        .iter()
        .enumerate()
        .filter_map(|(i, t)| if t == var { Some(i) } else { None })
        .collect();
    if var_positions.len() != 1 {
        return false;
    }
    let pos = var_positions[0];
    let prefix = &body_norm[..pos];
    let suffix = &body_norm[pos + 1..];
    concl_norm.len() > prefix.len() + suffix.len()
        && concl_norm.starts_with(prefix)
        && concl_norm.ends_with(suffix)
}

fn field_name_claims_crypto_or_protocol_soundness(field_name: &str) -> bool {
    let lower = field_name.to_ascii_lowercase();
    lower.contains("gkr")
        || lower.contains("zeroknowledge")
        || lower.contains("attested")
        || lower.contains("refines")
        || lower.contains("extract")
        || lower.contains("isaequiv")
        || lower.contains("kernelproof")
}

fn is_simple_scalar_zero_bound(concl: &[LeanToken]) -> bool {
    let Some((lhs, op, rhs)) =
        split_top_level_binary(concl, &[">", "<", ">=", "≥", "<=", "≤", "≠", "!="])
    else {
        return false;
    };
    let is_zero = |slice: &[LeanToken]| -> bool {
        slice.len() == 1 && matches!(&slice[0].kind, LeanTokenKind::NatLit(n) if n == "0")
    };
    let is_single_atom = |slice: &[LeanToken]| -> bool {
        slice.len() == 1 && matches!(&slice[0].kind, LeanTokenKind::Ident(_))
    };

    match op {
        ">" | ">=" | "≥" | "≠" | "!=" => is_single_atom(lhs) && is_zero(rhs),
        "<" | "<=" | "≤" => is_zero(lhs) && is_single_atom(rhs),
        _ => false,
    }
}

fn classify_obligation_field_signature(
    field_name: &str,
    field_binders: &[BinderParam],
    field_type_tokens: &[LeanToken],
) -> Option<String> {
    if field_type_tokens.is_empty() {
        return None;
    }

    let mut qbinders: Vec<QuantBinder> = field_binders
        .iter()
        .map(|b| QuantBinder {
            name: b.name.clone(),
            is_underscore: b.is_underscore,
            is_instance_bracket: b.is_instance_bracket,
            type_tokens: b.type_tokens.clone(),
        })
        .collect();
    let mut hyps: Vec<&[LeanToken]> = Vec::new();
    let concl = peel_forall_and_arrows(field_type_tokens, &mut qbinders, &mut hyps);

    if concl.is_empty() || is_non_obligation_sort_or_data_concl(concl) {
        return None;
    }

    // 1. Trivial `True` or syntactic reflexivity `e = e` / `e ↔ e`
    if is_pure_true_proposition(concl) {
        return Some("tautological `True` conclusion (`... → True`)".to_string());
    }
    if let Some((clhs, op, crhs)) = split_top_level_binary(concl, &["=", "==", "↔", "<->"]) {
        let nl = normalize_prop_tokens(clhs);
        let nr = normalize_prop_tokens(crhs);
        if !nl.is_empty() && nl == nr {
            return Some(format!(
                "syntactic reflexivity tautology (`{} {op} {}`)",
                render_tokens_compact(clhs),
                render_tokens_compact(crhs)
            ));
        }
    }

    // 2. Tautological implication / conjunction repackaging (`P → Q → P ∧ Q`, `P ∧ Q → P`, `P → P`)
    let mut hyp_atoms: Vec<Vec<String>> = Vec::new();
    let mut raw_hyp_atoms: Vec<&[LeanToken]> = Vec::new();
    for h in &hyps {
        for atom in split_top_level_op(h, &["∧"]) {
            let norm = normalize_prop_tokens(atom);
            if !norm.is_empty() {
                hyp_atoms.push(norm);
                raw_hyp_atoms.push(atom);
            }
        }
    }
    if !hyp_atoms.is_empty() {
        let concl_conjs: Vec<Vec<String>> = split_top_level_op(concl, &["∧"])
            .into_iter()
            .map(normalize_prop_tokens)
            .filter(|v| !v.is_empty())
            .collect();
        if !concl_conjs.is_empty()
            && concl_conjs
                .iter()
                .all(|cj| hyp_atoms.iter().any(|ha| ha == cj))
        {
            return Some(
                "tautological implication repackaging (`P → Q → P ∧ Q` / conclusion repeats hypotheses)"
                    .to_string(),
            );
        }

        let concl_disjs: Vec<Vec<String>> = split_top_level_op(concl, &["∨"])
            .into_iter()
            .map(normalize_prop_tokens)
            .filter(|v| !v.is_empty())
            .collect();
        if concl_disjs.len() > 1
            && concl_disjs
                .iter()
                .any(|dj| hyp_atoms.iter().any(|ha| ha == dj))
        {
            return Some("tautological disjunction weakening (`P → P ∨ Q`)".to_string());
        }
    }

    // 3. Equality congruence (`a = b → a.toNat = b.toNat`, `x = y → f x = f y`, `a = b → (a == b) = true`)
    let concl_eq_pair = if let Some((clhs, _, crhs)) = split_top_level_binary(concl, &["="]) {
        if crhs.len() == 1
            && matches!(&crhs[0].kind, LeanTokenKind::Ident(id) if id == "true" || id == "Bool.true")
        {
            split_top_level_binary(clhs, &["=="]).or(Some((clhs, "=", crhs)))
        } else {
            Some((clhs, "=", crhs))
        }
    } else {
        split_top_level_binary(concl, &["=="])
    };

    if let Some((clhs, _, crhs)) = concl_eq_pair {
        let clhs_norm = normalize_prop_tokens(clhs);
        let crhs_norm = normalize_prop_tokens(crhs);
        if !clhs_norm.is_empty() && clhs_norm != crhs_norm {
            for hatom in &raw_hyp_atoms {
                if let Some((hlhs, _, hrhs)) = split_top_level_binary(hatom, &["="])
                    .or_else(|| split_top_level_binary(hatom, &["=="]))
                {
                    let hlhs_norm = normalize_prop_tokens(hlhs);
                    let hrhs_norm = normalize_prop_tokens(hrhs);
                    if (hlhs_norm == clhs_norm && hrhs_norm == crhs_norm)
                        || (hlhs_norm == crhs_norm && hrhs_norm == clhs_norm)
                    {
                        return Some(format!(
                            "equality/BEq congruence tautology (`{} = {} → {}`)",
                            render_tokens_compact(hlhs),
                            render_tokens_compact(hrhs),
                            render_tokens_compact(concl)
                        ));
                    }
                    if hlhs.len() == 1
                        && hrhs.len() == 1
                        && let (LeanTokenKind::Ident(x), LeanTokenKind::Ident(y)) =
                            (&hlhs[0].kind, &hrhs[0].kind)
                        && x != y
                        && (substitute_ident_in_norm(&clhs_norm, x, y) == crhs_norm
                            || substitute_ident_in_norm(&clhs_norm, y, x) == crhs_norm)
                    {
                        return Some(format!(
                            "equality congruence tautology (`{x} = {y} → {} = {}`)",
                            render_tokens_compact(clhs),
                            render_tokens_compact(crhs)
                        ));
                    }
                }
            }
        }
    }

    // 4. Universal instantiation tautology (`(∀ z, P z) → ∀ y, P (g y)`)
    for hatom in &raw_hyp_atoms {
        if is_forall_instantiation_tautology(hatom, concl) {
            return Some(
                "universal instantiation tautology (`(∀ z, P z) → P term` without domain refinement)"
                    .to_string(),
            );
        }
    }

    // 5. Lattice / boolean algebra meet-join-implies tautology (`(φ.meet ψ).implies φ = true`)
    if hyps.is_empty() && is_lattice_meet_implies_tautology(concl) {
        return Some(format!(
            "boolean/lattice tautology (`{}`)",
            render_tokens_compact(concl)
        ));
    }

    // 6. Quantified domain binder never appearing in any subsequent binder type, hypothesis, or conclusion
    for (bi, qb) in qbinders.iter().enumerate() {
        if qb.is_instance_bracket || is_sort_binder_type(&qb.type_tokens) {
            continue;
        }
        if qb.is_underscore {
            return Some(format!(
                "discarded quantified domain binder `{}` in obligation signature",
                qb.name
            ));
        }
        let used_in_later_binder = qbinders[bi + 1..]
            .iter()
            .any(|later| ident_referenced(&later.type_tokens, &qb.name));
        let used_in_hyps = hyps.iter().any(|h| ident_referenced(h, &qb.name));
        let used_in_concl = ident_referenced(concl, &qb.name);
        if !used_in_later_binder && !used_in_hyps && !used_in_concl {
            return Some(format!(
                "quantified domain binder `{}` never appears in hypotheses or conclusion",
                qb.name
            ));
        }
    }

    // 7. High-claim cryptographic/protocol soundness name paired with scalar `> 0` consequence or non-existential fake `Extract`
    if field_name_claims_crypto_or_protocol_soundness(field_name) {
        if is_simple_scalar_zero_bound(concl) {
            return Some(format!(
                "field `{field_name}` claims cryptographic/protocol soundness but only states trivial scalar zero-bound `{}`",
                render_tokens_compact(concl)
            ));
        }
        if field_name.to_ascii_lowercase().contains("extract") {
            let has_witness_former = concl.iter().any(|t| {
                matches!(&t.kind, LeanTokenKind::Symbol(s) if s == "∃" || s == "Σ")
                    || matches!(
                        &t.kind,
                        LeanTokenKind::Ident(id)
                            if matches!(
                                id.as_str(),
                                "Exists" | "Nonempty" | "Sigma" | "PSigma" | "PSum" | "Sum"
                            )
                    )
            });
            let has_concl_unused_domain_binder = qbinders.iter().any(|qb| {
                !qb.is_instance_bracket
                    && !is_sort_binder_type(&qb.type_tokens)
                    && !ident_referenced(concl, &qb.name)
            });
            if !has_witness_former && has_concl_unused_domain_binder && !hyps.is_empty() {
                return Some(format!(
                    "field `{field_name}` claims witness extraction (`*Extract`) without any existential witness (`∃`) in conclusion (`{}`)",
                    render_tokens_compact(concl)
                ));
            }
        }
    }

    None
}

/// Stage-A Class-Signature Anti-Cosplay Rule (`lean/obligation-tautological-field`):
/// Inspects field signatures inside `class *Obligations`, `class *Ledger`, and `@[obb_obligation]` classes.
fn check_obligation_class_tautological_fields(
    file: &ParsedLeanFile,
    decl: &ParsedLeanDecl,
    obligation_classes: &HashSet<String>,
    findings: &mut Vec<Finding>,
) {
    let is_obl_class = obligation_classes.contains(&decl.fq_name)
        || obligation_classes.contains(&decl.name)
        || is_obligation_class_name(&decl.name)
        || decl.attributes.iter().any(|a| a == "obb_obligation");
    if !is_obl_class {
        return;
    }

    for sf in &decl.struct_fields {
        if let Some(reason) =
            classify_obligation_field_signature(&sf.name, &sf.binders, &sf.type_tokens)
        {
            findings.push(Finding {
                rule_id: "lean/obligation-tautological-field".to_string(),
                severity: Severity::Error,
                artifact_kind: ArtifactKind::S,
                max_regime: Regime::Attested,
                sink: Some(Sink::Theater),
                path: file.rel_path.clone(),
                line: sf.line,
                column: sf.col,
                symbol: Some(format!("{}.{}", decl.fq_name, sf.name)),
                message: format!(
                    "Stage-A obligation field `{}.{}` has a tautological/cosplay signature: {reason}",
                    decl.fq_name, sf.name
                ),
                remediation: "Replace tautological Stage-A obligation signatures (`P → Q → P ∧ Q`, `a = b → f a = f b`, `... → True`, lattice meet elimination, unused quantified binders, or scalar `> 0` bounds under crypto/protocol soundness names) with the real semantic, ISA, or cryptographic refinement statement (or prove trivial lemmas directly and delete the obligation field).".to_string(),
            });
        }
    }
}

fn is_turn_carrier_ident(id: &str) -> bool {
    let short = id.rsplit('.').next().unwrap_or(id);
    short == "Turn"
        || (short.ends_with("Turn")
            && short.len() > 4
            && short.chars().next().is_some_and(|c| c.is_ascii_uppercase()))
}

fn is_seq_container_ident(id: &str) -> bool {
    let short = id.rsplit('.').next().unwrap_or(id);
    matches!(short, "List" | "Array" | "Stream" | "Vector" | "Trace")
}

fn is_multi_turn_modal_or_trace_ident(id: &str) -> bool {
    let short = id.rsplit('.').next().unwrap_or(id);
    matches!(
        short,
        "Reach" | "Reachable" | "SafeWP" | "ValidTrace" | "MultiTurnHoare" | "GPaco" | "TraceSafe"
    ) || short.starts_with("Reach")
        || short.ends_with("Reach")
        || short.starts_with("SafeWP")
        || short.ends_with("SafeWP")
        || short.starts_with("ValidTrace")
        || short.ends_with("ValidTrace")
        || short.contains("MultiTurn")
}

fn tokens_have_multi_turn_form(tokens: &[LeanToken]) -> bool {
    for (i, tok) in tokens.iter().enumerate() {
        if let LeanTokenKind::Ident(id) = &tok.kind {
            if is_multi_turn_modal_or_trace_ident(id) {
                return true;
            }
            if is_seq_container_ident(id) {
                // `List Turn`, `List (SessionTurn)`, `Array GovTurn`, `Stream Turn`
                let rest = &tokens[i + 1..];
                for next_tok in rest.iter().take(3) {
                    match &next_tok.kind {
                        LeanTokenKind::Symbol(s) if s == "(" => continue,
                        LeanTokenKind::Ident(inner) if is_turn_carrier_ident(inner) => {
                            return true;
                        }
                        _ => break,
                    }
                }
            }
        }
    }
    false
}

fn decl_has_multi_turn_signature(decl: &ParsedLeanDecl) -> bool {
    decl.binders
        .iter()
        .any(|b| tokens_have_multi_turn_form(&b.type_tokens))
        || tokens_have_multi_turn_form(&decl.type_tokens)
}

fn first_single_turn_carrier_in_tokens(tokens: &[LeanToken]) -> Option<String> {
    for (i, tok) in tokens.iter().enumerate() {
        if let LeanTokenKind::Ident(id) = &tok.kind
            && is_turn_carrier_ident(id)
        {
            // Ignore when immediately preceded by `List` / `Array` / `Stream` (or `List (`)
            let preceded_by_seq = (i >= 1
                && matches!(&tokens[i - 1].kind, LeanTokenKind::Ident(prev) if is_seq_container_ident(prev)))
                || (i >= 2
                    && matches!(&tokens[i - 1].kind, LeanTokenKind::Symbol(s) if s == "(")
                    && matches!(&tokens[i - 2].kind, LeanTokenKind::Ident(prev) if is_seq_container_ident(prev)));
            if !preceded_by_seq {
                return Some(id.clone());
            }
        }
    }
    None
}

fn is_apex_single_turn_theorem_name(name: &str) -> bool {
    let short = name.rsplit('.').next().unwrap_or(name);
    short.starts_with("apex_")
        && (short.ends_with("_turn_safe")
            || short.ends_with("_turn_sound")
            || short.contains("_turn_safe_")
            || short.contains("_turn_sound_"))
}

/// Checks whether `decl` is a single-turn `apex_*_turn_{safe,sound}` theorem taking a `*Turn`
/// parameter in a module that lacks any multi-turn trace/reachability invariant theorem
/// (`List *Turn`, `Reach`, `SafeWP`, `ValidTrace`, `MultiTurnHoare`, `GPaco`).
pub fn single_turn_apex_violation(file: &ParsedLeanFile, decl: &ParsedLeanDecl) -> Option<String> {
    if decl.kind != DeclKind::Theorem || !is_apex_single_turn_theorem_name(&decl.name) {
        return None;
    }
    if decl_has_multi_turn_signature(decl) {
        return None;
    }

    let mut qbinders: Vec<QuantBinder> = Vec::new();
    let mut hyps: Vec<&[LeanToken]> = Vec::new();
    let _ = peel_forall_and_arrows(&decl.type_tokens, &mut qbinders, &mut hyps);

    let turn_carrier = decl
        .binders
        .iter()
        .find_map(|b| first_single_turn_carrier_in_tokens(&b.type_tokens))
        .or_else(|| {
            qbinders
                .iter()
                .find_map(|qb| first_single_turn_carrier_in_tokens(&qb.type_tokens))
        })?;

    let module_has_multi_turn_thm = file.declarations.iter().any(|other| {
        other.kind == DeclKind::Theorem
            && !other.fixture_kept
            && decl_has_multi_turn_signature(other)
    });

    if module_has_multi_turn_thm {
        None
    } else {
        Some(format!(
            "Single-turn apex theorem `{}` quantifies over single `{turn_carrier}` without any multi-turn trace/reachability invariant theorem (`List *Turn`, `Reach`, `SafeWP`, `ValidTrace`, `MultiTurnHoare`) in `{}`, leaving multi-turn state-accumulation hazards (`RevokedSet` growth, `Mandate` budget depletion, persistent `UMem`) unverified",
            decl.fq_name, file.rel_path
        ))
    }
}
