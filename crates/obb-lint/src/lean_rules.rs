//! Mechanical anti-slop & vacuity detectors for Lean 4 (`DESIGN.md` §2.6, `JUDGE.md`).

use crate::lean_index::{DeclKind, LeanIndex, ParsedLeanDecl, ParsedLeanFile};
use crate::lean_lexer::{LeanToken, LeanTokenKind};
use obb_core::{ArtifactKind, DirectoryCensus, Finding, Regime, Severity, Sink};
use std::collections::{BTreeMap, HashMap, HashSet};

pub const FILE_WIDE_EXPOSE_LINE_THRESHOLD: usize = 80;

#[derive(Debug, Clone, Copy, Default)]
pub struct LeanLintOptions {
    /// Escalate `lean/file-wide-expose` from `Severity::Warning` (legacy default) to `Severity::Error`.
    pub strict_expose: bool,
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
        if !is_teeth_or_test && file.rel_path.contains("Obend/") {
            if let Some(stem) = std::path::Path::new(&file.rel_path)
                .file_stem()
                .and_then(|s| s.to_str())
            {
                if let Some(pat) = cosplay_pattern(stem) {
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
            }
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

        // Map decl short name -> decl for cross-checking `Judge.check` helper bodies and `Format` decoders
        let mut decl_by_name: HashMap<&str, &ParsedLeanDecl> = HashMap::new();
        for decl in &file.declarations {
            decl_by_name.insert(decl.name.as_str(), decl);
        }

        // Module-level HypothesisLedger / inhabited-premise index
        let module_witnessed_preds = collect_module_satisfiability_witnesses(file);

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
                }
                DeclKind::TacticElab => {
                    check_tactic_elab(file, decl, &mut findings);
                }
                DeclKind::Theorem | DeclKind::Def | DeclKind::Abbrev | DeclKind::Instance => {
                    // 1. Check `sorry` inside theorem/def/instance proof or type (excluding deliberate planted-sorry test fixtures)
                    if !is_planted_sorry_fixture_name(&decl.name) {
                        for tok in decl.type_tokens.iter().chain(decl.body_tokens.iter()) {
                            if let LeanTokenKind::Ident(id) = &tok.kind {
                                if id == "sorry" || id == "sorryAx" {
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
                    }

                    // 2. Cosplay naming on load-bearing declarations
                    if !is_teeth_or_test && file.rel_path.contains("Obend/") {
                        if let Some(pat) = cosplay_pattern(&decl.name) {
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

                        let uses_native_decide = tokens_contain_ident(&decl.body_tokens, "native_decide")
                            || tokens_contain_ident(&decl.body_tokens, "bv_decide");

                        if !is_univ {
                            entry.attested_claims += 1;
                            if claims_general_soundness(&decl.name) && is_concrete_decision_proof(&decl.body_tokens) {
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
                    }

                    // 5. `Judge` instance tautological `Meaning` detector
                    if is_judge_instance_decl(decl) {
                        check_judge_meaning(file, decl, &decl_by_name, &mut findings);
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
                _ => {}
            }
        }
    }

    // Tally findings into directory census buckets
    for f in &findings {
        let bucket = bucket_for_finding_path(&f.path);
        let entry = dir_map.entry(bucket.clone()).or_insert_with(|| DirectoryCensus {
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
    lower.contains("sorry") && (lower.contains("info") || lower.contains("fixture") || lower.contains("bad"))
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
                if matches!(s.as_str(), "∧" | "∨" | "→" | "->" | "↔" | "<->" | "(" | ")") => {}
            _ => return false,
        }
    }
    saw_true
}

fn is_iff_rfl_body(body_tokens: &[LeanToken]) -> bool {
    if body_tokens.len() == 1 {
        if let LeanTokenKind::Ident(id) = &body_tokens[0].kind {
            return id == "Iff.rfl";
        }
    }
    if body_tokens.len() == 2 {
        if matches!(&body_tokens[0].kind, LeanTokenKind::Ident(id) if id == "by")
            && matches!(&body_tokens[1].kind, LeanTokenKind::Ident(id) if id == "rfl")
        {
            return false;
        }
    }
    false
}

fn ident_referenced(tokens: &[LeanToken], target: &str) -> bool {
    tokens.iter().any(|t| match &t.kind {
        LeanTokenKind::Ident(id) => {
            id == target
                || id
                    .split('.')
                    .next()
                    .is_some_and(|head| head == target)
        }
        LeanTokenKind::AntiquoteIdent(id) => id == target,
        _ => false,
    })
}

fn check_tactic_elab(
    file: &ParsedLeanFile,
    decl: &ParsedLeanDecl,
    findings: &mut Vec<Finding>,
) {
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
                if depth == 0 && rhs_end > j && toks[rhs_end].first_on_line && toks[rhs_end].col <= let_col {
                    break;
                }
                match &toks[rhs_end].kind {
                    LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{") => depth += 1,
                    LeanTokenKind::SyntaxQuoteOpen | LeanTokenKind::AntiquoteOpen => depth += 1,
                    LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}") => {
                        if depth > 0 {
                            depth -= 1;
                        }
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
            LeanTokenKind::Symbol(s) if s == ")" => {
                match stack.pop() {
                    Some(1) => quote_depth = quote_depth.saturating_sub(1),
                    Some(2) => antiquote_depth = antiquote_depth.saturating_sub(1),
                    _ => {}
                }
            }
            LeanTokenKind::Ident(id) => {
                if quote_depth == 0 || antiquote_depth > 0 {
                    out.insert(id.clone());
                    if let Some(head) = id.split('.').next() {
                        out.insert(head.to_string());
                    }
                }
            }
            _ => {}
        }
    }

    out
}

fn is_judge_instance_decl(decl: &ParsedLeanDecl) -> bool {
    if !matches!(decl.kind, DeclKind::Instance | DeclKind::Def) {
        return false;
    }
    decl.type_tokens.first().is_some_and(|t| {
        matches!(
            &t.kind,
            LeanTokenKind::Ident(id) if id == "Judge" || id == "Obend.Judge"
        )
    })
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
    let str_param = decl
        .binders
        .first()
        .map(|b| b.name.as_str())
        .unwrap_or("s");

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

fn find_preset_string_branch(tokens: &[LeanToken], param_name: &str) -> Option<(String, usize, usize)> {
    // Pattern A: `param == "preset"` or `param = "preset"`
    for w in tokens.windows(3) {
        let lhs_is_param = matches!(&w[0].kind, LeanTokenKind::Ident(id) if id == param_name);
        let is_eq = matches!(&w[1].kind, LeanTokenKind::Symbol(s) if s == "==" || s == "=");
        if lhs_is_param && is_eq {
            if let LeanTokenKind::StrLit(lit) = &w[2].kind {
                if !lit.is_empty() {
                    return Some((lit.clone(), w[2].line, w[2].col));
                }
            }
        }
    }
    // Pattern B: `match param with | "preset" => ...`
    find_match_string_literal_arm(tokens)
}

fn find_match_string_literal_arm(tokens: &[LeanToken]) -> Option<(String, usize, usize)> {
    for w in tokens.windows(3) {
        let is_pipe = matches!(&w[0].kind, LeanTokenKind::Symbol(s) if s == "|");
        let is_arrow = matches!(&w[2].kind, LeanTokenKind::Symbol(s) if s == "=>");
        if is_pipe && is_arrow {
            if let LeanTokenKind::StrLit(lit) = &w[1].kind {
                if !lit.is_empty() {
                    return Some((lit.clone(), w[1].line, w[1].col));
                }
            }
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
                "UInt8" | "UInt16" | "UInt32" | "UInt64" | "USize" | "Felt" | "Goldilocks" | "BabyBear" | "KoalaBear" | "Mersenne31"
            ) =>
        {
            tokens.len() == 1
        }
        LeanTokenKind::Ident(id) if id == "BitVec" && tokens.len() == 2 => {
            if let LeanTokenKind::NatLit(n_str) = &tokens[1].kind {
                if let Ok(bits) = n_str.replace('_', "").parse::<u64>() {
                    return bits <= 64;
                }
            }
            false
        }
        _ => false,
    }
}

fn find_single_limb_digest_weld(tokens: &[LeanToken]) -> Option<(String, usize, usize)> {
    let has_eq = tokens
        .iter()
        .any(|t| matches!(&t.kind, LeanTokenKind::Symbol(s) if s == "=" || s == "==")
            || matches!(&t.kind, LeanTokenKind::Ident(id) if id == "beq" || id.ends_with(".beq")));
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
                {
                    if matches!(n.as_str(), "1" | "2" | "3") {
                        accesses_higher_limb = true;
                    }
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
            LeanTokenKind::Symbol(s) if s == "." => {
                if tokens.get(i + 1).is_some_and(|t| {
                    matches!(&t.kind, LeanTokenKind::NatLit(n) if matches!(n.as_str(), "2" | "3" | "4"))
                }) {
                    accesses_higher_limb = true;
                }
            }
            _ => {}
        }
    }

    if accesses_higher_limb {
        return None;
    }

    for i in 0..tokens.len() {
        // Pattern 1: `digest[0]` / `digest[0]!`
        if let LeanTokenKind::Ident(id) = &tokens[i].kind {
            if is_crypto_digest_var_name(id)
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
        }

        // Pattern 2: `digest.get! 0` / `digest.getD 0` / `digest.get? 0` / `digest.get 0`
        if let LeanTokenKind::Ident(id) = &tokens[i].kind {
            if let Some((base, getter)) = id.rsplit_once('.') {
                if matches!(getter, "get!" | "getD" | "get?" | "get")
                    && is_crypto_digest_var_name(base)
                    && tokens
                        .get(i + 1)
                        .is_some_and(|t| matches!(&t.kind, LeanTokenKind::NatLit(n) if n == "0"))
                {
                    return Some((format!("{id} 0"), tokens[i].line, tokens[i].col));
                }
            }
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
                if d == 0 {
                    if let Some(LeanToken {
                        kind: LeanTokenKind::Ident(callee),
                        line,
                        col,
                        ..
                    }) = tokens.get(k + 1)
                    {
                        if is_crypto_digest_var_name(callee) {
                            let suffix = if is_idx0 { "[0]" } else { ".get! 0" };
                            return Some((format!("({callee} ...){suffix}"), *line, *col));
                        }
                    }
                }
            }
        }

        // Pattern 4: `Array.get! digest 0` / `List.get! digest 0`
        if let LeanTokenKind::Ident(id) = &tokens[i].kind {
            if matches!(
                id.as_str(),
                "Array.get!" | "Array.getD" | "List.get!" | "List.getD"
            ) {
                if let (
                    Some(LeanToken {
                        kind: LeanTokenKind::Ident(arg),
                        ..
                    }),
                    Some(LeanToken {
                        kind: LeanTokenKind::NatLit(n),
                        ..
                    }),
                ) = (tokens.get(i + 1), tokens.get(i + 2))
                {
                    if n == "0" && is_crypto_digest_var_name(arg) {
                        return Some((format!("{id} {arg} 0"), tokens[i].line, tokens[i].col));
                    }
                }
            }
        }

        // Pattern 5: `DescriptorIR2` function-limb projection `(m.newRoot 0)` / `(m.root 0)` / `(m.iroot 0)`
        if let LeanTokenKind::Ident(id) = &tokens[i].kind {
            if id.contains('.') && is_crypto_digest_var_name(id) {
                if tokens
                    .get(i + 1)
                    .is_some_and(|t| matches!(&t.kind, LeanTokenKind::NatLit(n) if n == "0"))
                {
                    return Some((format!("{id} 0"), tokens[i].line, tokens[i].col));
                }
            }
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
                if depth > 0 {
                    depth -= 1;
                }
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
fn collect_module_satisfiability_witnesses(file: &ParsedLeanFile) -> HashSet<String> {
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
        if is_judge_instance_decl(decl) && decl.where_fields.iter().any(|wf| wf.name == "complete")
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

        if matches!(decl.kind, DeclKind::Theorem | DeclKind::Example | DeclKind::Instance) {
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
                        if let Some(target_decl) = decl_by_name.get(short) {
                            if matches!(target_decl.kind, DeclKind::Def | DeclKind::Abbrev) {
                                return Some((
                                    short.to_string(),
                                    render_tokens_compact(hyp_tokens),
                                ));
                            }
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
            if let Some(target_decl) = decl_by_name.get(short) {
                if decl_defines_prop_predicate(target_decl) {
                    return Some((short.to_string(), render_tokens_compact(hyp_tokens)));
                }
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
        if let Some((target_sym, rendered_hyp)) = extract_premise_target(hyp_toks, decl_by_name) {
            if !module_witnessed_preds.contains(&target_sym)
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
}

fn is_obligation_class_name(name: &str) -> bool {
    let short = name.rsplit('.').next().unwrap_or(name);
    short == "HypothesisLedger"
        || short.contains("HypothesisLedger")
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
                if depth > 0 {
                    depth -= 1;
                }
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
                if depth > 0 {
                    depth -= 1;
                }
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
            LeanTokenKind::Symbol(s)
                if depth == 0 && delims.iter().any(|d| *d == s.as_str()) =>
            {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
                continue;
            }
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{" | "⟨") => {
                depth += 1;
            }
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}" | "⟩") => {
                if depth > 0 {
                    depth -= 1;
                }
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
                if depth > 0 {
                    depth -= 1;
                }
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

    // Struct literal `{ f := ..., g := ... }`
    if matches!(&body.first().unwrap().kind, LeanTokenKind::Symbol(s) if s == "{")
        && matches!(&body.last().unwrap().kind, LeanTokenKind::Symbol(s) if s == "}")
        && body.len() >= 2
    {
        let inner = &body[1..body.len() - 1];
        let chunks = split_top_level_delim(inner, &[",", ";"]);
        let mut parsed = Vec::new();
        for ch in &chunks {
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
                    if depth > 0 {
                        depth -= 1;
                    }
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
    loop {
        let Some(first) = slice.first() else {
            break;
        };
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
                    if let LeanTokenKind::Ident(id) = &slice[i].kind {
                        if id != "_" {
                            bound_params.insert(id.clone());
                        }
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
    if core.len() == 1 {
        if let LeanTokenKind::Ident(id) = &core[0].kind {
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
            "_"
                | "by"
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
                {
                    if n == "1" || n == "2" {
                        has_proj_op = true;
                    }
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
    let short_head = target_head.rsplit('.').next().unwrap_or(target_head.as_str());
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lean_index::build_lean_index;
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
}
