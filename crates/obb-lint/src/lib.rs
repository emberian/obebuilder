//! `obb-lint`: Mechanical anti-slop, vacuity, cross-language mirror, and Markdown symbol/constructor
//! verification engine (`DESIGN.md` §2.5–2.6, §6.1, `JUDGE.md`).

pub mod apex;
pub mod cone;
pub mod cross_lang;
pub mod harness;
pub mod lean_index;
pub mod lean_lexer;
pub mod lean_rules;
pub mod markdown_rules;
pub mod modularity;
pub mod obend_rules;
pub mod python_rules;
pub mod rust_rules;
pub mod spec_check;
pub mod test_in_library;

use anyhow::Result;
use chrono::Utc;
use cross_lang::scan_cross_lang_domain_tags;
use lean_index::build_lean_index;
use lean_rules::{LeanLintOptions, compute_tier1_test_counts, run_lean_lints_with_options};
use markdown_rules::scan_markdown_files;
use modularity::compute_modularity_report;
use obb_core::{DirectoryCensus, Finding, LintReport, Severity};
use obend_rules::scan_all_obend_files;
use python_rules::scan_python_files;
use rust_rules::scan_rust_files;
use std::collections::BTreeMap;
use std::path::Path;

/// Canonical sorted list of static lexical/AST lint rule IDs evaluated by `run_repo_lints_with_options`.
///
/// Note: `lean/spec-insensitive-change` is intentionally NOT in this static list because it requires
/// an external `lean-transport` census measurement rather than a pure static repo scan.
pub const KNOWN_STATIC_LINT_RULE_IDS: &[&str] = &[
    "cross-lang/domain-tag-drift",
    "javascript/test-in-library",
    "lean/closed-soundness-claim",
    "lean/cosplay-naming",
    "lean/discarded-tactic-binding",
    "lean/excessive-decl-expose",
    "lean/file-wide-expose",
    "lean/hardcoded-wire-decoder",
    "lean/judge-empty-fragment",
    "lean/judge-fragment-restates-check",
    "lean/monolithic-module",
    "lean/narrow-digest-weld",
    "lean/native-decide-in-proof",
    "lean/obligation-projection-cosplay",
    "lean/obligation-tautological-field",
    "lean/pigeonhole-vacuous-premise",
    "lean/public-meta-import-leak",
    "lean/single-sequence-harness",
    "lean/sorry-or-axiom",
    "lean/tautological-judge-meaning",
    "lean/test-in-library",
    "lean/trivial-conclusion",
    "lean/uninhabited-premise-risk",
    "lean/unused-param",
    "markdown/hallucinated-constructor",
    "markdown/missing-cited-file",
    "markdown/missing-lean-file",
    "markdown/missing-lean-symbol",
    "markdown/navel-prose",
    "obend/claim-restates-method",
    "obend/tautological-law",
    "python/e2e-mock-bridge",
    "python/e2e-self-mock",
    "python/test-in-library",
    "rust/mock-backend-in-src",
    "rust/obend-semantic-mirror",
    "rust/test-in-library",
];

/// Returns `true` iff `rule_id` is a real static rule evaluated by `run_repo_lints_with_options`.
pub fn is_known_static_lint_rule_id(rule_id: &str) -> bool {
    KNOWN_STATIC_LINT_RULE_IDS.binary_search(&rule_id).is_ok()
}

#[derive(Debug, Clone, Copy, Default)]
pub struct RepoLintOptions {
    /// Escalate `lean/file-wide-expose` and `lean/excessive-decl-expose` from `Severity::Warning` to `Severity::Error`.
    pub strict_expose: bool,
    /// Escalate `lean/single-sequence-harness` from `Severity::Warning` to `Severity::Error`.
    pub strict_harnesses: bool,
    /// Escalate `lean/judge-fragment-restates-check` and `lean/pigeonhole-vacuous-premise` from `Severity::Warning` to `Severity::Error`.
    pub strict_vacuity: bool,
    /// Escalate `cross-lang/domain-tag-drift` from `Severity::Warning` to `Severity::Error`.
    pub strict_wire: bool,
    /// Reject executable test declarations in Rust, JS/TS, Python and Lean library sources.
    pub strict_tests: bool,
}

/// Run all mechanical anti-slop, vacuity, seam-mirror, and doc-integrity checks over `repo_root`
/// strictly read-only.
pub fn run_repo_lints(repo_root: &Path) -> Result<LintReport> {
    run_repo_lints_with_options(repo_root, RepoLintOptions::default())
}

/// Run all mechanical lints over `repo_root` with configurable rule strictness.
pub fn run_repo_lints_with_options(
    repo_root: &Path,
    options: RepoLintOptions,
) -> Result<LintReport> {
    let canon = repo_root
        .canonicalize()
        .unwrap_or_else(|_| repo_root.to_path_buf());

    let index = build_lean_index(&canon);
    let lean_file_count = index.files.len();
    let lean_decls = index.total_declarations();
    let lean_inds = index.total_inductives();

    let modularity = compute_modularity_report(&index);
    let (tier1_guards, tier1_teeth, tier1_evals) = compute_tier1_test_counts(&index);
    let (mut findings, mut dir_census) = run_lean_lints_with_options(
        &index,
        LeanLintOptions {
            strict_expose: options.strict_expose,
            strict_harnesses: options.strict_harnesses,
            strict_vacuity: options.strict_vacuity,
            strict_tests: options.strict_tests,
        },
    );
    let (obend_count, obend_findings) = scan_all_obend_files(&canon);
    let (py_count, py_findings) = scan_python_files(&canon);
    let (rs_count, rs_findings) = scan_rust_files(&canon);
    let cross_lang_findings = scan_cross_lang_domain_tags(&canon, options.strict_wire);
    let (md_count, md_findings) = scan_markdown_files(&canon, &index);

    findings.extend(obend_findings);
    findings.extend(py_findings);
    findings.extend(rs_findings);
    findings.extend(cross_lang_findings);
    findings.extend(md_findings);
    if options.strict_tests {
        findings.extend(test_in_library::scan_test_in_library(&canon)?);
    }

    // Deterministic ordering by `(path, line, column, rule_id)`
    findings.sort_by(|a, b| {
        a.path
            .cmp(&b.path)
            .then_with(|| a.line.cmp(&b.line))
            .then_with(|| a.column.cmp(&b.column))
            .then_with(|| a.rule_id.cmp(&b.rule_id))
    });

    // Fold non-Lean findings into `directory_census` buckets as well
    let mut census_map: BTreeMap<String, DirectoryCensus> = dir_census
        .drain(..)
        .map(|c| (c.directory.clone(), c))
        .collect();

    for f in &findings {
        let bucket = non_lean_bucket_for_path(&f.path);
        let entry = census_map
            .entry(bucket.clone())
            .or_insert_with(|| DirectoryCensus {
                directory: bucket,
                ..Default::default()
            });
        // Note: `run_lean_lints` already populated `findings_count`? Let's recompute cleanly from `findings`!
        let _ = entry;
    }

    // Recompute per-directory finding tallies cleanly so Lean + non-Lean counts are exact
    for c in census_map.values_mut() {
        c.findings_count = 0;
        c.error_count = 0;
        c.warning_count = 0;
    }
    for f in &findings {
        let bucket = non_lean_bucket_for_path(&f.path);
        let entry = census_map
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

    let mut errors = 0usize;
    let mut warnings = 0usize;
    let mut by_rule: BTreeMap<String, usize> = BTreeMap::new();
    let mut by_artifact_kind: BTreeMap<String, usize> = BTreeMap::new();
    let mut by_regime: BTreeMap<String, usize> = BTreeMap::new();
    let mut by_sink: BTreeMap<String, usize> = BTreeMap::new();

    for f in &findings {
        match f.severity {
            Severity::Error => errors += 1,
            Severity::Warning => warnings += 1,
            Severity::Info => {}
        }
        *by_rule.entry(f.rule_id.clone()).or_insert(0) += 1;
        *by_artifact_kind
            .entry(f.artifact_kind.code().to_string())
            .or_insert(0) += 1;
        *by_regime
            .entry(f.max_regime.as_str().to_string())
            .or_insert(0) += 1;
        if let Some(sink) = f.sink {
            *by_sink.entry(sink.as_str().to_string()).or_insert(0) += 1;
        }
    }

    let directory_census: Vec<DirectoryCensus> = census_map.into_values().collect();
    let files_scanned = lean_file_count + obend_count + py_count + rs_count + md_count;

    Ok(LintReport {
        repo_root: canon.to_string_lossy().to_string(),
        generated_at: Utc::now().to_rfc3339(),
        files_scanned,
        lean_declarations_indexed: lean_decls,
        lean_inductives_indexed: lean_inds,
        total_findings: findings.len(),
        errors,
        warnings,
        tier1_guards,
        tier1_teeth,
        tier1_evals,
        by_rule,
        by_artifact_kind,
        by_regime,
        by_sink,
        directory_census,
        modularity,
        findings,
    })
}

/// Filter an existing `LintReport` by rule substring (`--rule`).
pub fn filter_report_by_rule(mut report: LintReport, filter: &str) -> LintReport {
    let filtered: Vec<Finding> = report
        .findings
        .into_iter()
        .filter(|f| f.rule_id.contains(filter))
        .collect();
    report.total_findings = filtered.len();
    report.errors = filtered
        .iter()
        .filter(|f| f.severity == Severity::Error)
        .count();
    report.warnings = filtered
        .iter()
        .filter(|f| f.severity == Severity::Warning)
        .count();
    report.by_rule.clear();
    report.by_artifact_kind.clear();
    report.by_regime.clear();
    report.by_sink.clear();
    for f in &filtered {
        *report.by_rule.entry(f.rule_id.clone()).or_insert(0) += 1;
        *report
            .by_artifact_kind
            .entry(f.artifact_kind.code().to_string())
            .or_insert(0) += 1;
        *report
            .by_regime
            .entry(f.max_regime.as_str().to_string())
            .or_insert(0) += 1;
        if let Some(sink) = f.sink {
            *report.by_sink.entry(sink.as_str().to_string()).or_insert(0) += 1;
        }
    }
    report.findings = filtered;
    report
}

fn non_lean_bucket_for_path(rel_path: &str) -> String {
    let trimmed = rel_path.strip_prefix("lean/").unwrap_or(rel_path);
    let parts: Vec<&str> = trimmed.split('/').collect();
    if parts.first() == Some(&"Obend") && parts.len() >= 3 {
        format!("Obend/{}", parts[1])
    } else if parts.first() == Some(&"crates") && parts.len() >= 2 {
        format!("crates/{}", parts[1])
    } else if parts.first() == Some(&"tests") && parts.len() >= 2 {
        format!("tests/{}", parts[1])
    } else if parts.first() == Some(&"apps") && parts.len() >= 2 {
        format!("apps/{}", parts[1])
    } else if parts.len() >= 2 {
        parts[0].to_string()
    } else if rel_path.ends_with(".md") {
        "docs-root".to_string()
    } else {
        "root".to_string()
    }
}
