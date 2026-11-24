//! `obb pipeline` — Two-Stage `[HypothesisLedger]` Interface-Lock & Swarm Proof-Fill Verifier.
//!
//! Enforces disciplined parallel `/swarm` execution without `sorry` or `axiom` smuggling:
//! - `STAGE_A_LOCKED`: Signatures and Apex composition theorems compile cleanly with explicit
//!   `[HypothesisLedger ...]` / `@[obb_obligation]` typeclass parameters (`0 sorry`, `0 axiom`) —
//!   safe to fan out producer and consumer `/swarm` workers simultaneously.
//! - `STAGE_B_SEALED`: Every `HypothesisLedger` / `@[obb_obligation]` class has a concrete,
//!   non-vacuous, acyclic discharged `instance` (`0 sorry`, `0 axiom`) — ready for `Landed -> Claimed`.
//! - `FAILED`: Immediate refusal if any worker smuggled `sorry` or `axiom`, left a cyclic instance
//!   loop (`[LedgerA] -> LedgerB -> LedgerA`), or instantiated an obligation over an uninhabited
//!   (`Empty` / `False` / 0-constructor) carrier witness.
//!
//! A repository without obligation classes is classified by [`PipelineLedgerBasis`]: its own Apex
//! manifest (`obb-apex.toml`, `quarry/obend-apex.toml` or a single `quarry/*-apex.toml`) seals it
//! only when every registered apex theorem verifies, and a present manifest that fails verification
//! is `FAILED` even under `--allow-empty`. Without a manifest, the report separates zero theorem
//! declarations, undeclared theorems and an explicit `--allow-empty` override.

use anyhow::{Context, Result, ensure};
use chrono::Utc;
use obb_lint::apex::{
    self, ApexCheckOptions, ApexManifestDiscovery, QUARRY_APEX_MANIFEST_PATTERN,
    discover_repo_apex_manifest, evaluate_apex_with_index,
};
use obb_lint::lean_index::{BinderParam, DeclKind, LeanIndex, ParsedLeanDecl, build_lean_index};
use obb_lint::lean_lexer::{LeanToken, LeanTokenKind};
use obb_lint::lean_rules::is_teeth_or_test_path;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::path::Path;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PipelineStage {
    #[serde(rename = "STAGE_A_LOCKED")]
    StageALocked,
    #[serde(rename = "STAGE_B_SEALED")]
    StageBSealed,
    #[serde(
        rename = "UNDECLARED",
        alias = "NO_LEDGER_CLASSES",
        alias = "STAGE_B_EMPTY"
    )]
    Undeclared,
    #[serde(rename = "FAILED")]
    Failed,
}

impl PipelineStage {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::StageALocked => "STAGE_A_LOCKED",
            Self::StageBSealed => "STAGE_B_SEALED",
            Self::Undeclared => "UNDECLARED",
            Self::Failed => "FAILED",
        }
    }
}

impl fmt::Display for PipelineStage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct PipelineCheckOptions {
    /// Refuse (`passed == false`) on `UNDECLARED`, and require zero unwired leaf islands when an
    /// Apex manifest is the ledger basis.
    pub strict: bool,
    /// Allow `STAGE_B_SEALED` with `0` obligation classes and no Apex manifest. The report records
    /// the override. A present Apex manifest must verify with zero unwired islands.
    pub allow_empty: bool,
}

/// The evidence a pipeline stage rests on, so an `--allow-empty` seal or an empty theorem tree
/// is never mistaken for verified coverage.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum PipelineLedgerBasis {
    /// `*Obligations` / `HypothesisLedger` / `@[obb_obligation]` classes were discovered.
    ObligationClasses,
    /// No obligation classes; the repository's own Apex manifest was checked against its Lean
    /// index. All counts are `0` when the manifest could not be resolved or loaded.
    ApexManifest {
        manifest_path: String,
        registered_apex_count: usize,
        valid_apex_count: usize,
        unwired_island_count: usize,
    },
    /// No obligation classes, no Apex manifest, and `--allow-empty` was requested.
    AllowEmptyOverride,
    /// No obligation classes, no Apex manifest, and no non-test theorem declarations.
    ZeroDeclarations,
    /// Non-test theorem declarations exist, but neither obligation classes nor an Apex manifest
    /// account for them.
    UndeclaredTheorems,
}

impl PipelineLedgerBasis {
    /// The serialized `kind` tag.
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::ObligationClasses => "obligation_classes",
            Self::ApexManifest { .. } => "apex_manifest",
            Self::AllowEmptyOverride => "allow_empty_override",
            Self::ZeroDeclarations => "zero_declarations",
            Self::UndeclaredTheorems => "undeclared_theorems",
        }
    }
}

impl fmt::Display for PipelineLedgerBasis {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PipelineViolation {
    pub kind: String,
    pub path: String,
    pub line: usize,
    pub symbol: String,
    pub message: String,
    pub remediation: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsumerSite {
    pub symbol: String,
    pub path: String,
    pub line: usize,
    pub ledger_class: String,
    #[serde(default)]
    pub carrier_args: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DischargingInstance {
    pub instance_name: String,
    pub path: String,
    pub line: usize,
    pub target_class: String,
    pub target_args: Vec<String>,
    #[serde(default)]
    pub normalized_args: Vec<String>,
    pub depends_on_ledgers: Vec<String>,
    #[serde(default)]
    pub depends_on_applications: Vec<(String, Vec<String>)>,
    pub witness_inhabited: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LedgerObligationStatus {
    pub class_name: String,
    pub fq_name: String,
    pub path: String,
    pub line: usize,
    pub field_count: usize,
    pub consumer_count: usize,
    #[serde(default)]
    pub required_carriers: Vec<Vec<String>>,
    #[serde(default)]
    pub unsealed_carriers: Vec<Vec<String>>,
    pub discharging_instances: Vec<DischargingInstance>,
    pub discharged: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PipelineReport {
    pub repo_root: String,
    pub checked_at: String,
    pub stage: PipelineStage,
    pub passed: bool,
    pub ready_for_parallel_swarm: bool,
    pub ready_for_claimed: bool,
    pub ledger_basis: PipelineLedgerBasis,
    /// `true` only when `--allow-empty` produced `STAGE_B_SEALED`: no obligation classes and no
    /// Apex manifest verified anything.
    pub allow_empty_override: bool,
    /// `theorem` / `lemma` declarations in the Lean index outside test-only paths.
    pub theorem_declaration_count: usize,
    pub smuggled_sorry_count: usize,
    pub smuggled_axiom_count: usize,
    pub total_obligations: usize,
    pub sealed_obligations: usize,
    pub open_stage_a_obligations: usize,
    pub consumer_sites: Vec<ConsumerSite>,
    pub obligations: Vec<LedgerObligationStatus>,
    pub violations: Vec<PipelineViolation>,
}

fn is_test_only_path(rel_path: &str) -> bool {
    rel_path.contains("/tests/")
        || rel_path.starts_with("tests/")
        || rel_path.starts_with("lean/tests/")
        || rel_path.ends_with("Test.lean")
        || rel_path.ends_with("Tests.lean")
}

fn is_planted_sorry_fixture_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower.contains("planted_sorry") || lower.contains("plantedsorry")
}

fn is_ledger_class_name(name: &str) -> bool {
    let short = name.rsplit('.').next().unwrap_or(name);
    short == "HypothesisLedger"
        || short.contains("HypothesisLedger")
        || short == "Obligations"
        || short.ends_with("Obligations")
}

fn is_dummy_unit_ident(ident: &str) -> bool {
    let short = ident.rsplit('.').next().unwrap_or(ident);
    matches!(short, "Unit" | "PUnit" | "True" | "unit")
        || matches!(ident, "()" | "Unit.unit" | "PUnit.unit" | "True.intro")
}

/// Trivial primitive/toy carriers (`Unit`, `PUnit`, `Bool`, `Nat`, `True`) that must NEVER seal
/// a type-parameterized production obligation class.
fn is_trivial_type_carrier_ident(ident: &str) -> bool {
    let short = ident.rsplit('.').next().unwrap_or(ident);
    is_dummy_unit_ident(ident) || matches!(short, "Bool" | "Nat")
}

fn is_trivial_type_carrier_expr(expr: &str) -> bool {
    if expr == "()" {
        return true;
    }
    let parts: Vec<&str> = expr
        .split(['(', ')', ',', ' ', '×'])
        .filter(|s| !s.is_empty())
        .collect();
    if parts.is_empty() {
        return false;
    }
    let all_trivial_or_wrapper = parts.iter().all(|p| {
        let short = p.rsplit('.').next().unwrap_or(p);
        is_trivial_type_carrier_ident(p) || matches!(short, "PLift" | "ULift" | "Prod" | "PProd")
    });
    let has_trivial_core = parts.iter().any(|p| is_trivial_type_carrier_ident(p));
    all_trivial_or_wrapper && has_trivial_core
}

fn is_concrete_scalar_lit(arg: &str) -> bool {
    arg.chars().all(|c| c.is_ascii_digit() || c == '_') && !arg.is_empty()
        || matches!(
            arg,
            "()" | "true"
                | "false"
                | "Bool.true"
                | "Bool.false"
                | "Nat.zero"
                | "Unit.unit"
                | "PUnit.unit"
                | "True.intro"
        )
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ClassParamKind {
    TypeCarrier,
    ValueCarrier(String),
}

fn classify_class_params(binders: &[BinderParam]) -> Vec<ClassParamKind> {
    let mut out = Vec::new();
    for b in binders {
        if b.is_instance_bracket {
            continue;
        }
        let kind = match binder_head_type(&b.type_tokens) {
            None => ClassParamKind::TypeCarrier,
            Some(h) => {
                let short = h.rsplit('.').next().unwrap_or(h);
                if matches!(short, "Type" | "Sort" | "Prop") {
                    ClassParamKind::TypeCarrier
                } else {
                    ClassParamKind::ValueCarrier(short.to_string())
                }
            }
        };
        out.push(kind);
    }
    out
}

fn extract_extended_parents(type_tokens: &[LeanToken]) -> Vec<String> {
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
            LeanTokenKind::Symbol(s) if after_extends && depth == 0 && s == ":" => {
                break;
            }
            LeanTokenKind::Ident(s) if after_extends && depth == 0 && s == "where" => {
                break;
            }
            LeanTokenKind::Ident(id) if after_extends && depth == 0 && expect_head => {
                parents.push(id.clone());
                expect_head = false;
            }
            _ => {}
        }
    }
    parents
}

fn tokens_have_unquoted_sorry(tokens: &[LeanToken]) -> Option<usize> {
    let mut quote_depth = 0usize;
    for tok in tokens {
        match &tok.kind {
            LeanTokenKind::SyntaxQuoteOpen => {
                quote_depth += 1;
            }
            LeanTokenKind::Symbol(s)
                if quote_depth > 0 && matches!(s.as_str(), "(" | "[" | "{") =>
            {
                quote_depth += 1;
            }
            LeanTokenKind::Symbol(s)
                if quote_depth > 0 && matches!(s.as_str(), ")" | "]" | "}") =>
            {
                quote_depth -= 1;
            }
            LeanTokenKind::Ident(id) if quote_depth == 0 && (id == "sorry" || id == "sorryAx") => {
                return Some(tok.line);
            }
            _ => {}
        }
    }
    None
}

fn find_sorry_in_decl(decl: &ParsedLeanDecl) -> Option<usize> {
    if let Some(l) = tokens_have_unquoted_sorry(&decl.type_tokens) {
        return Some(l);
    }
    if let Some(l) = tokens_have_unquoted_sorry(&decl.body_tokens) {
        return Some(l);
    }
    for wf in &decl.where_fields {
        if let Some(l) = tokens_have_unquoted_sorry(&wf.rhs_tokens) {
            return Some(l);
        }
    }
    for sf in &decl.struct_fields {
        if let Some(l) = tokens_have_unquoted_sorry(&sf.type_tokens) {
            return Some(l);
        }
    }
    None
}

/// Extract the head class name and top-level argument expressions from an instance or `[...]` binder type.
fn parse_head_class_and_args(tokens: &[LeanToken]) -> Option<(String, Vec<String>)> {
    // Skip leading `∀ ... ,` or `(x : T) →` if polymorphic instance type
    let mut start = 0usize;
    let mut depth = 0isize;
    for (idx, tok) in tokens.iter().enumerate() {
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

    let tail = &tokens[start..];
    let mut head_class: Option<String> = None;
    let mut args = Vec::new();
    let mut idx = 0usize;
    while idx < tail.len() {
        match &tail[idx].kind {
            LeanTokenKind::Ident(id)
                if matches!(id.as_str(), "where")
                    || (head_class.is_none()
                        && matches!(id.as_str(), "∀" | "forall" | "outParam" | "semiOutParam")) =>
            {
                if id == "where" {
                    break;
                }
                idx += 1;
            }
            LeanTokenKind::Symbol(s) if s == ":=" => break,
            LeanTokenKind::NatLit(n) if head_class.is_some() => {
                args.push(n.clone());
                idx += 1;
            }
            LeanTokenKind::Ident(id) => {
                if matches!(id.as_str(), "outParam" | "semiOutParam") {
                    idx += 1;
                    continue;
                }
                if head_class.is_none() {
                    head_class = Some(id.clone());
                } else {
                    args.push(id.clone());
                }
                idx += 1;
            }
            LeanTokenKind::Symbol(s) if s == "(" && head_class.is_some() => {
                let mut pdepth = 1usize;
                idx += 1;
                let mut inner_idents = Vec::new();
                while idx < tail.len() && pdepth > 0 {
                    match &tail[idx].kind {
                        LeanTokenKind::Symbol(ps) if ps == "(" => pdepth += 1,
                        LeanTokenKind::Symbol(ps) if ps == ")" => pdepth -= 1,
                        LeanTokenKind::Ident(pid)
                            if !matches!(pid.as_str(), "outParam" | "semiOutParam") =>
                        {
                            inner_idents.push(pid.clone());
                        }
                        LeanTokenKind::NatLit(n) => {
                            inner_idents.push(n.clone());
                        }
                        _ => {}
                    }
                    idx += 1;
                }
                if inner_idents.is_empty() {
                    args.push("()".to_string());
                } else if inner_idents.len() == 1 {
                    args.push(inner_idents.remove(0));
                } else {
                    let head = inner_idents.remove(0);
                    args.push(format!("{head}({})", inner_idents.join(",")));
                }
            }
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "{" | "[") => {
                let close = if s == "{" { "}" } else { "]" };
                let mut bdepth = 1usize;
                idx += 1;
                while idx < tail.len() && bdepth > 0 {
                    match &tail[idx].kind {
                        LeanTokenKind::Symbol(bs) if bs == s => bdepth += 1,
                        LeanTokenKind::Symbol(bs) if bs == close => bdepth -= 1,
                        _ => {}
                    }
                    idx += 1;
                }
            }
            _ => {
                idx += 1;
            }
        }
    }
    head_class.map(|c| (c, args))
}

fn binder_head_type(tokens: &[LeanToken]) -> Option<&str> {
    for tok in tokens {
        if let LeanTokenKind::Ident(id) = &tok.kind {
            if matches!(id.as_str(), "outParam" | "semiOutParam") {
                continue;
            }
            return Some(id.as_str());
        }
    }
    None
}

fn normalize_single_ident(ident: &str, binder_map: &HashMap<&str, String>) -> String {
    if let Some(mapped) = binder_map.get(ident) {
        return mapped.clone();
    }
    ident.rsplit('.').next().unwrap_or(ident).to_string()
}

fn normalize_carrier_args(raw_args: &[String], binders: &[BinderParam]) -> Vec<String> {
    let mut binder_map: HashMap<&str, String> = HashMap::new();
    for b in binders {
        if b.is_instance_bracket {
            continue;
        }
        let mapped = match binder_head_type(&b.type_tokens) {
            None => "*".to_string(),
            Some(h) => {
                let short = h.rsplit('.').next().unwrap_or(h);
                if matches!(short, "Type" | "Sort" | "Prop") {
                    "*".to_string()
                } else {
                    format!("*:{short}")
                }
            }
        };
        if !b.is_underscore && b.name != "_" {
            binder_map.insert(b.name.as_str(), mapped);
        }
    }

    raw_args
        .iter()
        .map(|arg| {
            if arg == "()" {
                "()".to_string()
            } else if let Some((head, rest)) = arg.split_once('(') {
                let inner = rest.strip_suffix(')').unwrap_or(rest);
                let norm_head = normalize_single_ident(head, &binder_map);
                let norm_inner: Vec<String> = inner
                    .split(',')
                    .filter(|s| !s.is_empty())
                    .map(|s| normalize_single_ident(s, &binder_map))
                    .collect();
                format!("{norm_head}({})", norm_inner.join(","))
            } else {
                normalize_single_ident(arg, &binder_map)
            }
        })
        .collect()
}

/// Returns `true` when an instance's normalized carrier tuple `inst_args` covers `req_args`.
/// - A universal type parameter `"*"` in `inst_args` covers any carrier in `req_args`.
/// - A universally quantified value parameter `"*:T"` in `inst_args` covers `"*:T"` or a concrete
///   term of that parameter slot, whereas a concrete value or concrete carrier (`"ToyPCS"`) NEVER
///   covers a different concrete carrier (`"CanopyPCS"`) or a universal requirement (`"*"` / `"*:T"`).
fn carrier_args_cover(inst_args: &[String], req_args: &[String]) -> bool {
    if inst_args.len() != req_args.len() {
        return false;
    }
    inst_args.iter().zip(req_args.iter()).all(|(ia, ra)| {
        ia == "*" || ia == ra || (ia.starts_with("*:") && ra != "*" && !ra.starts_with("*:"))
    })
}

fn unverified_apex_manifest_violation(
    path: &str,
    symbol: &str,
    message: String,
    remediation: String,
) -> PipelineViolation {
    PipelineViolation {
        kind: "unverified_apex_manifest".to_string(),
        path: path.to_string(),
        line: 1,
        symbol: symbol.to_string(),
        message,
        remediation,
    }
}

fn unresolved_apex_basis(manifest_path: &str) -> PipelineLedgerBasis {
    PipelineLedgerBasis::ApexManifest {
        manifest_path: manifest_path.to_string(),
        registered_apex_count: 0,
        valid_apex_count: 0,
        unwired_island_count: 0,
    }
}

/// Classify a repository that declares no obligation classes. A present Apex manifest is the
/// basis and must verify. Each failure adds an `unverified_apex_manifest` violation.
fn classify_without_obligation_classes(
    root: &Path,
    index: &LeanIndex,
    opts: PipelineCheckOptions,
    theorem_declaration_count: usize,
    violations: &mut Vec<PipelineViolation>,
) -> PipelineLedgerBasis {
    let manifest_rel = match discover_repo_apex_manifest(root) {
        Ok(ApexManifestDiscovery::Absent) => {
            let basis = if opts.allow_empty {
                PipelineLedgerBasis::AllowEmptyOverride
            } else if theorem_declaration_count == 0 {
                PipelineLedgerBasis::ZeroDeclarations
            } else {
                PipelineLedgerBasis::UndeclaredTheorems
            };
            return basis;
        }
        Ok(ApexManifestDiscovery::Found { rel_path }) => rel_path,
        Ok(ApexManifestDiscovery::Ambiguous { candidates }) => {
            violations.push(unverified_apex_manifest_violation(
                "quarry",
                QUARRY_APEX_MANIFEST_PATTERN,
                format!(
                    "{} Apex manifests match `{QUARRY_APEX_MANIFEST_PATTERN}` ({}) and none is `{}` or `{}`, so no single manifest is authoritative",
                    candidates.len(),
                    candidates.join(", "),
                    apex::REPO_ROOT_APEX_MANIFEST_REL,
                    apex::DEFAULT_APEX_MANIFEST_REL
                ),
                format!(
                    "Name the authoritative manifest `{}` at the repository root, or keep exactly one `{QUARRY_APEX_MANIFEST_PATTERN}`.",
                    apex::REPO_ROOT_APEX_MANIFEST_REL
                ),
            ));
            return unresolved_apex_basis(QUARRY_APEX_MANIFEST_PATTERN);
        }
        Err(e) => {
            violations.push(unverified_apex_manifest_violation(
                "quarry",
                QUARRY_APEX_MANIFEST_PATTERN,
                format!("Cannot resolve the repository's Apex manifest: {e:#}"),
                "Check the manifest paths and directory permissions.".to_string(),
            ));
            return unresolved_apex_basis(QUARRY_APEX_MANIFEST_PATTERN);
        }
    };

    let manifest = match apex::ApexManifest::load_from_path(&root.join(&manifest_rel)) {
        Ok(manifest) => manifest,
        Err(e) => {
            violations.push(unverified_apex_manifest_violation(
                &manifest_rel,
                &manifest_rel,
                format!("Apex manifest `{manifest_rel}` cannot be loaded: {e:#}"),
                "Fix the manifest so it parses and registers at least one `[[apex]]` theorem."
                    .to_string(),
            ));
            return unresolved_apex_basis(&manifest_rel);
        }
    };

    let strict_islands = opts.strict || opts.allow_empty;
    let report = evaluate_apex_with_index(
        &root.to_string_lossy(),
        index,
        &manifest,
        ApexCheckOptions {
            strict_islands,
            max_islands: None,
        },
    );
    let verified = report.registered_apex_count > 0 && report.check_passed;
    if !verified {
        let mut reasons = report.failure_reasons;
        if reasons.is_empty() {
            reasons.push(format!(
                "{} of {} registered apex theorem(s) verified",
                report.valid_apex_count, report.registered_apex_count
            ));
        }
        let strict_flag = if strict_islands {
            " --strict-islands"
        } else {
            ""
        };
        for reason in reasons {
            violations.push(unverified_apex_manifest_violation(
                &manifest_rel,
                &manifest.target_name,
                format!("Apex manifest `{manifest_rel}` does not verify: {reason}"),
                format!(
                    "Run `obb apex check --repo {} --manifest {}{strict_flag}` for per-theorem offenders and unwired leaf islands, then repair the apex cone or the manifest; `--allow-empty` never bypasses a present Apex manifest.",
                    root.display(), root.join(&manifest_rel).display()
                ),
            ));
        }
    }
    PipelineLedgerBasis::ApexManifest {
        manifest_path: manifest_rel,
        registered_apex_count: report.registered_apex_count,
        valid_apex_count: report.valid_apex_count,
        unwired_island_count: report.unwired_island_count,
    }
}

pub fn check_pipeline(repo_root: &Path) -> Result<PipelineReport> {
    check_pipeline_with_options(repo_root, PipelineCheckOptions::default())
}

pub fn check_pipeline_with_options(
    repo_root: &Path,
    opts: PipelineCheckOptions,
) -> Result<PipelineReport> {
    let canon = repo_root
        .canonicalize()
        .with_context(|| format!("cannot resolve pipeline repository {}", repo_root.display()))?;
    ensure!(
        canon.is_dir(),
        "pipeline repository {} must be a directory",
        canon.display()
    );
    let index = build_lean_index(&canon);
    Ok(check_pipeline_with_index_and_options(&canon, &index, opts))
}

pub fn check_pipeline_with_index(repo_root: &str, index: &LeanIndex) -> PipelineReport {
    check_pipeline_with_index_and_options(repo_root, index, PipelineCheckOptions::default())
}

/// `repo_root` is the directory `index` was built from; its Apex manifest is read from there when
/// no obligation classes are declared, and verified against `index` without re-parsing.
pub fn check_pipeline_with_index_and_options(
    repo_root: impl AsRef<Path>,
    index: &LeanIndex,
    opts: PipelineCheckOptions,
) -> PipelineReport {
    let repo_root = repo_root.as_ref();
    let mut violations = Vec::new();
    let mut theorem_declaration_count = 0;
    let mut smuggled_sorry_count = 0usize;
    let mut smuggled_axiom_count = 0usize;

    // Collect empty (0-constructor) inductives in the index to detect uninhabited carrier witnesses
    let mut zero_ctor_inductives: HashSet<String> = HashSet::from([
        "False".to_string(),
        "Empty".to_string(),
        "PEmpty".to_string(),
    ]);
    for file in &index.files {
        if is_test_only_path(&file.rel_path) {
            continue;
        }
        for decl in &file.declarations {
            if decl.kind == DeclKind::Inductive && decl.constructors.is_empty() {
                zero_ctor_inductives.insert(decl.name.clone());
                zero_ctor_inductives.insert(decl.fq_name.clone());
            }
        }
    }

    // Pass 1: Enforce zero smuggled `sorry` / `axiom`, and discover all
    // `HypothesisLedger` / `*Obligations` / `@[obb_obligation]` classes (plus subclasses via `extends`).
    #[derive(Clone)]
    struct DiscoveredClass {
        short_name: String,
        fq_name: String,
        path: String,
        line: usize,
        field_count: usize,
        has_extends: bool,
        explicit_param_count: usize,
        param_kinds: Vec<ClassParamKind>,
    }

    let mut ledger_classes: BTreeMap<String, DiscoveredClass> = BTreeMap::new();
    let mut short_to_key: HashMap<String, String> = HashMap::new();
    let mut candidate_subclasses: Vec<(&str, &ParsedLeanDecl, Vec<String>)> = Vec::new();
    let mut extended_parent_keys: HashSet<String> = HashSet::new();

    let count_explicit_params = |binders: &[BinderParam]| -> usize {
        binders.iter().filter(|b| !b.is_instance_bracket).count()
    };

    for file in &index.files {
        if is_test_only_path(&file.rel_path) {
            continue;
        }
        let count_theorems = !is_teeth_or_test_path(&file.rel_path);
        for decl in &file.declarations {
            if count_theorems && decl.kind == DeclKind::Theorem {
                theorem_declaration_count += 1;
            }
            if decl.fixture_kept {
                continue;
            }

            if decl.kind == DeclKind::Axiom {
                smuggled_axiom_count += 1;
                violations.push(PipelineViolation {
                    kind: "smuggled_axiom".to_string(),
                    path: file.rel_path.clone(),
                    line: decl.line,
                    symbol: decl.fq_name.clone(),
                    message: format!(
                        "Declared `axiom {}` smuggles an unverified global assumption outside `[HypothesisLedger]` / `*Obligations`",
                        decl.fq_name
                    ),
                    remediation: "Delete `axiom` and express cross-shard interface assumptions as an explicit `class *Obligations` / `HypothesisLedger` typeclass parameter.".to_string(),
                });
            } else if !is_planted_sorry_fixture_name(&decl.name)
                && let Some(sline) = find_sorry_in_decl(decl)
            {
                smuggled_sorry_count += 1;
                violations.push(PipelineViolation {
                        kind: "smuggled_sorry".to_string(),
                        path: file.rel_path.clone(),
                        line: sline,
                        symbol: decl.fq_name.clone(),
                        message: format!(
                            "Declaration `{}` smuggles `sorry`/`sorryAx` instead of an explicit `[HypothesisLedger]` / `*Obligations` interface obligation",
                            decl.fq_name
                        ),
                        remediation: "Remove `sorry`; parameterize Stage-A consumer theorems over `[HypothesisLedger ...]` / `[*Obligations ...]` and discharge the instance in Stage B.".to_string(),
                    });
            }

            let has_obl_attr = decl.attributes.iter().any(|a| a == "obb_obligation");
            if decl.kind == DeclKind::Class {
                let parents = extract_extended_parents(&decl.type_tokens);
                let has_extends = !parents.is_empty()
                    || decl
                        .type_tokens
                        .iter()
                        .any(|t| matches!(&t.kind, LeanTokenKind::Ident(s) if s == "extends"));
                let extends_named_ledger = parents.iter().any(|p| is_ledger_class_name(p));
                if is_ledger_class_name(&decl.name) || has_obl_attr || extends_named_ledger {
                    for p in &parents {
                        if let Some(pk) = short_to_key.get(p.as_str()).or_else(|| {
                            short_to_key.get(p.rsplit('.').next().unwrap_or(p.as_str()))
                        }) {
                            extended_parent_keys.insert(pk.clone());
                        } else {
                            extended_parent_keys.insert(p.clone());
                            extended_parent_keys
                                .insert(p.rsplit('.').next().unwrap_or(p.as_str()).to_string());
                        }
                    }
                    let entry = DiscoveredClass {
                        short_name: decl.name.clone(),
                        fq_name: decl.fq_name.clone(),
                        path: file.rel_path.clone(),
                        line: decl.line,
                        field_count: decl.struct_fields.len(),
                        has_extends,
                        explicit_param_count: count_explicit_params(&decl.binders),
                        param_kinds: classify_class_params(&decl.binders),
                    };
                    short_to_key.insert(decl.name.clone(), decl.fq_name.clone());
                    short_to_key.insert(decl.fq_name.clone(), decl.fq_name.clone());
                    ledger_classes.insert(decl.fq_name.clone(), entry);
                } else if !parents.is_empty() {
                    candidate_subclasses.push((&file.rel_path, decl, parents));
                }
            } else if has_obl_attr
                && matches!(
                    decl.kind,
                    DeclKind::Theorem | DeclKind::Def | DeclKind::Structure
                )
            {
                // Non-class `@[obb_obligation]` stub: track as an obligation entry
                let entry = DiscoveredClass {
                    short_name: decl.name.clone(),
                    fq_name: decl.fq_name.clone(),
                    path: file.rel_path.clone(),
                    line: decl.line,
                    field_count: decl.struct_fields.len().max(1),
                    has_extends: false,
                    explicit_param_count: count_explicit_params(&decl.binders),
                    param_kinds: classify_class_params(&decl.binders),
                };
                short_to_key.insert(decl.name.clone(), decl.fq_name.clone());
                short_to_key.insert(decl.fq_name.clone(), decl.fq_name.clone());
                ledger_classes.insert(decl.fq_name.clone(), entry);
            }
        }
    }

    // Transitively include classes that `extends` a discovered obligation class
    loop {
        let mut added = false;
        for (rel_path, decl, parents) in &candidate_subclasses {
            if ledger_classes.contains_key(&decl.fq_name) {
                continue;
            }
            let mut matched_parents = Vec::new();
            for p in parents {
                let short_p = p.rsplit('.').next().unwrap_or(p.as_str());
                if let Some(pk) = short_to_key
                    .get(p.as_str())
                    .or_else(|| short_to_key.get(short_p))
                {
                    matched_parents.push(pk.clone());
                } else if is_ledger_class_name(p) {
                    matched_parents.push(p.clone());
                }
            }
            if !matched_parents.is_empty() {
                for pk in matched_parents {
                    extended_parent_keys.insert(pk);
                }
                let entry = DiscoveredClass {
                    short_name: decl.name.clone(),
                    fq_name: decl.fq_name.clone(),
                    path: (*rel_path).to_string(),
                    line: decl.line,
                    field_count: decl.struct_fields.len(),
                    has_extends: true,
                    explicit_param_count: count_explicit_params(&decl.binders),
                    param_kinds: classify_class_params(&decl.binders),
                };
                short_to_key.insert(decl.name.clone(), decl.fq_name.clone());
                short_to_key.insert(decl.fq_name.clone(), decl.fq_name.clone());
                ledger_classes.insert(decl.fq_name.clone(), entry);
                added = true;
            }
        }
        if !added {
            break;
        }
    }

    let resolve_ledger_key = |ident: &str| -> Option<String> {
        if let Some(k) = short_to_key.get(ident) {
            return Some(k.clone());
        }
        let short = ident.rsplit('.').next().unwrap_or(ident);
        short_to_key.get(short).cloned()
    };

    // Pass 2: Scan consumer `[HypothesisLedger ...]` / `[*Obligations ...]` binders,
    // `variable [...]`, and discharging `instance`s keyed by `(class_key, normalized_args)`.
    let mut consumer_sites = Vec::new();
    let mut consumer_counts: HashMap<String, usize> = HashMap::new();
    let mut required_carriers_by_class: HashMap<String, BTreeSet<Vec<String>>> = HashMap::new();
    let mut instances_by_class: HashMap<String, Vec<DischargingInstance>> = HashMap::new();
    // Directed edges `class_key -> dep_class_key` across discharging instances
    let mut class_dep_edges: HashMap<String, BTreeSet<String>> = HashMap::new();
    // Track named ledger instances to catch mutual instance-body recursion (`instA` calls `instB` and `instB` calls `instA`)
    let mut inst_records: Vec<(String, String, String, usize, Vec<String>)> = Vec::new();

    let check_binder_for_consumer =
        |b: &BinderParam,
         scope_binders: &[BinderParam],
         owner_sym: &str,
         rel_path: &str,
         consumer_sites: &mut Vec<ConsumerSite>,
         consumer_counts: &mut HashMap<String, usize>,
         required_carriers_by_class: &mut HashMap<String, BTreeSet<Vec<String>>>,
         violations: &mut Vec<PipelineViolation>| {
            if !b.is_instance_bracket {
                return;
            }
            if let Some((head, raw_args)) = parse_head_class_and_args(&b.type_tokens) {
                if let Some(key) = resolve_ledger_key(&head) {
                    let norm_args = normalize_carrier_args(&raw_args, scope_binders);
                    *consumer_counts.entry(key.clone()).or_insert(0) += 1;
                    required_carriers_by_class
                        .entry(key.clone())
                        .or_default()
                        .insert(norm_args.clone());
                    consumer_sites.push(ConsumerSite {
                        symbol: owner_sym.to_string(),
                        path: rel_path.to_string(),
                        line: b.line,
                        ledger_class: key,
                        carrier_args: norm_args,
                    });
                } else if is_ledger_class_name(&head) {
                    violations.push(PipelineViolation {
                    kind: "undeclared_ledger_class".to_string(),
                    path: rel_path.to_string(),
                    line: b.line,
                    symbol: owner_sym.to_string(),
                    message: format!(
                        "`{}` assumes `[{} ...]` but no `class {}` is declared in the repository",
                        owner_sym, head, head
                    ),
                    remediation: "Declare the obligation `class` explicitly in the shared interface module.".to_string(),
                });
                }
            }
        };

    for file in &index.files {
        if is_test_only_path(&file.rel_path) {
            continue;
        }

        for sv in &file.section_variables {
            check_binder_for_consumer(
                sv,
                &file.section_variables,
                "<section-variable>",
                &file.rel_path,
                &mut consumer_sites,
                &mut consumer_counts,
                &mut required_carriers_by_class,
                &mut violations,
            );
        }

        for decl in &file.declarations {
            if decl.kind != DeclKind::Instance {
                let mut combined_binders = file.section_variables.clone();
                combined_binders.extend(decl.binders.iter().cloned());
                for b in &decl.binders {
                    check_binder_for_consumer(
                        b,
                        &combined_binders,
                        &decl.fq_name,
                        &file.rel_path,
                        &mut consumer_sites,
                        &mut consumer_counts,
                        &mut required_carriers_by_class,
                        &mut violations,
                    );
                }
                continue;
            }

            // Inspect `DeclKind::Instance`: does it target a `HypothesisLedger` / `*Obligations` / `@[obb_obligation]` class?
            let Some((target_head, target_args)) = parse_head_class_and_args(&decl.type_tokens)
            else {
                continue;
            };
            let Some(target_key) = resolve_ledger_key(&target_head) else {
                continue;
            };

            let cls_meta = ledger_classes.get(&target_key);
            let is_parameterized_obligation = cls_meta
                .map(|c| c.explicit_param_count > 0)
                .unwrap_or(!target_args.is_empty());

            let mut combined_binders = file.section_variables.clone();
            combined_binders.extend(decl.binders.iter().cloned());
            let normalized_args = normalize_carrier_args(&target_args, &combined_binders);

            // Check instance binders for:
            // (a) forwarding dependencies `[OtherLedger ...]` (with carrier args!)
            // (b) vacuous uninhabited premises `(h : False)` / `(x : EmptyCarrier)`
            let mut dep_ledgers = BTreeSet::new();
            let mut dep_applications: Vec<(String, Vec<String>)> = Vec::new();
            let mut witness_inhabited = true;

            // Track explicit binder names referenced in `target_args` so `(u : Unit) : FooObligations u` is caught as dummy carrier
            let referenced_arg_idents: HashSet<&str> = target_args
                .iter()
                .flat_map(|a| a.split(['(', ')', ',', ' ']))
                .filter(|s| !s.is_empty())
                .collect();

            let bound_value_names: HashSet<&str> = combined_binders
                .iter()
                .filter(|b| !b.is_instance_bracket && !b.is_underscore && b.name != "_")
                .map(|b| b.name.as_str())
                .collect();

            for b in &decl.binders {
                if b.is_instance_bracket {
                    if let Some((b_head, b_args)) = parse_head_class_and_args(&b.type_tokens)
                        && let Some(dep_key) = resolve_ledger_key(&b_head)
                    {
                        let dep_norm = normalize_carrier_args(&b_args, &combined_binders);
                        dep_ledgers.insert(dep_key.clone());
                        dep_applications.push((dep_key, dep_norm));
                    }
                } else {
                    let used_as_carrier =
                        !b.is_underscore && referenced_arg_idents.contains(b.name.as_str());
                    for tok in &b.type_tokens {
                        if let LeanTokenKind::Ident(tid) = &tok.kind {
                            let short_t = tid.rsplit('.').next().unwrap_or(tid.as_str());
                            if zero_ctor_inductives.contains(tid)
                                || zero_ctor_inductives.contains(short_t)
                            {
                                witness_inhabited = false;
                                violations.push(PipelineViolation {
                                    kind: "vacuous_instance_witness".to_string(),
                                    path: file.rel_path.clone(),
                                    line: decl.line,
                                    symbol: decl.fq_name.clone(),
                                    message: format!(
                                        "Instance `{}` for `{}` depends on uninhabited binder premise `{tid}`, discharging the obligation vacuously",
                                        decl.fq_name, target_key
                                    ),
                                    remediation: "Remove uninhabited binder premises (`False`/`Empty`/0-constructor inductives) and construct a real inhabited model.".to_string(),
                                });
                            } else if is_parameterized_obligation
                                && used_as_carrier
                                && is_dummy_unit_ident(tid)
                            {
                                witness_inhabited = false;
                                violations.push(PipelineViolation {
                                    kind: "trivial_carrier_instance".to_string(),
                                    path: file.rel_path.clone(),
                                    line: decl.line,
                                    symbol: decl.fq_name.clone(),
                                    message: format!(
                                        "Instance `{}` instantiates parameterized obligation `{}` over trivial dummy carrier `{tid}`",
                                        decl.fq_name, target_key
                                    ),
                                    remediation: "Discharge parameterized obligation classes on the real production carrier type, never on `Unit`, `PUnit`, or `True`.".to_string(),
                                });
                            }
                        }
                    }
                }
            }

            // Check if any type/carrier argument to the class is uninhabited (`VoidCarrier`) or a trivial carrier (`Unit`/`PUnit`/`Bool`/`Nat`/`True`)
            for (param_idx, arg) in target_args.iter().enumerate() {
                for sub_id in arg.split(['(', ')', ',', ' ']).filter(|s| !s.is_empty()) {
                    let short_a = sub_id.rsplit('.').next().unwrap_or(sub_id);
                    if zero_ctor_inductives.contains(sub_id)
                        || zero_ctor_inductives.contains(short_a)
                    {
                        witness_inhabited = false;
                        violations.push(PipelineViolation {
                            kind: "vacuous_instance_witness".to_string(),
                            path: file.rel_path.clone(),
                            line: decl.line,
                            symbol: decl.fq_name.clone(),
                            message: format!(
                                "Instance `{}` instantiates `{}` on uninhabited 0-constructor type `{sub_id}`",
                                decl.fq_name, target_key
                            ),
                            remediation: "Instantiate the obligation class on the real inhabited production carrier type.".to_string(),
                        });
                    }
                }

                if is_parameterized_obligation && !bound_value_names.contains(arg.as_str()) {
                    let param_kind = cls_meta
                        .and_then(|c| c.param_kinds.get(param_idx))
                        .cloned()
                        .unwrap_or(ClassParamKind::TypeCarrier);
                    let is_trivial = match &param_kind {
                        ClassParamKind::TypeCarrier => is_trivial_type_carrier_expr(arg),
                        ClassParamKind::ValueCarrier(expected_ty) => {
                            is_dummy_unit_ident(expected_ty)
                                || is_dummy_unit_ident(arg)
                                || (matches!(expected_ty.as_str(), "Bool" | "Nat")
                                    && is_concrete_scalar_lit(arg))
                        }
                    };
                    if is_trivial {
                        witness_inhabited = false;
                        violations.push(PipelineViolation {
                            kind: "trivial_carrier_instance".to_string(),
                            path: file.rel_path.clone(),
                            line: decl.line,
                            symbol: decl.fq_name.clone(),
                            message: format!(
                                "Instance `{}` attempts to seal parameterized obligation `{}` with trivial carrier `{arg}` (`Unit`/`PUnit`/`Bool`/`Nat`/`True`)",
                                decl.fq_name, target_key
                            ),
                            remediation: "Remove the trivial `Unit`/`PUnit`/`Bool`/`Nat` carrier instance and instantiate the obligation class on the production carrier.".to_string(),
                        });
                    }
                }
            }

            // Ensure body/where is non-empty and free of `sorry`
            if decl.body_tokens.is_empty() && decl.where_fields.is_empty() {
                witness_inhabited = false;
                violations.push(PipelineViolation {
                    kind: "vacuous_instance_witness".to_string(),
                    path: file.rel_path.clone(),
                    line: decl.line,
                    symbol: decl.fq_name.clone(),
                    message: format!(
                        "Instance `{}` for `{}` supplies no `where` fields or proof term",
                        decl.fq_name, target_key
                    ),
                    remediation:
                        "Provide concrete proof terms for all obligation fields in `where` or `:=`."
                            .to_string(),
                });
            }

            let mut body_idents = Vec::new();
            for tok in decl
                .body_tokens
                .iter()
                .chain(decl.where_fields.iter().flat_map(|w| w.rhs_tokens.iter()))
            {
                if let LeanTokenKind::Ident(id) = &tok.kind {
                    body_idents.push(id.clone());
                }
            }

            for dep in &dep_ledgers {
                class_dep_edges
                    .entry(target_key.clone())
                    .or_default()
                    .insert(dep.clone());
            }

            inst_records.push((
                decl.name.clone(),
                decl.fq_name.clone(),
                file.rel_path.clone(),
                decl.line,
                body_idents,
            ));

            instances_by_class
                .entry(target_key.clone())
                .or_default()
                .push(DischargingInstance {
                    instance_name: decl.fq_name.clone(),
                    path: file.rel_path.clone(),
                    line: decl.line,
                    target_class: target_key,
                    target_args,
                    normalized_args,
                    depends_on_ledgers: dep_ledgers.into_iter().collect(),
                    depends_on_applications: dep_applications,
                    witness_inhabited,
                });
        }
    }

    // Pass 3a: Detect cyclic class-to-class `[LedgerB] -> LedgerA` instance dependencies
    {
        let mut color: HashMap<&str, u8> = HashMap::new(); // 0=unvisited, 1=visiting, 2=done
        let mut stack_path: Vec<&str> = Vec::new();
        fn dfs_class_cycle<'a>(
            u: &'a str,
            edges: &'a HashMap<String, BTreeSet<String>>,
            color: &mut HashMap<&'a str, u8>,
            stack_path: &mut Vec<&'a str>,
            cycles: &mut Vec<Vec<String>>,
        ) {
            color.insert(u, 1);
            stack_path.push(u);
            if let Some(nbrs) = edges.get(u) {
                for v in nbrs {
                    let v_str = v.as_str();
                    match color.get(v_str).copied().unwrap_or(0) {
                        0 => dfs_class_cycle(v_str, edges, color, stack_path, cycles),
                        1 => {
                            let pos = stack_path.iter().position(|&x| x == v_str).unwrap_or(0);
                            let mut cyc: Vec<String> =
                                stack_path[pos..].iter().map(|s| (*s).to_string()).collect();
                            cyc.push(v_str.to_string());
                            cycles.push(cyc);
                        }
                        _ => {}
                    }
                }
            }
            stack_path.pop();
            color.insert(u, 2);
        }

        let mut cycles = Vec::new();
        for k in ledger_classes.keys() {
            if color.get(k.as_str()).copied().unwrap_or(0) == 0 {
                dfs_class_cycle(
                    k.as_str(),
                    &class_dep_edges,
                    &mut color,
                    &mut stack_path,
                    &mut cycles,
                );
            }
        }
        for cyc in cycles {
            let head = &cyc[0];
            let (path, line) = ledger_classes
                .get(head)
                .map(|c| (c.path.clone(), c.line))
                .unwrap_or_else(|| (String::new(), 1));
            violations.push(PipelineViolation {
                kind: "cyclic_instance_dependency".to_string(),
                path,
                line,
                symbol: head.clone(),
                message: format!(
                    "Cyclic obligation instance dependency detected: {}",
                    cyc.join(" -> ")
                ),
                remediation: "Break circular `[HypothesisLedger]` / `[*Obligations]` instance assumptions; discharge producer instances unconditionally from concrete module theorems.".to_string(),
            });
        }
    }

    // Pass 3b: Detect direct or mutual instance-body cycles (`instA` calls `instB` and `instB` calls `instA`, or `instA` calls `instA`)
    if !inst_records.is_empty() {
        let mut inst_idx_by_name: HashMap<&str, usize> = HashMap::new();
        for (idx, (short, fq, _, _, _)) in inst_records.iter().enumerate() {
            if !short.starts_with("inst@") {
                inst_idx_by_name.insert(short.as_str(), idx);
            }
            inst_idx_by_name.insert(fq.as_str(), idx);
        }
        let m = inst_records.len();
        let mut adj: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); m];
        for (u, (_, _, _, _, idents)) in inst_records.iter().enumerate() {
            for id in idents {
                if let Some(&v) = inst_idx_by_name.get(id.as_str()) {
                    adj[u].insert(v);
                } else {
                    let s = id.rsplit('.').next().unwrap_or(id.as_str());
                    if let Some(&v) = inst_idx_by_name.get(s) {
                        adj[u].insert(v);
                    }
                }
            }
        }
        let mut color = vec![0u8; m];
        let mut reported_cycle = HashSet::new();
        fn dfs_inst(
            u: usize,
            adj: &[BTreeSet<usize>],
            color: &mut [u8],
            found: &mut Vec<(usize, usize)>,
        ) {
            color[u] = 1;
            for &v in &adj[u] {
                if color[v] == 0 {
                    dfs_inst(v, adj, color, found);
                } else if color[v] == 1 {
                    found.push((u, v));
                }
            }
            color[u] = 2;
        }
        let mut back_edges = Vec::new();
        for u in 0..m {
            if color[u] == 0 {
                dfs_inst(u, &adj, &mut color, &mut back_edges);
            }
        }
        for (u, v) in back_edges {
            if reported_cycle.insert((u.min(v), u.max(v))) {
                let (_, fq_u, path_u, line_u, _) = &inst_records[u];
                let (_, fq_v, _, _, _) = &inst_records[v];
                violations.push(PipelineViolation {
                    kind: "cyclic_instance_dependency".to_string(),
                    path: path_u.clone(),
                    line: *line_u,
                    symbol: fq_u.clone(),
                    message: format!(
                        "Discharging obligation instance `{fq_u}` forms a cyclic body reference with `{fq_v}`"
                    ),
                    remediation: "Discharge obligation instances from non-cyclic constructive theorems.".to_string(),
                });
            }
        }
    }

    // Pass 4: Fixed-point resolution keyed by `(class_key, normalized_args)`!
    // An obligation class is sealed only when EVERY carrier tuple required by its consumer sites
    // is covered by a transitive, inhabited, non-dummy discharging instance.
    let mut active_applications: HashMap<String, Vec<Vec<String>>> = HashMap::new();
    let app_is_covered =
        |active: &HashMap<String, Vec<Vec<String>>>, cls: &str, req: &[String]| -> bool {
            active
                .get(cls)
                .map(|vec_args| vec_args.iter().any(|ia| carrier_args_cover(ia, req)))
                .unwrap_or(false)
        };

    loop {
        let mut progressed = false;
        for class_key in ledger_classes.keys() {
            if let Some(insts) = instances_by_class.get(class_key) {
                for inst in insts {
                    if !inst.witness_inhabited {
                        continue;
                    }
                    let already_recorded = active_applications
                        .get(class_key)
                        .map(|v| v.contains(&inst.normalized_args))
                        .unwrap_or(false);
                    if already_recorded {
                        continue;
                    }
                    let deps_ok = inst
                        .depends_on_applications
                        .iter()
                        .all(|(dep_cls, dep_args)| {
                            dep_cls != class_key
                                && app_is_covered(&active_applications, dep_cls, dep_args)
                        });
                    if deps_ok {
                        active_applications
                            .entry(class_key.clone())
                            .or_default()
                            .push(inst.normalized_args.clone());
                        progressed = true;
                    }
                }
            }
        }
        if !progressed {
            break;
        }
    }

    let mut obligations = Vec::with_capacity(ledger_classes.len());
    let mut sealed_obligations = 0usize;
    let mut open_stage_a_obligations = 0usize;

    for (key, cls) in &ledger_classes {
        let c_count = *consumer_counts.get(key).unwrap_or(&0);
        let is_extended_base =
            extended_parent_keys.contains(key) || extended_parent_keys.contains(&cls.short_name);
        if cls.field_count == 0 && !cls.has_extends {
            if is_extended_base && c_count == 0 && !instances_by_class.contains_key(key) {
                // Abstract 0-field base marker (`class HypothesisLedger : Prop`) extended by concrete obligation classes
                continue;
            }
            violations.push(PipelineViolation {
                kind: "vacuous_empty_ledger_class".to_string(),
                path: cls.path.clone(),
                line: cls.line,
                symbol: cls.fq_name.clone(),
                message: format!(
                    "Obligation class `{}` declares 0 fields and extends nothing, making any Stage-B instance vacuously trivial",
                    cls.fq_name
                ),
                remediation: "Add explicit proposition/witness fields to the obligation class before locking Stage A.".to_string(),
            });
        }

        let req_carriers: Vec<Vec<String>> = required_carriers_by_class
            .get(key)
            .map(|s| s.iter().cloned().collect())
            .unwrap_or_default();

        let (discharged, unsealed_carriers) = if !req_carriers.is_empty() {
            let unsealed: Vec<Vec<String>> = req_carriers
                .iter()
                .filter(|req| !app_is_covered(&active_applications, key, req))
                .cloned()
                .collect();
            (unsealed.is_empty(), unsealed)
        } else {
            let has_valid_inst = active_applications
                .get(key)
                .map(|vec_args| {
                    vec_args.iter().any(|ia| {
                        ia.len() >= cls.explicit_param_count || cls.explicit_param_count == 0
                    })
                })
                .unwrap_or(false);
            (has_valid_inst, Vec::new())
        };

        if discharged {
            sealed_obligations += 1;
        } else {
            open_stage_a_obligations += 1;
        }
        obligations.push(LedgerObligationStatus {
            class_name: cls.short_name.clone(),
            fq_name: cls.fq_name.clone(),
            path: cls.path.clone(),
            line: cls.line,
            field_count: cls.field_count,
            consumer_count: c_count,
            required_carriers: req_carriers,
            unsealed_carriers,
            discharging_instances: instances_by_class.remove(key).unwrap_or_default(),
            discharged,
        });
    }

    let ledger_basis = if obligations.is_empty() {
        classify_without_obligation_classes(
            repo_root,
            index,
            opts,
            theorem_declaration_count,
            &mut violations,
        )
    } else {
        PipelineLedgerBasis::ObligationClasses
    };

    let stage = if !violations.is_empty() {
        PipelineStage::Failed
    } else {
        match &ledger_basis {
            PipelineLedgerBasis::ObligationClasses if open_stage_a_obligations > 0 => {
                PipelineStage::StageALocked
            }
            PipelineLedgerBasis::ObligationClasses
            | PipelineLedgerBasis::AllowEmptyOverride
            | PipelineLedgerBasis::ApexManifest { .. } => PipelineStage::StageBSealed,
            PipelineLedgerBasis::ZeroDeclarations | PipelineLedgerBasis::UndeclaredTheorems => {
                PipelineStage::Undeclared
            }
        }
    };
    let allow_empty_override = ledger_basis == PipelineLedgerBasis::AllowEmptyOverride
        && stage == PipelineStage::StageBSealed;

    let passed =
        stage != PipelineStage::Failed && (!opts.strict || stage != PipelineStage::Undeclared);
    let ready_for_parallel_swarm = matches!(
        stage,
        PipelineStage::StageALocked | PipelineStage::StageBSealed
    );
    let ready_for_claimed = stage == PipelineStage::StageBSealed;

    PipelineReport {
        repo_root: repo_root.display().to_string(),
        checked_at: Utc::now().to_rfc3339(),
        stage,
        passed,
        ready_for_parallel_swarm,
        ready_for_claimed,
        ledger_basis,
        allow_empty_override,
        theorem_declaration_count,
        smuggled_sorry_count,
        smuggled_axiom_count,
        total_obligations: obligations.len(),
        sealed_obligations,
        open_stage_a_obligations,
        consumer_sites,
        obligations,
        violations,
    }
}
