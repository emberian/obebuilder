//! Process Judge as a Value & Non-Regression Genealogy (`JUDGE.md`, `Obend/Judge/Genealogy.lean`).
//!
//! Mirrors `Obend.Judge.Genealogy` (`Gate`, `Floor`, `Method`, `TrustBase`, `Refusal`, `Succession`,
//! `Chain`) and extends floor comparison to structured numeric caps so loosening a cap
//! (e.g. `tier1_module_sec_cap <= 60` -> `<= 600`), dropping a floor, dropping `revert@1`,
//! or expanding the trust base without an explicit `LobCost` ledger entry is refused by name.
//!
//! In `obb v7 (0.7.0)`:
//! - `#tooth` (`planted_fault_red`) executes real positive + mutated negative controls in isolated
//!   disposable `/private/tmp` copies, distinguishing `BIT`, `VACUOUS`, `INVALID_TOOTH`, and
//!   `POSITIVE_FAILED` without touching the working tree.
//! - Unknown named/cap floors (`UnknownFloor`) and missing timing/census measurements
//!   (`MissingMeasurement`) fail closed instead of silently defaulting to `0`.
//! - Static token/AST scanners are classified honestly under `TrustBase::Lexical` (`eval:lexical`,
//!   `Regime::Attested`) and refused under `eval:kernel` unless a `HEAD`-bound external kernel
//!   receipt (`KernelReceipt`) is verified.
//! - `issue_judge_receipt` binds evaluation results cryptographically to `(gate_sha256, base_sha,
//!   head_sha, tree_oid)` for `obb-state` transition verification.

mod cone_cache;
pub mod pipeline;
pub mod receipt_auth;
pub use cone_cache::is_runtime_status_entry;

use anyhow::{Context, Result, bail};
use chrono::Utc;
use obb_core::{Regime, sha256_hex};
use obb_lint::lean_index::{DeclKind, build_lean_index};
use obb_lint::spec_check::parse_transport_census_json;
use obb_lint::{RepoLintOptions, is_known_static_lint_rule_id, run_repo_lints_with_options};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::BTreeSet;
use std::fmt;
use std::io::Read;
use std::path::{Component, Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

fn is_false(value: &bool) -> bool {
    !value
}

pub const REVERT_FORMAT: &str = "revert@1";
pub const RECEIPT_VERSION: u32 = 1;

fn default_tooth_timeout_ms() -> u64 {
    15_000
}

fn default_attested_regime() -> Regime {
    Regime::Attested
}

/// Apply hermetic git/temp environment variables so user/global hooks or configs are never read.
fn configure_hermetic_git(cmd: &mut Command) -> &mut Command {
    cmd.env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_NOSYSTEM", "1");
    if Path::new("/private/tmp").is_dir() {
        cmd.env("TMPDIR", "/private/tmp");
    }
    cmd
}

fn create_isolated_tempdir(prefix: &str) -> Result<tempfile::TempDir> {
    let mut builder = tempfile::Builder::new();
    builder.prefix(prefix);
    if Path::new("/private/tmp").is_dir() {
        builder
            .tempdir_in("/private/tmp")
            .context("failed to create isolated tempdir in /private/tmp")
    } else {
        builder
            .tempdir()
            .context("failed to create isolated tempdir")
    }
}

/// What an automated check relies on to be sound (`Obend.Judge.Genealogy.TrustBase`).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TrustBase {
    /// External proof kernel verifier (`lean4checker` / Lean kernel audit with verified receipt).
    Kernel,
    /// Compiled native checker or executed behavioral negative control (`obb` / native runner).
    Compiled,
    /// Static lexical / token / structural scanner (no kernel or runtime execution; `attested`).
    Lexical,
    /// External solver or tool (`lean-transport`, `cadical`, `yosys`, `git`, etc.).
    External(String),
}

impl TrustBase {
    pub fn parse_wire(s: &str) -> Result<Self, String> {
        let trimmed = s.trim();
        if trimmed == "kernel" {
            Ok(Self::Kernel)
        } else if trimmed == "compiled" {
            Ok(Self::Compiled)
        } else if matches!(trimmed, "lexical" | "static_scan" | "static") {
            Ok(Self::Lexical)
        } else if let Some(who) = trimmed.strip_prefix("external:") {
            if who.trim().is_empty() {
                Err("external trust base requires a non-empty tool name (`external:<tool>`)".into())
            } else {
                Ok(Self::External(who.trim().to_string()))
            }
        } else {
            Err(format!("unknown TrustBase `{trimmed}`"))
        }
    }

    pub fn to_wire(&self) -> String {
        match self {
            Self::Kernel => "kernel".to_string(),
            Self::Compiled => "compiled".to_string(),
            Self::Lexical => "lexical".to_string(),
            Self::External(w) => format!("external:{w}"),
        }
    }

    /// Maximum epistemic regime achievable by this trust base alone.
    pub fn max_regime(&self) -> Regime {
        match self {
            Self::Kernel => Regime::Decided,
            Self::Compiled => Regime::Decided,
            Self::External(_) => Regime::Certified,
            Self::Lexical => Regime::Attested,
        }
    }
}

impl fmt::Display for TrustBase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_wire())
    }
}

impl Serialize for TrustBase {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.to_wire())
    }
}

impl<'de> Deserialize<'de> for TrustBase {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s = String::deserialize(deserializer)?;
        Self::parse_wire(&s).map_err(serde::de::Error::custom)
    }
}

/// How a `(format, floor)` pair is discharged (`Obend.Judge.Genealogy.Method`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Method {
    /// Discharged by structural/mathematical lemma (zero new runtime trust).
    Lemma,
    /// Discharged by running an evaluator on `TrustBase`.
    Eval(TrustBase),
}

impl Method {
    pub fn parse_wire(s: &str) -> Result<Self, String> {
        let trimmed = s.trim();
        if trimmed == "lemma" {
            Ok(Self::Lemma)
        } else if let Some(rest) = trimmed.strip_prefix("eval:") {
            Ok(Self::Eval(TrustBase::parse_wire(rest)?))
        } else {
            Err(format!("unknown Method `{trimmed}`"))
        }
    }

    pub fn to_wire(&self) -> String {
        match self {
            Self::Lemma => "lemma".to_string(),
            Self::Eval(tb) => format!("eval:{}", tb.to_wire()),
        }
    }
}

impl fmt::Display for Method {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_wire())
    }
}

impl Serialize for Method {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.to_wire())
    }
}

impl<'de> Deserialize<'de> for Method {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s = String::deserialize(deserializer)?;
        Self::parse_wire(&s).map_err(serde::de::Error::custom)
    }
}

/// Comparable floor specification (`JUDGE.md` §"The judge as a value").
///
/// Serializes cleanly to `Genealogy.lean`'s wire string form (`"home 10"`, `"tier1_module_sec_cap <= 60"`)
/// and also accepts structured JSON objects (`{"kind":"cap","cell":"...","max":60}`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Floor {
    /// Corrigibility bedrock (`home N`: last `N` commits revert cleanly).
    Home(u64),
    /// Numeric upper-bound cap (`<cell> <= <max>`): smaller `max` is stricter; larger `max` is looser!
    Cap { cell: String, max: u64 },
    /// Named invariant without numeric parameter.
    Named(String),
    /// Optional declared input cone and a shell check for a custom named floor.
    Configured {
        floor: Box<Floor>,
        inputs: Vec<String>,
        command: Option<String>,
        timeout_ms: u64,
    },
}

impl Floor {
    pub fn parse_wire(s: &str) -> Result<Self, String> {
        let trimmed = s.trim();
        if trimmed.is_empty() {
            return Err("empty floor string".into());
        }
        if let Some(rest) = trimmed.strip_prefix("home ") {
            let n = rest
                .trim()
                .parse::<u64>()
                .map_err(|_| format!("invalid `home N` floor `{trimmed}`"))?;
            if n == 0 {
                return Err("`home N` requires N >= 1".into());
            }
            return Ok(Self::Home(n));
        }
        if let Some((lhs, rhs)) = trimmed.split_once("<=") {
            let cell = lhs.trim();
            let max = rhs
                .trim()
                .parse::<u64>()
                .map_err(|_| format!("invalid numeric cap in floor `{trimmed}`"))?;
            if cell.is_empty() {
                return Err(format!("missing cell name in floor `{trimmed}`"));
            }
            return Ok(Self::Cap {
                cell: cell.to_string(),
                max,
            });
        }
        Ok(Self::Named(trimmed.to_string()))
    }

    pub fn core(&self) -> &Self {
        match self {
            Self::Configured { floor, .. } => floor.core(),
            _ => self,
        }
    }

    pub fn inputs(&self) -> &[String] {
        match self {
            Self::Configured { inputs, .. } => inputs,
            _ => &[],
        }
    }

    fn with_inputs(self, inputs: Vec<String>) -> Self {
        if inputs.is_empty() {
            self
        } else {
            Self::Configured {
                floor: Box::new(self),
                inputs,
                command: None,
                timeout_ms: default_tooth_timeout_ms(),
            }
        }
    }

    pub fn to_wire(&self) -> String {
        match self {
            Self::Configured { floor, .. } => floor.to_wire(),
            Self::Home(n) => format!("home {n}"),
            Self::Cap { cell, max } => format!("{cell} <= {max}"),
            Self::Named(s) => s.clone(),
        }
    }

    pub fn cell_key(&self) -> &str {
        match self {
            Self::Configured { floor, .. } => floor.cell_key(),
            Self::Home(_) => "home_revert_clean",
            Self::Cap { cell, .. } => cell.as_str(),
            Self::Named(s) => s.as_str(),
        }
    }
}

impl fmt::Display for Floor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_wire())
    }
}

impl Serialize for Floor {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if let Self::Configured {
            floor,
            inputs,
            command,
            timeout_ms,
        } = self
        {
            serde_json::json!({"floor": floor, "inputs": inputs, "command": command, "timeout_ms": timeout_ms}).serialize(serializer)
        } else {
            serializer.serialize_str(&self.to_wire())
        }
    }
}

#[derive(Deserialize)]
#[serde(untagged)]
enum FloorRepr {
    Configured {
        floor: Box<Floor>,
        #[serde(default)]
        inputs: Vec<String>,
        #[serde(default, alias = "check_cmd")]
        command: Option<String>,
        #[serde(default = "default_tooth_timeout_ms")]
        timeout_ms: u64,
    },
    Wire(String),
    StructuredHome {
        kind: String,
        commits: u64,
        #[serde(default)]
        inputs: Vec<String>,
    },
    StructuredCap {
        cell: String,
        max: u64,
        #[serde(default)]
        inputs: Vec<String>,
    },
    StructuredNamed {
        name: String,
        #[serde(default)]
        inputs: Vec<String>,
    },
}

impl<'de> Deserialize<'de> for Floor {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match FloorRepr::deserialize(deserializer)? {
            FloorRepr::Configured {
                floor,
                inputs,
                command,
                timeout_ms,
            } => {
                if matches!(*floor, Self::Configured { .. }) {
                    return Err(serde::de::Error::custom(
                        "nested floor configurations are not supported",
                    ));
                }
                Ok(Self::Configured {
                    floor,
                    inputs,
                    command,
                    timeout_ms,
                })
            }
            FloorRepr::Wire(s) => Self::parse_wire(&s).map_err(serde::de::Error::custom),
            FloorRepr::StructuredHome {
                kind,
                commits,
                inputs,
            } => {
                if kind != "home" || commits == 0 {
                    return Err(serde::de::Error::custom(
                        "structured home floor requires `kind == \"home\"` and `commits >= 1`",
                    ));
                }
                Ok(Self::Home(commits).with_inputs(inputs))
            }
            FloorRepr::StructuredCap { cell, max, inputs } => {
                Ok(Self::Cap { cell, max }.with_inputs(inputs))
            }
            FloorRepr::StructuredNamed { name, inputs } => Self::parse_wire(&name)
                .map(|floor| floor.with_inputs(inputs))
                .map_err(serde::de::Error::custom),
        }
    }
}

/// Planted-fault mutation applied inside an isolated disposable copy for `#tooth` execution.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ToothMutation {
    /// Execute the built-in tier-1 scanner/anti-vacuity positive and mutated controls.
    /// This certifies the linter probe, not arbitrary candidate program behavior.
    StructuralProbe,
    /// Replace `search` with `replace` inside repo-relative `file`.
    Replace {
        file: String,
        search: String,
        replace: String,
        #[serde(default)]
        replace_all: bool,
    },
    /// Apply a unified diff inside the disposable working tree via `git apply`.
    UnifiedDiff {
        #[serde(alias = "diff")]
        patch: String,
    },
    /// Activate a planted-fault toggle via environment variable `key=value` on the negative run.
    Env { key: String, value: String },
}

/// Executable `#tooth` specification (`planted_fault_red`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ToothSpec {
    pub id: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub inputs: Vec<String>,
    #[serde(default)]
    pub description: String,
    /// Optional build/syntax preflight command run BEFORE `check_cmd` on both positive and mutated
    /// copies. If `build_cmd` fails on the mutated copy, verdict is `INVALID_TOOTH`.
    #[serde(default)]
    pub build_cmd: Option<String>,
    /// Behavioral check command (`sh -c <check_cmd>`) that MUST pass (`exit == 0`) on the unmodified
    /// candidate and fail behaviorally (`exit != 0`) when `mutation` is applied.
    #[serde(default)]
    pub check_cmd: String,
    pub mutation: ToothMutation,
    /// Optional substring required in negative-control output to confirm the intended behavioral
    /// assertion tripped rather than an unrelated crash.
    #[serde(default)]
    pub expect_failure_substring: Option<String>,
    #[serde(default = "default_tooth_timeout_ms")]
    pub timeout_ms: u64,
}

/// Outcome of executing one `#tooth` (positive control + isolated mutated negative control).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum ToothVerdict {
    /// Positive check passed (`exit == 0`) and mutated negative control failed on behavioral assertion.
    Bit,
    /// Positive check passed (`exit == 0`), but mutated negative control ALSO exited `0`!
    Vacuous,
    /// Mutation failed to apply, broke syntax/compile/test-discovery, ran 0 tests, crashed by signal,
    /// missed `expect_failure_substring`, invoked forbidden tool, or timed out.
    InvalidTooth,
    /// Unmodified candidate failed `build_cmd` or `check_cmd` before any fault was planted.
    PositiveFailed,
}

impl ToothVerdict {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Bit => "BIT",
            Self::Vacuous => "VACUOUS",
            Self::InvalidTooth => "INVALID_TOOTH",
            Self::PositiveFailed => "POSITIVE_FAILED",
        }
    }
}

impl fmt::Display for ToothVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ToothExecutionResult {
    #[serde(default, skip_serializing_if = "is_false")]
    pub reused_from_cache: bool,
    pub id: String,
    pub verdict: ToothVerdict,
    pub positive_exit: Option<i32>,
    pub negative_exit: Option<i32>,
    pub duration_ms: u64,
    pub detail: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TeethReport {
    pub total: usize,
    pub bit_count: usize,
    pub vacuous_count: usize,
    pub invalid_count: usize,
    pub positive_failed_count: usize,
    pub all_bit: bool,
    pub results: Vec<ToothExecutionResult>,
}

/// One `(format, floor, method)` row in `Gate.methods`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MethodBinding {
    pub format: String,
    pub floor: Floor,
    pub method: Method,
}

/// Process Judge value (`Obend.Judge.Genealogy.Gate`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Gate {
    pub name: String,
    pub formats: Vec<String>,
    pub floors: Vec<Floor>,
    pub methods: Vec<MethodBinding>,
    pub basis: Vec<TrustBase>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub teeth: Vec<ToothSpec>,
}

impl Gate {
    pub fn load_from_path(path: &Path) -> Result<Self> {
        let raw = std::fs::read_to_string(path)
            .with_context(|| format!("failed to read judge file {}", path.display()))?;
        serde_json::from_str(&raw)
            .with_context(|| format!("failed to parse judge JSON {}", path.display()))
    }

    /// Strengthen this gate with all test-placement floors, preserving any tighter existing cap.
    pub fn require_strict_tests(&mut self) {
        for lang in ["rust", "javascript", "python", "lean"] {
            let cell = format!("{lang}/test-in-library");
            let floor = Floor::Cap {
                cell: cell.clone(),
                max: 0,
            };
            self.floors.retain(|f| f.cell_key() != cell);
            self.methods.retain(|m| m.floor.cell_key() != cell);
            self.floors.push(floor.clone());
            for format in &self.formats {
                self.methods.push(MethodBinding {
                    format: format.clone(),
                    floor: floor.clone(),
                    method: if format == REVERT_FORMAT {
                        Method::Lemma
                    } else {
                        Method::Eval(TrustBase::Lexical)
                    },
                });
            }
        }
        if !self.basis.contains(&TrustBase::Lexical) {
            self.basis.push(TrustBase::Lexical);
        }
    }

    pub fn method_for(&self, format: &str, floor: &Floor) -> Option<&Method> {
        self.methods
            .iter()
            .find(|m| m.format == format && m.floor.core() == floor.core())
            .map(|m| &m.method)
    }

    pub fn has_home_bedrock(&self) -> bool {
        self.floors
            .iter()
            .any(|fl| matches!(fl.core(), Floor::Home(n) if *n >= 1))
    }

    /// Returns `true` if any `(format, floor)` binding for `floor` claims `eval:kernel`.
    pub fn floor_claims_kernel(&self, floor: &Floor) -> bool {
        self.methods
            .iter()
            .any(|m| m.floor.core() == floor.core() && m.method == Method::Eval(TrustBase::Kernel))
    }

    /// Deterministic SHA-256 over the canonical serialized `Gate` value.
    pub fn canonical_sha256(&self) -> Result<String> {
        let bytes = serde_json::to_vec(self).context("failed to serialize Gate for hashing")?;
        Ok(sha256_hex(&bytes))
    }
}

/// Named, machine-checked refusal reason for `obb judge succeed` (`Genealogy.Refusal` + numeric cap non-regression).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, thiserror::Error)]
pub enum Refusal {
    #[error("NoBedrock: judge `{0}` declares no `home N` corrigibility floor")]
    NoBedrock(String),

    #[error("RefusesRevert: judge `{0}` drops required format `revert@1`")]
    RefusesRevert(String),

    #[error(
        "RevertUnproved: judge `{judge}` discharges (`revert@1`, `{floor}`) via `{method}` instead of `lemma`"
    )]
    RevertUnproved {
        judge: String,
        floor: String,
        method: String,
    },

    #[error("DropsFloor: candidate judge drops floor `{0}` present in current judge")]
    DropsFloor(String),

    #[error(
        "LoosensFloor: candidate judge loosens floor `{cell}` from `{old_bound}` to `{new_bound}`"
    )]
    LoosensFloor {
        cell: String,
        old_bound: String,
        new_bound: String,
    },

    #[error("Unchecked: judge `{judge}` has no method binding for (`{format}`, `{floor}`)")]
    Unchecked {
        judge: String,
        format: String,
        floor: String,
    },

    #[error(
        "Undeclared: judge `{judge}` uses `eval:{trust}` on (`{format}`, `{floor}`) without declaring `{trust}` in `basis`"
    )]
    Undeclared {
        judge: String,
        format: String,
        floor: String,
        trust: TrustBase,
    },

    #[error(
        "Stronger: Löb boundary crossed — candidate judge adds trust base `{0}` without `--lob {0}` and a `LobCost` ledger entry"
    )]
    Stronger(TrustBase),

    #[error(
        "LabelNotNeeded: `--lob {0}` was supplied, but `{0}` is not newly added by candidate judge"
    )]
    LabelNotNeeded(TrustBase),
}

/// Succession record (`JUDGE.md` `LobCost` ledger witness).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SuccessionRecord {
    pub old_name: String,
    pub new_name: String,
    pub added_floors: Vec<String>,
    pub tightened_floors: Vec<String>,
    pub lob_cost: Vec<TrustBase>,
    pub decided_at: String,
}

/// Check `WellFormed` (`Genealogy.lean:87-105`) on a single `Gate`.
pub fn check_well_formed(gate: &Gate) -> Result<(), Refusal> {
    if !gate.has_home_bedrock() {
        return Err(Refusal::NoBedrock(gate.name.clone()));
    }
    if !gate.formats.iter().any(|f| f == REVERT_FORMAT) {
        return Err(Refusal::RefusesRevert(gate.name.clone()));
    }
    for fmt in &gate.formats {
        for fl in &gate.floors {
            let Some(m) = gate.method_for(fmt, fl) else {
                return Err(Refusal::Unchecked {
                    judge: gate.name.clone(),
                    format: fmt.clone(),
                    floor: fl.to_wire(),
                });
            };
            if fmt == REVERT_FORMAT && *m != Method::Lemma {
                return Err(Refusal::RevertUnproved {
                    judge: gate.name.clone(),
                    floor: fl.to_wire(),
                    method: m.to_wire(),
                });
            }
            if let Method::Eval(tb) = m
                && !gate.basis.iter().any(|b| b == tb)
            {
                return Err(Refusal::Undeclared {
                    judge: gate.name.clone(),
                    format: fmt.clone(),
                    floor: fl.to_wire(),
                    trust: tb.clone(),
                });
            }
        }
    }
    Ok(())
}

/// Enforce G4 non-regression & Löb trust-base accounting (`JUDGE.md` & `Genealogy.succeed?`).
pub fn check_succeed(
    old: &Gate,
    new: &Gate,
    lob_labels: &[TrustBase],
) -> Result<SuccessionRecord, Refusal> {
    check_well_formed(old)?;
    check_well_formed(new)?;

    let mut tightened_floors = Vec::new();

    // 1. Every floor in `old` must still exist in `new` and must not be loosened!
    for old_fl in &old.floors {
        match old_fl.core() {
            Floor::Configured { .. } => unreachable!("core unwraps configurations"),
            Floor::Home(old_n) => {
                let new_home = new.floors.iter().find_map(|f| match f.core() {
                    Floor::Home(n) => Some(*n),
                    _ => None,
                });
                match new_home {
                    None => return Err(Refusal::DropsFloor(old_fl.to_wire())),
                    Some(new_n) if new_n < *old_n => {
                        return Err(Refusal::LoosensFloor {
                            cell: "home".to_string(),
                            old_bound: format!("home {old_n}"),
                            new_bound: format!("home {new_n}"),
                        });
                    }
                    Some(new_n) if new_n > *old_n => {
                        tightened_floors.push(format!("home {old_n} -> home {new_n}"));
                    }
                    _ => {}
                }
            }
            Floor::Cap { cell, max: old_max } => {
                let matching_cap = new.floors.iter().find_map(|f| match f.core() {
                    Floor::Cap {
                        cell: c2,
                        max: new_max,
                    } if c2 == cell => Some(*new_max),
                    _ => None,
                });
                match matching_cap {
                    None => return Err(Refusal::DropsFloor(old_fl.to_wire())),
                    Some(new_max) if new_max > *old_max => {
                        return Err(Refusal::LoosensFloor {
                            cell: cell.clone(),
                            old_bound: format!("{cell} <= {old_max}"),
                            new_bound: format!("{cell} <= {new_max}"),
                        });
                    }
                    Some(new_max) if new_max < *old_max => {
                        tightened_floors.push(format!("{cell}: <= {old_max} -> <= {new_max}"));
                    }
                    _ => {}
                }
            }
            Floor::Named(name) => {
                let present = new
                    .floors
                    .iter()
                    .any(|f| matches!(f.core(), Floor::Named(n2) if n2 == name));
                if !present {
                    return Err(Refusal::DropsFloor(old_fl.to_wire()));
                }
            }
        }
    }

    // 2. Löb trust-base accounting: `new.basis \ old.basis` must match `lob_labels` set-wise
    let old_basis: BTreeSet<TrustBase> = old.basis.iter().cloned().collect();
    let new_basis: BTreeSet<TrustBase> = new.basis.iter().cloned().collect();
    let label_set: BTreeSet<TrustBase> = lob_labels.iter().cloned().collect();

    for tb in &new_basis {
        if !old_basis.contains(tb) && !label_set.contains(tb) {
            return Err(Refusal::Stronger(tb.clone()));
        }
    }
    for tb in &label_set {
        if old_basis.contains(tb) || !new_basis.contains(tb) {
            return Err(Refusal::LabelNotNeeded(tb.clone()));
        }
    }

    // Compute newly added floors for the ledger record
    let old_cells: BTreeSet<&str> = old.floors.iter().map(|f| f.cell_key()).collect();
    let added_floors: Vec<String> = new
        .floors
        .iter()
        .filter(|f| !old_cells.contains(f.cell_key()))
        .map(|f| f.to_wire())
        .collect();

    Ok(SuccessionRecord {
        old_name: old.name.clone(),
        new_name: new.name.clone(),
        added_floors,
        tightened_floors,
        lob_cost: label_set.into_iter().collect(),
        decided_at: Utc::now().to_rfc3339(),
    })
}

/// Result of checking whether a commit reverts cleanly (`home N` corrigibility check).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RevertCheckResult {
    pub repo: String,
    pub commit_rev: String,
    pub commit_sha: String,
    pub parent_sha: String,
    pub head_sha: String,
    pub clean: bool,
    pub result_tree_oid: Option<String>,
    pub conflict_summary: Vec<String>,
}

/// Verify in an isolated temporary bare git directory (`objects/info/alternates`) that `<commit_rev>`
/// reverts cleanly on top of `<repo_root>`'s `HEAD` without touching `<repo_root>` or `.git/objects`.
pub fn check_revert_clean(repo_root: &Path, commit_rev: &str) -> Result<RevertCheckResult> {
    let canon_repo = repo_root
        .canonicalize()
        .with_context(|| format!("repo path does not exist: {}", repo_root.display()))?;

    let common_dir_raw = run_git_ro(&canon_repo, &["rev-parse", "--git-common-dir"])?;
    let common_dir = {
        let p = Path::new(common_dir_raw.trim());
        if p.is_absolute() {
            p.to_path_buf()
        } else {
            canon_repo.join(p)
        }
    };
    let objects_dir = common_dir
        .join("objects")
        .canonicalize()
        .with_context(|| format!("missing git objects dir under {}", common_dir.display()))?;

    let commit_sha = run_git_ro(
        &canon_repo,
        &["rev-parse", "--verify", &format!("{commit_rev}^{{commit}}")],
    )?
    .trim()
    .to_string();

    let parent_sha = run_git_ro(
        &canon_repo,
        &["rev-parse", "--verify", &format!("{commit_sha}^1")],
    )
    .with_context(|| {
        format!(
            "commit {commit_sha} has no first parent (root commit cannot be reverted via 3-way merge)"
        )
    })?
    .trim()
    .to_string();

    let head_sha = run_git_ro(&canon_repo, &["rev-parse", "--verify", "HEAD^{commit}"])?
        .trim()
        .to_string();

    // Isolated scratch bare repo pointing read-only at `objects_dir` via `info/alternates`
    let scratch = create_isolated_tempdir("obb-revert-")?;
    let mut init_cmd = Command::new("git");
    configure_hermetic_git(&mut init_cmd)
        .arg("init")
        .arg("--bare")
        .arg("--quiet")
        .arg(scratch.path());
    let init_out = init_cmd
        .output()
        .context("failed to run `git init --bare` in scratch dir")?;
    if !init_out.status.success() {
        bail!(
            "`git init --bare` failed: {}",
            String::from_utf8_lossy(&init_out.stderr).trim()
        );
    }

    let info_dir = scratch.path().join("objects/info");
    std::fs::create_dir_all(&info_dir)?;
    std::fs::write(
        info_dir.join("alternates"),
        format!("{}\n", objects_dir.display()),
    )?;

    // Reverting `commit_sha` on top of `head_sha` is a 3-way merge with base=`commit_sha`,
    // branch1=`head_sha`, branch2=`parent_sha`!
    let mut mt_cmd = Command::new("git");
    configure_hermetic_git(&mut mt_cmd)
        .arg("--git-dir")
        .arg(scratch.path())
        .arg("merge-tree")
        .arg("--write-tree")
        .arg(format!("--merge-base={commit_sha}"))
        .arg(&head_sha)
        .arg(&parent_sha);
    let mt_out = mt_cmd
        .output()
        .context("failed to run `git merge-tree --write-tree`")?;

    let stdout = String::from_utf8_lossy(&mt_out.stdout);
    let stderr = String::from_utf8_lossy(&mt_out.stderr);
    let lines: Vec<String> = stdout
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .map(str::to_string)
        .collect();

    if mt_out.status.success() {
        Ok(RevertCheckResult {
            repo: canon_repo.to_string_lossy().to_string(),
            commit_rev: commit_rev.to_string(),
            commit_sha,
            parent_sha,
            head_sha,
            clean: true,
            result_tree_oid: lines.first().cloned(),
            conflict_summary: Vec::new(),
        })
    } else if mt_out.status.code() == Some(1) {
        let conflict_summary: Vec<String> = lines.into_iter().skip(1).collect();
        Ok(RevertCheckResult {
            repo: canon_repo.to_string_lossy().to_string(),
            commit_rev: commit_rev.to_string(),
            commit_sha,
            parent_sha,
            head_sha,
            clean: false,
            result_tree_oid: None,
            conflict_summary,
        })
    } else {
        bail!(
            "`git merge-tree` failed with {}: {}",
            mt_out.status,
            stderr.trim()
        );
    }
}

fn run_git_ro(repo_root: &Path, args: &[&str]) -> Result<String> {
    let mut cmd = Command::new("git");
    configure_hermetic_git(&mut cmd)
        .arg("--no-optional-locks")
        .arg("-C")
        .arg(repo_root)
        .args(args);
    let out = cmd
        .output()
        .with_context(|| format!("failed to run git {:?}", args))?;
    if !out.status.success() {
        bail!(
            "git {:?} failed in {}: {}",
            args,
            repo_root.display(),
            String::from_utf8_lossy(&out.stderr).trim()
        );
    }
    Ok(String::from_utf8_lossy(&out.stdout).to_string())
}

/// Verified external proof-kernel audit receipt (`.obb/kernel-receipt.json` or `reports/kernel-receipt.json`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct KernelReceipt {
    /// External proof-kernel checker (`"lean4checker"`, `"lean-kernel"`, `"nanoda"`, etc.).
    pub checker: String,
    /// Git `HEAD` commit SHA verified by the kernel checker.
    pub head_sha: String,
    /// Process exit code (`0` means kernel accepted all replayed declarations).
    pub exit_code: i32,
    /// Count of `sorryAx` occurrences observed in the exported kernel environment.
    pub sorry_ax_count: u64,
    /// Count of user-declared `axiom` constants observed in the exported kernel environment.
    pub user_axiom_count: u64,
    #[serde(default)]
    pub modules_checked: u64,
    #[serde(default)]
    pub checked_at: String,
}

/// Fail-closed diagnostic reason attached to a `FloorEvaluation` when a floor cannot pass honestly.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum FloorDiagnostic {
    UnknownFloor {
        cell: String,
    },
    MissingMeasurement {
        cell: String,
        expected_artifact: String,
    },
    UnverifiedKernelClaim {
        cell: String,
        reason: String,
    },
    StaleKernelReceipt {
        cell: String,
        receipt_head_sha: String,
        repo_head_sha: String,
    },
    MissingToothExecution {
        detail: String,
    },
    ToothFailure {
        tooth_id: String,
        verdict: ToothVerdict,
        detail: String,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FloorEvaluation {
    #[serde(default, skip_serializing_if = "is_false")]
    pub reused_from_cache: bool,
    pub floor: String,
    pub cell: String,
    pub measured: u64,
    pub bound: String,
    pub passed: bool,
    pub detail: String,
    #[serde(default = "default_attested_regime")]
    pub regime: Regime,
    #[serde(default)]
    pub evaluator_kind: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub diagnostic: Option<FloorDiagnostic>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JudgeCheckReport {
    pub judge_name: String,
    pub repo_root: String,
    pub checked_at: String,
    pub well_formed: bool,
    pub all_passed: bool,
    pub achieved_regime: Regime,
    pub kernel_verified: bool,
    pub basis: Vec<TrustBase>,
    pub teeth_report: TeethReport,
    pub evaluations: Vec<FloorEvaluation>,
    #[serde(default)]
    pub clock: JudgeClock,
    /// Floors not evaluated on this clock. `all_passed` speaks only for `evaluations`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub deferred_floors: Vec<String>,
}

/// Which clock a gate evaluation runs on.
///
/// `Construction` is the inner loop: static scans and recorded measurements only. Executed
/// `#tooth` sandboxes and the `home N` revert merges are deferred, the result is never better
/// than `attested`, and no `JudgeReceipt` is issued from it. `Convergence` runs everything.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum JudgeClock {
    #[default]
    Convergence,
    Construction,
}

/// Content-addressed candidate evaluation receipt consumed by `obb-state` transitions.
///
/// `receipt_hash` identifies the canonical payload; `receipt_mac` authenticates that hash
/// with HMAC-SHA256. `obb-state` requires authentication whenever a key is configured and
/// independently checks git facts plus the exact proposed candidate and receipt identity.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JudgeReceipt {
    pub receipt_version: u32,
    pub judge_name: String,
    pub gate_sha256: String,
    pub repo_root: String,
    pub base_sha: String,
    pub head_sha: String,
    pub tree_oid: String,
    pub clean_working_tree: bool,
    pub changed_paths: Vec<String>,
    pub checked_at: String,
    pub all_passed: bool,
    pub achieved_regime: Regime,
    pub kernel_verified: bool,
    pub teeth_report: TeethReport,
    pub evaluations: Vec<FloorEvaluation>,
    pub receipt_hash: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub receipt_mac: Option<String>,
}

#[derive(Serialize)]
struct JudgeReceiptSignable<'a> {
    receipt_version: u32,
    judge_name: &'a str,
    gate_sha256: &'a str,
    repo_root: &'a str,
    base_sha: &'a str,
    head_sha: &'a str,
    tree_oid: &'a str,
    clean_working_tree: bool,
    changed_paths: &'a [String],
    checked_at: &'a str,
    all_passed: bool,
    achieved_regime: Regime,
    kernel_verified: bool,
    teeth_report: &'a TeethReport,
    evaluations: &'a [FloorEvaluation],
}

impl JudgeReceipt {
    pub fn compute_hash(&self) -> Result<String> {
        let signable = JudgeReceiptSignable {
            receipt_version: self.receipt_version,
            judge_name: &self.judge_name,
            gate_sha256: &self.gate_sha256,
            repo_root: &self.repo_root,
            base_sha: &self.base_sha,
            head_sha: &self.head_sha,
            tree_oid: &self.tree_oid,
            clean_working_tree: self.clean_working_tree,
            changed_paths: &self.changed_paths,
            checked_at: &self.checked_at,
            all_passed: self.all_passed,
            achieved_regime: self.achieved_regime,
            kernel_verified: self.kernel_verified,
            teeth_report: &self.teeth_report,
            evaluations: &self.evaluations,
        };
        let bytes =
            serde_json::to_vec(&signable).context("failed to serialize JudgeReceiptSignable")?;
        Ok(sha256_hex(&bytes))
    }

    /// Authenticate the content hash; the hash itself covers every evaluation field.
    pub fn authenticate(&mut self, key: &[u8]) -> Result<()> {
        self.receipt_hash = self.compute_hash()?;
        self.receipt_mac = Some(receipt_auth::mac_hex(key, self.receipt_hash.as_bytes()));
        Ok(())
    }

    pub fn verify_authenticated(&self, key: &[u8]) -> Result<()> {
        self.verify_integrity()?;
        if !self
            .receipt_mac
            .as_deref()
            .is_some_and(|mac| receipt_auth::verify_mac(key, self.receipt_hash.as_bytes(), mac))
        {
            bail!("JudgeReceipt receipt_mac is missing or invalid");
        }
        Ok(())
    }

    pub fn verify_integrity(&self) -> Result<()> {
        if self.receipt_version != RECEIPT_VERSION {
            bail!(
                "unsupported JudgeReceipt version {} (expected {})",
                self.receipt_version,
                RECEIPT_VERSION
            );
        }
        let expected = self.compute_hash()?;
        if expected != self.receipt_hash {
            bail!(
                "JudgeReceipt hash mismatch: expected {}, found {} (tampered receipt)",
                expected,
                self.receipt_hash
            );
        }
        Ok(())
    }

    pub fn load_from_path(path: &Path) -> Result<Self> {
        let raw = std::fs::read_to_string(path)
            .with_context(|| format!("failed to read JudgeReceipt at {}", path.display()))?;
        let receipt: Self = serde_json::from_str(&raw)
            .with_context(|| format!("failed to parse JudgeReceipt JSON at {}", path.display()))?;
        receipt.verify_integrity()?;
        Ok(receipt)
    }
}

#[derive(Deserialize)]
#[serde(untagged)]
enum TeethFileRepr {
    List(Vec<ToothSpec>),
    Wrapped { teeth: Vec<ToothSpec> },
}

/// Discover executable `#tooth` specs declared inline on `gate` and in `<repo>/{teeth.json,.obb/teeth.json,tests/teeth.json}`.
pub fn load_repo_teeth(gate: &Gate, repo_root: &Path) -> Result<Vec<ToothSpec>> {
    let mut specs = gate.teeth.clone();
    let mut seen_ids: BTreeSet<String> = specs.iter().map(|t| t.id.clone()).collect();

    for rel in ["teeth.json", ".obb/teeth.json", "tests/teeth.json"] {
        let p = repo_root.join(rel);
        if p.is_file() {
            let raw = std::fs::read_to_string(&p)
                .with_context(|| format!("failed to read teeth file {}", p.display()))?;
            let parsed: TeethFileRepr = serde_json::from_str(&raw)
                .with_context(|| format!("failed to parse teeth JSON {}", p.display()))?;
            let items = match parsed {
                TeethFileRepr::List(v) => v,
                TeethFileRepr::Wrapped { teeth } => teeth,
            };
            for item in items {
                if seen_ids.insert(item.id.clone()) {
                    specs.push(item);
                }
            }
        }
    }
    Ok(specs)
}

fn validate_safe_rel_path(rel: &str) -> Result<PathBuf, String> {
    let p = Path::new(rel);
    if rel.trim().is_empty() || p.is_absolute() {
        return Err(format!(
            "tooth target path `{rel}` must be a non-empty relative path"
        ));
    }
    for comp in p.components() {
        match comp {
            Component::Normal(_) | Component::CurDir => {}
            Component::ParentDir | Component::RootDir | Component::Prefix(_) => {
                return Err(format!(
                    "tooth target path `{rel}` escapes sandbox via disallowed path component"
                ));
            }
        }
    }
    Ok(p.to_path_buf())
}

fn should_skip_sandbox_entry(name: &str) -> bool {
    matches!(
        name,
        ".git" | "target" | ".lake" | "node_modules" | ".obb-state" | ".direnv"
    )
}

fn entry_relative_metadata<'a>(path: &'a Path, repo: &Path) -> Option<&'a str> {
    path.strip_prefix(repo.join(".obb")).ok()?.to_str()
}

fn copy_repo_to_sandbox(repo_root: &Path, dst_root: &Path) -> Result<()> {
    std::fs::create_dir_all(dst_root)?;
    let walker = walkdir::WalkDir::new(repo_root)
        .into_iter()
        .filter_entry(|e| {
            if e.depth() == 0 {
                return true;
            }
            let name = e.file_name().to_string_lossy();
            !should_skip_sandbox_entry(&name)
                && !matches!(
                    entry_relative_metadata(e.path(), repo_root),
                    Some("receipt.key" | "cache")
                )
        });

    for entry in walker {
        let entry = entry?;
        if entry.depth() == 0 {
            continue;
        }
        let rel = entry.path().strip_prefix(repo_root)?;
        let target = dst_root.join(rel);
        let ft = entry.file_type();
        if ft.is_dir() {
            std::fs::create_dir_all(&target)?;
        } else if ft.is_file() {
            if let Some(parent) = target.parent() {
                std::fs::create_dir_all(parent)?;
            }
            std::fs::copy(entry.path(), &target)?;
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let mode = entry.metadata()?.permissions().mode();
                let _ = std::fs::set_permissions(&target, std::fs::Permissions::from_mode(mode));
            }
        }
    }
    Ok(())
}

fn command_invokes_forbidden_macos_lean(cmd_str: &str) -> bool {
    if !cfg!(target_os = "macos") {
        return false;
    }
    for segment in cmd_str.split([';', '|', '&', '\n', '(', ')']) {
        let words = segment.split_whitespace();
        for w in words {
            // Skip leading `KEY=VAL` env assignments or `env` wrapper
            if w == "env" || (w.contains('=') && !w.starts_with('=')) {
                continue;
            }
            let bin = Path::new(w)
                .file_name()
                .and_then(|s| s.to_str())
                .unwrap_or(w);
            if matches!(bin, "lake" | "lean") {
                return true;
            }
            break;
        }
    }
    false
}

struct CmdRunOutput {
    exit_code: Option<i32>,
    timed_out: bool,
    stdout: String,
    stderr: String,
}

impl CmdRunOutput {
    fn combined(&self) -> String {
        if self.stdout.is_empty() {
            self.stderr.clone()
        } else if self.stderr.is_empty() {
            self.stdout.clone()
        } else {
            format!("{}\n{}", self.stdout, self.stderr)
        }
    }
}

fn run_sandboxed_shell_cmd(
    work_dir: &Path,
    cmd_str: &str,
    env_override: Option<(&str, &str)>,
    env_remove: Option<&str>,
    timeout_ms: u64,
) -> Result<CmdRunOutput> {
    let mut cmd = Command::new("/bin/sh");
    configure_hermetic_git(&mut cmd)
        .arg("-c")
        .arg(cmd_str)
        .current_dir(work_dir)
        .env("GIT_CEILING_DIRECTORIES", work_dir)
        .env_remove("OBB_RECEIPT_KEY")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    if let Some(rm_key) = env_remove {
        cmd.env_remove(rm_key);
    }
    if let Some((k, v)) = env_override {
        cmd.env(k, v);
    }

    let mut child = cmd
        .spawn()
        .with_context(|| format!("failed to spawn shell command `{cmd_str}`"))?;

    let mut stdout_pipe = child.stdout.take();
    let mut stderr_pipe = child.stderr.take();

    let out_handle = std::thread::spawn(move || {
        let mut buf = Vec::new();
        if let Some(ref mut p) = stdout_pipe {
            let _ = p.read_to_end(&mut buf);
        }
        String::from_utf8_lossy(&buf).to_string()
    });
    let err_handle = std::thread::spawn(move || {
        let mut buf = Vec::new();
        if let Some(ref mut p) = stderr_pipe {
            let _ = p.read_to_end(&mut buf);
        }
        String::from_utf8_lossy(&buf).to_string()
    });

    let deadline = Instant::now() + Duration::from_millis(timeout_ms.max(50));
    let mut timed_out = false;
    let status = loop {
        match child.try_wait()? {
            Some(st) => break st,
            None => {
                if Instant::now() >= deadline {
                    timed_out = true;
                    let _ = child.kill();
                    break child.wait()?;
                }
                std::thread::sleep(Duration::from_millis(10));
            }
        }
    };

    let stdout = out_handle.join().unwrap_or_default();
    let stderr = err_handle.join().unwrap_or_default();

    Ok(CmdRunOutput {
        exit_code: status.code(),
        timed_out,
        stdout,
        stderr,
    })
}

fn output_ran_zero_tests(combined: &str) -> bool {
    let lower = combined.to_ascii_lowercase();
    lower.contains("running 0 tests")
        || lower.contains("collected 0 items")
        || lower.contains("ran 0 tests in")
        || lower.contains("no tests to run")
}

fn output_is_non_behavioral_build_or_syntax_error(exit_code: Option<i32>, combined: &str) -> bool {
    // Exit 126 (permission denied / not executable) or 127 (command not found) or signal death (`None`)
    if exit_code.is_none() || matches!(exit_code, Some(126 | 127)) {
        return true;
    }
    if output_ran_zero_tests(combined) {
        return true;
    }
    let lower = combined.to_ascii_lowercase();
    lower.contains("syntaxerror:")
        || lower.contains("indentationerror:")
        || lower.contains("taberror:")
        || lower.contains("modulenotfounderror:")
        || lower.contains("importerror:")
        || lower.contains("syntax error")
        || lower.contains("parse error")
        || lower.contains("unexpected eof while looking for matching")
        || lower.contains("error: could not compile")
        || lower.contains("cannot find binary")
}

fn apply_tooth_mutation<'a>(
    work_dir: &Path,
    mutation: &'a ToothMutation,
) -> Result<Option<(&'a str, &'a str)>, String> {
    match mutation {
        ToothMutation::StructuralProbe => Err("structural probes do not use shell mutation".into()),
        ToothMutation::Replace {
            file,
            search,
            replace,
            replace_all,
        } => {
            if search.is_empty() {
                return Err("tooth `search` string must not be empty".into());
            }
            if search == replace {
                return Err(
                    "tooth `search` and `replace` strings are identical (no-op mutation)".into(),
                );
            }
            let rel = validate_safe_rel_path(file)?;
            let target = work_dir.join(&rel);
            let raw = std::fs::read_to_string(&target)
                .map_err(|e| format!("failed to read tooth target `{file}`: {e}"))?;
            if !raw.contains(search.as_str()) {
                return Err(format!(
                    "tooth search snippet `{search}` not found in `{file}`"
                ));
            }
            let mutated = if *replace_all {
                raw.replace(search.as_str(), replace.as_str())
            } else {
                raw.replacen(search.as_str(), replace.as_str(), 1)
            };
            std::fs::write(&target, mutated)
                .map_err(|e| format!("failed to write mutated file `{file}`: {e}"))?;
            Ok(None)
        }
        ToothMutation::UnifiedDiff { patch } => {
            if patch.trim().is_empty() {
                return Err("tooth unified diff patch is empty".into());
            }
            for line in patch.lines() {
                if let Some(rest) = line
                    .strip_prefix("+++ ")
                    .or_else(|| line.strip_prefix("--- "))
                {
                    let trimmed = rest.split_whitespace().next().unwrap_or("");
                    if trimmed != "/dev/null" {
                        let stripped = trimmed
                            .strip_prefix("a/")
                            .or_else(|| trimmed.strip_prefix("b/"))
                            .unwrap_or(trimmed);
                        validate_safe_rel_path(stripped)?;
                    }
                }
            }
            let patch_file = work_dir.join(".obb-tooth.patch");
            std::fs::write(&patch_file, patch)
                .map_err(|e| format!("failed to write temporary patch file: {e}"))?;
            let mut apply_cmd = Command::new("git");
            configure_hermetic_git(&mut apply_cmd)
                .current_dir(work_dir)
                .arg("apply")
                .arg("--whitespace=nowarn")
                .arg(&patch_file);
            let out = apply_cmd
                .output()
                .map_err(|e| format!("failed to run `git apply`: {e}"))?;
            let _ = std::fs::remove_file(&patch_file);
            if !out.status.success() {
                return Err(format!(
                    "`git apply` rejected tooth patch: {}",
                    String::from_utf8_lossy(&out.stderr).trim()
                ));
            }
            Ok(None)
        }
        ToothMutation::Env { key, value } => {
            if key.trim().is_empty() {
                return Err("tooth env `key` must not be empty".into());
            }
            Ok(Some((key.as_str(), value.as_str())))
        }
    }
}

fn summarize_cmd_snippet(s: &str) -> String {
    let flat: String = s
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .take(3)
        .collect::<Vec<_>>()
        .join(" | ");
    if flat.chars().count() > 220 {
        let prefix: String = flat.chars().take(220).collect();
        format!("{prefix}...")
    } else {
        flat
    }
}

/// Execute one `#tooth` in fresh disposable `/private/tmp` copies without touching `repo_root`.
pub fn execute_single_tooth(repo_root: &Path, spec: &ToothSpec) -> Result<ToothExecutionResult> {
    let started = Instant::now();
    if matches!(spec.mutation, ToothMutation::StructuralProbe) {
        return evaluate_with_planted_fault_tooth(&spec.id);
    }

    if spec.check_cmd.trim().is_empty() {
        return Ok(ToothExecutionResult {
            reused_from_cache: false,
            id: spec.id.clone(),
            verdict: ToothVerdict::InvalidTooth,
            positive_exit: None,
            negative_exit: None,
            duration_ms: started.elapsed().as_millis() as u64,
            detail: "tooth `check_cmd` is empty".into(),
        });
    }
    if command_invokes_forbidden_macos_lean(&spec.check_cmd)
        || spec
            .build_cmd
            .as_deref()
            .is_some_and(command_invokes_forbidden_macos_lean)
    {
        return Ok(ToothExecutionResult {
            reused_from_cache: false,
            id: spec.id.clone(),
            verdict: ToothVerdict::InvalidTooth,
            positive_exit: None,
            negative_exit: None,
            duration_ms: started.elapsed().as_millis() as u64,
            detail: "local `lake`/`lean` execution is forbidden on macOS".into(),
        });
    }

    let env_key_to_unset = match &spec.mutation {
        ToothMutation::Env { key, .. } => Some(key.as_str()),
        _ => None,
    };

    // 1. Positive control on unmodified disposable copy
    let pos_tmp = create_isolated_tempdir("obb-tooth-pos-")?;
    let pos_dir = pos_tmp.path().join("work");
    copy_repo_to_sandbox(repo_root, &pos_dir)?;

    if let Some(ref bcmd) = spec.build_cmd {
        let bout =
            run_sandboxed_shell_cmd(&pos_dir, bcmd, None, env_key_to_unset, spec.timeout_ms)?;
        if bout.timed_out || bout.exit_code != Some(0) {
            return Ok(ToothExecutionResult {
                reused_from_cache: false,
                id: spec.id.clone(),
                verdict: ToothVerdict::PositiveFailed,
                positive_exit: bout.exit_code,
                negative_exit: None,
                duration_ms: started.elapsed().as_millis() as u64,
                detail: format!(
                    "positive control `build_cmd` failed (timed_out={}, exit={:?}): {}",
                    bout.timed_out,
                    bout.exit_code,
                    summarize_cmd_snippet(&bout.combined())
                ),
            });
        }
    }

    let pos_out = run_sandboxed_shell_cmd(
        &pos_dir,
        &spec.check_cmd,
        None,
        env_key_to_unset,
        spec.timeout_ms,
    )?;
    let pos_combined = pos_out.combined();
    if pos_out.timed_out || pos_out.exit_code != Some(0) {
        return Ok(ToothExecutionResult {
            reused_from_cache: false,
            id: spec.id.clone(),
            verdict: ToothVerdict::PositiveFailed,
            positive_exit: pos_out.exit_code,
            negative_exit: None,
            duration_ms: started.elapsed().as_millis() as u64,
            detail: format!(
                "positive control `check_cmd` failed on unmodified tree (timed_out={}, exit={:?}): {}",
                pos_out.timed_out,
                pos_out.exit_code,
                summarize_cmd_snippet(&pos_combined)
            ),
        });
    }
    if output_ran_zero_tests(&pos_combined) {
        return Ok(ToothExecutionResult {
            reused_from_cache: false,
            id: spec.id.clone(),
            verdict: ToothVerdict::InvalidTooth,
            positive_exit: pos_out.exit_code,
            negative_exit: None,
            duration_ms: started.elapsed().as_millis() as u64,
            detail: "positive control discovered 0 tests (`INVALID_TOOTH`)".into(),
        });
    }

    // 2. Negative control on fresh isolated copy with planted fault applied
    let neg_tmp = create_isolated_tempdir("obb-tooth-neg-")?;
    let neg_dir = neg_tmp.path().join("work");
    copy_repo_to_sandbox(repo_root, &neg_dir)?;

    let env_override = match apply_tooth_mutation(&neg_dir, &spec.mutation) {
        Ok(ov) => ov,
        Err(reason) => {
            return Ok(ToothExecutionResult {
                reused_from_cache: false,
                id: spec.id.clone(),
                verdict: ToothVerdict::InvalidTooth,
                positive_exit: pos_out.exit_code,
                negative_exit: None,
                duration_ms: started.elapsed().as_millis() as u64,
                detail: format!("invalid tooth mutation: {reason}"),
            });
        }
    };

    if let Some(ref bcmd) = spec.build_cmd {
        let bout = run_sandboxed_shell_cmd(&neg_dir, bcmd, env_override, None, spec.timeout_ms)?;
        if bout.timed_out || bout.exit_code != Some(0) {
            return Ok(ToothExecutionResult {
                reused_from_cache: false,
                id: spec.id.clone(),
                verdict: ToothVerdict::InvalidTooth,
                positive_exit: pos_out.exit_code,
                negative_exit: bout.exit_code,
                duration_ms: started.elapsed().as_millis() as u64,
                detail: format!(
                    "mutation broke `build_cmd` instead of tripping behavioral `check_cmd` (timed_out={}, exit={:?}): {}",
                    bout.timed_out,
                    bout.exit_code,
                    summarize_cmd_snippet(&bout.combined())
                ),
            });
        }
    }

    let neg_out = run_sandboxed_shell_cmd(
        &neg_dir,
        &spec.check_cmd,
        env_override,
        None,
        spec.timeout_ms,
    )?;
    let neg_combined = neg_out.combined();
    let duration_ms = started.elapsed().as_millis() as u64;

    if neg_out.timed_out {
        return Ok(ToothExecutionResult {
            reused_from_cache: false,
            id: spec.id.clone(),
            verdict: ToothVerdict::InvalidTooth,
            positive_exit: pos_out.exit_code,
            negative_exit: neg_out.exit_code,
            duration_ms,
            detail: format!(
                "negative control timed out after {}ms (`INVALID_TOOTH`)",
                spec.timeout_ms
            ),
        });
    }

    if neg_out.exit_code == Some(0) {
        return Ok(ToothExecutionResult {
            reused_from_cache: false,
            id: spec.id.clone(),
            verdict: ToothVerdict::Vacuous,
            positive_exit: pos_out.exit_code,
            negative_exit: Some(0),
            duration_ms,
            detail: "VACUOUS: mutated negative control still exited 0 (planted fault did not bite)"
                .into(),
        });
    }

    if output_is_non_behavioral_build_or_syntax_error(neg_out.exit_code, &neg_combined) {
        return Ok(ToothExecutionResult {
            reused_from_cache: false,
            id: spec.id.clone(),
            verdict: ToothVerdict::InvalidTooth,
            positive_exit: pos_out.exit_code,
            negative_exit: neg_out.exit_code,
            duration_ms,
            detail: format!(
                "INVALID_TOOTH: mutation caused syntax/compile/discovery/signal failure (exit={:?}): {}",
                neg_out.exit_code,
                summarize_cmd_snippet(&neg_combined)
            ),
        });
    }

    if let Some(ref expected) = spec.expect_failure_substring
        && !expected.is_empty()
        && !neg_combined.contains(expected.as_str())
    {
        return Ok(ToothExecutionResult {
            reused_from_cache: false,
            id: spec.id.clone(),
            verdict: ToothVerdict::InvalidTooth,
            positive_exit: pos_out.exit_code,
            negative_exit: neg_out.exit_code,
            duration_ms,
            detail: format!(
                "INVALID_TOOTH: negative control exited {:?} without expected behavioral failure marker `{expected}` (got: {})",
                neg_out.exit_code,
                summarize_cmd_snippet(&neg_combined)
            ),
        });
    }

    Ok(ToothExecutionResult {
        reused_from_cache: false,
        id: spec.id.clone(),
        verdict: ToothVerdict::Bit,
        positive_exit: pos_out.exit_code,
        negative_exit: neg_out.exit_code,
        duration_ms,
        detail: format!(
            "BIT: positive exit 0, mutated negative exit {:?} ({})",
            neg_out.exit_code,
            summarize_cmd_snippet(&neg_combined)
        ),
    })
}

/// Execute all `#tooth` specifications in isolated disposable sandboxes and summarize verdicts.
pub fn evaluate_teeth(repo_root: &Path, specs: &[ToothSpec]) -> Result<TeethReport> {
    evaluate_teeth_with_key(repo_root, specs, None)
}

fn evaluate_teeth_with_key(
    repo_root: &Path,
    specs: &[ToothSpec],
    signing_key: Option<&[u8]>,
) -> Result<TeethReport> {
    let mut results = Vec::with_capacity(specs.len());
    let mut bit_count = 0usize;
    let mut vacuous_count = 0usize;
    let mut invalid_count = 0usize;
    let mut positive_failed_count = 0usize;

    let cache = cone_cache::ConeCache::open(
        repo_root,
        specs.iter().any(|s| !s.inputs.is_empty()),
        signing_key,
    )?;
    for spec in specs {
        let digest = cache.digest(&spec.inputs, spec, &[])?;
        let res = if let Some(mut cached) = cache.read::<ToothExecutionResult>(digest.as_deref())? {
            cached.reused_from_cache = true;
            cached
        } else {
            let result = execute_single_tooth(repo_root, spec)?;
            cache.write(digest.as_deref(), &result)?;
            result
        };
        // Duration on a reused entry records the original execution, not cache lookup time.
        match res.verdict {
            ToothVerdict::Bit => bit_count += 1,
            ToothVerdict::Vacuous => vacuous_count += 1,
            ToothVerdict::InvalidTooth => invalid_count += 1,
            ToothVerdict::PositiveFailed => positive_failed_count += 1,
        }
        results.push(res);
    }

    let total = results.len();
    let all_bit = total > 0 && bit_count == total;

    Ok(TeethReport {
        total,
        bit_count,
        vacuous_count,
        invalid_count,
        positive_failed_count,
        all_bit,
        results,
    })
}

/// Evaluate all floors of `gate`; opted-in convergence checks may write `.obb` cache metadata.
pub fn evaluate_gate(gate: &Gate, repo_root: &Path) -> Result<JudgeCheckReport> {
    evaluate_gate_on(gate, repo_root, JudgeClock::Convergence)
}

/// Evaluate `gate` on the given clock (see [`JudgeClock`]).
pub fn evaluate_gate_on(
    gate: &Gate,
    repo_root: &Path,
    clock: JudgeClock,
) -> Result<JudgeCheckReport> {
    evaluate_gate_with_key(gate, repo_root, clock, None)
}

fn evaluate_gate_with_key(
    gate: &Gate,
    repo_root: &Path,
    clock: JudgeClock,
    signing_key: Option<&[u8]>,
) -> Result<JudgeCheckReport> {
    check_well_formed(gate).context("judge failed WellFormed check")?;
    let fast = clock == JudgeClock::Construction;
    let mut deferred_floors = Vec::new();

    let canon = repo_root
        .canonicalize()
        .unwrap_or_else(|_| repo_root.to_path_buf());

    let cache = cone_cache::ConeCache::open(
        &canon,
        !fast && gate.floors.iter().any(|f| !f.inputs().is_empty()),
        signing_key,
    )?;
    let mut floor_cache = Vec::with_capacity(gate.floors.len());
    for floor in &gate.floors {
        // These consume untracked measurements or already-cached teeth, not just tree inputs.
        let cacheable = !fast
            && !gate.floor_claims_kernel(floor)
            && !matches!(
                floor.cell_key(),
                "planted_fault_red"
                    | "tier1_module_sec_cap"
                    | "spec_insensitive_decls"
                    | "lean/spec-insensitive-change"
            );
        let extra = if !fast && !floor.inputs().is_empty() && matches!(floor.core(), Floor::Home(_))
        {
            vec![
                run_git_ro(&canon, &["rev-parse", "HEAD"])?
                    .trim()
                    .to_string(),
            ]
        } else {
            Vec::new()
        };
        let digest = if cacheable {
            cache.digest(floor.inputs(), &(floor, &gate.methods, &gate.basis), &extra)?
        } else {
            None
        };
        let cached = cache.read::<FloorEvaluation>(digest.as_deref())?;
        floor_cache.push((digest, cached));
    }
    let needs_scan = gate
        .floors
        .iter()
        .zip(&floor_cache)
        .any(|(floor, (_, cached))| {
            cached.is_none()
                && !matches!(floor.core(), Floor::Home(_))
                && floor.cell_key() != "planted_fault_red"
        });

    let gate_mentions_test_in_library = gate
        .floors
        .iter()
        .any(|fl| fl.cell_key().ends_with("test-in-library"));
    let lint_report = if needs_scan {
        Some(run_repo_lints_with_options(
            &canon,
            RepoLintOptions {
                strict_tests: gate_mentions_test_in_library,
                ..Default::default()
            },
        )?)
    } else {
        None
    };
    let lean_idx = if needs_scan {
        build_lean_index(&canon)
    } else {
        Default::default()
    };

    let count_rule = |rule_id: &str| -> u64 {
        lint_report
            .iter()
            .flat_map(|r| &r.findings)
            .filter(|f| f.rule_id == rule_id)
            .count() as u64
    };

    let declared_axioms = lean_idx
        .files
        .iter()
        .flat_map(|f| f.declarations.iter())
        .filter(|d| d.kind == DeclKind::Axiom && !d.fixture_kept)
        .count() as u64;

    let sorry_sites = lint_report
        .iter()
        .flat_map(|r| &r.findings)
        .filter(|f| {
            f.rule_id == "lean/sorry-or-axiom"
                && f.symbol.as_deref() != Some("axiom")
                && !f.message.starts_with("`axiom ")
        })
        .count() as u64;

    // Count `maxHeartbeats > 400_000` directly from the indexed Lean AST (`obb-lint` indexes them in `LeanFile.max_heartbeats`).
    let hb_violations = lean_idx
        .files
        .iter()
        .flat_map(|f| f.max_heartbeats.iter())
        .filter(|(val, _)| *val > 400_000)
        .count() as u64;

    let measured_max_sec_opt = read_max_tier1_sec(&canon);
    let repo_head_sha = resolve_optional_head_sha(&canon);
    let kernel_receipt_opt = read_kernel_receipt(&canon);

    let gate_needs_teeth = gate
        .floors
        .iter()
        .any(|fl| fl.cell_key() == "planted_fault_red");
    let teeth_specs = load_repo_teeth(gate, &canon)?;
    let teeth_report = if !fast && (gate_needs_teeth || !teeth_specs.is_empty()) {
        evaluate_teeth_with_key(&canon, &teeth_specs, signing_key)?
    } else {
        TeethReport::default()
    };

    let mut kernel_verified_any = false;
    let mut compiled_or_external_passed = false;
    let mut evaluations = Vec::new();

    for (fl, (digest, cached)) in gate.floors.iter().zip(floor_cache) {
        if fast
            && (matches!(fl.cell_key(), "home_revert_clean" | "planted_fault_red")
                || matches!(
                    fl,
                    Floor::Configured {
                        command: Some(_),
                        ..
                    }
                ))
        {
            deferred_floors.push(fl.to_wire());
            continue;
        }
        if let Some(mut cached) = cached {
            compiled_or_external_passed |= cached.passed && cached.regime == Regime::Certified;
            cached.reused_from_cache = true;
            evaluations.push(cached);
            continue;
        }
        let claims_kernel = gate.floor_claims_kernel(fl);
        match fl.core() {
            Floor::Configured { .. } => unreachable!("core unwraps configurations"),
            Floor::Home(n) => {
                if claims_kernel {
                    evaluations.push(FloorEvaluation {
                        reused_from_cache: false,
                        floor: fl.to_wire(),
                        cell: "home_revert_clean".to_string(),
                        measured: 1,
                        bound: format!("0 revert conflicts across last {n} non-merge commits"),
                        passed: false,
                        detail: "home N git revert check cannot claim `eval:kernel`".to_string(),
                        regime: Regime::Attested,
                        evaluator_kind: "unverified_kernel_claim".to_string(),
                        diagnostic: Some(FloorDiagnostic::UnverifiedKernelClaim {
                            cell: "home_revert_clean".to_string(),
                            reason: "git merge-tree is an external git check, not a proof kernel"
                                .to_string(),
                        }),
                    });
                    continue;
                }
                let (conflicts, checked_commits, note) = check_recent_reverts(&canon, *n as usize);
                let passed = conflicts == 0;
                if passed {
                    compiled_or_external_passed = true;
                }
                evaluations.push(FloorEvaluation {
                    reused_from_cache: false,
                    floor: fl.to_wire(),
                    cell: "home_revert_clean".to_string(),
                    measured: conflicts,
                    bound: format!("0 revert conflicts across last {n} non-merge commits"),
                    passed,
                    detail: format!("checked {checked_commits} commits ({note})"),
                    regime: if passed {
                        Regime::Certified
                    } else {
                        Regime::Attested
                    },
                    evaluator_kind: "external:git-merge-tree".to_string(),
                    diagnostic: None,
                });
            }
            Floor::Cap { cell, max } => {
                let eval = evaluate_cap_or_named_cell(
                    fl,
                    cell,
                    *max,
                    format!("<= {max}"),
                    claims_kernel,
                    &canon,
                    sorry_sites,
                    declared_axioms,
                    hb_violations,
                    measured_max_sec_opt,
                    repo_head_sha.as_deref(),
                    kernel_receipt_opt.as_ref(),
                    &lean_idx,
                    &teeth_report,
                    &count_rule,
                    &mut kernel_verified_any,
                    &mut compiled_or_external_passed,
                );
                evaluations.push(eval);
            }
            Floor::Named(name) => {
                let eval = evaluate_cap_or_named_cell(
                    fl,
                    name,
                    0,
                    "== 0".to_string(),
                    claims_kernel,
                    &canon,
                    sorry_sites,
                    declared_axioms,
                    hb_violations,
                    measured_max_sec_opt,
                    repo_head_sha.as_deref(),
                    kernel_receipt_opt.as_ref(),
                    &lean_idx,
                    &teeth_report,
                    &count_rule,
                    &mut kernel_verified_any,
                    &mut compiled_or_external_passed,
                );
                evaluations.push(eval);
            }
        }
        if let Some(eval) = evaluations.last_mut() {
            if let Floor::Configured {
                command: Some(command),
                timeout_ms,
                ..
            } = fl
            {
                // Commands discharge custom named floors only; never override registered checks.
                if !matches!(eval.diagnostic, Some(FloorDiagnostic::UnknownFloor { .. }))
                    || claims_kernel
                    || !matches!(fl.core(), Floor::Named(_))
                    || !gate.methods.iter().any(|binding| {
                        binding.floor.core() == fl.core()
                            && binding.method == Method::Eval(TrustBase::External("shell".into()))
                    })
                {
                    bail!(
                        "command requires a custom named floor with eval:external:shell and no kernel claim: {}",
                        fl.to_wire()
                    );
                }
                *eval = evaluate_command_floor(fl, &canon, command, *timeout_ms)?;
                compiled_or_external_passed |= eval.passed;
            }
            cache.write(digest.as_deref(), eval)?;
        }
    }

    let all_passed = evaluations.iter().all(|e| e.passed);
    let teeth_executed_bit = teeth_report.all_bit
        && teeth_report
            .results
            .iter()
            .any(|r| r.positive_exit == Some(0) && r.negative_exit.is_some());
    let achieved_regime = if !all_passed || fast {
        Regime::Attested
    } else if kernel_verified_any || teeth_executed_bit {
        Regime::Decided
    } else if compiled_or_external_passed {
        Regime::Certified
    } else {
        Regime::Attested
    };

    Ok(JudgeCheckReport {
        judge_name: gate.name.clone(),
        repo_root: canon.to_string_lossy().to_string(),
        checked_at: Utc::now().to_rfc3339(),
        well_formed: true,
        all_passed,
        achieved_regime,
        kernel_verified: kernel_verified_any && all_passed,
        basis: gate.basis.clone(),
        teeth_report,
        evaluations,
        clock,
        deferred_floors,
    })
}

fn evaluate_command_floor(
    fl: &Floor,
    repo: &Path,
    command: &str,
    timeout_ms: u64,
) -> Result<FloorEvaluation> {
    if command.trim().is_empty() || command_invokes_forbidden_macos_lean(command) {
        bail!("empty or forbidden floor command for {}", fl.to_wire());
    }
    let sandbox = create_isolated_tempdir("obb-floor-")?;
    copy_repo_to_sandbox(repo, sandbox.path())?;
    let output = run_sandboxed_shell_cmd(sandbox.path(), command, None, None, timeout_ms)?;
    let passed = output.exit_code == Some(0) && !output.timed_out;
    Ok(FloorEvaluation {
        reused_from_cache: false,
        floor: fl.to_wire(),
        cell: fl.cell_key().into(),
        measured: u64::from(!passed),
        bound: "exit == 0".into(),
        passed,
        detail: format!(
            "command exit {:?}, timed_out={}: {}",
            output.exit_code,
            output.timed_out,
            summarize_cmd_snippet(&output.combined())
        ),
        regime: if passed {
            Regime::Certified
        } else {
            Regime::Attested
        },
        evaluator_kind: "external:shell".into(),
        diagnostic: None,
    })
}

#[allow(clippy::too_many_arguments)]
fn evaluate_cap_or_named_cell<F>(
    fl: &Floor,
    cell: &str,
    max: u64,
    bound_label: String,
    claims_kernel: bool,
    canon: &Path,
    sorry_sites: u64,
    declared_axioms: u64,
    hb_violations: u64,
    measured_max_sec_opt: Option<u64>,
    repo_head_sha: Option<&str>,
    kernel_receipt_opt: Option<&Result<KernelReceipt, String>>,
    lean_idx: &obb_lint::lean_index::LeanIndex,
    teeth_report: &TeethReport,
    count_rule: &F,
    kernel_verified_any: &mut bool,
    compiled_or_external_passed: &mut bool,
) -> FloorEvaluation
where
    F: Fn(&str) -> u64,
{
    // Helper to validate `KernelReceipt` whenever `eval:kernel` is claimed on a kernel-auditable cell.
    let verify_kernel_receipt_for = |cell_name: &str| -> Result<&KernelReceipt, FloorDiagnostic> {
        let Some(res) = kernel_receipt_opt else {
            return Err(FloorDiagnostic::UnverifiedKernelClaim {
                cell: cell_name.to_string(),
                reason: "gate claims `eval:kernel` (`decided`), but no `.obb/kernel-receipt.json` or `reports/kernel-receipt.json` from an external proof kernel (`lean4checker`) was found; lexical token scan cannot self-certify as `kernel`".to_string(),
            });
        };
        let kr = match res {
            Ok(kr) => kr,
            Err(parse_err) => {
                return Err(FloorDiagnostic::UnverifiedKernelClaim {
                    cell: cell_name.to_string(),
                    reason: format!("invalid kernel-receipt.json: {parse_err}"),
                });
            }
        };
        if kr.checker.trim().is_empty() || kr.exit_code != 0 {
            return Err(FloorDiagnostic::UnverifiedKernelClaim {
                cell: cell_name.to_string(),
                reason: format!(
                    "kernel checker `{}` did not succeed (exit_code={})",
                    kr.checker, kr.exit_code
                ),
            });
        }
        if !lean_idx.files.is_empty() && kr.modules_checked == 0 {
            return Err(FloorDiagnostic::UnverifiedKernelClaim {
                cell: cell_name.to_string(),
                reason: format!(
                    "kernel receipt from `{}` checked 0 modules despite {} Lean file(s) in repo",
                    kr.checker,
                    lean_idx.files.len()
                ),
            });
        }
        if let Some(live_head) = repo_head_sha {
            if kr.head_sha.trim() != live_head {
                return Err(FloorDiagnostic::StaleKernelReceipt {
                    cell: cell_name.to_string(),
                    receipt_head_sha: kr.head_sha.clone(),
                    repo_head_sha: live_head.to_string(),
                });
            }
        } else if kr.head_sha.trim().is_empty() {
            return Err(FloorDiagnostic::UnverifiedKernelClaim {
                cell: cell_name.to_string(),
                reason: "kernel receipt has empty `head_sha`".to_string(),
            });
        }
        Ok(kr)
    };

    match cell {
        "no_sorry_ax" => {
            if claims_kernel {
                match verify_kernel_receipt_for(cell) {
                    Ok(kr) => {
                        let measured = sorry_sites.max(kr.sorry_ax_count);
                        let passed = measured <= max;
                        if passed {
                            *kernel_verified_any = true;
                        }
                        FloorEvaluation {
                            reused_from_cache: false,
                            floor: fl.to_wire(),
                            cell: cell.to_string(),
                            measured,
                            bound: bound_label,
                            passed,
                            detail: format!(
                                "kernel `{}` verified HEAD ({} sorryAx in kernel env; {sorry_sites} lexical sorry token(s))",
                                kr.checker, kr.sorry_ax_count
                            ),
                            regime: if passed {
                                Regime::Decided
                            } else {
                                Regime::Attested
                            },
                            evaluator_kind: format!("kernel:{}", kr.checker),
                            diagnostic: None,
                        }
                    }
                    Err(diag) => FloorEvaluation {
                        reused_from_cache: false,
                        floor: fl.to_wire(),
                        cell: cell.to_string(),
                        measured: max.saturating_add(1),
                        bound: bound_label,
                        passed: false,
                        detail: format!(
                            "refused unverified `eval:kernel` on `{cell}` ({sorry_sites} lexical sorry token(s))"
                        ),
                        regime: Regime::Attested,
                        evaluator_kind: "lexical_unverified_kernel_claim".to_string(),
                        diagnostic: Some(diag),
                    },
                }
            } else {
                let passed = sorry_sites <= max;
                FloorEvaluation {
                    reused_from_cache: false,
                    floor: fl.to_wire(),
                    cell: cell.to_string(),
                    measured: sorry_sites,
                    bound: bound_label,
                    passed,
                    detail: format!(
                        "{sorry_sites} `sorry`/`sorryAx` token(s) in Lean corpus (lexical scan; attested)"
                    ),
                    regime: Regime::Attested,
                    evaluator_kind: "lexical".to_string(),
                    diagnostic: None,
                }
            }
        }
        "no_declared_axiom" => {
            if claims_kernel {
                match verify_kernel_receipt_for(cell) {
                    Ok(kr) => {
                        let measured = declared_axioms.max(kr.user_axiom_count);
                        let passed = measured <= max;
                        if passed {
                            *kernel_verified_any = true;
                        }
                        FloorEvaluation {
                            reused_from_cache: false,
                            floor: fl.to_wire(),
                            cell: cell.to_string(),
                            measured,
                            bound: bound_label,
                            passed,
                            detail: format!(
                                "kernel `{}` verified HEAD ({} user axiom(s) in kernel env; {declared_axioms} lexical `axiom` decl(s))",
                                kr.checker, kr.user_axiom_count
                            ),
                            regime: if passed {
                                Regime::Decided
                            } else {
                                Regime::Attested
                            },
                            evaluator_kind: format!("kernel:{}", kr.checker),
                            diagnostic: None,
                        }
                    }
                    Err(diag) => FloorEvaluation {
                        reused_from_cache: false,
                        floor: fl.to_wire(),
                        cell: cell.to_string(),
                        measured: max.saturating_add(1),
                        bound: bound_label,
                        passed: false,
                        detail: format!(
                            "refused unverified `eval:kernel` on `{cell}` ({declared_axioms} lexical `axiom` decl(s))"
                        ),
                        regime: Regime::Attested,
                        evaluator_kind: "lexical_unverified_kernel_claim".to_string(),
                        diagnostic: Some(diag),
                    },
                }
            } else {
                let passed = declared_axioms <= max;
                FloorEvaluation {
                    reused_from_cache: false,
                    floor: fl.to_wire(),
                    cell: cell.to_string(),
                    measured: declared_axioms,
                    bound: bound_label,
                    passed,
                    detail: format!(
                        "{declared_axioms} declared `axiom` command(s) in Lean corpus (lexical scan; attested)"
                    ),
                    regime: Regime::Attested,
                    evaluator_kind: "lexical".to_string(),
                    diagnostic: None,
                }
            }
        }
        "tier1_module_sec_cap" => {
            if claims_kernel {
                return FloorEvaluation {
                    reused_from_cache: false,
                    floor: fl.to_wire(),
                    cell: cell.to_string(),
                    measured: max.saturating_add(1),
                    bound: bound_label,
                    passed: false,
                    detail: "timing cap floor cannot claim `eval:kernel`".to_string(),
                    regime: Regime::Attested,
                    evaluator_kind: "unverified_kernel_claim".to_string(),
                    diagnostic: Some(FloorDiagnostic::UnverifiedKernelClaim {
                        cell: cell.to_string(),
                        reason:
                            "wall-clock module timing is a measurement, not a proof-kernel judgment"
                                .to_string(),
                    }),
                };
            }
            if !lean_idx
                .files
                .iter()
                .any(|f| obb_lint::lean_rules::is_tier1_library_lean_path(&f.rel_path))
            {
                return FloorEvaluation {
                    reused_from_cache: false,
                    floor: fl.to_wire(),
                    cell: cell.to_string(),
                    measured: 0,
                    bound: bound_label,
                    passed: true,
                    detail: "not applicable: repository has no tier-1 Lean library modules".into(),
                    regime: Regime::Attested,
                    evaluator_kind: "not_applicable:no_tier1_lean".into(),
                    diagnostic: None,
                };
            }
            let Some(measured_max_sec) = measured_max_sec_opt else {
                return FloorEvaluation {
                    reused_from_cache: false,
                    floor: fl.to_wire(),
                    cell: cell.to_string(),
                    measured: max.saturating_add(1),
                    bound: bound_label,
                    passed: false,
                    detail: "missing required timing measurement (`max_tier1_sec` in `.obb/build-timings.json` or `reports/build-timings.json`)".to_string(),
                    regime: Regime::Attested,
                    evaluator_kind: "missing_measurement".to_string(),
                    diagnostic: Some(FloorDiagnostic::MissingMeasurement {
                        cell: cell.to_string(),
                        expected_artifact: ".obb/build-timings.json (or reports/build-timings.json) with numeric `max_tier1_sec`".to_string(),
                    }),
                };
            };
            let eff = if hb_violations > 0 {
                measured_max_sec.max(max.saturating_add(hb_violations))
            } else {
                measured_max_sec
            };
            let passed = eff <= max;
            if passed {
                *compiled_or_external_passed = true;
            }
            FloorEvaluation {
                reused_from_cache: false,
                floor: fl.to_wire(),
                cell: cell.to_string(),
                measured: eff,
                bound: bound_label,
                passed,
                detail: format!(
                    "max recorded module build = {measured_max_sec}s; maxHeartbeats > 400k sites = {hb_violations}"
                ),
                regime: if passed {
                    Regime::Certified
                } else {
                    Regime::Attested
                },
                evaluator_kind: "compiled:timing+heartbeat".to_string(),
                diagnostic: None,
            }
        }
        "spec_insensitive_decls" | "lean/spec-insensitive-change" => {
            if claims_kernel {
                return FloorEvaluation {
                    reused_from_cache: false,
                    floor: fl.to_wire(),
                    cell: cell.to_string(),
                    measured: max.saturating_add(1),
                    bound: bound_label,
                    passed: false,
                    detail: "spec-sensitivity census floor cannot claim `eval:kernel`".to_string(),
                    regime: Regime::Attested,
                    evaluator_kind: "unverified_kernel_claim".to_string(),
                    diagnostic: Some(FloorDiagnostic::UnverifiedKernelClaim {
                        cell: cell.to_string(),
                        reason: "spec sensitivity requires an external `lean-transport` census measurement".to_string(),
                    }),
                };
            }
            let Some((insens_count, summary)) = read_spec_insensitive_measurement(canon) else {
                return FloorEvaluation {
                    reused_from_cache: false,
                    floor: fl.to_wire(),
                    cell: cell.to_string(),
                    measured: max.saturating_add(1),
                    bound: bound_label,
                    passed: false,
                    detail: "missing required spec-sensitivity measurement (`.obb/spec-check.json` or `reports/spec-check.json`)".to_string(),
                    regime: Regime::Attested,
                    evaluator_kind: "missing_measurement".to_string(),
                    diagnostic: Some(FloorDiagnostic::MissingMeasurement {
                        cell: cell.to_string(),
                        expected_artifact: ".obb/spec-check.json (or reports/spec-check.json)".to_string(),
                    }),
                };
            };
            let passed = insens_count <= max;
            if passed {
                *compiled_or_external_passed = true;
            }
            FloorEvaluation {
                reused_from_cache: false,
                floor: fl.to_wire(),
                cell: cell.to_string(),
                measured: insens_count,
                bound: bound_label,
                passed,
                detail: summary,
                regime: if passed {
                    Regime::Certified
                } else {
                    Regime::Attested
                },
                evaluator_kind: "external:lean-transport".to_string(),
                diagnostic: None,
            }
        }
        "docs_symbols_exist" => {
            if claims_kernel {
                return unverified_lexical_kernel_eval(fl, cell, max, bound_label);
            }
            let missing_files = count_rule("markdown/missing-lean-file");
            let missing_syms = count_rule("markdown/missing-lean-symbol");
            let bad_ctors = count_rule("markdown/hallucinated-constructor");
            let tot = missing_files + missing_syms + bad_ctors;
            FloorEvaluation {
                reused_from_cache: false,
                floor: fl.to_wire(),
                cell: cell.to_string(),
                measured: tot,
                bound: bound_label,
                passed: tot <= max,
                detail: format!(
                    "{missing_files} missing files, {missing_syms} missing symbols, {bad_ctors} hallucinated constructors (lexical scan; attested)"
                ),
                regime: Regime::Attested,
                evaluator_kind: "lexical".to_string(),
                diagnostic: None,
            }
        }
        "no_tautological_judge_meaning" => {
            if claims_kernel {
                return unverified_lexical_kernel_eval(fl, cell, max, bound_label);
            }
            let c = count_rule("lean/tautological-judge-meaning");
            FloorEvaluation {
                reused_from_cache: false,
                floor: fl.to_wire(),
                cell: cell.to_string(),
                measured: c,
                bound: bound_label,
                passed: c <= max,
                detail: format!(
                    "{c} tautological `Judge.Meaning` instance(s) (lexical scan; attested)"
                ),
                regime: Regime::Attested,
                evaluator_kind: "lexical".to_string(),
                diagnostic: None,
            }
        }
        "no_discarded_tactic_result" => {
            if claims_kernel {
                return unverified_lexical_kernel_eval(fl, cell, max, bound_label);
            }
            let c = count_rule("lean/discarded-tactic-binding");
            FloorEvaluation {
                reused_from_cache: false,
                floor: fl.to_wire(),
                cell: cell.to_string(),
                measured: c,
                bound: bound_label,
                passed: c <= max,
                detail: format!(
                    "{c} tactic `elab`/`macro` discarded binding(s) (lexical scan; attested)"
                ),
                regime: Regime::Attested,
                evaluator_kind: "lexical".to_string(),
                diagnostic: None,
            }
        }
        "no_native_decide_in_proof" => {
            if claims_kernel {
                return unverified_lexical_kernel_eval(fl, cell, max, bound_label);
            }
            let c = count_rule("lean/native-decide-in-proof");
            FloorEvaluation {
                reused_from_cache: false,
                floor: fl.to_wire(),
                cell: cell.to_string(),
                measured: c,
                bound: bound_label,
                passed: c <= max,
                detail: format!(
                    "{c} unaudited `native_decide`/`Lean.ofReduceBool` bypass(es) in library modules (lexical scan; attested)"
                ),
                regime: Regime::Attested,
                evaluator_kind: "lexical".to_string(),
                diagnostic: None,
            }
        }
        "no_narrow_digest_weld" => {
            if claims_kernel {
                return unverified_lexical_kernel_eval(fl, cell, max, bound_label);
            }
            let c = count_rule("lean/narrow-digest-weld");
            FloorEvaluation {
                reused_from_cache: false,
                floor: fl.to_wire(),
                cell: cell.to_string(),
                measured: c,
                bound: bound_label,
                passed: c <= max,
                detail: format!(
                    "{c} narrow <=64-bit or 1-limb digest weld(s) (lexical scan; attested)"
                ),
                regime: Regime::Attested,
                evaluator_kind: "lexical".to_string(),
                diagnostic: None,
            }
        }
        "tooth_structural_presence" | "structural_presence" => {
            if claims_kernel {
                return unverified_lexical_kernel_eval(fl, cell, max, bound_label);
            }
            let has_structural_witness = canon
                .join("crates/obb-cli/tests/planted_faults.rs")
                .is_file()
                || lean_idx.files.iter().any(|f| !f.tooth_targets.is_empty())
                || canon.join("teeth.json").is_file()
                || canon.join(".obb/teeth.json").is_file()
                || canon.join("tests/teeth.json").is_file();
            let failures = if has_structural_witness { 0 } else { 1 };
            FloorEvaluation {
                reused_from_cache: false,
                floor: fl.to_wire(),
                cell: cell.to_string(),
                measured: failures,
                bound: bound_label,
                passed: failures <= max,
                detail: if has_structural_witness {
                    "static `#tooth` / planted-fault structural presence verified (`attested` only; not executed)".to_string()
                } else {
                    "no static `#tooth` / planted-fault files found".to_string()
                },
                regime: Regime::Attested,
                evaluator_kind: "lexical:structural_presence".to_string(),
                diagnostic: None,
            }
        }
        "planted_fault_red" => {
            if claims_kernel {
                return FloorEvaluation {
                    reused_from_cache: false,
                    floor: fl.to_wire(),
                    cell: cell.to_string(),
                    measured: max.saturating_add(1),
                    bound: bound_label,
                    passed: false,
                    detail: "`planted_fault_red` is an executed negative-control test (`eval:compiled`), not `eval:kernel`".to_string(),
                    regime: Regime::Attested,
                    evaluator_kind: "unverified_kernel_claim".to_string(),
                    diagnostic: Some(FloorDiagnostic::UnverifiedKernelClaim {
                        cell: cell.to_string(),
                        reason: "planted_fault_red executes negative-control tests rather than a proof kernel".to_string(),
                    }),
                };
            }
            if teeth_report.total == 0 {
                return FloorEvaluation {
                    reused_from_cache: false,
                    floor: fl.to_wire(),
                    cell: cell.to_string(),
                    measured: max.saturating_add(1),
                    bound: bound_label,
                    passed: false,
                    detail: "no executable `#tooth` specs found in `gate.teeth` or `<repo>/{teeth.json,.obb/teeth.json,tests/teeth.json}`; static file/index existence cannot certify `planted_fault_red`".to_string(),
                    regime: Regime::Attested,
                    evaluator_kind: "executed_tooth".to_string(),
                    diagnostic: Some(FloorDiagnostic::MissingToothExecution {
                        detail: "0 executable teeth declared; provide `teeth.json` or use `tooth_structural_presence` (`eval:lexical`) for attested static checks".to_string(),
                    }),
                };
            }
            let non_bit = (teeth_report.total - teeth_report.bit_count) as u64;
            let passed = non_bit <= max && teeth_report.all_bit;
            let first_bad = teeth_report
                .results
                .iter()
                .find(|r| r.verdict != ToothVerdict::Bit);
            let diag = first_bad.map(|r| FloorDiagnostic::ToothFailure {
                tooth_id: r.id.clone(),
                verdict: r.verdict,
                detail: r.detail.clone(),
            });
            if passed {
                *compiled_or_external_passed = true;
            }
            FloorEvaluation {
                reused_from_cache: false,
                floor: fl.to_wire(),
                cell: cell.to_string(),
                measured: non_bit,
                bound: bound_label,
                passed,
                detail: format!(
                    "executed {} tooth/teeth in isolated sandbox: {} BIT, {} VACUOUS, {} INVALID_TOOTH, {} POSITIVE_FAILED",
                    teeth_report.total,
                    teeth_report.bit_count,
                    teeth_report.vacuous_count,
                    teeth_report.invalid_count,
                    teeth_report.positive_failed_count
                ),
                regime: if passed
                    && teeth_report
                        .results
                        .iter()
                        .any(|r| r.positive_exit == Some(0) && r.negative_exit.is_some())
                {
                    Regime::Decided
                } else if passed {
                    Regime::Certified
                } else {
                    Regime::Attested
                },
                evaluator_kind: "executed_tooth".to_string(),
                diagnostic: diag,
            }
        }
        other => {
            if claims_kernel {
                return unverified_lexical_kernel_eval(fl, other, max, bound_label);
            }
            if is_known_static_lint_rule_id(other) {
                let c = count_rule(other);
                FloorEvaluation {
                    reused_from_cache: false,
                    floor: fl.to_wire(),
                    cell: other.to_string(),
                    measured: c,
                    bound: bound_label,
                    passed: c <= max,
                    detail: format!("static lint rule `{other}` count = {c} (lexical; attested)"),
                    regime: Regime::Attested,
                    evaluator_kind: "lexical".to_string(),
                    diagnostic: None,
                }
            } else {
                FloorEvaluation {
                    reused_from_cache: false,
                    floor: fl.to_wire(),
                    cell: other.to_string(),
                    measured: max.saturating_add(1),
                    bound: bound_label,
                    passed: false,
                    detail: format!(
                        "unknown floor `{other}`: no registered evaluator or `obb-lint` rule (failing closed)"
                    ),
                    regime: Regime::Attested,
                    evaluator_kind: "unknown_floor".to_string(),
                    diagnostic: Some(FloorDiagnostic::UnknownFloor {
                        cell: other.to_string(),
                    }),
                }
            }
        }
    }
}

fn unverified_lexical_kernel_eval(
    fl: &Floor,
    cell: &str,
    max: u64,
    bound_label: String,
) -> FloorEvaluation {
    FloorEvaluation {
        reused_from_cache: false,
        floor: fl.to_wire(),
        cell: cell.to_string(),
        measured: max.saturating_add(1),
        bound: bound_label,
        passed: false,
        detail: format!(
            "lexical/static scanner `{cell}` cannot claim `eval:kernel` (`decided`); bind `eval:lexical` instead"
        ),
        regime: Regime::Attested,
        evaluator_kind: "lexical_unverified_kernel_claim".to_string(),
        diagnostic: Some(FloorDiagnostic::UnverifiedKernelClaim {
            cell: cell.to_string(),
            reason: format!("`{cell}` is a static Rust token/AST scan, not a proof-kernel check"),
        }),
    }
}

/// Evaluate `gate` against git repository `repo_root` and issue a SHA-bound `JudgeReceipt`
/// against `base_rev` (`(base_sha, head_sha, tree_oid)`).
pub fn issue_judge_receipt(gate: &Gate, repo_root: &Path, base_rev: &str) -> Result<JudgeReceipt> {
    issue_judge_receipt_with_state_dir(gate, repo_root, base_rev, None)
}

/// Issue with the selected state vault's key, falling back to the repo key.
pub fn issue_judge_receipt_with_state_dir(
    gate: &Gate,
    repo_root: &Path,
    base_rev: &str,
    state_dir: Option<&Path>,
) -> Result<JudgeReceipt> {
    let canon = repo_root
        .canonicalize()
        .with_context(|| format!("repo path does not exist: {}", repo_root.display()))?;

    let key = receipt_auth::ensure_receipt_key(state_dir, &canon)?;

    let base_sha = run_git_ro(
        &canon,
        &["rev-parse", "--verify", &format!("{base_rev}^{{commit}}")],
    )
    .with_context(|| {
        format!(
            "failed to resolve base revision `{base_rev}` in {}",
            canon.display()
        )
    })?
    .trim()
    .to_string();

    let head_sha = run_git_ro(&canon, &["rev-parse", "--verify", "HEAD^{commit}"])?
        .trim()
        .to_string();
    let tree_oid = run_git_ro(&canon, &["rev-parse", "--verify", "HEAD^{tree}"])?
        .trim()
        .to_string();

    let clean_working_tree = cone_cache::clean_for_cache(&canon)?;

    let diff_raw = run_git_ro(&canon, &["diff", "--name-only", &base_sha, &head_sha])?;
    let changed_paths: Vec<String> = diff_raw
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .map(str::to_string)
        .collect();

    let report = evaluate_gate_with_key(gate, &canon, JudgeClock::Convergence, Some(&key))?;
    let clean_working_tree = clean_working_tree
        && cone_cache::clean_for_cache(&canon)?
        && run_git_ro(&canon, &["rev-parse", "HEAD^{commit}"])?.trim() == head_sha;
    let gate_sha256 = gate.canonical_sha256()?;

    let mut receipt = JudgeReceipt {
        receipt_version: RECEIPT_VERSION,
        judge_name: report.judge_name,
        gate_sha256,
        repo_root: canon.to_string_lossy().to_string(),
        base_sha,
        head_sha,
        tree_oid,
        clean_working_tree,
        changed_paths,
        checked_at: report.checked_at,
        all_passed: report.all_passed,
        achieved_regime: report.achieved_regime,
        kernel_verified: report.kernel_verified,
        teeth_report: report.teeth_report,
        evaluations: report.evaluations,
        receipt_hash: String::new(),
        receipt_mac: None,
    };
    receipt.authenticate(&key)?;
    Ok(receipt)
}

fn resolve_optional_head_sha(repo_root: &Path) -> Option<String> {
    if !repo_root.join(".git").exists() {
        return None;
    }
    run_git_ro(repo_root, &["rev-parse", "--verify", "HEAD^{commit}"])
        .ok()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
}

fn read_kernel_receipt(repo_root: &Path) -> Option<Result<KernelReceipt, String>> {
    for rel in [".obb/kernel-receipt.json", "reports/kernel-receipt.json"] {
        let p = repo_root.join(rel);
        if p.is_file() {
            let res = std::fs::read_to_string(&p)
                .map_err(|e| e.to_string())
                .and_then(|raw| {
                    serde_json::from_str::<KernelReceipt>(&raw).map_err(|e| e.to_string())
                });
            return Some(res);
        }
    }
    None
}

fn read_max_tier1_sec(repo_root: &Path) -> Option<u64> {
    for rel in [".obb/build-timings.json", "reports/build-timings.json"] {
        let p = repo_root.join(rel);
        if let Ok(raw) = std::fs::read_to_string(&p)
            && let Ok(val) = serde_json::from_str::<serde_json::Value>(&raw)
            && let Some(m) = val.get("max_tier1_sec").and_then(|v| v.as_u64())
        {
            return Some(m);
        }
    }
    None
}

fn read_spec_insensitive_measurement(repo_root: &Path) -> Option<(u64, String)> {
    for rel in [".obb/spec-check.json", "reports/spec-check.json"] {
        let p = repo_root.join(rel);
        if let Ok(raw) = std::fs::read_to_string(&p) {
            if let Ok(val) = serde_json::from_str::<serde_json::Value>(&raw) {
                if let Some(c) = val.get("spec_insensitive_decls").and_then(|v| v.as_u64()) {
                    return Some((c, format!("spec_insensitive_decls = {c} from `{rel}`")));
                }
                if let Some(spec_sens) = val.get("spec_sensitive").and_then(|v| v.as_bool()) {
                    let broken = val
                        .get("broken_decls")
                        .and_then(|v| v.as_u64())
                        .unwrap_or(0);
                    let insens = if spec_sens { 0 } else { 1 };
                    return Some((
                        insens,
                        format!(
                            "spec_sensitive = {spec_sens} (broken_decls = {broken}) from `{rel}`"
                        ),
                    ));
                }
            }
            if let Ok(parsed) = parse_transport_census_json(&raw, rel) {
                let insens = if parsed.spec_sensitive { 0 } else { 1 };
                return Some((
                    insens,
                    format!(
                        "lean-transport census spec_sensitive = {} (broken_decls = {}) from `{rel}`",
                        parsed.spec_sensitive, parsed.broken_decls
                    ),
                ));
            }
        }
    }
    None
}

/// Check how many of the most recent `limit` non-merge, non-root commits fail to revert cleanly
/// against `HEAD`. Note: in linear histories where subsequent commits edit the same file, earlier
/// commits may naturally conflict with later commits; `HEAD` itself (the latest landed commit) MUST
/// always revert cleanly against `HEAD` (`parent_sha == HEAD^1`, trivial clean revert), while multi-commit
/// checks inspect independent commits on `HEAD`.
fn check_recent_reverts(repo_root: &Path, window: usize) -> (u64, usize, String) {
    if !repo_root.join(".git").exists() {
        return (0, 0, "not a git repository".to_string());
    }
    let Ok(log_out) = run_git_ro(
        repo_root,
        &[
            "rev-list",
            "--no-merges",
            "--max-parents=1",
            "--min-parents=1",
            "-n",
            &window.max(1).to_string(),
            "HEAD",
        ],
    ) else {
        return (0, 0, "no non-root commits yet".to_string());
    };

    let revs: Vec<&str> = log_out
        .lines()
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .collect();
    if revs.is_empty() {
        return (
            0,
            0,
            "single root commit (nothing above root yet)".to_string(),
        );
    }

    let head_rev = revs[0];
    let head_ok = check_revert_clean(repo_root, head_rev)
        .map(|r| r.clean)
        .unwrap_or(false);

    let mut clean_in_window = 0usize;
    for r in &revs {
        if let Ok(res) = check_revert_clean(repo_root, r)
            && res.clean
        {
            clean_in_window += 1;
        }
    }

    let head_failures = if head_ok { 0 } else { 1 };
    (
        head_failures,
        revs.len(),
        format!(
            "latest commit revert clean = {head_ok}; {clean_in_window}/{} in window revert standalone on HEAD",
            revs.len()
        ),
    )
}

/// Run real structural positive/negative controls without invoking any language compiler.
/// The candidate repository is never modified. These controls test scanner sensitivity,
/// independently of declared behavioral teeth for the candidate implementation.
pub fn evaluate_with_planted_fault_tooth(id: &str) -> Result<ToothExecutionResult> {
    let started = Instant::now();
    let temp = create_isolated_tempdir("obb-structural-tooth-")?;
    let cases = [
        (
            "src/lib.rs",
            "rust/test-in-library",
            "pub fn value() -> u8 { 1 }\n",
            "#[test]\nfn misplaced() {}\n",
        ),
        (
            "src/library.ts",
            "javascript/test-in-library",
            "export const value = 1;\n",
            "test('misplaced', () => {});\n",
        ),
        (
            "src/library.py",
            "python/test-in-library",
            "def value():\n    return 1\n",
            "def test_misplaced():\n    pass\n",
        ),
        (
            "src/Library.lean",
            "lean/test-in-library",
            "def value : Nat := 1\n",
            "#eval value\n",
        ),
        (
            "lean/Obend/Probe.lean",
            "lean/tautological-judge-meaning",
            "def verifyFlowpipe (p c : Nat) : Bool := p == c\ninstance : Obend.Judge Nat Nat where\n  check p c := verifyFlowpipe p c\n  Meaning p c := p = c\n  sound p c h := by simpa using h\n",
            "def verifyFlowpipe (p c : Nat) : Bool := p == c\ninstance : Obend.Judge Nat Nat where\n  check p c := verifyFlowpipe p c\n  Meaning p c := verifyFlowpipe p c = true\n  sound p c h := h\n",
        ),
    ];
    let options = RepoLintOptions {
        strict_tests: true,
        ..Default::default()
    };
    let mut verdict = ToothVerdict::Bit;
    let mut detail = Vec::new();
    for (path, rule, positive, negative) in cases {
        let file = temp.path().join(path);
        std::fs::create_dir_all(file.parent().unwrap())?;
        std::fs::write(&file, positive)?;
        let clean = run_repo_lints_with_options(temp.path(), options)?;
        if clean.findings.iter().any(|f| f.rule_id == rule) {
            verdict = ToothVerdict::PositiveFailed;
            detail.push(format!("{rule}: positive control rejected"));
            break;
        }
        std::fs::write(&file, negative)?;
        let faulty = run_repo_lints_with_options(temp.path(), options)?;
        if !faulty
            .findings
            .iter()
            .any(|f| f.rule_id == rule && f.path == path)
        {
            verdict = ToothVerdict::Vacuous;
            detail.push(format!("{rule}: planted fault escaped"));
            break;
        }
        detail.push(format!("{rule}: BIT"));
        std::fs::write(file, positive)?;
    }
    Ok(ToothExecutionResult {
        reused_from_cache: false,
        id: id.into(),
        verdict,
        positive_exit: None,
        negative_exit: None,
        duration_ms: started.elapsed().as_millis() as u64,
        detail: format!(
            "built-in structural controls (no shell/kernel execution): {}",
            detail.join("; ")
        ),
    })
}
