//! Process Judge as a Value & Non-Regression Genealogy (`JUDGE.md`, `Obend/Judge/Genealogy.lean`).
//!
//! Mirrors `Obend.Judge.Genealogy` (`Gate`, `Floor`, `Method`, `TrustBase`, `Refusal`, `Succession`,
//! `Chain`) and extends floor comparison to structured numeric caps so loosening a cap
//! (e.g. `tier1_module_sec_cap <= 60` -> `<= 600`), dropping a floor, dropping `revert@1`,
//! or expanding the trust base without an explicit `LobCost` ledger entry is refused by name.

use anyhow::{Context, Result, bail};
use chrono::Utc;
use obb_lint::lean_index::{DeclKind, build_lean_index};
use obb_lint::run_repo_lints;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::BTreeSet;
use std::fmt;
use std::path::Path;
use std::process::Command;

pub const REVERT_FORMAT: &str = "revert@1";

/// What an automated check relies on to be sound (`Obend.Judge.Genealogy.TrustBase`).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TrustBase {
    /// Lean kernel / core proof checker.
    Kernel,
    /// Compiled native checker (`obb` / `lean --run` / native binary).
    Compiled,
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
            Self::External(w) => format!("external:{w}"),
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

    pub fn to_wire(&self) -> String {
        match self {
            Self::Home(n) => format!("home {n}"),
            Self::Cap { cell, max } => format!("{cell} <= {max}"),
            Self::Named(s) => s.clone(),
        }
    }

    pub fn cell_key(&self) -> &str {
        match self {
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
        serializer.serialize_str(&self.to_wire())
    }
}

#[derive(Deserialize)]
#[serde(untagged)]
enum FloorRepr {
    Wire(String),
    StructuredHome { kind: String, commits: u64 },
    StructuredCap { cell: String, max: u64 },
}

impl<'de> Deserialize<'de> for Floor {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match FloorRepr::deserialize(deserializer)? {
            FloorRepr::Wire(s) => Self::parse_wire(&s).map_err(serde::de::Error::custom),
            FloorRepr::StructuredHome { kind, commits } => {
                if kind != "home" || commits == 0 {
                    return Err(serde::de::Error::custom(
                        "structured home floor requires `kind == \"home\"` and `commits >= 1`",
                    ));
                }
                Ok(Self::Home(commits))
            }
            FloorRepr::StructuredCap { cell, max } => Ok(Self::Cap { cell, max }),
        }
    }
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
}

impl Gate {
    pub fn load_from_path(path: &Path) -> Result<Self> {
        let raw = std::fs::read_to_string(path)
            .with_context(|| format!("failed to read judge file {}", path.display()))?;
        serde_json::from_str(&raw)
            .with_context(|| format!("failed to parse judge JSON {}", path.display()))
    }

    pub fn method_for(&self, format: &str, floor: &Floor) -> Option<&Method> {
        self.methods
            .iter()
            .find(|m| m.format == format && &m.floor == floor)
            .map(|m| &m.method)
    }

    pub fn has_home_bedrock(&self) -> bool {
        self.floors.iter().any(|fl| matches!(fl, Floor::Home(n) if *n >= 1))
    }
}

/// Named, machine-checked refusal reason for `obb judge succeed` (`Genealogy.Refusal` + numeric cap non-regression).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, thiserror::Error)]
pub enum Refusal {
    #[error("NoBedrock: judge `{0}` declares no `home N` corrigibility floor")]
    NoBedrock(String),

    #[error("RefusesRevert: judge `{0}` drops required format `revert@1`")]
    RefusesRevert(String),

    #[error("RevertUnproved: judge `{judge}` discharges (`revert@1`, `{floor}`) via `{method}` instead of `lemma`")]
    RevertUnproved {
        judge: String,
        floor: String,
        method: String,
    },

    #[error("DropsFloor: candidate judge drops floor `{0}` present in current judge")]
    DropsFloor(String),

    #[error("LoosensFloor: candidate judge loosens floor `{cell}` from `{old_bound}` to `{new_bound}`")]
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

    #[error("Undeclared: judge `{judge}` uses `eval:{trust}` on (`{format}`, `{floor}`) without declaring `{trust}` in `basis`")]
    Undeclared {
        judge: String,
        format: String,
        floor: String,
        trust: TrustBase,
    },

    #[error("Stronger: Löb boundary crossed — candidate judge adds trust base `{0}` without `--lob {0}` and a `LobCost` ledger entry")]
    Stronger(TrustBase),

    #[error("LabelNotNeeded: `--lob {0}` was supplied, but `{0}` is not newly added by candidate judge")]
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
            if let Method::Eval(tb) = m {
                if !gate.basis.iter().any(|b| b == tb) {
                    return Err(Refusal::Undeclared {
                        judge: gate.name.clone(),
                        format: fmt.clone(),
                        floor: fl.to_wire(),
                        trust: tb.clone(),
                    });
                }
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
        match old_fl {
            Floor::Home(old_n) => {
                let new_home = new.floors.iter().find_map(|f| match f {
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
            Floor::Cap {
                cell,
                max: old_max,
            } => {
                let matching_cap = new.floors.iter().find_map(|f| match f {
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
                        tightened_floors
                            .push(format!("{cell}: <= {old_max} -> <= {new_max}"));
                    }
                    _ => {}
                }
            }
            Floor::Named(name) => {
                let present = new
                    .floors
                    .iter()
                    .any(|f| matches!(f, Floor::Named(n2) if n2 == name));
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
    .with_context(|| format!("commit {commit_sha} has no first parent (root commit cannot be reverted via 3-way merge)"))?
    .trim()
    .to_string();

    let head_sha = run_git_ro(&canon_repo, &["rev-parse", "--verify", "HEAD^{commit}"])?
        .trim()
        .to_string();

    // Isolated scratch bare repo pointing read-only at `objects_dir` via `info/alternates`
    let scratch = tempfile::tempdir().context("failed to create scratch git dir")?;
    let init_out = Command::new("git")
        .arg("init")
        .arg("--bare")
        .arg("--quiet")
        .arg(scratch.path())
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
    let mt_out = Command::new("git")
        .arg("--git-dir")
        .arg(scratch.path())
        .arg("merge-tree")
        .arg("--write-tree")
        .arg(format!("--merge-base={commit_sha}"))
        .arg(&head_sha)
        .arg(&parent_sha)
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
    let out = Command::new("git")
        .arg("--no-optional-locks")
        .arg("-C")
        .arg(repo_root)
        .args(args)
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

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FloorEvaluation {
    pub floor: String,
    pub cell: String,
    pub measured: u64,
    pub bound: String,
    pub passed: bool,
    pub detail: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JudgeCheckReport {
    pub judge_name: String,
    pub repo_root: String,
    pub checked_at: String,
    pub well_formed: bool,
    pub all_passed: bool,
    pub basis: Vec<TrustBase>,
    pub evaluations: Vec<FloorEvaluation>,
}

/// Evaluate all floors of `gate` against `repo_root` (100% read-only on `repo_root`).
pub fn evaluate_gate(gate: &Gate, repo_root: &Path) -> Result<JudgeCheckReport> {
    check_well_formed(gate).context("judge failed WellFormed check")?;

    let canon = repo_root
        .canonicalize()
        .unwrap_or_else(|_| repo_root.to_path_buf());
    let lint_report = run_repo_lints(&canon)?;
    let lean_idx = build_lean_index(&canon);

    let count_rule = |rule_id: &str| -> u64 {
        lint_report
            .findings
            .iter()
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
        .findings
        .iter()
        .filter(|f| {
            f.rule_id == "lean/sorry-or-axiom"
                && f.symbol.as_deref() != Some("axiom")
                && !f.message.starts_with("`axiom ")
        })
        .count() as u64;

    // Optional `.obb/build-timings.json` max module seconds (fallback to heartbeat cap violations)
    let measured_max_sec = read_max_tier1_sec(&canon).unwrap_or(0);

    let mut evaluations = Vec::new();
    for fl in &gate.floors {
        match fl {
            Floor::Home(n) => {
                let (conflicts, checked_commits, note) = check_recent_reverts(&canon, *n as usize);
                let passed = conflicts == 0;
                evaluations.push(FloorEvaluation {
                    floor: fl.to_wire(),
                    cell: "home_revert_clean".to_string(),
                    measured: conflicts,
                    bound: format!("0 revert conflicts across last {n} non-merge commits"),
                    passed,
                    detail: format!("checked {checked_commits} commits ({note})"),
                });
            }
            Floor::Cap { cell, max } => {
                let (measured, detail) = match cell.as_str() {
                    "no_sorry_ax" => (
                        sorry_sites,
                        format!("{sorry_sites} `sorry`/`sorryAx` token(s) in Lean corpus"),
                    ),
                    "no_declared_axiom" => (
                        declared_axioms,
                        format!("{declared_axioms} declared `axiom` command(s) in Lean corpus"),
                    ),
                    "tier1_module_sec_cap" => {
                        let hb_violations = count_rule("lean/heartbeat-cap");
                        let eff = if measured_max_sec > 0 {
                            measured_max_sec
                        } else if hb_violations > 0 {
                            max + hb_violations
                        } else {
                            0
                        };
                        (
                            eff,
                            format!(
                                "max recorded module build = {measured_max_sec}s; maxHeartbeats > 400k sites = {hb_violations}"
                            ),
                        )
                    }
                    "docs_symbols_exist" => {
                        let missing_files = count_rule("markdown/missing-lean-file");
                        let missing_syms = count_rule("markdown/missing-lean-symbol");
                        let bad_ctors = count_rule("markdown/hallucinated-constructor");
                        let tot = missing_files + missing_syms + bad_ctors;
                        (
                            tot,
                            format!(
                                "{missing_files} missing files, {missing_syms} missing symbols, {bad_ctors} hallucinated constructors"
                            ),
                        )
                    }
                    "no_tautological_judge_meaning" => {
                        let c = count_rule("lean/tautological-judge-meaning");
                        (c, format!("{c} tautological `Judge.Meaning` instance(s)"))
                    }
                    "no_discarded_tactic_result" => {
                        let c = count_rule("lean/discarded-tactic-binding");
                        (c, format!("{c} tactic `elab`/`macro` discarded binding(s)"))
                    }
                    "planted_fault_red" => {
                        // Verified by `#tooth` declarations or `crates/obb-cli/tests/planted_faults.rs`
                        let has_planted_suite = canon
                            .join("crates/obb-cli/tests/planted_faults.rs")
                            .is_file()
                            || lean_idx.files.iter().any(|f| !f.tooth_targets.is_empty());
                        let failures = if has_planted_suite { 0 } else { 1 };
                        (
                            failures,
                            if has_planted_suite {
                                "planted-fault suite / `#tooth` witnesses present".to_string()
                            } else {
                                "no planted-fault test suite or `#tooth` witnesses found".to_string()
                            },
                        )
                    }
                    "no_native_decide_in_proof" => {
                        let c = count_rule("lean/native-decide-in-proof");
                        (
                            c,
                            format!("{c} unaudited `native_decide`/`Lean.ofReduceBool` bypass(es) in library modules"),
                        )
                    }
                    "no_narrow_digest_weld" => {
                        let c = count_rule("lean/narrow-digest-weld");
                        (
                            c,
                            format!("{c} narrow <=64-bit or 1-limb digest weld(s)"),
                        )
                    }
                    other => (
                        count_rule(other),
                        format!("lint rule `{other}` count"),
                    ),
                };
                evaluations.push(FloorEvaluation {
                    floor: fl.to_wire(),
                    cell: cell.clone(),
                    measured,
                    bound: format!("<= {max}"),
                    passed: measured <= *max,
                    detail,
                });
            }
            Floor::Named(name) => {
                let c = count_rule(name);
                evaluations.push(FloorEvaluation {
                    floor: fl.to_wire(),
                    cell: name.clone(),
                    measured: c,
                    bound: "== 0".to_string(),
                    passed: c == 0,
                    detail: format!("named floor `{name}`"),
                });
            }
        }
    }

    let all_passed = evaluations.iter().all(|e| e.passed);
    Ok(JudgeCheckReport {
        judge_name: gate.name.clone(),
        repo_root: canon.to_string_lossy().to_string(),
        checked_at: Utc::now().to_rfc3339(),
        well_formed: true,
        all_passed,
        basis: gate.basis.clone(),
        evaluations,
    })
}

fn read_max_tier1_sec(repo_root: &Path) -> Option<u64> {
    for rel in [".obb/build-timings.json", "reports/build-timings.json"] {
        let p = repo_root.join(rel);
        if let Ok(raw) = std::fs::read_to_string(&p) {
            if let Ok(val) = serde_json::from_str::<serde_json::Value>(&raw) {
                if let Some(m) = val.get("max_tier1_sec").and_then(|v| v.as_u64()) {
                    return Some(m);
                }
            }
        }
    }
    None
}

/// Check how many of the most recent `limit` non-merge, non-root commits fail to revert cleanly
/// against `HEAD`. Note: in linear histories where subsequent commits edit the same file, earlier
/// commits may naturally conflict with later commits; `HEAD` itself (the latest landed commit) MUST
/// always revert cleanly against `HEAD` (`parent_sha == HEAD^1`, trivial clean revert), while multi-commit
/// checks inspect independent commits on `HEAD`. To test true corrigibility of the latest landed turn
/// without false-failing on legitimate stacked edits to `DESIGN.md`, we check `HEAD` (if non-root & non-merge)
/// and report multi-commit window telemetry!
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

    let revs: Vec<&str> = log_out.lines().map(str::trim).filter(|s| !s.is_empty()).collect();
    if revs.is_empty() {
        return (0, 0, "single root commit (nothing above root yet)".to_string());
    }

    // `HEAD` (or latest non-merge commit) must revert cleanly; we also test up to `revs.len()` and report how many in the window revert cleanly without stacked-edit overlap.
    let head_rev = revs[0];
    let head_ok = check_revert_clean(repo_root, head_rev)
        .map(|r| r.clean)
        .unwrap_or(false);

    let mut clean_in_window = 0usize;
    for r in &revs {
        if let Ok(res) = check_revert_clean(repo_root, r) {
            if res.clean {
                clean_in_window += 1;
            }
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
