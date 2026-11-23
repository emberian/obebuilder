//! Core domain types for `obb` (`DESIGN.md` §2.5, §3, `PROCESS.md`, `spec/process.json`).

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fmt;
use std::path::Path;

/// Gunter–Jackson–Zave (2000) five artifact kinds (`DESIGN.md` §2.5, §3).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ArtifactKind {
    /// Domain knowledge (`W`): facts/assumptions about the physical or operational world.
    W,
    /// Requirement (`R`): desired properties in the world/user vocabulary.
    R,
    /// Specification (`S`): interface/theorem statements at the machine-world boundary.
    S,
    /// Program (`P`): executable implementation, proof term, RTL, or script.
    P,
    /// Platform / Machine (`M`): runtime, compiler, FPGA, build box, or harness.
    M,
}

impl ArtifactKind {
    pub fn label(self) -> &'static str {
        match self {
            Self::W => "W (Domain Knowledge)",
            Self::R => "R (Requirement)",
            Self::S => "S (Specification)",
            Self::P => "P (Program)",
            Self::M => "M (Platform)",
        }
    }

    pub fn code(self) -> &'static str {
        match self {
            Self::W => "W",
            Self::R => "R",
            Self::S => "S",
            Self::P => "P",
            Self::M => "M",
        }
    }
}

impl fmt::Display for ArtifactKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.code())
    }
}

/// Epistemic claim regime (`DESIGN.md` §2.5, `JUDGE.md`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Regime {
    /// An oracle outside the author agreed (Lean kernel over independent spec, measurement,
    /// reference tool, published benchmark, operational semantics).
    Decided,
    /// A checkable artifact or certificate exists and was re-checked by compiled/external checker.
    Certified,
    /// Asserted without an independent non-vacuous oracle (prose, closed concrete pin, or tautology).
    Attested,
}

impl Regime {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Decided => "decided",
            Self::Certified => "certified",
            Self::Attested => "attested",
        }
    }
}

impl fmt::Display for Regime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Finding severity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    Error,
    Warning,
    Info,
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Error => f.write_str("error"),
            Self::Warning => f.write_str("warning"),
            Self::Info => f.write_str("info"),
        }
    }
}

/// The eighteen frustration sinks from `PROCESS.md` §3 and `spec/process.json`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Sink {
    Theater,
    Label,
    Ritual,
    Stalled,
    EmberGated,
    Lost,
    SummaryRebuilt,
    Miscalibrated,
    Shrunk,
    SideBranched,
    Mirror,
    HarnessLoss,
    Slow,
    Navel,
    Appended,
    Scar,
    Stomped,
    Alone,
}

impl Sink {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Theater => "Theater",
            Self::Label => "Label",
            Self::Ritual => "Ritual",
            Self::Stalled => "Stalled",
            Self::EmberGated => "EmberGated",
            Self::Lost => "Lost",
            Self::SummaryRebuilt => "SummaryRebuilt",
            Self::Miscalibrated => "Miscalibrated",
            Self::Shrunk => "Shrunk",
            Self::SideBranched => "SideBranched",
            Self::Mirror => "Mirror",
            Self::HarnessLoss => "HarnessLoss",
            Self::Slow => "Slow",
            Self::Navel => "Navel",
            Self::Appended => "Appended",
            Self::Scar => "Scar",
            Self::Stomped => "Stomped",
            Self::Alone => "Alone",
        }
    }
}

impl fmt::Display for Sink {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// One mechanical lint finding with actionable remediation (`DESIGN.md` §2.6).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Finding {
    pub rule_id: String,
    pub severity: Severity,
    pub artifact_kind: ArtifactKind,
    pub max_regime: Regime,
    pub sink: Option<Sink>,
    pub path: String,
    pub line: usize,
    pub column: usize,
    pub symbol: Option<String>,
    pub message: String,
    pub remediation: String,
}

/// Per-directory classification extending `Obend/Census.lean`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DirectoryCensus {
    pub directory: String,
    pub files: usize,
    pub universal_theorems: usize,
    pub closed_theorems: usize,
    pub examples: usize,
    pub teeth: usize,
    pub decided_claims: usize,
    pub certified_claims: usize,
    pub attested_claims: usize,
    pub findings_count: usize,
    pub error_count: usize,
    pub warning_count: usize,
}

/// Giant monolithic `.lean` module (> 4,000 lines) risking elaboration RSS blowup.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct MonolithicModule {
    pub path: String,
    pub lines: usize,
    pub declarations: usize,
    pub theorems: usize,
    pub structures_and_classes: usize,
}

/// Per-directory modularity and compositionality breakdown.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct DirectoryModularity {
    pub directory: String,
    pub files: usize,
    pub total_lines: usize,
    pub max_lines: usize,
    pub structures_and_classes: usize,
    pub instances: usize,
    pub total_theorems: usize,
    pub composed_theorems: usize,
    pub isolated_leaf_theorems: usize,
    pub carrier_to_leaf_ratio: f64,
}

/// High-blast-radius `.lean` hub whose public `.olean` header rebuilds many downstream modules.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConeHubSummary {
    pub module: String,
    pub path: String,
    pub public_fan_in: usize,
    pub blast_radius: usize,
}

/// Repository-wide Modularity & Compositionality Index (`obb lint --modularity`).
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct ModularityReport {
    pub monolithic_line_threshold: usize,
    pub lean_files: usize,
    pub total_lean_lines: usize,
    pub max_module_lines: usize,
    pub max_module_path: Option<String>,
    pub structures: usize,
    pub classes: usize,
    pub instances: usize,
    pub inductives: usize,
    pub total_theorems: usize,
    pub composed_theorems: usize,
    pub isolated_leaf_theorems: usize,
    /// `(structures + classes) / max(1, isolated_leaf_theorems)`.
    pub carrier_to_leaf_ratio: f64,
    /// `composed_theorems / max(1, total_theorems)`.
    pub theorem_reuse_ratio: f64,
    /// Composite 0..100 modularity score weighting theorem reuse, algebraic interfaces, and module size bounds.
    pub compositionality_index: f64,
    #[serde(default)]
    pub max_public_cone_depth: usize,
    #[serde(default)]
    pub critical_path: Vec<String>,
    #[serde(default)]
    pub high_blast_radius_hubs: Vec<ConeHubSummary>,
    #[serde(default)]
    pub file_wide_expose_modules: usize,
    #[serde(default)]
    pub public_meta_import_leaks: usize,
    pub monolithic_modules: Vec<MonolithicModule>,
    pub by_directory: Vec<DirectoryModularity>,
}

/// Complete `obb lint` report over a repository.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LintReport {
    pub repo_root: String,
    pub generated_at: String,
    pub files_scanned: usize,
    pub lean_declarations_indexed: usize,
    pub lean_inductives_indexed: usize,
    pub total_findings: usize,
    pub errors: usize,
    pub warnings: usize,
    #[serde(default)]
    pub tier1_guards: usize,
    #[serde(default)]
    pub tier1_teeth: usize,
    #[serde(default)]
    pub tier1_evals: usize,
    pub by_rule: BTreeMap<String, usize>,
    pub by_artifact_kind: BTreeMap<String, usize>,
    pub by_regime: BTreeMap<String, usize>,
    pub by_sink: BTreeMap<String, usize>,
    pub directory_census: Vec<DirectoryCensus>,
    #[serde(default)]
    pub modularity: ModularityReport,
    pub findings: Vec<Finding>,
}

/// Machine-readable process specification loaded from `spec/process.json`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProcessSpec {
    pub version: u32,
    pub source: String,
    pub ember_events: Vec<String>,
    pub machines: MachinesSpec,
    pub guards: BTreeMap<String, GuardSpec>,
    pub sinks: BTreeMap<String, SinkSpec>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MachinesSpec {
    pub campaign: CampaignMachineSpec,
    pub quest: QuestMachineSpec,
    pub segment: SegmentMachineSpec,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CampaignMachineSpec {
    pub initial: String,
    pub states: Vec<String>,
    pub transitions: Vec<TransitionSpec>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QuestMachineSpec {
    pub initial: String,
    pub states: Vec<String>,
    pub sinks: Vec<String>,
    pub transitions: Vec<TransitionSpec>,
    pub sink_edges: BTreeMap<String, Vec<String>>,
    pub sink_exit_rule: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SegmentMachineSpec {
    pub initial: String,
    pub states: Vec<String>,
    pub transitions: Vec<TransitionSpec>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TransitionSpec {
    pub from: String,
    pub to: String,
    #[serde(default)]
    pub guard: Option<String>,
    #[serde(default)]
    pub when: Option<String>,
    #[serde(default)]
    pub on: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GuardSpec {
    pub source: String,
    pub passes: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SinkSpec {
    pub detector: String,
    pub exit: String,
}

impl ProcessSpec {
    pub fn load_from_path(path: &Path) -> Result<Self> {
        let raw = std::fs::read_to_string(path)
            .with_context(|| format!("failed to read process spec at {}", path.display()))?;
        serde_json::from_str(&raw)
            .with_context(|| format!("failed to parse process spec JSON at {}", path.display()))
    }

    pub fn embedded_default() -> Result<Self> {
        let raw = include_str!("../../../spec/process.json");
        serde_json::from_str(raw).context("failed to parse embedded spec/process.json")
    }

    /// Find matching campaign transition `(from -> to)`.
    pub fn find_campaign_transition(&self, from: &str, to: &str) -> Option<&TransitionSpec> {
        self.machines
            .campaign
            .transitions
            .iter()
            .find(|t| t.from == from && t.to == to)
    }

    /// Find matching normal quest transition `(from -> to)`.
    pub fn find_quest_transition(&self, from: &str, to: &str) -> Option<&TransitionSpec> {
        self.machines
            .quest
            .transitions
            .iter()
            .find(|t| t.from == from && t.to == to)
    }

    /// Check whether a quest in `from_state` can enter `sink`.
    pub fn can_quest_enter_sink(&self, from_state: &str, sink: &str) -> bool {
        if !self.machines.quest.sinks.iter().any(|s| s == sink) {
            return false;
        }
        if let Some(allowed) = self.machines.quest.sink_edges.get("*")
            && allowed.iter().any(|s| s == sink)
        {
            return true;
        }
        if let Some(allowed) = self.machines.quest.sink_edges.get(from_state)
            && allowed.iter().any(|s| s == sink)
        {
            return true;
        }
        false
    }

    /// Find matching segment transition `(from -> to)`.
    pub fn find_segment_transition(&self, from: &str, to: &str) -> Option<&TransitionSpec> {
        self.machines
            .segment
            .transitions
            .iter()
            .find(|t| t.from == from && t.to == to)
    }

    /// Validate that an ember-facing event is strictly one of `["aim", "decision", "taste"]`.
    pub fn is_valid_ember_event(&self, event_kind: &str) -> bool {
        self.ember_events.iter().any(|e| e == event_kind)
    }
}

/// Deterministic SHA-256 hex digest helper for artifacts and ledger records.
pub fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hex::encode(hasher.finalize())
}
