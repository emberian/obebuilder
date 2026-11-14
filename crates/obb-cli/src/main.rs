//! `obb` — Process Supervisor, Mechanical Anti-Slop Linter & Non-Regression Judge (`DESIGN.md` §6).

use anyhow::{Result, bail};
use clap::{Parser, Subcommand};
use obb_broker::{
    BuildPlanOptions, HostChoice, SshExecutor, plan_build as broker_plan_build, probe_hosts,
};
use obb_cli::serve::run_server_with_options;
use obb_judge::pipeline::{PipelineCheckOptions, PipelineStage, check_pipeline_with_options};
use obb_judge::{
    Gate, JudgeClock, JudgeReceipt, TrustBase, check_revert_clean, check_succeed,
    check_well_formed, evaluate_gate_on, issue_judge_receipt_with_state_dir,
};
use obb_lint::apex::{ApexCheckOptions, ApexManifest, DEFAULT_APEX_MANIFEST_REL, evaluate_apex};
use obb_lint::cone::{ProposedShard, plan_cone_shards, scan_repo_cone};
use obb_lint::harness::{harness_check, harness_install, harness_list};
use obb_lint::spec_check::run_spec_sensitivity_check;
use obb_lint::{RepoLintOptions, filter_report_by_rule, run_repo_lints_with_options};
use obb_quarry::{
    DEFAULT_QUARRY_MANIFEST_REL, QuarryManifest, QuarryState, inspect_quarry_target, status_quarry,
    sync_quarry,
};
use obb_state::{CampaignGuardEvidence, QuestGuardEvidence, StateStore};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

#[derive(Parser, Debug)]
#[command(
    name = "obb",
    version,
    about = "Obebuilder metaharness: anti-slop linter, genealogy judge, process statechart & visualizer"
)]
struct Cli {
    /// Workspace root containing `judge.json` and `spec/process.json`
    #[arg(long, global = true, default_value = ".")]
    workspace: PathBuf,

    /// Local state vault for `state.db` and `events.jsonl`; overrides OBB_STATE_DIR and default workspace/XDG locations
    #[arg(long, global = true)]
    state_dir: Option<PathBuf>,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// Mechanical anti-slop, vacuity, cross-language mirror & Markdown symbol/constructor linter
    Lint {
        /// Repository root to scan (strictly read-only)
        #[arg(long, default_value = ".")]
        repo: PathBuf,

        /// Emit structured JSON report
        #[arg(long)]
        json: bool,

        /// Filter findings by rule ID substring (e.g. `lean/discarded`, `markdown/hallucinated`)
        #[arg(long)]
        rule: Option<String>,

        /// Exit with non-zero code when errors > 0
        #[arg(long)]
        strict: bool,

        /// Escalate `lean/file-wide-expose` (`@[expose] public section`) and `lean/excessive-decl-expose` (`> 12` `@[expose]` decls in `> 80`-line `module` files) from warning to error
        #[arg(long)]
        strict_expose: bool,

        /// Escalate `lean/single-sequence-harness` (`apex_*_turn_{safe,sound}` without multi-turn trace/reachability theorem) from warning to error
        #[arg(long)]
        strict_harnesses: bool,

        /// Escalate `lean/judge-fragment-restates-check` and `lean/pigeonhole-vacuous-premise` from warning to error
        #[arg(long)]
        strict_vacuity: bool,

        /// Escalate `cross-lang/domain-tag-drift` (Rust↔Lean domain tag & framing arity drift) from warning to error
        #[arg(long)]
        strict_wire: bool,

        /// Reject test declarations in Rust, JS/TS, Python and Lean library sources
        #[arg(long)]
        strict_tests: bool,

        /// Print detailed Modularity & Compositionality Index (carrier/leaf ratios & >1,500-line monoliths)
        #[arg(long)]
        modularity: bool,

        #[command(subcommand)]
        sub: Option<LintSubcommand>,
    },

    /// Sub-50ms Lean 4.35 `public import` Cone Analyzer, Blast-Radius Calculator & Disjoint Swarm Shard Planner (`LAW-M1`, `LAW-M2`, `LAW-M6`)
    Cone {
        /// Repository root to scan (strictly read-only)
        #[arg(long, global = true, default_value = ".")]
        repo: PathBuf,

        /// Emit structured JSON report
        #[arg(long, global = true)]
        json: bool,

        /// Fail when any module's outgoing `public import` DAG depth exceeds `<MAX_DEPTH>`
        #[arg(long)]
        max_depth: Option<usize>,

        #[command(subcommand)]
        sub: Option<ConeSubcommand>,
    },

    /// Whole-System Compositional Assurance & Anti-Leaf-Island Engine (`quarry/obend-apex.toml`)
    Apex {
        #[command(subcommand)]
        sub: ApexSubcommand,
    },

    /// Two-Stage `[HypothesisLedger]` Interface-Lock & Swarm Proof-Fill Verifier (`STAGE_A_LOCKED` -> `STAGE_B_SEALED`)
    Pipeline {
        #[command(subcommand)]
        sub: PipelineSubcommand,
    },

    /// Canonical Multi-Agent Harness Customizations (`AGENTS.md`, `GEMINI.md`, `CLAUDE.md`, `.agents/skills/*`, `.claude/skills/*`)
    Harness {
        #[command(subcommand)]
        sub: HarnessSubcommand,
    },

    /// Remote `hbox` + `bb2` `.olean` Hardlink Seed Pool, Health Prober & Bounded `lake build` Batcher
    Broker {
        #[command(subcommand)]
        sub: BrokerSubcommand,
    },

    /// Donor History Namespace Manager (`refs/quarry/<donor>/*`) & 6-Gate Pre-Uptake Surgery Auditor
    Quarry {
        #[command(subcommand)]
        sub: QuarrySubcommand,
    },

    /// Process Judge as a Value & machine-checked G4 non-regression (`JUDGE.md`)
    Judge {
        #[command(subcommand)]
        sub: JudgeSubcommand,
    },

    /// Campaign & Quest statechart supervisor + live `cv` / disk / git guards (`PROCESS.md`)
    State {
        #[command(subcommand)]
        sub: Box<StateSubcommand>,
    },

    /// First-class Segment lifecycle (`new`, `fork`, `continue`, `distill`, `merge`, `forget`, `adopt`, `compare`, `list`)
    Seg {
        #[command(subcommand)]
        sub: SegSubcommand,
    },

    /// Append-only hash-chained JSONL ledger (`<state_dir>/events.jsonl`)
    Ledger {
        #[command(subcommand)]
        sub: LedgerSubcommand,
    },

    /// Lightweight localhost dashboard + JSON/SSE API (`DESIGN.md` §5)
    Serve {
        #[arg(long, default_value = "127.0.0.1")]
        host: String,

        #[arg(long, default_value_t = 7878)]
        port: u16,

        /// Target repository for live `obb lint` inspection (read-only)
        #[arg(long, default_value = "/Users/ember/dev/obend")]
        repo: PathBuf,

        /// Explicitly populate an empty state vault with `demo_seed` fixture rows for UI preview
        #[arg(long)]
        seed_demo: bool,
    },
}

#[derive(Subcommand, Debug)]
enum LintSubcommand {
    /// Invoke `lean-transport --no-repair` to verify a spec edit breaks downstream theorems
    SpecCheck {
        #[arg(long)]
        lean_root: PathBuf,

        #[arg(long)]
        changed: PathBuf,

        #[arg(long)]
        transport_bin: Option<PathBuf>,

        #[arg(long)]
        json: bool,
    },
}

#[derive(Subcommand, Debug)]
enum ConeSubcommand {
    /// Partition modules into K disjoint swarm write slices or validate proposed worker slices & `fan_in > 25` hub contention
    Plan {
        /// Number of parallel swarm worker shards when auto-partitioning
        #[arg(long, default_value_t = 4)]
        shards: usize,

        /// Proposed parallel worker slice(s) `<shard_name>=<file1>,<file2>,...` to validate for disjointness & hub contention
        #[arg(long = "propose")]
        propose: Vec<String>,

        /// Proposed Wave-0 barrier slice(s) `<shard_name>=<file1>,<file2>,...` allowed to edit `fan_in > 25` hubs before fanout
        #[arg(long = "wave0")]
        wave0: Vec<String>,
    },
}

#[derive(Subcommand, Debug)]
enum ApexSubcommand {
    /// Report Apex theorem verification, per-subsystem compositional coverage %, and unwired leaf islands
    Status {
        /// Target repository root (strictly read-only)
        #[arg(long, default_value = ".")]
        repo: PathBuf,

        /// Path to `obend-apex.toml` manifest (defaults to `<workspace>/quarry/obend-apex.toml`)
        #[arg(long)]
        manifest: Option<PathBuf>,

        /// Emit structured JSON report
        #[arg(long)]
        json: bool,
    },

    /// Enforce that all registered `[apex]` theorems exist with `0 sorry` / `0` custom axioms (and optional island cap)
    Check {
        /// Target repository root (strictly read-only)
        #[arg(long, default_value = ".")]
        repo: PathBuf,

        /// Path to `obend-apex.toml` manifest (defaults to `<workspace>/quarry/obend-apex.toml`)
        #[arg(long)]
        manifest: Option<PathBuf>,

        /// Require zero unwired leaf-island modules
        #[arg(long)]
        strict_islands: bool,

        /// Fail if unwired leaf-island modules exceed `<MAX_ISLANDS>`
        #[arg(long)]
        max_islands: Option<usize>,

        /// Emit structured JSON report
        #[arg(long)]
        json: bool,
    },
}

#[derive(Subcommand, Debug)]
enum PipelineSubcommand {
    /// Verify Stage-A `[HypothesisLedger]` / `[*Obligations]` interface lock or Stage-B concrete instance seal (`0 sorry`, `0 axiom`, acyclic, inhabited)
    Check {
        /// Target repository root (strictly read-only)
        #[arg(long, default_value = ".")]
        repo: PathBuf,

        /// Require `STAGE_B_SEALED` (fail if open Stage-A obligations remain or stage is `UNDECLARED`)
        #[arg(long)]
        require_sealed: bool,

        /// Refuse (`exit 2`) when `0` obligation classes are discovered (`UNDECLARED`)
        #[arg(long)]
        strict: bool,

        /// Allow `STAGE_B_SEALED` when `0` obligation classes are discovered in the repository
        #[arg(long)]
        allow_empty: bool,

        /// Emit structured JSON report
        #[arg(long)]
        json: bool,
    },
}

#[derive(Subcommand, Debug)]
enum HarnessSubcommand {
    /// Materialize canonical `AGENTS.md`, `GEMINI.md`, `CLAUDE.md`, `.agents/skills/*`, and `.claude/skills/*`
    Install {
        /// Target repository root into which harness rules & skills are written
        #[arg(long, default_value = ".")]
        repo: PathBuf,

        /// Overwrite pre-existing unmanaged files lacking an `obb-harness` marker header
        #[arg(long)]
        force: bool,

        /// Emit structured JSON report
        #[arg(long)]
        json: bool,
    },

    /// Verify root rule budgets (`< 24,000` B with includes), YAML frontmatter, SHA-256 markers & `.agents`/`.claude` parity
    Check {
        /// Target repository root to check (strictly read-only)
        #[arg(long, default_value = ".")]
        repo: PathBuf,

        /// Emit structured JSON report
        #[arg(long)]
        json: bool,
    },

    /// List canonical `obb harness` customization artifacts, byte budgets, and SHA-256 digests
    List {
        /// Emit structured JSON report
        #[arg(long)]
        json: bool,
    },
}

#[derive(Subcommand, Debug)]
enum BrokerSubcommand {
    /// Probe remote hosts (`bb2`, `hbox`) for load average, ZFS-ARC-aware free GiB, active `lean`/`lake` jobs & `>30m` runaways
    Probe {
        /// Comma-separated SSH host aliases to probe
        #[arg(long, value_delimiter = ',', default_value = "bb2,hbox")]
        hosts: Vec<String>,

        /// Offline dry-run mode (emits probe telemetry script & synthetic baseline without spawning SSH)
        #[arg(long)]
        dry_run: bool,

        /// Emit structured JSON report
        #[arg(long)]
        json: bool,
    },

    /// Route & batch Lean/GPU/EDA targets into git-tree-seeded (`cp -R --reflink=auto`), SHA-pinned, time/RSS-bounded remote `lake build` invocations
    PlanBuild {
        /// Build targets (module names like `Obend.Vault.Replay`, `.lean` paths, or executables like `rdna2-check`, `emit-sv`)
        #[arg(required = true)]
        targets: Vec<String>,

        /// Host routing policy (`auto`, `bb2`, or `hbox`)
        #[arg(long, default_value = "auto")]
        host: String,

        /// Hard wall-clock timeout per batched `lake build` invocation (wrapped in `timeout --kill-after=10s`)
        #[arg(long, default_value_t = 600)]
        timeout_secs: u64,

        /// Per-batch memory ceiling in GiB (`SWARM_MEM_MAX=<N>G swarm-build` or `ulimit -v`)
        #[arg(long, default_value_t = 12)]
        max_rss_gb: u64,

        /// Optional local repository path used to derive exact commit SHA and `HEAD:lean` `.olean` seed cache key
        #[arg(long)]
        repo: Option<PathBuf>,

        /// Optional explicit git revision / SHA to checkout (`git fetch` + `git checkout --detach <sha>`) on the remote host
        #[arg(long)]
        commit: Option<String>,

        /// Optional override for the remote `.olean` seed pool directory
        #[arg(long)]
        seed_root: Option<String>,

        /// Offline dry-run mode (skips live SSH host probing and execution)
        #[arg(long)]
        dry_run: bool,

        /// Execute the planned remote build recipe(s) over SSH
        #[arg(long)]
        exec: bool,

        /// Emit structured JSON report
        #[arg(long)]
        json: bool,
    },
}

#[derive(Subcommand, Debug)]
enum QuarrySubcommand {
    /// Fetch donor repository branches cleanly into `refs/quarry/<donor>/*` (`--no-tags`, never touching HEAD/index/worktree)
    Sync {
        /// Target repository receiving `refs/quarry/<donor>/*`
        #[arg(long)]
        repo: PathBuf,

        /// Path to `quarry.toml` manifest (defaults to `<workspace>/quarry/obend-quarry.toml`)
        #[arg(long)]
        manifest: Option<PathBuf>,

        /// Preview exact `git fetch --no-tags --no-write-fetch-head` refspecs without touching `--repo`
        #[arg(long)]
        dry_run: bool,

        /// Emit structured JSON report
        #[arg(long)]
        json: bool,
    },

    /// Summarize tracked donor subsystems across `uptaken`, `queued_for_upgrade`, `idea_only`, and `retired_slop`
    Status {
        /// Optional target repository override to verify `uptaken` destination paths and synced `refs/quarry/*`
        #[arg(long)]
        repo: Option<PathBuf>,

        /// Path to `quarry.toml` manifest (defaults to `<workspace>/quarry/obend-quarry.toml`)
        #[arg(long)]
        manifest: Option<PathBuf>,

        /// Filter entries by state (`uptaken`, `queued_for_upgrade`, `idea_only`, `retired_slop`)
        #[arg(long)]
        filter: Option<String>,

        /// Emit structured JSON report
        #[arg(long)]
        json: bool,
    },

    /// Run `obb lint` + the 6-Gate Quarry Surgery Checklist on `<donor>:<path>` before uptake into `obend`
    Inspect {
        /// Donor target specification `<donor>:<path>` (e.g. `breadstuffs:orb/Crypto.lean` or `minidregg:Pred`)
        target: String,

        /// Target repository containing synced `refs/quarry/<donor>/*` git blobs
        #[arg(long)]
        repo: Option<PathBuf>,

        /// Explicit read-only donor directory override
        #[arg(long)]
        donor_path: Option<PathBuf>,

        /// Path to `quarry.toml` manifest (defaults to `<workspace>/quarry/obend-quarry.toml` if present)
        #[arg(long)]
        manifest: Option<PathBuf>,

        /// Optional donor branch override when reading from `refs/quarry/<donor>/<branch>`
        #[arg(long)]
        branch: Option<String>,

        /// Emit structured JSON report
        #[arg(long)]
        json: bool,
    },
}

#[derive(Subcommand, Debug)]
enum JudgeSubcommand {
    /// Evaluate current `judge.json` floors against `--repo` (isolated checks with opt-in cone caching)
    Check {
        #[arg(long)]
        judge: Option<PathBuf>,

        #[arg(long, default_value = ".")]
        repo: PathBuf,

        /// Enforce test placement in Rust, JS/TS, Python and Lean library sources
        #[arg(long)]
        strict_tests: bool,

        /// Base git revision (`main`, commit SHA, etc.) when issuing a SHA-bound `JudgeReceipt`
        #[arg(long)]
        base: Option<String>,

        /// Write a SHA-bound `JudgeReceipt` JSON file for `obb state propose` / `obb state land`
        #[arg(long)]
        emit_receipt: Option<PathBuf>,

        /// Construction clock: static floors only. Executed `#tooth` runs and `home N` revert
        /// merges are deferred and listed; the result is at most `attested` and issues no receipt
        #[arg(long, conflicts_with = "emit_receipt")]
        fast: bool,

        #[arg(long)]
        json: bool,
    },

    /// Machine-check G4 non-regression (`current judge.json -> candidate`) and record `LobCost` if valid
    Succeed {
        /// Candidate `judge.json` path
        candidate: PathBuf,

        /// Current baseline `judge.json` (defaults to `<workspace>/judge.json`)
        #[arg(long)]
        judge: Option<PathBuf>,

        /// Explicit Löb trust-base additions acknowledged by ember (e.g. `--lob external:lean-transport`)
        #[arg(long = "lob")]
        lobs: Vec<String>,

        /// Replace `<judge>` on disk and record `LobCost` to `<state_dir>/events.jsonl` if accepted
        #[arg(long)]
        apply: bool,

        #[arg(long)]
        json: bool,
    },

    /// Verify in an isolated scratch git dir that `<commit>` reverts cleanly on `<repo>` (`home N` floor)
    CheckRevert {
        #[arg(long)]
        repo: PathBuf,

        commit: String,

        #[arg(long)]
        json: bool,
    },

    /// Print parsed `judge.json` summary and verify `WellFormed`
    Show {
        #[arg(long)]
        judge: Option<PathBuf>,
    },
}

#[derive(Subcommand, Debug)]
enum StateSubcommand {
    /// Initialize out-of-tree `state.db` and `events.jsonl`
    Init,

    /// Seed an explicitly marked `demo_seed` Campaign/Quest/Segment fixture (`origin="demo_seed"`)
    SeedObend {
        #[arg(long, default_value = "/Users/ember/dev/obend")]
        repo: PathBuf,
    },

    /// Show full Campaign, Quest, Segment, Ember-Queue, and Machine headroom snapshot
    Status {
        #[arg(long)]
        json: bool,
    },

    /// Create or transition a Campaign (with verified `G1`/`G2` evidence or explicit `AttestedOverride`)
    Campaign {
        #[arg(long)]
        id: String,
        #[arg(long)]
        to: Option<String>,
        #[arg(long, default_value = "Obend Campaign")]
        title: String,
        #[arg(long, default_value = "")]
        aim: String,
        #[arg(long, default_value = ".")]
        repo: String,
        #[arg(long, default_value = "manual")]
        evidence: String,
        #[arg(long = "foundation-file")]
        foundation_files: Vec<String>,
        #[arg(long)]
        judge: Option<PathBuf>,
        #[arg(long)]
        override_operator: Option<String>,
        #[arg(long)]
        override_reason: Option<String>,
    },

    /// Create or transition a Quest (enforcing `spec/process.json`, real `JudgeReceipt`s, 18 sinks + `sink_exit_rule`)
    Quest {
        #[arg(long)]
        id: String,
        #[arg(long, default_value = "C1-obend-reground")]
        campaign: String,
        #[arg(long)]
        to: Option<String>,
        #[arg(long, default_value = "Quest")]
        title: String,
        #[arg(long, default_value = "agent-main")]
        actor: String,
        #[arg(long, default_value = "decided")]
        regime: String,
        #[arg(long)]
        remedial_action: Option<String>,
        #[arg(long)]
        tooth: Option<String>,
        #[arg(long, default_value = ".")]
        repo: PathBuf,
        #[arg(long = "artifact")]
        artifacts: Vec<String>,
        #[arg(long = "footprint")]
        footprints: Vec<String>,
        #[arg(long, default_value = "")]
        deliverable: String,
        #[arg(long, default_value_t = 1.0)]
        hours: f64,
        #[arg(long)]
        receipt: Option<PathBuf>,
        #[arg(long, default_value = "main")]
        trunk: String,
        #[arg(long, default_value = "")]
        summary: String,
        #[arg(long)]
        override_operator: Option<String>,
        #[arg(long)]
        override_reason: Option<String>,
    },

    /// Take a `Grounded` quest with an exclusive non-overlapping footprint lease pinned to `--trunk`
    Take {
        id: String,
        #[arg(long, default_value = "agent-main")]
        actor: String,
        #[arg(long)]
        deliverable: String,
        #[arg(long = "footprint", required = true)]
        footprints: Vec<String>,
        #[arg(long, default_value_t = 2.0)]
        hours: f64,
        #[arg(long, default_value = ".")]
        repo: PathBuf,
        #[arg(long, default_value = "main")]
        trunk: String,
    },

    /// Propose a committed candidate with a SHA-bound `JudgeReceipt` (`Scoped` -> `Toothed`)
    Propose {
        id: String,
        #[arg(long, default_value = "agent-main")]
        actor: String,
        #[arg(long)]
        receipt: PathBuf,
        #[arg(long, default_value = ".")]
        repo: PathBuf,
        #[arg(long, default_value = "main")]
        trunk: String,
    },

    /// Land a `Toothed` quest onto `--trunk` via fast-forward + `JudgeReceipt` re-verification (or `--override-*` emergency bypass)
    Land {
        id: String,
        #[arg(long, default_value = "agent-main")]
        actor: String,
        #[arg(long)]
        receipt: Option<PathBuf>,
        #[arg(long, default_value = ".")]
        repo: PathBuf,
        #[arg(long, default_value = "main")]
        trunk: String,
        #[arg(long)]
        override_operator: Option<String>,
        #[arg(long)]
        override_reason: Option<String>,
        #[arg(long, default_value = "HEAD")]
        head: String,
    },

    /// Enqueue an event for ember (`aim`, `decision`, or `taste` ONLY — operational noise refused!)
    Ember {
        #[arg(long)]
        kind: String,
        #[arg(long)]
        subject: String,
        #[arg(long)]
        prompt: String,
    },

    /// Probe local + optional SSH (`hbox`, `bb2`) disk headroom against the 20 GB floor
    ProbeMachines {
        #[arg(long)]
        remotes: bool,
        #[arg(long)]
        json: bool,
    },

    /// Probe git cleanliness guard `Q5` (clean tree, 0 `git stash`, 0 surviving merged side-branches)
    ProbeGit {
        #[arg(long, default_value = ".")]
        repo: PathBuf,
        #[arg(long)]
        json: bool,
    },

    /// Probe `/Users/ember/.cargo/bin/cv --frozen` (`G1`, `S2`, `S6`)
    ProbeCv {
        #[arg(long)]
        cv_bin: Option<PathBuf>,
        #[arg(long)]
        json: bool,
    },
}

#[derive(Subcommand, Debug)]
enum SegSubcommand {
    /// Create a fresh segment (enforces 20 GB disk headroom guard)
    New {
        id: String,
        #[arg(long)]
        quest: String,
        #[arg(long, default_value = "pro")]
        model: String,
        #[arg(long, default_value = "local")]
        host: String,
        #[arg(long, default_value = "")]
        notes: String,
    },

    /// Continue an active segment and record token growth (`S2` pressure tracking)
    Continue {
        id: String,
        #[arg(long, default_value_t = 4000)]
        tokens: u64,
        #[arg(long, default_value = "")]
        notes: String,
    },

    /// Distill a pressured/active segment into a content-addressed artifact (`S3`)
    Distill {
        id: String,
        #[arg(long)]
        summary: String,
    },

    /// Fork a segment enforcing `S4` (no large-context fork without distill) and `S5` (handoff-tax direction)
    Fork {
        parent: String,
        child: String,
        #[arg(long, default_value = "flash")]
        model: String,
        #[arg(long, default_value = "local")]
        host: String,
        /// `downshift` (requires `--mode full`), `escalate` (requires `--mode compacted`), or `peer`
        #[arg(long, default_value = "downshift")]
        direction: String,
        #[arg(long, default_value = "full")]
        mode: String,
    },

    /// Merge segment `id` into `into`
    Merge {
        id: String,
        #[arg(long)]
        into: String,
    },

    /// Retire / forget a dead-end segment prefix (`forget` in `DESIGN.md` §4.3)
    Forget {
        id: String,
        #[arg(long, default_value = "dead-end retired")]
        reason: String,
    },

    /// Adopt an external session transcript into the segment tree
    Adopt {
        id: String,
        #[arg(long)]
        quest: String,
        #[arg(long)]
        path: String,
        #[arg(long, default_value = "local")]
        host: String,
    },

    /// Compare two segments side-by-side
    Compare { left: String, right: String },

    /// List all segments
    List {
        #[arg(long)]
        json: bool,
    },
}

#[derive(Subcommand, Debug)]
enum LedgerSubcommand {
    /// List ledger events
    List {
        #[arg(long)]
        json: bool,
    },

    /// Print a deterministic fold of the verified local event ledger
    Snapshot,

    /// Import a legacy ledger into an empty local vault (source retained)
    Migrate {
        #[arg(long)]
        from: PathBuf,
    },

    /// Verify SHA-256 hash chain integrity of `<state_dir>/events.jsonl`
    Verify,
}

#[tokio::main]
async fn main() -> ExitCode {
    match run().await {
        Ok(code) => code,
        Err(err) => {
            eprintln!("error: {err:#}");
            ExitCode::from(1)
        }
    }
}

async fn run() -> Result<ExitCode> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Lint {
            repo,
            json,
            rule,
            strict,
            strict_expose,
            strict_harnesses,
            strict_vacuity,
            strict_wire,
            strict_tests,
            modularity,
            sub,
        } => {
            if let Some(LintSubcommand::SpecCheck {
                lean_root,
                changed,
                transport_bin,
                json: spec_json,
            }) = sub
            {
                let res =
                    run_spec_sensitivity_check(&lean_root, &changed, transport_bin.as_deref())?;
                if spec_json || json {
                    println!("{}", serde_json::to_string_pretty(&res)?);
                } else {
                    println!(
                        "spec-check `{}`: broken={}/{} (intact={}, spec_sensitive={})",
                        res.changed_file,
                        res.broken_decls,
                        res.total_downstream_decls,
                        res.intact_decls,
                        res.spec_sensitive
                    );
                    for f in &res.findings {
                        println!("  [{}] {}: {}", f.severity, f.rule_id, f.message);
                    }
                }
                return Ok(if res.spec_sensitive {
                    ExitCode::SUCCESS
                } else {
                    ExitCode::from(2)
                });
            }

            let mut report = run_repo_lints_with_options(
                &repo,
                RepoLintOptions {
                    strict_expose,
                    strict_harnesses,
                    strict_vacuity,
                    strict_wire,
                    strict_tests,
                },
            )?;
            if let Some(ref flt) = rule {
                report = filter_report_by_rule(report, flt);
            }

            if json {
                println!("{}", serde_json::to_string_pretty(&report)?);
            } else {
                print_human_lint_report(&report, modularity);
            }

            if strict && report.errors > 0 {
                Ok(ExitCode::from(2))
            } else {
                Ok(ExitCode::SUCCESS)
            }
        }

        Commands::Cone {
            repo,
            json,
            max_depth,
            sub,
        } => {
            let cone = scan_repo_cone(&repo, max_depth)?;
            if let Some(ConeSubcommand::Plan {
                shards,
                propose,
                wave0,
            }) = sub
            {
                let mut proposed = Vec::new();
                for spec in &wave0 {
                    proposed.push(parse_proposed_shard_spec(spec, true)?);
                }
                for spec in &propose {
                    proposed.push(parse_proposed_shard_spec(spec, false)?);
                }
                let plan = plan_cone_shards(&cone, shards, &proposed)?;
                if json {
                    println!("{}", serde_json::to_string_pretty(&plan)?);
                } else {
                    print_human_cone_plan(&plan, cone.scan_ms);
                }
                return Ok(if plan.disjoint_write_slices {
                    ExitCode::SUCCESS
                } else {
                    ExitCode::from(2)
                });
            }

            if json {
                println!("{}", serde_json::to_string_pretty(&cone)?);
            } else {
                print_human_cone_report(&cone);
            }
            if max_depth.is_some() && !cone.depth_violations.is_empty() {
                Ok(ExitCode::from(2))
            } else {
                Ok(ExitCode::SUCCESS)
            }
        }

        Commands::Apex { sub } => match sub {
            ApexSubcommand::Status {
                repo,
                manifest,
                json,
            } => {
                let mpath = resolve_apex_manifest_path(&cli.workspace, manifest)?;
                let amanifest = ApexManifest::load_from_path(&mpath)?;
                let rep = evaluate_apex(&repo, &amanifest, ApexCheckOptions::default())?;
                if json {
                    println!("{}", serde_json::to_string_pretty(&rep)?);
                } else {
                    print_human_apex_report(&rep, "status");
                }
                Ok(ExitCode::SUCCESS)
            }

            ApexSubcommand::Check {
                repo,
                manifest,
                strict_islands,
                max_islands,
                json,
            } => {
                let mpath = resolve_apex_manifest_path(&cli.workspace, manifest)?;
                let amanifest = ApexManifest::load_from_path(&mpath)?;
                let rep = evaluate_apex(
                    &repo,
                    &amanifest,
                    ApexCheckOptions {
                        strict_islands,
                        max_islands,
                    },
                )?;
                if json {
                    println!("{}", serde_json::to_string_pretty(&rep)?);
                } else {
                    print_human_apex_report(&rep, "check");
                }
                Ok(if rep.check_passed {
                    ExitCode::SUCCESS
                } else {
                    ExitCode::from(2)
                })
            }
        },

        Commands::Pipeline { sub } => match sub {
            PipelineSubcommand::Check {
                repo,
                require_sealed,
                strict,
                allow_empty,
                json,
            } => {
                let rep = check_pipeline_with_options(
                    &repo,
                    PipelineCheckOptions {
                        strict,
                        allow_empty,
                    },
                )?;
                if json {
                    println!("{}", serde_json::to_string_pretty(&rep)?);
                } else {
                    print_human_pipeline_report(&rep, require_sealed, strict);
                }
                let ok =
                    rep.passed && (!require_sealed || rep.stage == PipelineStage::StageBSealed);
                Ok(if ok {
                    ExitCode::SUCCESS
                } else {
                    ExitCode::from(2)
                })
            }
        },

        Commands::Harness { sub } => match sub {
            HarnessSubcommand::Install { repo, force, json } => {
                let rep = harness_install(&repo, force)?;
                if json {
                    println!("{}", serde_json::to_string_pretty(&rep)?);
                } else {
                    print_human_harness_install(&rep);
                }
                Ok(if rep.passed {
                    ExitCode::SUCCESS
                } else {
                    ExitCode::from(2)
                })
            }

            HarnessSubcommand::Check { repo, json } => {
                let rep = harness_check(&repo)?;
                if json {
                    println!("{}", serde_json::to_string_pretty(&rep)?);
                } else {
                    print_human_harness_check(&rep);
                }
                Ok(if rep.passed {
                    ExitCode::SUCCESS
                } else {
                    ExitCode::from(2)
                })
            }

            HarnessSubcommand::List { json } => {
                let rep = harness_list();
                if json {
                    println!("{}", serde_json::to_string_pretty(&rep)?);
                } else {
                    print_human_harness_list(&rep);
                }
                Ok(ExitCode::SUCCESS)
            }
        },

        Commands::Broker { sub } => match sub {
            BrokerSubcommand::Probe {
                hosts,
                dry_run,
                json,
            } => {
                let cleaned: Vec<String> = hosts
                    .into_iter()
                    .map(|h| h.trim().to_string())
                    .filter(|h| !h.is_empty())
                    .collect();
                let rep = probe_hosts(&cleaned, &SshExecutor, dry_run);
                if json {
                    println!("{}", serde_json::to_string_pretty(&rep)?);
                } else {
                    print_human_broker_probe(&rep);
                }
                Ok(ExitCode::SUCCESS)
            }

            BrokerSubcommand::PlanBuild {
                targets,
                host,
                timeout_secs,
                max_rss_gb,
                repo,
                commit,
                seed_root,
                dry_run,
                exec,
                json,
            } => {
                let host_choice = HostChoice::parse_str(&host)?;
                let opts = BuildPlanOptions {
                    host_choice,
                    timeout_secs,
                    max_rss_gb,
                    dry_run,
                    exec,
                    repo_root: repo,
                    target_commit: commit,
                    remote_seed_root: seed_root,
                };
                let rep = broker_plan_build(&targets, &opts, &SshExecutor)?;
                if json {
                    println!("{}", serde_json::to_string_pretty(&rep)?);
                } else {
                    print_human_broker_plan(&rep);
                }
                let any_failed = rep
                    .batches
                    .iter()
                    .filter_map(|b| b.execution.as_ref())
                    .any(|ex| ex.executed && ex.exit_code != 0);
                Ok(if any_failed {
                    ExitCode::from(2)
                } else {
                    ExitCode::SUCCESS
                })
            }
        },

        Commands::Quarry { sub } => match sub {
            QuarrySubcommand::Sync {
                repo,
                manifest,
                dry_run,
                json,
            } => {
                let mpath = resolve_quarry_manifest_path(&cli.workspace, manifest)?;
                let qmanifest = QuarryManifest::load_from_path(&mpath)?;
                let rep = sync_quarry(&qmanifest, &repo, dry_run)?;
                if json {
                    println!("{}", serde_json::to_string_pretty(&rep)?);
                } else {
                    print_human_quarry_sync(&rep);
                }
                Ok(ExitCode::SUCCESS)
            }

            QuarrySubcommand::Status {
                repo,
                manifest,
                filter,
                json,
            } => {
                let mpath = resolve_quarry_manifest_path(&cli.workspace, manifest)?;
                let qmanifest = QuarryManifest::load_from_path(&mpath)?;
                let parsed_filter = match filter {
                    Some(ref raw) => Some(QuarryState::parse_filter(raw)?),
                    None => None,
                };
                let rep = status_quarry(&qmanifest, repo.as_deref(), parsed_filter)?;
                if json {
                    println!("{}", serde_json::to_string_pretty(&rep)?);
                } else {
                    print_human_quarry_status(&rep);
                }
                Ok(if rep.all_uptaken_verified {
                    ExitCode::SUCCESS
                } else {
                    ExitCode::from(2)
                })
            }

            QuarrySubcommand::Inspect {
                target,
                repo,
                donor_path,
                manifest,
                branch,
                json,
            } => {
                let loaded_manifest = match manifest {
                    Some(explicit) => Some(QuarryManifest::load_from_path(&explicit)?),
                    None => resolve_quarry_manifest_path(&cli.workspace, None)
                        .ok()
                        .and_then(|p| QuarryManifest::load_from_path(&p).ok()),
                };
                let rep = inspect_quarry_target(
                    &target,
                    repo.as_deref(),
                    donor_path.as_deref(),
                    loaded_manifest.as_ref(),
                    branch.as_deref(),
                )?;
                if json {
                    println!("{}", serde_json::to_string_pretty(&rep)?);
                } else {
                    print_human_quarry_inspect(&rep);
                }
                Ok(if rep.ready_for_uptake {
                    ExitCode::SUCCESS
                } else {
                    ExitCode::from(2)
                })
            }
        },

        Commands::Judge { sub } => match sub {
            JudgeSubcommand::Show { judge } => {
                let jpath = resolve_judge_path(&cli.workspace, judge);
                let gate = Gate::load_from_path(&jpath)?;
                check_well_formed(&gate)?;
                println!(
                    "Judge `{}` (WellFormed = true)\n  formats ({}): {}\n  floors  ({}): {}\n  basis   ({}): {}",
                    gate.name,
                    gate.formats.len(),
                    gate.formats.join(", "),
                    gate.floors.len(),
                    gate.floors
                        .iter()
                        .map(|f| f.to_wire())
                        .collect::<Vec<_>>()
                        .join(", "),
                    gate.basis.len(),
                    gate.basis
                        .iter()
                        .map(|b| b.to_wire())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                Ok(ExitCode::SUCCESS)
            }

            JudgeSubcommand::Check {
                judge,
                repo,
                base,
                emit_receipt,
                strict_tests,
                fast,
                json,
            } => {
                let jpath = resolve_judge_path(&cli.workspace, judge);
                let mut gate = Gate::load_from_path(&jpath)?;
                if strict_tests {
                    gate.require_strict_tests();
                }
                if let Some(ref out_path) = emit_receipt {
                    let base_rev = base.as_deref().unwrap_or("main");
                    let receipt = issue_judge_receipt_with_state_dir(
                        &gate,
                        &repo,
                        base_rev,
                        cli.state_dir.as_deref(),
                    )?;
                    if let Some(parent) = out_path.parent()
                        && !parent.as_os_str().is_empty()
                    {
                        std::fs::create_dir_all(parent)?;
                    }
                    std::fs::write(
                        out_path,
                        format!("{}\n", serde_json::to_string_pretty(&receipt)?),
                    )?;
                    if json {
                        println!("{}", serde_json::to_string_pretty(&receipt)?);
                    } else {
                        println!(
                            "obb judge check: gate=`{}` base=`{}` head=`{}` all_passed={} clean_tree={} achieved_regime={} receipt=`{}`",
                            receipt.judge_name,
                            &receipt.base_sha[..receipt.base_sha.len().min(12)],
                            &receipt.head_sha[..receipt.head_sha.len().min(12)],
                            receipt.all_passed,
                            receipt.clean_working_tree,
                            receipt.achieved_regime,
                            out_path.display()
                        );
                        for ev in &receipt.evaluations {
                            let tag = if ev.passed { "PASS" } else { "FAIL" };
                            println!(
                                "  [{tag}] {:<36} regime={:<10} measured={:<4} bound={:<12} ({})",
                                ev.floor, ev.regime, ev.measured, ev.bound, ev.detail
                            );
                        }
                    }
                    return Ok(if receipt.all_passed && receipt.clean_working_tree {
                        ExitCode::SUCCESS
                    } else {
                        ExitCode::from(2)
                    });
                }

                let clock = if fast {
                    JudgeClock::Construction
                } else {
                    JudgeClock::Convergence
                };
                let rep = evaluate_gate_on(&gate, &repo, clock)?;
                if json {
                    println!("{}", serde_json::to_string_pretty(&rep)?);
                } else {
                    println!(
                        "obb judge check: gate=`{}` repo=`{}` all_passed={} achieved_regime={}",
                        rep.judge_name, rep.repo_root, rep.all_passed, rep.achieved_regime
                    );
                    for floor in &rep.deferred_floors {
                        println!("  [DEFERRED] {floor} (not run on the construction clock)");
                    }
                    for ev in &rep.evaluations {
                        let tag = if ev.passed { "PASS" } else { "FAIL" };
                        println!(
                            "  [{tag}] {:<36} regime={:<10} measured={:<4} bound={:<12} ({})",
                            ev.floor, ev.regime, ev.measured, ev.bound, ev.detail
                        );
                    }
                }
                Ok(if rep.all_passed {
                    ExitCode::SUCCESS
                } else {
                    ExitCode::from(2)
                })
            }

            JudgeSubcommand::Succeed {
                candidate,
                judge,
                lobs,
                apply,
                json,
            } => {
                let jpath = resolve_judge_path(&cli.workspace, judge);
                let old_gate = Gate::load_from_path(&jpath)?;
                let new_gate = Gate::load_from_path(&candidate)?;
                let mut parsed_lobs = Vec::new();
                for l in &lobs {
                    let tb = TrustBase::parse_wire(l)
                        .map_err(|e| anyhow::anyhow!("invalid `--lob {l}`: {e}"))?;
                    parsed_lobs.push(tb);
                }

                match check_succeed(&old_gate, &new_gate, &parsed_lobs) {
                    Ok(rec) => {
                        if apply {
                            let store = StateStore::open_with_state_dir(
                                &cli.workspace,
                                cli.state_dir.as_deref(),
                            )?;
                            store.record_lob_succession(&rec)?;
                            let formatted = serde_json::to_string_pretty(&new_gate)?;
                            std::fs::write(&jpath, format!("{formatted}\n"))?;
                        }
                        if json {
                            println!(
                                "{}",
                                serde_json::to_string_pretty(&serde_json::json!({
                                    "accepted": true,
                                    "record": rec,
                                }))?
                            );
                        } else {
                            println!(
                                "ACCEPTED succession `{}` -> `{}` (lob_cost={:?})",
                                rec.old_name, rec.new_name, rec.lob_cost
                            );
                        }
                        Ok(ExitCode::SUCCESS)
                    }
                    Err(refusal) => {
                        if json {
                            println!(
                                "{}",
                                serde_json::to_string_pretty(&serde_json::json!({
                                    "accepted": false,
                                    "refusal": refusal.to_string(),
                                }))?
                            );
                        } else {
                            eprintln!("REFUSED judge succession: {refusal}");
                        }
                        Ok(ExitCode::from(2))
                    }
                }
            }

            JudgeSubcommand::CheckRevert { repo, commit, json } => {
                let res = check_revert_clean(&repo, &commit)?;
                if json {
                    println!("{}", serde_json::to_string_pretty(&res)?);
                } else if res.clean {
                    println!(
                        "PASS check-revert: commit `{}` ({}) reverts cleanly on HEAD ({}) -> tree {}",
                        res.commit_rev,
                        &res.commit_sha[..10.min(res.commit_sha.len())],
                        &res.head_sha[..10.min(res.head_sha.len())],
                        res.result_tree_oid.as_deref().unwrap_or("<tree>")
                    );
                } else {
                    eprintln!(
                        "FAIL check-revert: commit `{}` ({}) conflicts with HEAD ({}):",
                        res.commit_rev, res.commit_sha, res.head_sha
                    );
                    for c in &res.conflict_summary {
                        eprintln!("  {c}");
                    }
                }
                Ok(if res.clean {
                    ExitCode::SUCCESS
                } else {
                    ExitCode::from(2)
                })
            }
        },

        Commands::State { sub } => {
            let store = StateStore::open_with_state_dir(&cli.workspace, cli.state_dir.as_deref())?;
            match *sub {
                StateSubcommand::Init => {
                    let _ = store.probe_machines(false)?;
                    println!(
                        "Initialized `state.db` and `events.jsonl` in {}",
                        store.state_dir().display()
                    );
                    Ok(ExitCode::SUCCESS)
                }
                StateSubcommand::SeedObend { repo } => {
                    let snap = store.seed_obend_campaign(&repo)?;
                    println!(
                        "Seeded DEMO campaign [origin=demo_seed] ({} quests, {} segments, {} ember events; live_transitions={})",
                        snap.quests.len(),
                        snap.segments.len(),
                        snap.waiting_on_ember.len(),
                        snap.live_transition_count
                    );
                    Ok(ExitCode::SUCCESS)
                }
                StateSubcommand::Status { json } => {
                    let snap = store.snapshot()?;
                    if json {
                        println!("{}", serde_json::to_string_pretty(&snap)?);
                    } else {
                        println!(
                            "Workspace: {} | scheduler_paused={} | live_transitions={} verified_quests={} ungated_overrides={} demo_seed_events={}",
                            snap.workspace_root,
                            snap.scheduler_paused,
                            snap.live_transition_count,
                            snap.verified_quest_count,
                            snap.ungated_override_count,
                            snap.demo_seed_event_count
                        );
                        println!("Campaigns ({}):", snap.campaigns.len());
                        for c in &snap.campaigns {
                            println!(
                                "  - {} [{}] (origin={}): {}",
                                c.id, c.state, c.origin, c.title
                            );
                        }
                        println!("Quests ({}):", snap.quests.len());
                        for q in &snap.quests {
                            let sink_tag = if q.is_sink { " (SINK)" } else { "" };
                            let ov_tag = if q.merged_ungated { " [UNGATED]" } else { "" };
                            println!(
                                "  - {} [{}{}{}] effective={} target={} origin={} holder={}: {}",
                                q.id,
                                q.state,
                                sink_tag,
                                ov_tag,
                                q.effective_regime,
                                q.target_regime,
                                q.origin,
                                q.holder_agent,
                                q.title
                            );
                        }
                        println!("Segments ({}):", snap.segments.len());
                        for s in &snap.segments {
                            println!(
                                "  - {} (quest={}, parent={}) [{}] tokens={} mode={} host={} origin={}",
                                s.id,
                                s.quest_id,
                                s.parent_id.as_deref().unwrap_or("-"),
                                s.state,
                                s.token_count,
                                s.transcript_mode,
                                s.host,
                                s.origin
                            );
                        }
                        println!("Waiting on ember ({}):", snap.waiting_on_ember.len());
                        for e in &snap.waiting_on_ember {
                            println!("  - [{}] {}: {}", e.kind, e.subject_id, e.prompt);
                        }
                    }
                    Ok(ExitCode::SUCCESS)
                }
                StateSubcommand::Campaign {
                    id,
                    to,
                    title,
                    aim,
                    repo,
                    evidence,
                    foundation_files,
                    judge,
                    override_operator,
                    override_reason,
                } => {
                    if let Some(target) = to {
                        let ev = if let (Some(op), Some(reason)) =
                            (override_operator, override_reason)
                        {
                            CampaignGuardEvidence::AttestedOverride {
                                operator: op,
                                reason,
                            }
                        } else if target == "Grounded" {
                            CampaignGuardEvidence::WholeRead {
                                foundation_files,
                                note: evidence,
                            }
                        } else if target == "Running"
                            && !foundation_files.is_empty()
                            && judge.is_none()
                        {
                            CampaignGuardEvidence::Unconditional { note: evidence }
                        } else if target == "Running" {
                            let jpath = resolve_judge_path(&cli.workspace, judge);
                            CampaignGuardEvidence::Briefed {
                                judge_path: jpath,
                                note: evidence,
                            }
                        } else if target == "Reground" {
                            CampaignGuardEvidence::RegroundTrigger { trigger: evidence }
                        } else {
                            CampaignGuardEvidence::Unconditional { note: evidence }
                        };
                        let row = store
                            .transition_campaign(&id, &target, ev)
                            .map_err(|e| anyhow::anyhow!(e.to_string()))?;
                        println!("Campaign `{}` -> `{}`", row.id, row.state);
                    } else {
                        let row = store.create_campaign(&id, &title, &aim, &repo)?;
                        println!("Created campaign `{}` in `{}`", row.id, row.state);
                    }
                    Ok(ExitCode::SUCCESS)
                }
                StateSubcommand::Quest {
                    id,
                    campaign,
                    to,
                    title,
                    actor,
                    regime,
                    remedial_action,
                    tooth,
                    repo,
                    artifacts,
                    footprints,
                    deliverable,
                    hours,
                    receipt,
                    trunk,
                    summary,
                    override_operator,
                    override_reason,
                } => {
                    if let Some(target) = to {
                        let cur_opt = store.get_quest(&id)?;
                        let is_sink_target =
                            store.spec.machines.quest.sinks.iter().any(|s| s == &target);
                        let is_currently_sink = cur_opt.as_ref().is_some_and(|q| q.is_sink);

                        let ev = if let (Some(op), Some(reason)) =
                            (override_operator, override_reason)
                        {
                            QuestGuardEvidence::AttestedOverride {
                                operator: op,
                                reason,
                                head_sha: None,
                            }
                        } else if is_sink_target {
                            QuestGuardEvidence::EnterSink {
                                reason: remedial_action
                                    .unwrap_or_else(|| "sink entered".to_string()),
                            }
                        } else if is_currently_sink {
                            QuestGuardEvidence::ExitSink {
                                remedial_action: remedial_action.unwrap_or_default(),
                            }
                        } else if target == "Scoped" {
                            QuestGuardEvidence::ScopeBrief {
                                deliverable: if deliverable.is_empty() {
                                    title.clone()
                                } else {
                                    deliverable
                                },
                                footprint_paths: footprints,
                                estimated_swarm_hours: hours,
                                base_sha: None,
                            }
                        } else if matches!(target.as_str(), "Built" | "Wired") {
                            QuestGuardEvidence::RepoCheck {
                                repo_root: repo,
                                artifacts,
                            }
                        } else if matches!(target.as_str(), "Toothed" | "Landed" | "Claimed") {
                            let rpath = receipt.ok_or_else(|| {
                                anyhow::anyhow!(
                                    "transition to `{target}` requires `--receipt <receipt.json>` from `obb judge check --emit-receipt`"
                                )
                            })?;
                            let loaded = JudgeReceipt::load_from_path(&rpath)?;
                            QuestGuardEvidence::Receipt {
                                receipt: Box::new(loaded),
                                repo_root: repo,
                                trunk_branch: trunk,
                            }
                        } else if target == "Recorded" {
                            QuestGuardEvidence::RecordCheck {
                                repo_root: repo,
                                summary,
                            }
                        } else {
                            QuestGuardEvidence::EnterSink {
                                reason: "transition".to_string(),
                            }
                        };

                        let row = store
                            .transition_quest(&id, &target, &actor, tooth.as_deref(), ev)
                            .map_err(|e| anyhow::anyhow!(e.to_string()))?;
                        println!(
                            "Quest `{}` -> `{}` (sink={}, effective_regime={}, merged_ungated={})",
                            row.id,
                            row.state,
                            row.is_sink,
                            row.effective_regime,
                            row.merged_ungated
                        );
                    } else {
                        let row = store.create_quest(&id, &campaign, &title, &actor, &regime)?;
                        println!("Created quest `{}` in `{}`", row.id, row.state);
                    }
                    Ok(ExitCode::SUCCESS)
                }
                StateSubcommand::Take {
                    id,
                    actor,
                    deliverable,
                    footprints,
                    hours,
                    repo,
                    trunk,
                } => {
                    let row = store
                        .take_quest(&id, &actor, &deliverable, footprints, hours, &repo, &trunk)
                        .map_err(|e| anyhow::anyhow!(e.to_string()))?;
                    println!(
                        "Took quest `{}` -> `{}` (base_sha={}, footprint={:?})",
                        row.id,
                        row.state,
                        row.base_sha.as_deref().unwrap_or("-"),
                        row.footprint_lease
                    );
                    Ok(ExitCode::SUCCESS)
                }
                StateSubcommand::Propose {
                    id,
                    actor,
                    receipt,
                    repo,
                    trunk,
                } => {
                    let loaded = JudgeReceipt::load_from_path(&receipt)?;
                    let row = store
                        .propose_quest(&id, &actor, &loaded, &repo, &trunk)
                        .map_err(|e| anyhow::anyhow!(e.to_string()))?;
                    println!(
                        "Proposed quest `{}` -> `{}` (head_sha={}, receipt={})",
                        row.id,
                        row.state,
                        row.proposed_head_sha.as_deref().unwrap_or("-"),
                        row.verified_receipt_hash.as_deref().unwrap_or("-")
                    );
                    Ok(ExitCode::SUCCESS)
                }
                StateSubcommand::Land {
                    id,
                    actor,
                    receipt,
                    repo,
                    trunk,
                    override_operator,
                    override_reason,
                    head,
                } => {
                    let row = if let (Some(op), Some(reason)) = (override_operator, override_reason)
                    {
                        store
                            .land_quest_ungated(&id, &op, &reason, &repo, &trunk, &head)
                            .map_err(|e| anyhow::anyhow!(e.to_string()))?
                    } else {
                        let rpath = receipt.ok_or_else(|| {
                            anyhow::anyhow!(
                                "`obb state land` requires `--receipt <receipt.json>` (or `--override-operator` + `--override-reason`)"
                            )
                        })?;
                        let loaded = JudgeReceipt::load_from_path(&rpath)?;
                        store
                            .land_quest(&id, &actor, &loaded, &repo, &trunk)
                            .map_err(|e| anyhow::anyhow!(e.to_string()))?
                    };
                    println!(
                        "Landed quest `{}` -> `{}` (landed_sha={}, effective_regime={}, merged_ungated={})",
                        row.id,
                        row.state,
                        row.landed_sha.as_deref().unwrap_or("-"),
                        row.effective_regime,
                        row.merged_ungated
                    );
                    Ok(ExitCode::SUCCESS)
                }
                StateSubcommand::Ember {
                    kind,
                    subject,
                    prompt,
                } => {
                    let row = store
                        .enqueue_ember_event(&kind, &subject, &prompt)
                        .map_err(|e| anyhow::anyhow!(e.to_string()))?;
                    println!(
                        "Queued ember `{}` event #{} on `{}`",
                        row.kind, row.id, row.subject_id
                    );
                    Ok(ExitCode::SUCCESS)
                }
                StateSubcommand::ProbeMachines { remotes, json } => {
                    let ms = store.probe_machines(remotes)?;
                    if json {
                        println!("{}", serde_json::to_string_pretty(&ms)?);
                    } else {
                        for m in &ms {
                            println!(
                                "{:<8} reachable={:<5} avail={:>6.1} GB / {:>6.1} GB below_20gb_floor={:<5} ({})",
                                m.host,
                                m.reachable,
                                m.avail_gb,
                                m.total_gb,
                                m.below_floor,
                                m.load_summary
                            );
                        }
                    }
                    let any_below = ms.iter().any(|m| m.reachable && m.below_floor);
                    Ok(if any_below {
                        ExitCode::from(2)
                    } else {
                        ExitCode::SUCCESS
                    })
                }
                StateSubcommand::ProbeGit { repo, json } => {
                    let rep = StateStore::probe_git_q5(&repo)?;
                    if json {
                        println!("{}", serde_json::to_string_pretty(&rep)?);
                    } else {
                        println!(
                            "Q5 git guard on `{}` (branch `{}`): passed={} clean_tree={} stashes={} merged_side_branches={:?}",
                            rep.repo,
                            rep.current_branch,
                            rep.q5_passed,
                            rep.clean_working_tree,
                            rep.stash_count,
                            rep.merged_side_branches
                        );
                    }
                    Ok(if rep.q5_passed {
                        ExitCode::SUCCESS
                    } else {
                        ExitCode::from(2)
                    })
                }
                StateSubcommand::ProbeCv { cv_bin, json } => {
                    let rep = store.probe_cv(cv_bin.as_deref());
                    if json {
                        println!("{}", serde_json::to_string_pretty(&rep)?);
                    } else {
                        println!("cv probe (`{}`): {}", rep.cv_bin, rep.summary);
                    }
                    Ok(ExitCode::SUCCESS)
                }
            }
        }

        Commands::Seg { sub } => {
            let store = StateStore::open_with_state_dir(&cli.workspace, cli.state_dir.as_deref())?;
            match sub {
                SegSubcommand::New {
                    id,
                    quest,
                    model,
                    host,
                    notes,
                } => {
                    let r = store
                        .seg_new(&id, &quest, &model, &host, &notes)
                        .map_err(|e| anyhow::anyhow!(e.to_string()))?;
                    println!("Segment `{}` created in `{}`", r.id, r.state);
                }
                SegSubcommand::Continue { id, tokens, notes } => {
                    let r = store
                        .seg_continue(&id, tokens, &notes)
                        .map_err(|e| anyhow::anyhow!(e.to_string()))?;
                    println!(
                        "Segment `{}` -> `{}` ({} tokens)",
                        r.id, r.state, r.token_count
                    );
                }
                SegSubcommand::Distill { id, summary } => {
                    let r = store
                        .seg_distill(&id, &summary)
                        .map_err(|e| anyhow::anyhow!(e.to_string()))?;
                    println!(
                        "Segment `{}` distilled (hash={})",
                        r.id,
                        r.distill_hash.as_deref().unwrap_or("")
                    );
                }
                SegSubcommand::Fork {
                    parent,
                    child,
                    model,
                    host,
                    direction,
                    mode,
                } => {
                    let r = store
                        .seg_fork(&parent, &child, &model, &host, &direction, &mode)
                        .map_err(|e| anyhow::anyhow!(e.to_string()))?;
                    println!(
                        "Forked `{}` -> `{}` (state={}, tokens={}, mode={})",
                        parent, r.id, r.state, r.token_count, r.transcript_mode
                    );
                }
                SegSubcommand::Merge { id, into } => {
                    let r = store
                        .seg_merge(&id, &into)
                        .map_err(|e| anyhow::anyhow!(e.to_string()))?;
                    println!("Merged `{}` -> `{}` ({})", r.id, into, r.state);
                }
                SegSubcommand::Forget { id, reason } => {
                    let r = store
                        .seg_forget(&id, &reason)
                        .map_err(|e| anyhow::anyhow!(e.to_string()))?;
                    println!("Retired `{}` ({})", r.id, r.state);
                }
                SegSubcommand::Adopt {
                    id,
                    quest,
                    path,
                    host,
                } => {
                    let r = store
                        .seg_adopt(&id, &quest, &path, &host)
                        .map_err(|e| anyhow::anyhow!(e.to_string()))?;
                    println!("Adopted `{}` ({} approx tokens)", r.id, r.token_count);
                }
                SegSubcommand::Compare { left, right } => {
                    let cmp = store.seg_compare(&left, &right)?;
                    println!("{}", serde_json::to_string_pretty(&cmp)?);
                }
                SegSubcommand::List { json } => {
                    let segs = store.list_segments()?;
                    if json {
                        println!("{}", serde_json::to_string_pretty(&segs)?);
                    } else {
                        for s in &segs {
                            println!(
                                "{:<18} quest={:<8} parent={:<16} state={:<10} tokens={:<7} mode={}",
                                s.id,
                                s.quest_id,
                                s.parent_id.as_deref().unwrap_or("-"),
                                s.state,
                                s.token_count,
                                s.transcript_mode
                            );
                        }
                    }
                }
            }
            Ok(ExitCode::SUCCESS)
        }

        Commands::Ledger { sub } => {
            let store = StateStore::open_with_state_dir(&cli.workspace, cli.state_dir.as_deref())?;
            match sub {
                LedgerSubcommand::List { json } => {
                    let evs = store.read_ledger()?;
                    if json {
                        println!("{}", serde_json::to_string_pretty(&evs)?);
                    } else {
                        for ev in &evs {
                            println!(
                                "#{:<4} {} {:<20} {:<16} {} [{}]",
                                ev.seq,
                                ev.timestamp,
                                ev.event_type,
                                ev.entity_id,
                                ev.summary,
                                ev.event_hash.get(..12).unwrap_or(&ev.event_hash)
                            );
                        }
                    }
                }
                LedgerSubcommand::Snapshot => {
                    println!(
                        "{}",
                        serde_json::to_string_pretty(&store.ledger_snapshot()?)?
                    );
                }
                LedgerSubcommand::Migrate { from } => {
                    println!("Migrated {} events", store.migrate_ledger(&from)?);
                }
                LedgerSubcommand::Verify => {
                    let count = store.verify_ledger_chain()?;
                    println!("PASS ledger hash-chain verified ({count} event(s))");
                }
            }
            Ok(ExitCode::SUCCESS)
        }

        Commands::Serve {
            host,
            port,
            repo,
            seed_demo,
        } => {
            let jpath = resolve_judge_path(&cli.workspace, None);
            if !jpath.is_file() {
                bail!("judge.json not found at {}", jpath.display());
            }
            run_server_with_options(
                &host,
                port,
                &cli.workspace,
                cli.state_dir.as_deref(),
                &repo,
                &jpath,
                seed_demo,
            )
            .await?;
            Ok(ExitCode::SUCCESS)
        }
    }
}

fn resolve_judge_path(workspace: &Path, explicit: Option<PathBuf>) -> PathBuf {
    explicit.unwrap_or_else(|| workspace.join("judge.json"))
}

fn resolve_quarry_manifest_path(workspace: &Path, explicit: Option<PathBuf>) -> Result<PathBuf> {
    if let Some(p) = explicit {
        return Ok(p);
    }
    let ws_candidate = workspace.join(DEFAULT_QUARRY_MANIFEST_REL);
    if ws_candidate.is_file() {
        return Ok(ws_candidate);
    }
    let crate_root_candidate = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../")
        .join(DEFAULT_QUARRY_MANIFEST_REL);
    if crate_root_candidate.is_file() {
        return Ok(crate_root_candidate);
    }
    bail!(
        "quarry manifest not found at {} (pass `--manifest <quarry.toml>`)",
        ws_candidate.display()
    )
}

fn resolve_apex_manifest_path(workspace: &Path, explicit: Option<PathBuf>) -> Result<PathBuf> {
    if let Some(p) = explicit {
        return Ok(p);
    }
    let ws_candidate = workspace.join(DEFAULT_APEX_MANIFEST_REL);
    if ws_candidate.is_file() {
        return Ok(ws_candidate);
    }
    let crate_root_candidate = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../")
        .join(DEFAULT_APEX_MANIFEST_REL);
    if crate_root_candidate.is_file() {
        return Ok(crate_root_candidate);
    }
    bail!(
        "apex manifest not found at {} (pass `--manifest <obend-apex.toml>`)",
        ws_candidate.display()
    )
}

fn parse_proposed_shard_spec(raw: &str, wave0_barrier: bool) -> Result<ProposedShard> {
    let Some((name, files_csv)) = raw.split_once('=') else {
        bail!(
            "invalid shard slice `{raw}`; expected `<shard_name>=<file_or_module1>,<file_or_module2>,...`"
        );
    };
    let name = name.trim();
    if name.is_empty() {
        bail!("shard name in `{raw}` must be non-empty");
    }
    let files: Vec<String> = files_csv
        .split(',')
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .collect();
    if files.is_empty() {
        bail!("shard `{name}` in `{raw}` must list at least one module or `.lean` file");
    }
    Ok(ProposedShard {
        name: name.to_string(),
        files,
        wave0_barrier,
    })
}

fn print_human_lint_report(rep: &obb_core::LintReport, show_modularity_detail: bool) {
    println!(
        "obb lint: repo={} files_scanned={} lean_decls={} lean_inductives={}",
        rep.repo_root,
        rep.files_scanned,
        rep.lean_declarations_indexed,
        rep.lean_inductives_indexed
    );
    println!(
        "totals: {} findings ({} errors, {} warnings)",
        rep.total_findings, rep.errors, rep.warnings
    );
    println!(
        "tier1_tests: tier1_guards={} tier1_teeth={} tier1_evals={}",
        rep.tier1_guards, rep.tier1_teeth, rep.tier1_evals
    );

    if rep.modularity.lean_files > 0 || show_modularity_detail {
        let m = &rep.modularity;
        println!(
            "modularity: index={:.2}/100 carriers={} (struct={}, class={}, inst={}) thms={} (composed={}, isolated_leaf={}, reuse={:.1}%) carrier/leaf={:.4} monoliths(>{}L)={}",
            m.compositionality_index,
            m.structures + m.classes,
            m.structures,
            m.classes,
            m.instances,
            m.total_theorems,
            m.composed_theorems,
            m.isolated_leaf_theorems,
            m.theorem_reuse_ratio * 100.0,
            m.carrier_to_leaf_ratio,
            m.monolithic_line_threshold,
            m.monolithic_modules.len()
        );
    }

    if show_modularity_detail {
        let m = &rep.modularity;
        if !m.by_directory.is_empty() {
            println!("\nModularity & Compositionality by directory:");
            println!(
                "  {:<28} {:>5} {:>8} {:>7} {:>8} {:>9} {:>9} {:>10}",
                "Directory",
                "Files",
                "Lines",
                "MaxLine",
                "Carriers",
                "CompThm",
                "LeafThm",
                "Carr/Leaf"
            );
            for d in &m.by_directory {
                println!(
                    "  {:<28} {:>5} {:>8} {:>7} {:>8} {:>9} {:>9} {:>10.4}",
                    d.directory,
                    d.files,
                    d.total_lines,
                    d.max_lines,
                    d.structures_and_classes,
                    d.composed_theorems,
                    d.isolated_leaf_theorems,
                    d.carrier_to_leaf_ratio
                );
            }
        }
        if !m.monolithic_modules.is_empty() {
            println!(
                "\nMonolithic Lean modules (>{} lines — elaboration RSS blowup risk):",
                m.monolithic_line_threshold
            );
            for mm in &m.monolithic_modules {
                println!(
                    "  {:>6} lines | {:>4} decls | {:>4} thms | {:>3} carriers | {}",
                    mm.lines, mm.declarations, mm.theorems, mm.structures_and_classes, mm.path
                );
            }
        }
        println!(
            "\nModule-cone hygiene: max_public_cone_depth={} hubs(fan_in>25)={} file_wide_expose(>80L)={} public_meta_import_leaks={}",
            m.max_public_cone_depth,
            m.high_blast_radius_hubs.len(),
            m.file_wide_expose_modules,
            m.public_meta_import_leaks
        );
    }

    if !rep.by_rule.is_empty() {
        println!("\nFindings by rule:");
        for (rule, count) in &rep.by_rule {
            println!("  {:<38} {:>5}", rule, count);
        }
    }

    if !rep.by_artifact_kind.is_empty() {
        println!("\nFindings by Gunter-Jackson-Zave artifact kind (W/R/S/P/M):");
        for (k, count) in &rep.by_artifact_kind {
            println!("  {:<8} {:>5}", k, count);
        }
    }

    if !rep.directory_census.is_empty() {
        println!("\nDirectory epistemic & theorem census:");
        println!(
            "  {:<28} {:>5} {:>7} {:>7} {:>8} {:>8} {:>8}",
            "Directory", "Files", "UnivThm", "Closed", "Decided", "Attested", "Findings"
        );
        for d in &rep.directory_census {
            if d.files > 0 || d.findings_count > 0 {
                println!(
                    "  {:<28} {:>5} {:>7} {:>7} {:>8} {:>8} {:>8}",
                    d.directory,
                    d.files,
                    d.universal_theorems,
                    d.closed_theorems,
                    d.decided_claims,
                    d.attested_claims,
                    d.findings_count
                );
            }
        }
    }

    println!("\nFindings detail (showing up to 60):");
    for f in rep.findings.iter().take(60) {
        let sink_str = f.sink.map(|s| format!(" sink={s}")).unwrap_or_default();
        println!(
            "  [{}][{}][max_regime={}{}] {}:{}:{} ({})\n    {}\n    fix: {}",
            f.severity,
            f.artifact_kind,
            f.max_regime,
            sink_str,
            f.path,
            f.line,
            f.column,
            f.rule_id,
            f.message,
            f.remediation
        );
    }
    if rep.findings.len() > 60 {
        println!(
            "  ... ({} additional findings; pass `--json` for full list)",
            rep.findings.len() - 60
        );
    }
}

fn print_human_quarry_sync(rep: &obb_quarry::QuarrySyncReport) {
    let mode = if rep.dry_run { "DRY-RUN" } else { "SYNCED" };
    println!(
        "obb quarry sync [{mode}]: target={} head={} (head_unchanged={} index_unchanged={} worktree_unchanged={})",
        rep.target_repo,
        rep.head_after
            .as_deref()
            .map(|h| &h[..10.min(h.len())])
            .unwrap_or("<unborn>"),
        rep.head_unchanged,
        rep.index_unchanged,
        rep.worktree_unchanged
    );
    for act in &rep.actions {
        let prev = act
            .previous_target_sha
            .as_deref()
            .map(|s| &s[..10.min(s.len())])
            .unwrap_or("<none>");
        let next = &act.new_target_sha[..10.min(act.new_target_sha.len())];
        let tag = if !act.updated {
            "UP-TO-DATE"
        } else if rep.dry_run {
            "WOULD-FETCH"
        } else {
            "UPDATED"
        };
        println!(
            "  [{tag:<11}] {:<16} {:<34} {prev} -> {next}\n    cmd: {}",
            act.donor, act.target_ref, act.command_preview
        );
    }
}

fn print_human_quarry_status(rep: &obb_quarry::QuarryStatusReport) {
    println!(
        "obb quarry status: target={} total_entries={} all_uptaken_verified={}",
        rep.target_repo.as_deref().unwrap_or("<none>"),
        rep.total_entries,
        rep.all_uptaken_verified
    );
    println!("By state:");
    for (state, count) in &rep.by_state {
        println!("  {:<22} {:>4}", state, count);
    }

    println!("\nDonors ({}):", rep.donors.len());
    for d in &rep.donors {
        let synced_str = if d.synced_quarry_refs.is_empty() {
            "not yet synced in target".to_string()
        } else {
            d.synced_quarry_refs
                .iter()
                .map(|(br, sha)| format!("{br}@{}", &sha[..10.min(sha.len())]))
                .collect::<Vec<_>>()
                .join(", ")
        };
        println!(
            "  - {:<15} reachable={:<5} entries={:<3} synced=[{}] ({})",
            d.donor, d.donor_reachable, d.total_entries, synced_str, d.donor_path
        );
    }

    if !rep.uptake_violations.is_empty() {
        println!(
            "\nUPTAKE VERIFICATION VIOLATIONS ({}):",
            rep.uptake_violations.len()
        );
        for v in &rep.uptake_violations {
            println!("  [FAIL] {} ({}): {}", v.entry_id, v.donor, v.reason);
        }
    }

    println!(
        "\nEntries ({}{}):",
        rep.entries.len(),
        rep.state_filter
            .as_deref()
            .map(|f| format!(", filter={f}"))
            .unwrap_or_default()
    );
    for e in &rep.entries {
        let dest = e.destination_path.as_deref().unwrap_or("-");
        let dest_ok = match e.destination_exists {
            Some(true) => " [exists]",
            Some(false) => " [MISSING]",
            None => "",
        };
        println!(
            "  [{:<18}] {:<38} {}:{} -> {}{}\n    notes: {}",
            e.state.as_str(),
            e.id,
            e.donor,
            e.source_path,
            dest,
            dest_ok,
            e.audit_notes
        );
    }
}

fn print_human_quarry_inspect(rep: &obb_quarry::QuarryInspectReport) {
    let verdict = if rep.ready_for_uptake {
        "READY FOR UPTAKE"
    } else {
        "BLOCKED — SURGERY REQUIRED"
    };
    println!(
        "obb quarry inspect `{}` [{}]\n  source={} files={} defects={} ({} errors, {} warnings)",
        rep.spec,
        verdict,
        rep.resolution_source,
        rep.files_inspected,
        rep.total_defects,
        rep.errors,
        rep.warnings
    );

    if !rep.matched_manifest_entries.is_empty() {
        println!(
            "\nManifest tracking ({}):",
            rep.matched_manifest_entries.len()
        );
        for m in &rep.matched_manifest_entries {
            println!(
                "  - {} [state={}] -> {}\n    audit: {}",
                m.id,
                m.state,
                m.destination_path.as_deref().unwrap_or("<retired>"),
                m.audit_notes
            );
            for cure in &m.required_cures {
                println!("    cure:  {cure}");
            }
        }
    }

    println!("\n6-Gate Pre-Uptake Quarry Surgery Checklist:");
    for g in &rep.gates {
        let tag = if g.passed { "PASS" } else { "FAIL" };
        println!("  [{tag}] {:<34} {} — {}", g.gate_id, g.summary, g.title);
    }

    if rep.modularity.lean_files > 0 {
        let m = &rep.modularity;
        println!(
            "\nDonor Modularity Profile: lean_files={} lines={} max_lines={} carriers={} thms={} (composed={}, leaf={}) index={:.2}/100",
            m.lean_files,
            m.total_lean_lines,
            m.max_module_lines,
            m.structures + m.classes,
            m.total_theorems,
            m.composed_theorems,
            m.isolated_leaf_theorems,
            m.compositionality_index
        );
    }

    if !rep.findings.is_empty() {
        println!("\nDefects that must be cured before entering `obend` (showing up to 60):");
        for f in rep.findings.iter().take(60) {
            println!(
                "  [{}][{}] {}:{}:{} ({})\n    {}\n    cure: {}",
                f.severity,
                f.artifact_kind,
                f.path,
                f.line,
                f.column,
                f.rule_id,
                f.message,
                f.remediation
            );
        }
        if rep.findings.len() > 60 {
            println!(
                "  ... ({} additional defects; pass `--json` for full list)",
                rep.findings.len() - 60
            );
        }
    }
}

fn print_human_cone_report(rep: &obb_lint::cone::ConeReport) {
    println!(
        "obb cone: repo={} scan_ms={:.2}ms modules={} (`module`={}, legacy={})",
        rep.repo_root,
        rep.scan_ms,
        rep.total_modules,
        rep.module_system_files,
        rep.legacy_non_module_files
    );
    println!(
        "imports: public={} private={} meta={} | max_public_cone_depth={} | file_wide_expose(>80L)={} | public_meta_leaks={} | proof_cone_leaks={}",
        rep.total_public_imports,
        rep.total_private_imports,
        rep.total_meta_imports,
        rep.max_public_cone_depth,
        rep.file_wide_expose_modules,
        rep.public_meta_import_leaks.len(),
        rep.proof_cone_leaks.len()
    );
    if !rep.critical_path.is_empty() {
        println!(
            "critical `public import` chain (depth {}): {}",
            rep.max_public_cone_depth,
            rep.critical_path.join(" -> ")
        );
    }
    if !rep.high_blast_radius_hubs.is_empty() {
        println!(
            "\nHigh-blast-radius hubs (`fan_in > 25`, showing top {} of {} — require Wave-0 barrier):",
            rep.high_blast_radius_hubs.len().min(20),
            rep.high_blast_radius_hubs.len()
        );
        println!(
            "  {:<42} {:>10} {:>12}  Path",
            "Module", "PubFanIn", "BlastRadius"
        );
        for h in rep.high_blast_radius_hubs.iter().take(20) {
            println!(
                "  {:<42} {:>10} {:>12}  {}",
                h.module, h.public_fan_in, h.blast_radius, h.path
            );
        }
    }
    if !rep.public_meta_import_leaks.is_empty() {
        println!(
            "\n`lean/public-meta-import-leak` findings ({}):",
            rep.public_meta_import_leaks.len()
        );
        for lk in &rep.public_meta_import_leaks {
            println!(
                "  [ERROR] {}:{} ({}) -> `public meta import {}` outside Obend/{{Tactic,Elab}}",
                lk.rel_path, lk.line, lk.module, lk.imported
            );
        }
    }
    if !rep.depth_violations.is_empty() {
        println!(
            "\n`--max-depth` violations ({}):",
            rep.depth_violations.len()
        );
        for v in rep.depth_violations.iter().take(20) {
            println!(
                "  [FAIL] {} ({}) depth={} > max_allowed={}",
                v.module, v.rel_path, v.depth, v.max_allowed
            );
        }
    }
}

fn print_human_cone_plan(plan: &obb_lint::cone::ConePlanReport, scan_ms: f64) {
    let verdict = if plan.disjoint_write_slices {
        "DISJOINT"
    } else {
        "OVERLAP REFUSED"
    };
    println!(
        "obb cone plan [{verdict}]: repo={} mode={} shards={} wave0_hubs(fan_in>{})={} scan_ms={:.2}ms",
        plan.repo_root,
        plan.mode,
        plan.shards.len(),
        plan.hub_threshold,
        plan.wave0_barrier_hubs.len(),
        scan_ms
    );
    if !plan.overlapping_assignments.is_empty() {
        println!(
            "\nOVERLAPPING WRITE SLICES ({} file(s) assigned to multiple workers):",
            plan.overlapping_assignments.len()
        );
        for ov in &plan.overlapping_assignments {
            println!("  [FAIL] {} -> owned by {:?}", ov.path, ov.shards);
        }
    }
    if !plan.hub_warnings.is_empty() {
        println!(
            "\nHIGH-BLAST-RADIUS HUB CONTENTION WARNINGS ({}):",
            plan.hub_warnings.len()
        );
        for w in &plan.hub_warnings {
            println!("  [WARN] {}", w.message);
        }
    }
    println!("\nPlanned worker shards:");
    for s in &plan.shards {
        println!(
            "  - {:<12} modules={:<4} lines={:<7} max_blast={:<4} groups=[{}]",
            s.name,
            s.module_count,
            s.total_lines,
            s.max_blast_radius,
            s.subsystem_groups.join(", ")
        );
    }
}

fn print_human_apex_report(rep: &obb_lint::apex::ApexReport, subcmd: &str) {
    let verdict = if rep.check_passed { "PASS" } else { "FAIL" };
    println!(
        "obb apex {subcmd} [{verdict}]: repo={} apex_valid={}/{} planned_materialized={}/{}",
        rep.repo_root,
        rep.valid_apex_count,
        rep.registered_apex_count,
        rep.planned_materialized_count,
        rep.planned_apex_count
    );
    println!(
        "coverage: apex_cone={}/{} modules ({:.1}%) | wired(apex+exe)={}/{} ({:.1}%) | apex_decls={}/{} | unwired_leaf_islands={}",
        rep.apex_covered_library_modules,
        rep.total_library_modules,
        rep.overall_apex_coverage_pct,
        rep.wired_library_modules,
        rep.total_library_modules,
        rep.overall_wired_coverage_pct,
        rep.apex_reachable_declarations,
        rep.total_library_declarations,
        rep.unwired_island_count
    );

    println!("\nApex Compositional Coverage by Subsystem:");
    println!(
        "  {:<14} {:>5} {:>7} {:>9} {:>8} {:>9} {:>8} {:>8}",
        "Subsystem", "Apex#", "Modules", "ApexCone", "Apex%", "Wired", "Wired%", "Islands"
    );
    for s in &rep.subsystem_coverage {
        println!(
            "  {:<14} {:>5} {:>7} {:>9} {:>7.1}% {:>9} {:>7.1}% {:>8}",
            s.subsystem,
            s.registered_apex_theorems,
            s.total_modules,
            s.apex_covered_modules,
            s.apex_coverage_pct,
            s.wired_modules,
            s.wired_coverage_pct,
            s.unwired_islands
        );
    }

    println!(
        "\nRegistered `[apex]` Whole-System Theorems ({}):",
        rep.apex_theorems.len()
    );
    for a in &rep.apex_theorems {
        let tag = if a.valid { "PASS" } else { "FAIL" };
        println!(
            "  [{tag}] {:<36} {:<10} {}::{} (cone={} mods, {} decls, sorry={}, axiom={})",
            a.id,
            a.subsystem,
            a.module,
            a.theorem,
            a.cone_modules,
            a.cone_declarations,
            a.sorry_count,
            a.custom_axiom_count
        );
        for off in &a.offenders {
            println!("         offender: {off}");
        }
    }

    if !rep.planned_apex.is_empty() {
        println!("\nPlanned Wave 4–5 Vertical Spines (`[planned_apex]`):");
        for p in &rep.planned_apex {
            let st = if p.materialized {
                "MATERIALIZED"
            } else {
                "PENDING"
            };
            println!(
                "  [{st:<12}] [{}] {:<32} {}::{} ({})",
                p.pillar, p.id, p.target_module, p.target_theorem, p.wave
            );
        }
    }

    if !rep.failure_reasons.is_empty() {
        println!("\nApex Gate Refusals ({}):", rep.failure_reasons.len());
        for r in &rep.failure_reasons {
            println!("  [FAIL] {r}");
        }
    }

    if !rep.unwired_leaf_islands.is_empty() {
        println!(
            "\nUnwired leaf-island modules in `lean/Obend/` (showing up to 30 of {}):",
            rep.unwired_leaf_islands.len()
        );
        for isl in rep.unwired_leaf_islands.iter().take(30) {
            println!(
                "  [{:<10}] {:<44} ({:>4} lines, {:>2} thms) {}",
                isl.subsystem, isl.module, isl.lines, isl.theorems, isl.rel_path
            );
        }
        if rep.unwired_leaf_islands.len() > 30 {
            println!(
                "  ... ({} additional unwired leaf islands; pass `--json` for full list)",
                rep.unwired_leaf_islands.len() - 30
            );
        }
    }
}

fn print_human_pipeline_report(
    rep: &obb_judge::pipeline::PipelineReport,
    require_sealed: bool,
    strict: bool,
) {
    println!(
        "obb pipeline check [{}]: repo={} passed={} ready_for_parallel_swarm={} ready_for_claimed={}",
        rep.stage, rep.repo_root, rep.passed, rep.ready_for_parallel_swarm, rep.ready_for_claimed
    );
    println!(
        "obligations: total={} sealed={} open_stage_a={} consumer_sites={} | smuggled_sorry={} smuggled_axiom={}",
        rep.total_obligations,
        rep.sealed_obligations,
        rep.open_stage_a_obligations,
        rep.consumer_sites.len(),
        rep.smuggled_sorry_count,
        rep.smuggled_axiom_count
    );
    if !rep.obligations.is_empty() {
        println!("\nHypothesisLedger / *Obligations / @[obb_obligation] classes:");
        for ob in &rep.obligations {
            let st = if ob.discharged {
                "SEALED"
            } else {
                "OPEN_STAGE_A"
            };
            println!(
                "  [{st:<12}] {} ({}:{}) fields={} consumers={} instances={}",
                ob.fq_name,
                ob.path,
                ob.line,
                ob.field_count,
                ob.consumer_count,
                ob.discharging_instances.len()
            );
        }
    }
    if !rep.violations.is_empty() {
        println!("\nPipeline Violations ({}):", rep.violations.len());
        for v in &rep.violations {
            println!(
                "  [FAIL][{}] {}:{} `{}`: {}\n    fix: {}",
                v.kind, v.path, v.line, v.symbol, v.message, v.remediation
            );
        }
    } else if strict && rep.stage == PipelineStage::Undeclared {
        println!(
            "\n[FAIL] `--strict` is set, and 0 obligation classes (`*Obligations` / `HypothesisLedger` / `@[obb_obligation]`) were declared (`UNDECLARED`)."
        );
    } else if require_sealed && rep.stage != PipelineStage::StageBSealed {
        println!(
            "\n[FAIL] `--require-sealed` is set, but pipeline stage is `{}` ({} open Stage-A obligation(s)).",
            rep.stage, rep.open_stage_a_obligations
        );
    }
}

fn print_human_broker_probe(rep: &obb_broker::BrokerProbeReport) {
    println!(
        "obb broker probe: dry_run={} recommended_general_host={}",
        rep.dry_run,
        rep.recommended_general_host.as_deref().unwrap_or("<none>")
    );
    for h in &rep.hosts {
        println!(
            "  {:<8} reachable={:<5} cores={:<2} load=({:.2},{:.2},{:.2}) free={:>6.1}/{:>6.1} GiB (zfs_arc={:>5.1} GiB) disk={:>6.1} GiB active_lean={} runaways(>30m)={} swarm_build={} score={:>5.1} ({})",
            h.host,
            h.reachable,
            h.cpu_cores,
            h.load_1m,
            h.load_5m,
            h.load_15m,
            h.mem_free_gib,
            h.mem_total_gib,
            h.zfs_arc_reclaimable_gib,
            h.disk_free_gib,
            h.active_lean_lake_procs,
            h.runaway_procs.len(),
            h.has_swarm_build,
            h.health_score,
            h.note
        );
        for r in &h.runaway_procs {
            println!(
                "    [RUNAWAY] pid={} age={}s rss={}MiB {} `{}`",
                r.pid, r.elapsed_secs, r.rss_mib, r.comm, r.args
            );
        }
    }
}

fn print_human_broker_plan(rep: &obb_broker::BuildPlanReport) {
    println!(
        "obb broker plan-build: targets={} batches={} seed_key={} timeout={}s max_rss={}GiB",
        rep.total_targets,
        rep.total_batches,
        &rep.seed_key[..rep.seed_key.len().min(16)],
        rep.timeout_secs,
        rep.max_rss_gb
    );
    for w in &rep.warnings {
        println!("  [WARN] {w}");
    }
    println!("\nTarget routing:");
    for r in &rep.routing {
        println!(
            "  {:<36} -> {:<6} [{}] ({})",
            r.lake_target, r.assigned_host, r.workload_class, r.reason
        );
    }
    for b in &rep.batches {
        println!(
            "\nBatch on `{}` ({} target(s), seed_pool={}):\n  cmd: {}",
            b.host,
            b.lake_targets.len(),
            b.seed_pool_dir,
            b.batched_lake_command
        );
        if let Some(ref ex) = b.execution {
            println!(
                "  execution: exit_code={} duration_ms={}",
                ex.exit_code, ex.duration_ms
            );
            if !ex.stdout_tail.is_empty() {
                println!("  stdout:\n{}", ex.stdout_tail);
            }
            if !ex.stderr_tail.is_empty() {
                println!("  stderr:\n{}", ex.stderr_tail);
            }
        } else {
            println!("  recipe:\n{}", b.remote_recipe.trim_end());
        }
    }
}

fn print_human_harness_list(rep: &obb_lint::harness::HarnessListReport) {
    println!(
        "obb harness list: schema={} total_artifacts={} (root_rules={}, skills={}) rule_hard_cap={}B",
        rep.schema_version,
        rep.total_artifacts,
        rep.root_rules,
        rep.skills,
        rep.rule_hard_cap_bytes
    );
    for art in &rep.artifacts {
        println!(
            "  [{:<9}] {:<48} {:>6}/{:<6}B sha256={} harnesses=[{}]",
            match art.kind {
                obb_lint::harness::HarnessArtifactKind::RootRule => "root_rule",
                obb_lint::harness::HarnessArtifactKind::Skill => "skill",
            },
            art.rel_path,
            art.byte_len,
            art.byte_budget,
            &art.sha256[..12],
            art.harnesses.join(",")
        );
    }
}

fn print_human_harness_install(rep: &obb_lint::harness::HarnessInstallReport) {
    let verdict = if rep.passed { "INSTALLED" } else { "REFUSED" };
    println!(
        "obb harness install [{verdict}]: repo={} schema={} written={} unchanged={} force={}",
        rep.repo_root, rep.schema_version, rep.files_written, rep.files_unchanged, rep.force
    );
    for r in &rep.refusals {
        eprintln!("  [REFUSED][{}] {}: {}", r.kind, r.rel_path, r.message);
    }
    for act in &rep.actions {
        println!(
            "  [{:<9}] {:<48} {:>6}B sha256={}",
            act.action,
            act.rel_path,
            act.bytes_written,
            &act.sha256[..12]
        );
    }
}

fn print_human_harness_check(rep: &obb_lint::harness::HarnessCheckReport) {
    let verdict = if rep.passed { "PASS" } else { "FAIL" };
    println!(
        "obb harness check [{verdict}]: repo={} schema={} checked_files={} issues={}",
        rep.repo_root,
        rep.schema_version,
        rep.checked_files.len(),
        rep.issues.len()
    );
    for cf in &rep.checked_files {
        let tag = if cf.exists
            && cf.marker_valid
            && cf.checksum_matches_template
            && cf.frontmatter_valid.unwrap_or(true)
            && cf.byte_len <= cf.byte_budget
            && cf.expanded_byte_len < obb_lint::harness::RULE_FILE_HARD_CAP_BYTES
        {
            "PASS"
        } else {
            "FAIL"
        };
        println!(
            "  [{tag}] {:<48} bytes={:>6}/{:<6} expanded={:>6}B marker={} sha_match={}",
            cf.rel_path,
            cf.byte_len,
            cf.byte_budget,
            cf.expanded_byte_len,
            cf.marker_valid,
            cf.checksum_matches_template
        );
    }
    if !rep.issues.is_empty() {
        println!("\nHarness Check Issues ({}):", rep.issues.len());
        for iss in &rep.issues {
            println!(
                "  [FAIL][{}] {}: {}\n    fix: {}",
                iss.kind, iss.rel_path, iss.message, iss.remediation
            );
        }
    }
}
