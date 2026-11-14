//! Statechart Supervisor, Segment Tree, Append-Only JSONL Ledger & Live Probes
//! (`PROCESS.md`, `DESIGN.md` §4–5, `spec/process.json`).
//!
//! In `obb v7 (0.7.0)`:
//! - Caller-supplied `guard_passed: bool` self-attestation is eliminated from both campaign and
//!   quest statechart transitions (`CampaignGuardEvidence`, `QuestGuardEvidence`).
//! - Authoritative quest transitions (`Toothed`, `Landed`, `Claimed`, `Recorded`, and composite
//!   verbs `take_quest`, `propose_quest`, `land_quest`) verify content-addressed `JudgeReceipt`s bound
//!   to `(base_sha, head_sha, tree_oid)`, live trunk SHA freshness (`StaleBaseSha`), and non-overlapping
//!   footprint leases. A lease detects contention between quests (`FootprintLeaseConflict`); an
//!   uncontended out-of-lease path extends the lease at `propose` and is recorded, never refused.
//! - Emergency operator overrides record reality unconditionally in the append-only ledger with
//!   `effective_regime = "AttestedOverride"` and `merged_ungated = true` without certifying the
//!   quest as `decided` or `certified` (`obend-swarm` Finding 14).
//! - Demo seed state (`seed_obend_campaign`) is tagged `origin = "demo_seed"` and separated from
//!   live operational transitions in `StateSnapshot`.

use anyhow::{Context, Result, bail};
use chrono::Utc;
use obb_core::{ProcessSpec, Regime, Sink, sha256_hex};
use obb_judge::{Gate, JudgeReceipt, SuccessionRecord, check_well_formed};
use obb_lint::run_repo_lints;
use rusqlite::{Connection, OptionalExtension, params};
use serde::{Deserialize, Serialize};
use std::fs::{self, OpenOptions};
use std::io::{BufRead, BufReader, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

pub const DEFAULT_CV_BIN: &str = "/Users/ember/.cargo/bin/cv";
pub const DISK_FREE_FLOOR_GB: f64 = 20.0;
pub const SEGMENT_FORK_TOKEN_CAP: u64 = 64_000;
pub const SEGMENT_PRESSURE_TOKEN_CAP: u64 = 120_000;

pub const ORIGIN_LIVE: &str = "live";
pub const ORIGIN_DEMO_SEED: &str = "demo_seed";
pub const REGIME_ATTESTED_OVERRIDE: &str = "AttestedOverride";

fn default_live_origin() -> String {
    ORIGIN_LIVE.to_string()
}

fn default_attested_str() -> String {
    "attested".to_string()
}

fn configure_hermetic_git(cmd: &mut Command) -> &mut Command {
    cmd.env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_NOSYSTEM", "1");
    if Path::new("/private/tmp").is_dir() {
        cmd.env("TMPDIR", "/private/tmp");
    }
    cmd
}

fn run_git(repo_root: &Path, args: &[&str]) -> Result<String> {
    let mut cmd = Command::new("git");
    configure_hermetic_git(&mut cmd)
        .arg("-C")
        .arg(repo_root)
        .env("GIT_AUTHOR_NAME", "obb-state")
        .env("GIT_AUTHOR_EMAIL", "obb-state@localhost")
        .env("GIT_COMMITTER_NAME", "obb-state")
        .env("GIT_COMMITTER_EMAIL", "obb-state@localhost")
        .args(args);
    let out = cmd
        .output()
        .with_context(|| format!("failed to run git {:?} in {}", args, repo_root.display()))?;
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

fn run_git_ro(repo_root: &Path, args: &[&str]) -> Result<String> {
    let mut cmd = Command::new("git");
    configure_hermetic_git(&mut cmd)
        .arg("--no-optional-locks")
        .arg("-C")
        .arg(repo_root)
        .args(args);
    let out = cmd
        .output()
        .with_context(|| format!("failed to run git {:?} in {}", args, repo_root.display()))?;
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

fn normalize_footprint_entry(p: &str) -> String {
    let trimmed = p.trim().trim_start_matches("./").trim_end_matches('/');
    if trimmed.is_empty() {
        ".".to_string()
    } else {
        trimmed.to_string()
    }
}

fn footprint_entries_overlap(a: &str, b: &str) -> bool {
    let na = normalize_footprint_entry(a);
    let nb = normalize_footprint_entry(b);
    if na == "*" || nb == "*" || na == "." || nb == "." || na == nb {
        return true;
    }
    na.starts_with(&format!("{nb}/")) || nb.starts_with(&format!("{na}/"))
}

fn path_within_footprint(changed_path: &str, footprint: &[String]) -> bool {
    if footprint.is_empty() {
        return true;
    }
    let cp = normalize_footprint_entry(changed_path);
    footprint.iter().any(|entry| {
        let ne = normalize_footprint_entry(entry);
        ne == "*" || ne == "." || cp == ne || cp.starts_with(&format!("{ne}/"))
    })
}

fn regime_satisfies_target(achieved: Regime, target_str: &str) -> bool {
    match target_str.trim().to_ascii_lowercase().as_str() {
        "decided" => achieved == Regime::Decided,
        "certified" => matches!(achieved, Regime::Decided | Regime::Certified),
        "attested" => true,
        _ => false,
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, thiserror::Error)]
pub enum StateRefusal {
    #[error(
        "IllegalTransition: {machine} `{id}` cannot move `{from}` -> `{to}` (not in `spec/process.json`)"
    )]
    IllegalTransition {
        machine: String,
        id: String,
        from: String,
        to: String,
    },

    #[error(
        "SinkExitViolation: quest `{id}` is in sink `{sink}`; leaving requires `{required_exit}` by holder `{holder}` (got actor `{actor}`, action `{action}`)"
    )]
    SinkExitViolation {
        id: Box<str>,
        sink: Box<str>,
        required_exit: Box<str>,
        holder: Box<str>,
        actor: Box<str>,
        action: Box<str>,
    },

    #[error("GuardFailed({guard}): {reason}")]
    GuardFailed { guard: String, reason: String },

    #[error("TamperedReceipt: quest `{quest_id}` rejected invalid `JudgeReceipt`: {reason}")]
    TamperedReceipt { quest_id: String, reason: String },

    #[error(
        "StaleBaseSha: quest `{quest_id}` receipt base `{receipt_base_sha}` does not match live `{trunk_branch}` tip `{current_trunk_sha}` (rebase and re-run `obb judge`)"
    )]
    StaleBaseSha {
        quest_id: String,
        trunk_branch: String,
        receipt_base_sha: String,
        current_trunk_sha: String,
    },

    #[error(
        "FootprintLeaseConflict: quest `{quest_id}` requested `{requested}` which overlaps active quest `{conflicting_quest}` lease `{conflicting_entry}`"
    )]
    FootprintLeaseConflict {
        quest_id: String,
        requested: String,
        conflicting_quest: String,
        conflicting_entry: String,
    },

    #[error(
        "FootprintViolation: quest `{quest_id}` modified `{violating_paths:?}` outside leased footprint `{allowed_footprint:?}`"
    )]
    FootprintViolation {
        quest_id: String,
        violating_paths: Vec<String>,
        allowed_footprint: Vec<String>,
    },

    #[error(
        "InvalidEmberEvent: `{event}` is forbidden on ember's channel; allowed events are strictly {allowed:?}"
    )]
    InvalidEmberEvent { event: String, allowed: Vec<String> },

    #[error(
        "DiskHeadroomFloor: machine `{host}` has {avail_gb:.2} GB free (< {floor_gb:.1} GB floor); scheduling paused"
    )]
    DiskHeadroomFloor {
        host: String,
        avail_gb: f64,
        floor_gb: f64,
    },

    #[error(
        "LargeContextFork(S4): segment `{seg_id}` has {tokens} tokens (> {cap} cap) in state `{state}`; run `obb seg distill` before forking"
    )]
    LargeContextFork {
        seg_id: String,
        tokens: u64,
        cap: u64,
        state: String,
    },

    #[error(
        "HandoffDirectionViolation(S5): `{direction}` handoff requires `{expected_mode}`, got `{actual_mode}`"
    )]
    HandoffDirectionViolation {
        direction: String,
        expected_mode: String,
        actual_mode: String,
    },

    #[error(
        "LedgerAppendFailed: failed to append `{event_type}` for `{entity_id}` to `{path}`: {reason}"
    )]
    LedgerAppendFailed {
        event_type: String,
        entity_id: String,
        path: String,
        reason: String,
    },

    #[error("StorageError: {0}")]
    StorageError(String),
}

/// Evaluated evidence required for campaign statechart transitions (replaces `guard_passed: bool`).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum CampaignGuardEvidence {
    /// Unguarded transitions (`Aim -> Alone`, `Alone -> Aim`, `Running -> Running`, `Running -> Done`).
    Unconditional { note: String },
    /// `G1` (`Aim -> Grounded`): verified foundation files read in `target_repo`.
    WholeRead {
        foundation_files: Vec<String>,
        note: String,
    },
    /// `G2` (`Grounded -> Running`): verified WellFormed `Gate` (`judge.json`) on disk.
    Briefed { judge_path: PathBuf, note: String },
    /// `G3` (`Running -> Reground`): budget spent, `ember.aim` event, or doctrine contradiction.
    RegroundTrigger { trigger: String },
    /// `G4` (`Reground -> Aim`): verified non-regressing `SuccessionRecord`.
    JudgeSuccession { record: SuccessionRecord },
    /// Emergency operator override recorded as `AttestedOverride`.
    AttestedOverride { operator: String, reason: String },
}

/// Evaluated evidence required for quest statechart transitions (replaces `guard_passed: bool`).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum QuestGuardEvidence {
    /// Enter one of the 18 frustration sinks (`spec/process.json` `sink_edges`).
    EnterSink { reason: String },
    /// Exit a frustration sink (`actor == holder_agent` + non-empty `remedial_action`).
    ExitSink { remedial_action: String },
    /// `Q1` (`Grounded -> Scoped`): scope brief, leased footprint paths, and swarm-hour estimate.
    ScopeBrief {
        deliverable: String,
        footprint_paths: Vec<String>,
        estimated_swarm_hours: f64,
        #[serde(default)]
        base_sha: Option<String>,
    },
    /// `Q2` (`Scoped -> Built`) or `Q3` (`Built -> Wired`): evaluated directly on `repo_root` via
    /// artifact existence, footprint-lease compliance, and `obb-lint` `Theater`/`Mirror` checks.
    RepoCheck {
        repo_root: PathBuf,
        artifacts: Vec<String>,
    },
    /// `Q4` (`Toothed`), `Q5` (`Landed`), or `Q6` (`Claimed`): verified `JudgeReceipt` bound to
    /// `(base_sha, head_sha, tree_oid)` + live trunk SHA freshness + executed `#tooth` + footprint check.
    Receipt {
        receipt: Box<JudgeReceipt>,
        repo_root: PathBuf,
        trunk_branch: String,
    },
    /// `Q7` (`Claimed -> Recorded`): verifies quest was NOT `merged_ungated`, ledger hash chain is
    /// intact, and `obb-lint` reports 0 markdown/navel errors on `repo_root`.
    RecordCheck { repo_root: PathBuf, summary: String },
    /// Explicit operator emergency bypass (`obend-swarm` Finding 14): records reality unconditionally
    /// in SQLite + ledger with `effective_regime = "AttestedOverride"` and `merged_ungated = true`,
    /// never marking the quest `decided` or `certified`.
    AttestedOverride {
        operator: String,
        reason: String,
        #[serde(default)]
        head_sha: Option<String>,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CampaignRow {
    pub id: String,
    pub title: String,
    pub state: String,
    pub aim_statement: String,
    pub target_repo: String,
    #[serde(default = "default_live_origin")]
    pub origin: String,
    pub updated_at: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QuestRow {
    pub id: String,
    pub campaign_id: String,
    pub title: String,
    pub state: String,
    pub is_sink: bool,
    pub prior_state: Option<String>,
    pub holder_agent: String,
    pub target_regime: String,
    #[serde(default = "default_attested_str")]
    pub effective_regime: String,
    #[serde(default)]
    pub merged_ungated: bool,
    #[serde(default = "default_live_origin")]
    pub origin: String,
    #[serde(default)]
    pub footprint_lease: Vec<String>,
    #[serde(default)]
    pub base_sha: Option<String>,
    #[serde(default)]
    pub proposed_head_sha: Option<String>,
    #[serde(default)]
    pub landed_sha: Option<String>,
    #[serde(default)]
    pub verified_receipt_hash: Option<String>,
    pub tooth_witness: Option<String>,
    pub updated_at: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SegmentRow {
    pub id: String,
    pub quest_id: String,
    pub parent_id: Option<String>,
    pub state: String,
    pub model_tier: String,
    pub host: String,
    pub token_count: u64,
    pub transcript_mode: String,
    pub distill_hash: Option<String>,
    pub notes: String,
    #[serde(default = "default_live_origin")]
    pub origin: String,
    pub updated_at: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EmberEventRow {
    pub id: i64,
    pub kind: String,
    pub subject_id: String,
    pub prompt: String,
    pub resolved: bool,
    pub resolution: Option<String>,
    pub created_at: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MachineStatus {
    pub host: String,
    pub reachable: bool,
    pub required_for_dispatch: bool,
    pub avail_gb: f64,
    pub total_gb: f64,
    pub load_summary: String,
    pub below_floor: bool,
    pub checked_at: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GitProbeReport {
    pub repo: String,
    pub clean_working_tree: bool,
    pub modified_paths: Vec<String>,
    pub stash_count: usize,
    pub merged_side_branches: Vec<String>,
    pub current_branch: String,
    pub q5_passed: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CvProbeReport {
    pub cv_bin: String,
    pub available: bool,
    pub g1_whole_read_events: usize,
    pub s2_doctor_ok: bool,
    pub s6_stranded_lanes: usize,
    pub deferrals_open: usize,
    pub summary: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LedgerEvent {
    pub seq: usize,
    pub timestamp: String,
    pub event_type: String,
    pub entity_id: String,
    pub summary: String,
    pub payload: serde_json::Value,
    pub prev_hash: String,
    pub event_hash: String,
}

impl LedgerEvent {
    pub fn is_demo_seed(&self) -> bool {
        self.event_type.starts_with("demo_seed.")
            || self
                .payload
                .get("origin")
                .and_then(|v| v.as_str())
                .is_some_and(|o| o == ORIGIN_DEMO_SEED)
    }

    pub fn is_live_transition(&self) -> bool {
        !self.is_demo_seed()
            && matches!(
                self.event_type.as_str(),
                "campaign.transition"
                    | "quest.transition"
                    | "quest.taken"
                    | "quest.proposed"
                    | "quest.landed"
                    | "quest.sink_entered"
                    | "quest.sink_exited"
            )
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StateSnapshot {
    pub workspace_root: String,
    #[serde(default)]
    pub state_dir: String,
    pub scheduler_paused: bool,
    pub pause_reasons: Vec<String>,
    #[serde(default)]
    pub contains_demo_seed: bool,
    #[serde(default)]
    pub live_event_count: usize,
    #[serde(default)]
    pub live_transition_count: usize,
    #[serde(default)]
    pub demo_seed_event_count: usize,
    #[serde(default)]
    pub verified_quest_count: usize,
    #[serde(default)]
    pub ungated_override_count: usize,
    pub campaigns: Vec<CampaignRow>,
    pub quests: Vec<QuestRow>,
    pub segments: Vec<SegmentRow>,
    pub waiting_on_ember: Vec<EmberEventRow>,
    pub machines: Vec<MachineStatus>,
    pub recent_ledger: Vec<LedgerEvent>,
}

/// Resolve an out-of-tree state directory so `obb` NEVER pollutes audited git worktrees with `.obb/state.db`:
/// 1. `OBB_STATE_DIR` environment override (exact directory)
/// 2. `$XDG_STATE_HOME/obb/<repo_hash>/`
/// 3. `<obb_workspace>/.obb-state/<repo_hash>/` when `workspace_root` itself is the `obebuilder` workspace (`spec/process.json`)
/// 4. `$OBB_HOME/.obb-state/<repo_hash>/` if `OBB_HOME` is set
/// 5. `<workspace_root>/.obb/ledger/` (gitignore `.obb/` in the target repository)
pub fn resolve_default_state_dir(workspace_root: &Path) -> PathBuf {
    let canon = workspace_root
        .canonicalize()
        .unwrap_or_else(|_| workspace_root.to_path_buf());
    let repo_hash = &sha256_hex(canon.to_string_lossy().as_bytes())[..16];

    if let Ok(explicit) = std::env::var("OBB_STATE_DIR") {
        let trimmed = explicit.trim();
        if !trimmed.is_empty() {
            return PathBuf::from(trimmed);
        }
    }
    if let Ok(xdg) = std::env::var("XDG_STATE_HOME") {
        let trimmed = xdg.trim();
        if !trimmed.is_empty() {
            return PathBuf::from(trimmed).join("obb").join(repo_hash);
        }
    }
    if canon.join("spec/process.json").is_file() {
        return canon.join(".obb-state").join(repo_hash);
    }
    if let Ok(obb_home) = std::env::var("OBB_HOME") {
        let trimmed = obb_home.trim();
        if !trimmed.is_empty() {
            return PathBuf::from(trimmed).join(".obb-state").join(repo_hash);
        }
    }
    canon.join(".obb").join("ledger")
}

/// Persistent SQLite + JSONL Statechart Supervisor.
pub struct StateStore {
    workspace_root: PathBuf,
    state_dir: PathBuf,
    db_path: PathBuf,
    ledger_path: PathBuf,
    pub spec: ProcessSpec,
}

impl StateStore {
    pub fn open(workspace_root: &Path) -> Result<Self> {
        Self::open_with_state_dir(workspace_root, None)
    }

    pub fn open_with_state_dir(
        workspace_root: &Path,
        explicit_state_dir: Option<&Path>,
    ) -> Result<Self> {
        let spec_path = workspace_root.join("spec/process.json");
        let spec = if spec_path.is_file() {
            ProcessSpec::load_from_path(&spec_path)?
        } else {
            ProcessSpec::embedded_default()?
        };

        let state_dir = match explicit_state_dir {
            Some(dir) => dir.to_path_buf(),
            None => resolve_default_state_dir(workspace_root),
        };
        fs::create_dir_all(&state_dir)
            .with_context(|| format!("failed to create state directory {}", state_dir.display()))?;

        let db_path = state_dir.join("state.db");
        let ledger_path = state_dir.join("events.jsonl");

        let store = Self {
            workspace_root: workspace_root.to_path_buf(),
            state_dir,
            db_path,
            ledger_path,
            spec,
        };
        store.init_schema()?;
        Ok(store)
    }

    pub fn state_dir(&self) -> &Path {
        &self.state_dir
    }

    pub fn db_path(&self) -> &Path {
        &self.db_path
    }

    pub fn ledger_path(&self) -> &Path {
        &self.ledger_path
    }

    fn conn(&self) -> Result<Connection> {
        let conn = Connection::open(&self.db_path)
            .with_context(|| format!("failed to open SQLite DB at {}", self.db_path.display()))?;
        conn.pragma_update(None, "journal_mode", "WAL")?;
        conn.pragma_update(None, "foreign_keys", "ON")?;
        Ok(conn)
    }

    fn init_schema(&self) -> Result<()> {
        let conn = self.conn()?;
        conn.execute_batch(
            "
            CREATE TABLE IF NOT EXISTS campaigns (
                id TEXT PRIMARY KEY,
                title TEXT NOT NULL,
                state TEXT NOT NULL,
                aim_statement TEXT NOT NULL,
                target_repo TEXT NOT NULL,
                origin TEXT NOT NULL DEFAULT 'live',
                updated_at TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS quests (
                id TEXT PRIMARY KEY,
                campaign_id TEXT NOT NULL,
                title TEXT NOT NULL,
                state TEXT NOT NULL,
                is_sink INTEGER NOT NULL DEFAULT 0,
                prior_state TEXT,
                holder_agent TEXT NOT NULL,
                target_regime TEXT NOT NULL,
                effective_regime TEXT NOT NULL DEFAULT 'attested',
                merged_ungated INTEGER NOT NULL DEFAULT 0,
                origin TEXT NOT NULL DEFAULT 'live',
                footprint_json TEXT NOT NULL DEFAULT '[]',
                base_sha TEXT,
                proposed_head_sha TEXT,
                landed_sha TEXT,
                verified_receipt_hash TEXT,
                tooth_witness TEXT,
                updated_at TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS segments (
                id TEXT PRIMARY KEY,
                quest_id TEXT NOT NULL,
                parent_id TEXT,
                state TEXT NOT NULL,
                model_tier TEXT NOT NULL,
                host TEXT NOT NULL,
                token_count INTEGER NOT NULL DEFAULT 0,
                transcript_mode TEXT NOT NULL DEFAULT 'full',
                distill_hash TEXT,
                notes TEXT NOT NULL DEFAULT '',
                origin TEXT NOT NULL DEFAULT 'live',
                updated_at TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS ember_queue (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                kind TEXT NOT NULL,
                subject_id TEXT NOT NULL,
                prompt TEXT NOT NULL,
                resolved INTEGER NOT NULL DEFAULT 0,
                resolution TEXT,
                created_at TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS machines (
                host TEXT PRIMARY KEY,
                reachable INTEGER NOT NULL,
                required_for_dispatch INTEGER NOT NULL DEFAULT 1,
                avail_gb REAL NOT NULL,
                total_gb REAL NOT NULL,
                load_summary TEXT NOT NULL,
                below_floor INTEGER NOT NULL,
                checked_at TEXT NOT NULL
            );
            ",
        )?;

        // Safe schema migration for any pre-v7 SQLite DBs
        for (table, col_ddl) in [
            ("campaigns", "origin TEXT NOT NULL DEFAULT 'live'"),
            (
                "quests",
                "effective_regime TEXT NOT NULL DEFAULT 'attested'",
            ),
            ("quests", "merged_ungated INTEGER NOT NULL DEFAULT 0"),
            ("quests", "origin TEXT NOT NULL DEFAULT 'live'"),
            ("quests", "footprint_json TEXT NOT NULL DEFAULT '[]'"),
            ("quests", "base_sha TEXT"),
            ("quests", "proposed_head_sha TEXT"),
            ("quests", "landed_sha TEXT"),
            ("quests", "verified_receipt_hash TEXT"),
            ("segments", "origin TEXT NOT NULL DEFAULT 'live'"),
        ] {
            let col_name = col_ddl.split_whitespace().next().unwrap_or("");
            if !table_has_column(&conn, table, col_name)? {
                conn.execute(&format!("ALTER TABLE {table} ADD COLUMN {col_ddl}"), [])?;
            }
        }
        Ok(())
    }

    // -------------------------------------------------------------------------
    // Hash-chained Append-Only JSONL Ledger (`<state_dir>/events.jsonl`)
    // -------------------------------------------------------------------------

    fn ledger_lock(&self, exclusive: bool) -> Result<fs::File> {
        let file = OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .open(self.state_dir.join("ledger.lock"))?;
        if exclusive {
            file.lock()?;
        } else {
            file.lock_shared()?;
        }
        Ok(file) // OS releases the lock when this handle is dropped, including on errors.
    }

    pub fn read_ledger(&self) -> Result<Vec<LedgerEvent>> {
        let _lock = self.ledger_lock(false)?;
        self.read_ledger_unlocked()
    }

    fn read_ledger_unlocked(&self) -> Result<Vec<LedgerEvent>> {
        if !self.ledger_path.is_file() {
            return Ok(Vec::new());
        }
        let f = fs::File::open(&self.ledger_path)?;
        let reader = BufReader::new(f);
        let mut out = Vec::new();
        for (idx, line_res) in reader.lines().enumerate() {
            let line = line_res?;
            let trimmed = line.trim();
            if trimmed.is_empty() {
                continue;
            }
            let ev: LedgerEvent = serde_json::from_str(trimmed)
                .with_context(|| format!("corrupt JSONL ledger line {}", idx + 1))?;
            out.push(ev);
        }
        Ok(out)
    }

    pub fn verify_ledger_chain(&self) -> Result<usize> {
        let events = self.read_ledger()?;
        Self::verify_events(&events)
    }

    fn verify_events(events: &[LedgerEvent]) -> Result<usize> {
        let mut expected_prev = "0".repeat(64);
        for (index, ev) in events.iter().enumerate() {
            if ev.seq != index + 1 {
                bail!("ledger sequence gap at {}", ev.seq);
            }
            if ev.prev_hash != expected_prev {
                bail!(
                    "ledger hash chain broken at seq {}: expected prev_hash {}, got {}",
                    ev.seq,
                    expected_prev,
                    ev.prev_hash
                );
            }
            let canonical = format!(
                "{}|{}|{}|{}|{}|{}|{}",
                ev.seq,
                ev.timestamp,
                ev.event_type,
                ev.entity_id,
                ev.summary,
                serde_json::to_string(&ev.payload)?,
                ev.prev_hash
            );
            let actual_hash = sha256_hex(canonical.as_bytes());
            if ev.event_hash != actual_hash {
                bail!(
                    "ledger tamper detected at seq {}: expected hash {}, got {}",
                    ev.seq,
                    actual_hash,
                    ev.event_hash
                );
            }
            expected_prev = ev.event_hash.clone();
        }
        Ok(events.len())
    }

    /// Deterministic fold of the verified audit stream, without wall clock or disk measurements.
    pub fn ledger_snapshot(&self) -> Result<serde_json::Value> {
        let events = self.read_ledger()?;
        Self::verify_events(&events)?;
        let mut counts = std::collections::BTreeMap::<String, usize>::new();
        let mut latest = std::collections::BTreeMap::new();
        for event in &events {
            *counts.entry(event.event_type.clone()).or_default() += 1;
            latest.insert(event.entity_id.clone(), event);
        }
        Ok(serde_json::json!({
            "version": 1, "event_count": events.len(),
            "tip_hash": events.last().map(|e| e.event_hash.clone()).unwrap_or_else(|| "0".repeat(64)),
            "counts_by_type": counts, "latest_by_entity": latest,
        }))
    }

    /// Import a legacy ledger into an empty local vault. Repeated imports are idempotent;
    /// divergent histories are refused. The source remains intact for review/git removal.
    pub fn migrate_ledger(&self, source: &Path) -> Result<usize> {
        let raw = fs::read_to_string(source)?;
        let events: Vec<LedgerEvent> = raw
            .lines()
            .filter(|l| !l.trim().is_empty())
            .map(serde_json::from_str)
            .collect::<std::result::Result<_, _>>()?;
        let count = Self::verify_events(&events)?;
        let _lock = self.ledger_lock(true)?;
        let current = self.read_ledger_unlocked()?;
        if !current.is_empty() {
            Self::verify_events(&current)?;
            if serde_json::to_value(&current)? == serde_json::to_value(&events)? {
                return Ok(count);
            }
            bail!("cannot migrate over a different nonempty local ledger");
        }
        let temporary = self.state_dir.join("events.migration.tmp");
        let mut file = fs::File::create(&temporary)?;
        for event in &events {
            writeln!(file, "{}", serde_json::to_string(event)?)?;
        }
        file.sync_all()?;
        fs::rename(temporary, &self.ledger_path)?;
        Ok(count)
    }

    fn read_ledger_tail_meta(&self) -> Result<(usize, String)> {
        if !self.ledger_path.exists() {
            return Ok((0, "0".repeat(64)));
        }
        let mut f = fs::File::open(&self.ledger_path).with_context(|| {
            format!(
                "failed to open JSONL ledger at {}",
                self.ledger_path.display()
            )
        })?;
        let file_len = f.metadata()?.len();
        if file_len == 0 {
            return Ok((0, "0".repeat(64)));
        }

        let mut window: u64 = 65_536;
        loop {
            let seek_pos = file_len.saturating_sub(window);
            f.seek(SeekFrom::Start(seek_pos))?;
            let mut buf = Vec::new();
            f.read_to_end(&mut buf)?;
            if buf.last() != Some(&b'\n') {
                bail!("ledger has an incomplete final record (missing newline)");
            }
            let end = buf.iter().rposition(|b| !b.is_ascii_whitespace());
            let Some(end) = end else {
                if seek_pos == 0 {
                    return Ok((0, "0".repeat(64)));
                }
                window = window.saturating_mul(4);
                continue;
            };
            let start = buf[..=end].iter().rposition(|b| *b == b'\n').map(|n| n + 1);
            if start.is_some() || seek_pos == 0 {
                // The seek may split a UTF-8 code point in an earlier record. Decode only
                // the complete final JSON line, never the arbitrary start of the window.
                let ev: LedgerEvent = serde_json::from_slice(&buf[start.unwrap_or(0)..=end])
                    .context("corrupt tail JSONL ledger entry")?;
                return Ok((ev.seq, ev.event_hash));
            }
            window = window.saturating_mul(4);
        }
    }

    pub fn append_ledger(
        &self,
        event_type: &str,
        entity_id: &str,
        summary: &str,
        payload: serde_json::Value,
    ) -> Result<LedgerEvent> {
        let _lock = self.ledger_lock(true)?;
        let (last_seq, prev_hash) = self.read_ledger_tail_meta()?;
        let seq = last_seq + 1;
        let timestamp = Utc::now().to_rfc3339();
        let canonical = format!(
            "{}|{}|{}|{}|{}|{}|{}",
            seq,
            timestamp,
            event_type,
            entity_id,
            summary,
            serde_json::to_string(&payload)?,
            prev_hash
        );
        let event_hash = sha256_hex(canonical.as_bytes());
        let ev = LedgerEvent {
            seq,
            timestamp,
            event_type: event_type.to_string(),
            entity_id: entity_id.to_string(),
            summary: summary.to_string(),
            payload,
            prev_hash,
            event_hash,
        };

        if let Some(parent) = self.ledger_path.parent() {
            fs::create_dir_all(parent).with_context(|| {
                format!(
                    "failed to create ledger parent directory {}",
                    parent.display()
                )
            })?;
        }
        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.ledger_path)
            .with_context(|| {
                format!(
                    "failed to open JSONL ledger for append at {}",
                    self.ledger_path.display()
                )
            })?;
        writeln!(file, "{}", serde_json::to_string(&ev)?).with_context(|| {
            format!(
                "failed to write JSONL ledger event to {}",
                self.ledger_path.display()
            )
        })?;
        file.flush().with_context(|| {
            format!(
                "failed to flush JSONL ledger at {}",
                self.ledger_path.display()
            )
        })?;
        file.sync_data()?;
        Ok(ev)
    }

    fn append_ledger_or_refuse(
        &self,
        event_type: &str,
        entity_id: &str,
        summary: &str,
        payload: serde_json::Value,
    ) -> std::result::Result<LedgerEvent, StateRefusal> {
        self.append_ledger(event_type, entity_id, summary, payload)
            .map_err(|e| StateRefusal::LedgerAppendFailed {
                event_type: event_type.to_string(),
                entity_id: entity_id.to_string(),
                path: self.ledger_path.display().to_string(),
                reason: format!("{e:#}"),
            })
    }

    pub fn record_lob_succession(&self, rec: &SuccessionRecord) -> Result<LedgerEvent> {
        let summary = if rec.lob_cost.is_empty() {
            format!(
                "Judge succession {} -> {} (conservatively stronger, 0 new trust)",
                rec.old_name, rec.new_name
            )
        } else {
            let costs: Vec<String> = rec.lob_cost.iter().map(|t| t.to_wire()).collect();
            format!(
                "Judge succession {} -> {} with LobCost [{}]",
                rec.old_name,
                rec.new_name,
                costs.join(", ")
            )
        };
        self.append_ledger(
            "judge.lob_cost",
            &rec.new_name,
            &summary,
            serde_json::to_value(rec)?,
        )
    }

    // -------------------------------------------------------------------------
    // Campaign & Quest State Machines (`spec/process.json`)
    // -------------------------------------------------------------------------

    pub fn create_campaign(
        &self,
        id: &str,
        title: &str,
        aim_statement: &str,
        target_repo: &str,
    ) -> Result<CampaignRow> {
        let now = Utc::now().to_rfc3339();
        let initial = self.spec.machines.campaign.initial.clone();
        let mut conn = self.conn()?;
        let tx = conn.transaction()?;
        tx.execute(
            "INSERT OR REPLACE INTO campaigns (id, title, state, aim_statement, target_repo, origin, updated_at)
             VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7)",
            params![id, title, initial, aim_statement, target_repo, ORIGIN_LIVE, now],
        )?;
        let row = CampaignRow {
            id: id.to_string(),
            title: title.to_string(),
            state: initial.clone(),
            aim_statement: aim_statement.to_string(),
            target_repo: target_repo.to_string(),
            origin: ORIGIN_LIVE.to_string(),
            updated_at: now,
        };
        self.append_ledger(
            "campaign.created",
            id,
            &format!("Campaign `{title}` initialized in `{initial}`"),
            serde_json::to_value(&row)?,
        )?;
        tx.commit()?;
        Ok(row)
    }

    pub fn transition_campaign(
        &self,
        id: &str,
        to_state: &str,
        evidence: CampaignGuardEvidence,
    ) -> std::result::Result<CampaignRow, StateRefusal> {
        let mut conn = self
            .conn()
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?;
        let tx = conn
            .transaction()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        let cur: Option<(String, String, String, String, String)> = tx
            .query_row(
                "SELECT title, state, aim_statement, target_repo, origin FROM campaigns WHERE id = ?1",
                params![id],
                |r| Ok((r.get(0)?, r.get(1)?, r.get(2)?, r.get(3)?, r.get(4)?)),
            )
            .optional()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;

        let Some((title, from_state, aim_statement, target_repo, origin)) = cur else {
            return Err(StateRefusal::IllegalTransition {
                machine: "campaign".into(),
                id: id.into(),
                from: "<missing>".into(),
                to: to_state.into(),
            });
        };

        let Some(tr) = self.spec.find_campaign_transition(&from_state, to_state) else {
            return Err(StateRefusal::IllegalTransition {
                machine: "campaign".into(),
                id: id.into(),
                from: from_state,
                to: to_state.into(),
            });
        };

        let (evidence_note, is_override) = self.evaluate_campaign_guard(
            &tx,
            id,
            &from_state,
            to_state,
            tr.guard.as_deref(),
            &target_repo,
            &evidence,
        )?;

        let now = Utc::now().to_rfc3339();
        tx.execute(
            "UPDATE campaigns SET state = ?1, updated_at = ?2 WHERE id = ?3",
            params![to_state, now, id],
        )
        .map_err(|e| StateRefusal::StorageError(e.to_string()))?;

        let updated = CampaignRow {
            id: id.to_string(),
            title,
            state: to_state.to_string(),
            aim_statement,
            target_repo,
            origin: origin.clone(),
            updated_at: now,
        };
        let event_type = if is_override {
            "campaign.override_transition"
        } else {
            "campaign.transition"
        };
        self.append_ledger_or_refuse(
            event_type,
            id,
            &format!("Campaign `{id}`: `{from_state}` -> `{to_state}` ({evidence_note})"),
            serde_json::json!({
                "from": from_state,
                "to": to_state,
                "origin": origin,
                "regime": if is_override { REGIME_ATTESTED_OVERRIDE } else { "verified_guard" },
                "merged_ungated": is_override,
                "evidence": evidence,
            }),
        )?;
        tx.commit()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Ok(updated)
    }

    #[allow(clippy::too_many_arguments)]
    fn evaluate_campaign_guard(
        &self,
        tx: &rusqlite::Transaction<'_>,
        id: &str,
        from_state: &str,
        to_state: &str,
        guard_name: Option<&str>,
        target_repo: &str,
        evidence: &CampaignGuardEvidence,
    ) -> std::result::Result<(String, bool), StateRefusal> {
        if let CampaignGuardEvidence::AttestedOverride { operator, reason } = evidence {
            if operator.trim().is_empty() || reason.trim().is_empty() {
                return Err(StateRefusal::GuardFailed {
                    guard: guard_name.unwrap_or("override").into(),
                    reason: "AttestedOverride requires non-empty `operator` and `reason`".into(),
                });
            }
            return Ok((format!("AttestedOverride by `{operator}`: {reason}"), true));
        }

        if to_state == "Done" {
            let counts: (i64, i64) = tx
                .query_row(
                    "SELECT COUNT(*), COALESCE(SUM(CASE WHEN state = 'Recorded' AND merged_ungated = 0 THEN 1 ELSE 0 END), 0)
                     FROM quests WHERE campaign_id = ?1 AND origin = 'live'",
                    params![id],
                    |r| Ok((r.get(0)?, r.get(1)?)),
                )
                .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
            if counts.0 == 0 || counts.0 != counts.1 {
                return Err(StateRefusal::GuardFailed {
                    guard: "Done".into(),
                    reason: format!(
                        "campaign `{id}` cannot enter `Done`: {}/{} live quests are verified `Recorded`",
                        counts.1, counts.0
                    ),
                });
            }
        }

        match guard_name {
            None => match evidence {
                CampaignGuardEvidence::Unconditional { note } => {
                    if note.trim().is_empty() {
                        return Err(StateRefusal::GuardFailed {
                            guard: format!("{from_state}->{to_state}"),
                            reason: "campaign transition requires non-empty evidence note".into(),
                        });
                    }
                    Ok((note.clone(), false))
                }
                _ => Ok((format!("{from_state} -> {to_state}"), false)),
            },
            Some("G1") => match evidence {
                CampaignGuardEvidence::WholeRead {
                    foundation_files,
                    note,
                } => {
                    if foundation_files.is_empty() {
                        return Err(StateRefusal::GuardFailed {
                            guard: "G1".into(),
                            reason: "G1 requires at least one named foundation file".into(),
                        });
                    }
                    let repo_p = Path::new(target_repo);
                    for rel in foundation_files {
                        let p = if Path::new(rel).is_absolute() {
                            PathBuf::from(rel)
                        } else {
                            repo_p.join(rel)
                        };
                        if !p.is_file() {
                            return Err(StateRefusal::GuardFailed {
                                guard: "G1".into(),
                                reason: format!(
                                    "G1 foundation file `{}` does not exist at `{}`",
                                    rel,
                                    p.display()
                                ),
                            });
                        }
                    }
                    Ok((
                        format!(
                            "G1 verified {} foundation file(s): {note}",
                            foundation_files.len()
                        ),
                        false,
                    ))
                }
                _ => Err(StateRefusal::GuardFailed {
                    guard: "G1".into(),
                    reason: format!(
                        "campaign `{id}` transition `{from_state}` -> `{to_state}` requires `WholeRead` evidence"
                    ),
                }),
            },
            Some("G2") => match evidence {
                CampaignGuardEvidence::Briefed { judge_path, note } => {
                    let gate = Gate::load_from_path(judge_path).map_err(|e| {
                        StateRefusal::GuardFailed {
                            guard: "G2".into(),
                            reason: format!(
                                "G2 failed to load judge `{}`: {e:#}",
                                judge_path.display()
                            ),
                        }
                    })?;
                    check_well_formed(&gate).map_err(|e| StateRefusal::GuardFailed {
                        guard: "G2".into(),
                        reason: format!("G2 active judge `{}` is not WellFormed: {e}", gate.name),
                    })?;
                    Ok((
                        format!("G2 verified WellFormed judge `{}` ({note})", gate.name),
                        false,
                    ))
                }
                _ => Err(StateRefusal::GuardFailed {
                    guard: "G2".into(),
                    reason: format!(
                        "campaign `{id}` transition `{from_state}` -> `{to_state}` requires `Briefed` evidence with WellFormed `judge.json`"
                    ),
                }),
            },
            Some("G3") => match evidence {
                CampaignGuardEvidence::RegroundTrigger { trigger }
                    if !trigger.trim().is_empty() =>
                {
                    Ok((format!("G3 trigger: {trigger}"), false))
                }
                _ => Err(StateRefusal::GuardFailed {
                    guard: "G3".into(),
                    reason: "G3 requires non-empty `RegroundTrigger`".into(),
                }),
            },
            Some("G4") => match evidence {
                CampaignGuardEvidence::JudgeSuccession { record }
                    if !record.old_name.is_empty() && !record.new_name.is_empty() =>
                {
                    Ok((
                        format!("G4 succession `{} -> {}`", record.old_name, record.new_name),
                        false,
                    ))
                }
                _ => Err(StateRefusal::GuardFailed {
                    guard: "G4".into(),
                    reason: "G4 requires verified `JudgeSuccession` record".into(),
                }),
            },
            Some(other) => Err(StateRefusal::GuardFailed {
                guard: other.to_string(),
                reason: format!("unrecognized campaign guard `{other}`"),
            }),
        }
    }

    pub fn create_quest(
        &self,
        id: &str,
        campaign_id: &str,
        title: &str,
        holder_agent: &str,
        target_regime: &str,
    ) -> Result<QuestRow> {
        let norm_target = target_regime.trim().to_ascii_lowercase();
        if !matches!(norm_target.as_str(), "decided" | "certified" | "attested") {
            bail!(
                "invalid target_regime `{target_regime}` (expected `decided`, `certified`, or `attested`)"
            );
        }
        let now = Utc::now().to_rfc3339();
        let initial = self.spec.machines.quest.initial.clone();
        let mut conn = self.conn()?;
        let tx = conn.transaction()?;
        tx.execute(
            "INSERT OR REPLACE INTO quests
             (id, campaign_id, title, state, is_sink, prior_state, holder_agent, target_regime,
              effective_regime, merged_ungated, origin, footprint_json, base_sha, proposed_head_sha,
              landed_sha, verified_receipt_hash, tooth_witness, updated_at)
             VALUES (?1, ?2, ?3, ?4, 0, NULL, ?5, ?6, 'attested', 0, ?7, '[]', NULL, NULL, NULL, NULL, NULL, ?8)",
            params![
                id,
                campaign_id,
                title,
                initial,
                holder_agent,
                norm_target,
                ORIGIN_LIVE,
                now
            ],
        )?;
        let row = QuestRow {
            id: id.to_string(),
            campaign_id: campaign_id.to_string(),
            title: title.to_string(),
            state: initial.clone(),
            is_sink: false,
            prior_state: None,
            holder_agent: holder_agent.to_string(),
            target_regime: norm_target.clone(),
            effective_regime: "attested".to_string(),
            merged_ungated: false,
            origin: ORIGIN_LIVE.to_string(),
            footprint_lease: Vec::new(),
            base_sha: None,
            proposed_head_sha: None,
            landed_sha: None,
            verified_receipt_hash: None,
            tooth_witness: None,
            updated_at: now,
        };
        self.append_ledger(
            "quest.created",
            id,
            &format!("Quest `{id}` ({title}) created in `{initial}` [target_regime={norm_target}]"),
            serde_json::to_value(&row)?,
        )?;
        tx.commit()?;
        Ok(row)
    }

    pub fn get_quest(&self, id: &str) -> Result<Option<QuestRow>> {
        let conn = self.conn()?;
        Self::load_quest_in_conn(&conn, id)
    }

    fn load_quest_in_conn(conn: &Connection, id: &str) -> Result<Option<QuestRow>> {
        conn.query_row(
            "SELECT id, campaign_id, title, state, is_sink, prior_state, holder_agent, target_regime,
                    effective_regime, merged_ungated, origin, footprint_json, base_sha,
                    proposed_head_sha, landed_sha, verified_receipt_hash, tooth_witness, updated_at
             FROM quests WHERE id = ?1",
            params![id],
            Self::map_quest_row,
        )
        .optional()
        .map_err(Into::into)
    }

    fn map_quest_row(r: &rusqlite::Row<'_>) -> rusqlite::Result<QuestRow> {
        let fp_raw: String = r.get(11)?;
        let footprint_lease: Vec<String> = serde_json::from_str(&fp_raw).unwrap_or_default();
        Ok(QuestRow {
            id: r.get(0)?,
            campaign_id: r.get(1)?,
            title: r.get(2)?,
            state: r.get(3)?,
            is_sink: r.get::<_, i64>(4)? != 0,
            prior_state: r.get(5)?,
            holder_agent: r.get(6)?,
            target_regime: r.get(7)?,
            effective_regime: r.get(8)?,
            merged_ungated: r.get::<_, i64>(9)? != 0,
            origin: r.get(10)?,
            footprint_lease,
            base_sha: r.get(12)?,
            proposed_head_sha: r.get(13)?,
            landed_sha: r.get(14)?,
            verified_receipt_hash: r.get(15)?,
            tooth_witness: r.get(16)?,
            updated_at: r.get(17)?,
        })
    }

    fn upsert_quest_in_tx(
        tx: &rusqlite::Transaction<'_>,
        q: &QuestRow,
    ) -> std::result::Result<(), StateRefusal> {
        let fp_json =
            serde_json::to_string(&q.footprint_lease).unwrap_or_else(|_| "[]".to_string());
        tx.execute(
            "INSERT OR REPLACE INTO quests
             (id, campaign_id, title, state, is_sink, prior_state, holder_agent, target_regime,
              effective_regime, merged_ungated, origin, footprint_json, base_sha, proposed_head_sha,
              landed_sha, verified_receipt_hash, tooth_witness, updated_at)
             VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16, ?17, ?18)",
            params![
                q.id,
                q.campaign_id,
                q.title,
                q.state,
                q.is_sink as i64,
                q.prior_state,
                q.holder_agent,
                q.target_regime,
                q.effective_regime,
                q.merged_ungated as i64,
                q.origin,
                fp_json,
                q.base_sha,
                q.proposed_head_sha,
                q.landed_sha,
                q.verified_receipt_hash,
                q.tooth_witness,
                q.updated_at,
            ],
        )
        .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Ok(())
    }

    fn check_footprint_lease_conflicts(
        tx: &rusqlite::Transaction<'_>,
        quest_id: &str,
        campaign_id: &str,
        requested_paths: &[String],
    ) -> std::result::Result<(), StateRefusal> {
        let mut stmt = tx
            .prepare(
                "SELECT id, footprint_json FROM quests
                 WHERE campaign_id = ?1 AND id != ?2
                   AND state NOT IN ('Landed', 'Claimed', 'Recorded')
                   AND origin = 'live'",
            )
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        let active_others: Vec<(String, Vec<String>)> = stmt
            .query_map(params![campaign_id, quest_id], |r| {
                let other_id: String = r.get(0)?;
                let fp_raw: String = r.get(1)?;
                let fp: Vec<String> = serde_json::from_str(&fp_raw).unwrap_or_default();
                Ok((other_id, fp))
            })
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?
            .collect::<std::result::Result<Vec<_>, _>>()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;

        for req in requested_paths {
            for (other_id, other_fp) in &active_others {
                for existing in other_fp {
                    if footprint_entries_overlap(req, existing) {
                        return Err(StateRefusal::FootprintLeaseConflict {
                            quest_id: quest_id.to_string(),
                            requested: req.clone(),
                            conflicting_quest: other_id.clone(),
                            conflicting_entry: existing.clone(),
                        });
                    }
                }
            }
        }
        Ok(())
    }

    /// Verify a `JudgeReceipt` against live git state, trunk SHA freshness, `#tooth` execution,
    /// footprint lease, and `target_regime`.
    fn verify_candidate_receipt(
        q: &QuestRow,
        guard_name: &str,
        receipt: &JudgeReceipt,
        repo_root: &Path,
        trunk_branch: &str,
        allow_already_fast_forwarded: bool,
    ) -> std::result::Result<Vec<String>, StateRefusal> {
        receipt
            .verify_integrity()
            .map_err(|e| StateRefusal::TamperedReceipt {
                quest_id: q.id.clone(),
                reason: format!("{e:#}"),
            })?;

        if !receipt.all_passed {
            let failed_cells: Vec<String> = receipt
                .evaluations
                .iter()
                .filter(|ev| !ev.passed)
                .map(|ev| format!("{} ({})", ev.cell, ev.detail))
                .collect();
            return Err(StateRefusal::GuardFailed {
                guard: guard_name.into(),
                reason: format!(
                    "JudgeReceipt `{}` did not pass all floors: {}",
                    receipt.judge_name,
                    failed_cells.join("; ")
                ),
            });
        }

        if !receipt.clean_working_tree {
            return Err(StateRefusal::GuardFailed {
                guard: guard_name.into(),
                reason: "JudgeReceipt was issued on a dirty working tree".into(),
            });
        }

        if receipt.teeth_report.total == 0 || !receipt.teeth_report.all_bit {
            return Err(StateRefusal::GuardFailed {
                guard: guard_name.into(),
                reason: format!(
                    "quest `{}` requires executed red `#tooth` (`BIT`), got total={}, bit={}, vacuous={}, invalid={}",
                    q.id,
                    receipt.teeth_report.total,
                    receipt.teeth_report.bit_count,
                    receipt.teeth_report.vacuous_count,
                    receipt.teeth_report.invalid_count
                ),
            });
        }

        if !regime_satisfies_target(receipt.achieved_regime, &q.target_regime) {
            return Err(StateRefusal::GuardFailed {
                guard: guard_name.into(),
                reason: format!(
                    "quest `{}` targets regime `{}`, receipt only achieved `{}`",
                    q.id, q.target_regime, receipt.achieved_regime
                ),
            });
        }

        let live_trunk_sha = run_git_ro(
            repo_root,
            &[
                "rev-parse",
                "--verify",
                &format!("{trunk_branch}^{{commit}}"),
            ],
        )
        .map_err(|e| StateRefusal::GuardFailed {
            guard: guard_name.into(),
            reason: format!(
                "failed to resolve trunk `{trunk_branch}` in `{}`: {e:#}",
                repo_root.display()
            ),
        })?
        .trim()
        .to_string();

        let trunk_matches_base = live_trunk_sha == receipt.base_sha;
        let trunk_already_at_head =
            allow_already_fast_forwarded && live_trunk_sha == receipt.head_sha;
        if !trunk_matches_base && !trunk_already_at_head {
            return Err(StateRefusal::StaleBaseSha {
                quest_id: q.id.clone(),
                trunk_branch: trunk_branch.to_string(),
                receipt_base_sha: receipt.base_sha.clone(),
                current_trunk_sha: live_trunk_sha,
            });
        }

        // Verify `receipt.head_sha` and `receipt.tree_oid` exist in `repo_root` and match!
        let actual_tree_oid = run_git_ro(
            repo_root,
            &[
                "rev-parse",
                "--verify",
                &format!("{}^{{tree}}", receipt.head_sha),
            ],
        )
        .map_err(|e| StateRefusal::GuardFailed {
            guard: guard_name.into(),
            reason: format!(
                "candidate commit `{}` not found in `{}`: {e:#}",
                receipt.head_sha,
                repo_root.display()
            ),
        })?
        .trim()
        .to_string();

        if actual_tree_oid != receipt.tree_oid {
            return Err(StateRefusal::TamperedReceipt {
                quest_id: q.id.clone(),
                reason: format!(
                    "commit `{}` tree OID is `{}`, receipt claimed `{}`",
                    receipt.head_sha, actual_tree_oid, receipt.tree_oid
                ),
            });
        }

        if !allow_already_fast_forwarded {
            let live_head_sha = run_git_ro(repo_root, &["rev-parse", "--verify", "HEAD^{commit}"])
                .map_err(|e| StateRefusal::GuardFailed {
                    guard: guard_name.into(),
                    reason: format!("failed to read HEAD in `{}`: {e:#}", repo_root.display()),
                })?
                .trim()
                .to_string();
            if live_head_sha != receipt.head_sha {
                return Err(StateRefusal::GuardFailed {
                    guard: guard_name.into(),
                    reason: format!(
                        "live repo HEAD `{live_head_sha}` != receipt `head_sha` `{}`",
                        receipt.head_sha
                    ),
                });
            }
        }

        // Verify `receipt.base_sha` is an ancestor of `receipt.head_sha` (fast-forwardable) and non-empty
        if receipt.base_sha == receipt.head_sha {
            return Err(StateRefusal::GuardFailed {
                guard: guard_name.into(),
                reason: format!(
                    "empty candidate range (`base_sha == head_sha == {}`): no candidate commit committed",
                    receipt.head_sha
                ),
            });
        }
        let mut anc_cmd = Command::new("git");
        configure_hermetic_git(&mut anc_cmd)
            .args(["--no-optional-locks", "-C"])
            .arg(repo_root)
            .args([
                "merge-base",
                "--is-ancestor",
                &receipt.base_sha,
                &receipt.head_sha,
            ]);
        let is_anc = anc_cmd
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false);
        if !is_anc {
            return Err(StateRefusal::StaleBaseSha {
                quest_id: q.id.clone(),
                trunk_branch: trunk_branch.to_string(),
                receipt_base_sha: receipt.base_sha.clone(),
                current_trunk_sha: live_trunk_sha,
            });
        }

        // Compute the live git diff `base_sha..head_sha`; callers decide what the lease means for it
        let diff_raw = run_git_ro(
            repo_root,
            &["diff", "--name-only", &receipt.base_sha, &receipt.head_sha],
        )
        .map_err(|e| StateRefusal::GuardFailed {
            guard: guard_name.into(),
            reason: format!("git diff failed: {e:#}"),
        })?;
        let changed_paths: Vec<String> = diff_raw
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .map(str::to_string)
            .collect();

        if changed_paths.is_empty() {
            return Err(StateRefusal::GuardFailed {
                guard: guard_name.into(),
                reason: "candidate commit touches 0 files relative to `base_sha`".into(),
            });
        }

        Ok(changed_paths)
    }

    /// Changed paths that fall outside the quest's footprint lease.
    fn paths_outside_lease(q: &QuestRow, changed_paths: &[String]) -> Vec<String> {
        if q.footprint_lease.is_empty() {
            return Vec::new();
        }
        changed_paths
            .iter()
            .filter(|p| !path_within_footprint(p, &q.footprint_lease))
            .cloned()
            .collect()
    }

    /// A lease only grows through `propose_quest`, where the new paths are checked against
    /// sibling leases. Any other receipt-bearing transition must stay inside the current lease.
    fn enforce_lease(
        q: &QuestRow,
        changed_paths: &[String],
    ) -> std::result::Result<(), StateRefusal> {
        let violating = Self::paths_outside_lease(q, changed_paths);
        if violating.is_empty() {
            return Ok(());
        }
        Err(StateRefusal::FootprintViolation {
            quest_id: q.id.clone(),
            violating_paths: violating,
            allowed_footprint: q.footprint_lease.clone(),
        })
    }

    /// The lease is a contention detector, not an edit ceiling: a candidate that had to touch a
    /// path nobody else holds (a shared type, a helper) gets that path added to its lease and the
    /// expansion is recorded for convergence review. Only an overlap with another active quest's
    /// lease is refused (`FootprintLeaseConflict`).
    fn extend_footprint_lease(
        &self,
        quest_id: &str,
        outside: &[String],
        head_sha: &str,
    ) -> std::result::Result<QuestRow, StateRefusal> {
        let mut conn = self
            .conn()
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?;
        let tx = conn
            .transaction()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        let mut q = Self::load_quest_in_conn(&tx, quest_id)
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?
            .ok_or_else(|| StateRefusal::IllegalTransition {
                machine: "quest".into(),
                id: quest_id.into(),
                from: "<missing>".into(),
                to: "Toothed".into(),
            })?;
        Self::check_footprint_lease_conflicts(&tx, quest_id, &q.campaign_id, outside)?;
        let declared = q.footprint_lease.clone();
        for path in outside {
            if !q.footprint_lease.contains(path) {
                q.footprint_lease.push(path.clone());
            }
        }
        q.updated_at = Utc::now().to_rfc3339();
        Self::upsert_quest_in_tx(&tx, &q)?;
        self.append_ledger_or_refuse(
            "quest.footprint_extended",
            quest_id,
            &format!(
                "Quest `{quest_id}` candidate touched {} path(s) outside its declared footprint; lease extended",
                outside.len()
            ),
            serde_json::json!({
                "origin": q.origin,
                "head_sha": head_sha,
                "declared_footprint": declared,
                "out_of_declared_footprint": outside,
            }),
        )?;
        tx.commit()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Ok(q)
    }

    pub fn transition_quest(
        &self,
        id: &str,
        to_state: &str,
        actor: &str,
        tooth_witness: Option<&str>,
        evidence: QuestGuardEvidence,
    ) -> std::result::Result<QuestRow, StateRefusal> {
        let mut conn = self
            .conn()
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?;
        let tx = conn
            .transaction()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        let cur = Self::load_quest_in_conn(&tx, id)
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?;

        let Some(mut q) = cur else {
            return Err(StateRefusal::IllegalTransition {
                machine: "quest".into(),
                id: id.into(),
                from: "<missing>".into(),
                to: to_state.into(),
            });
        };

        let now = Utc::now().to_rfc3339();
        let entering_sink = self.spec.machines.quest.sinks.iter().any(|s| s == to_state);

        // Case 1: Entering one of the 18 frustration sinks (always recorded unconditionally if edge exists)
        if entering_sink {
            if !self.spec.can_quest_enter_sink(&q.state, to_state) {
                return Err(StateRefusal::IllegalTransition {
                    machine: "quest".into(),
                    id: id.into(),
                    from: q.state,
                    to: to_state.into(),
                });
            }
            let sink_reason = match &evidence {
                QuestGuardEvidence::EnterSink { reason } => reason.clone(),
                _ => "sink detector triggered".to_string(),
            };
            let prior = if q.is_sink {
                q.prior_state.clone()
            } else {
                Some(q.state.clone())
            };
            q.state = to_state.to_string();
            q.is_sink = true;
            q.prior_state = prior;
            q.updated_at = now;
            Self::upsert_quest_in_tx(&tx, &q)?;
            self.append_ledger_or_refuse(
                "quest.sink_entered",
                id,
                &format!("Quest `{id}` entered sink `{to_state}` ({sink_reason})"),
                serde_json::to_value(&q).unwrap_or_default(),
            )?;
            tx.commit()
                .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
            return Ok(q);
        }

        // Case 2: Exiting a sink (`sink_exit_rule`: holder agent must execute the sink's remedial action)
        if q.is_sink {
            let required_exit = self
                .spec
                .sinks
                .get(&q.state)
                .map(|s| s.exit.clone())
                .unwrap_or_else(|| "remediate".to_string());
            let act = match &evidence {
                QuestGuardEvidence::ExitSink { remedial_action } => remedial_action.as_str(),
                _ => "",
            };
            if actor != q.holder_agent || act.trim().is_empty() {
                return Err(StateRefusal::SinkExitViolation {
                    id: id.into(),
                    sink: q.state.into(),
                    required_exit: required_exit.into(),
                    holder: q.holder_agent.into(),
                    actor: actor.into(),
                    action: act.into(),
                });
            }
            let valid_target = self
                .spec
                .machines
                .quest
                .states
                .iter()
                .any(|s| s == to_state);
            if !valid_target {
                return Err(StateRefusal::IllegalTransition {
                    machine: "quest".into(),
                    id: id.into(),
                    from: q.state,
                    to: to_state.into(),
                });
            }
            let from_sink = q.state.clone();
            q.state = to_state.to_string();
            q.is_sink = false;
            q.prior_state = None;
            q.updated_at = now;
            Self::upsert_quest_in_tx(&tx, &q)?;
            self.append_ledger_or_refuse(
                "quest.sink_exited",
                id,
                &format!("Quest `{id}` exited sink `{from_sink}` to `{to_state}` via `{act}` by `{actor}`"),
                serde_json::json!({
                    "from": from_sink,
                    "to": to_state,
                    "actor": actor,
                    "origin": q.origin,
                    "remedial_action": act,
                }),
            )?;
            tx.commit()
                .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
            return Ok(q);
        }

        // Case 3: Normal forward progression (`Grounded -> Scoped -> Built -> Wired -> Toothed -> Landed -> Claimed -> Recorded`)
        let Some(tr) = self.spec.find_quest_transition(&q.state, to_state) else {
            return Err(StateRefusal::IllegalTransition {
                machine: "quest".into(),
                id: id.into(),
                from: q.state,
                to: to_state.into(),
            });
        };

        let guard_name = tr.guard.as_deref().unwrap_or("");
        let from_state = q.state.clone();

        // Explicit emergency operator override (`obend-swarm` Finding 14):
        // Note: `Claimed` and `Recorded` are certification sinks and CANNOT be reached via ungated override!
        if let QuestGuardEvidence::AttestedOverride {
            operator,
            reason,
            head_sha,
        } = &evidence
        {
            if matches!(to_state, "Claimed" | "Recorded") {
                return Err(StateRefusal::GuardFailed {
                    guard: guard_name.into(),
                    reason: format!(
                        "quest `{id}` cannot enter `{to_state}` via `AttestedOverride`: ungated emergency bypasses record reality up to `Landed` without certifying `Claimed`/`Recorded`"
                    ),
                });
            }
            if operator.trim().is_empty() || reason.trim().is_empty() {
                return Err(StateRefusal::GuardFailed {
                    guard: guard_name.into(),
                    reason: "AttestedOverride requires non-empty `operator` and `reason`".into(),
                });
            }
            q.state = to_state.to_string();
            q.merged_ungated = true;
            q.effective_regime = REGIME_ATTESTED_OVERRIDE.to_string();
            if to_state == "Landed" {
                q.landed_sha = head_sha.clone().or_else(|| q.proposed_head_sha.clone());
            }
            if let Some(tw) = tooth_witness {
                q.tooth_witness = Some(tw.to_string());
            }
            q.updated_at = now;
            Self::upsert_quest_in_tx(&tx, &q)?;
            self.append_ledger_or_refuse(
                "quest.override_transition",
                id,
                &format!(
                    "Quest `{id}` OVERRIDE `{from_state}` -> `{to_state}` by `{operator}` [regime=AttestedOverride, merged_ungated=true]: {reason}"
                ),
                serde_json::json!({
                    "from": from_state,
                    "to": to_state,
                    "operator": operator,
                    "override_reason": reason,
                    "regime": REGIME_ATTESTED_OVERRIDE,
                    "merged_ungated": true,
                    "quest": q,
                }),
            )?;
            tx.commit()
                .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
            return Ok(q);
        }

        // Non-override authoritative guard evaluation
        match guard_name {
            "Q1" => match &evidence {
                QuestGuardEvidence::ScopeBrief {
                    deliverable,
                    footprint_paths,
                    estimated_swarm_hours,
                    base_sha,
                } => {
                    if deliverable.trim().is_empty() {
                        return Err(StateRefusal::GuardFailed {
                            guard: "Q1".into(),
                            reason: "Q1 requires a non-empty deliverable statement".into(),
                        });
                    }
                    if !estimated_swarm_hours.is_finite() || *estimated_swarm_hours <= 0.0 {
                        return Err(StateRefusal::GuardFailed {
                            guard: "Q1".into(),
                            reason: "Q1 requires positive finite `estimated_swarm_hours`".into(),
                        });
                    }
                    if footprint_paths.is_empty() {
                        return Err(StateRefusal::GuardFailed {
                            guard: "Q1".into(),
                            reason: "Q1 requires a non-empty `footprint_paths` lease".into(),
                        });
                    }
                    let normalized: Vec<String> = footprint_paths
                        .iter()
                        .map(|p| normalize_footprint_entry(p))
                        .collect();
                    Self::check_footprint_lease_conflicts(&tx, id, &q.campaign_id, &normalized)?;
                    q.footprint_lease = normalized;
                    if let Some(b) = base_sha {
                        q.base_sha = Some(b.clone());
                    }
                    q.holder_agent = actor.to_string();
                }
                _ => {
                    return Err(StateRefusal::GuardFailed {
                        guard: "Q1".into(),
                        reason: format!(
                            "quest `{id}` transition `Grounded -> Scoped` requires `ScopeBrief` evidence"
                        ),
                    });
                }
            },
            "Q2" | "Q3" => match &evidence {
                QuestGuardEvidence::RepoCheck {
                    repo_root,
                    artifacts,
                } => {
                    if artifacts.is_empty() {
                        return Err(StateRefusal::GuardFailed {
                            guard: guard_name.into(),
                            reason: format!(
                                "{guard_name} requires at least one real artifact path"
                            ),
                        });
                    }
                    let mut violating = Vec::new();
                    for rel in artifacts {
                        let p = repo_root.join(rel);
                        if !p.exists() {
                            return Err(StateRefusal::GuardFailed {
                                guard: guard_name.into(),
                                reason: format!(
                                    "{guard_name} artifact `{rel}` does not exist under `{}`",
                                    repo_root.display()
                                ),
                            });
                        }
                        if !q.footprint_lease.is_empty()
                            && !path_within_footprint(rel, &q.footprint_lease)
                        {
                            violating.push(rel.clone());
                        }
                    }
                    if !violating.is_empty() {
                        return Err(StateRefusal::FootprintViolation {
                            quest_id: q.id.clone(),
                            violating_paths: violating,
                            allowed_footprint: q.footprint_lease.clone(),
                        });
                    }
                    let lint =
                        run_repo_lints(repo_root).map_err(|e| StateRefusal::GuardFailed {
                            guard: guard_name.into(),
                            reason: format!("{guard_name} repo lint failed: {e:#}"),
                        })?;
                    let target_sink = if guard_name == "Q2" {
                        Sink::Theater
                    } else {
                        Sink::Mirror
                    };
                    let sink_hits: Vec<String> = lint
                        .findings
                        .iter()
                        .filter(|f| f.sink == Some(target_sink))
                        .map(|f| format!("{}:{} ({})", f.path, f.line, f.rule_id))
                        .collect();
                    if !sink_hits.is_empty() {
                        return Err(StateRefusal::GuardFailed {
                            guard: guard_name.into(),
                            reason: format!(
                                "{guard_name} detected {:?} violation(s): {}",
                                target_sink,
                                sink_hits.join(", ")
                            ),
                        });
                    }
                }
                _ => {
                    return Err(StateRefusal::GuardFailed {
                        guard: guard_name.into(),
                        reason: format!(
                            "quest `{id}` transition `{from_state} -> {to_state}` requires `RepoCheck` evidence"
                        ),
                    });
                }
            },
            "Q4" => match &evidence {
                QuestGuardEvidence::Receipt {
                    receipt,
                    repo_root,
                    trunk_branch,
                } => {
                    let changed = Self::verify_candidate_receipt(
                        &q,
                        "Q4",
                        receipt,
                        repo_root,
                        trunk_branch,
                        false,
                    )?;
                    Self::enforce_lease(&q, &changed)?;
                    let first_tooth = receipt
                        .teeth_report
                        .results
                        .first()
                        .map(|t| t.id.clone())
                        .unwrap_or_else(|| "executed-tooth".to_string());
                    q.tooth_witness = tooth_witness
                        .map(str::to_string)
                        .or_else(|| q.tooth_witness.clone())
                        .or(Some(first_tooth));
                    q.base_sha = Some(receipt.base_sha.clone());
                    q.proposed_head_sha = Some(receipt.head_sha.clone());
                    q.verified_receipt_hash = Some(receipt.receipt_hash.clone());
                }
                _ => {
                    return Err(StateRefusal::GuardFailed {
                        guard: "Q4".into(),
                        reason: format!(
                            "quest `{id}` transition `Wired -> Toothed` requires a verified `JudgeReceipt` with executed red `#tooth`"
                        ),
                    });
                }
            },
            "Q5" => match &evidence {
                QuestGuardEvidence::Receipt {
                    receipt,
                    repo_root,
                    trunk_branch,
                } => {
                    if q.merged_ungated {
                        return Err(StateRefusal::GuardFailed {
                            guard: "Q5".into(),
                            reason: format!(
                                "quest `{id}` carries `merged_ungated = true` from a prior override and cannot certify Q5"
                            ),
                        });
                    }
                    let changed = Self::verify_candidate_receipt(
                        &q,
                        "Q5",
                        receipt,
                        repo_root,
                        trunk_branch,
                        true,
                    )?;
                    Self::enforce_lease(&q, &changed)?;
                    // Verify trunk is now fast-forwarded to `receipt.head_sha` and `probe_git_q5` passes!
                    let live_trunk_sha = run_git_ro(
                        repo_root,
                        &[
                            "rev-parse",
                            "--verify",
                            &format!("{trunk_branch}^{{commit}}"),
                        ],
                    )
                    .map_err(|e| StateRefusal::GuardFailed {
                        guard: "Q5".into(),
                        reason: format!("failed to read `{trunk_branch}` SHA: {e:#}"),
                    })?
                    .trim()
                    .to_string();
                    if live_trunk_sha != receipt.head_sha {
                        return Err(StateRefusal::GuardFailed {
                            guard: "Q5".into(),
                            reason: format!(
                                "Q5 requires `{trunk_branch}` fast-forwarded to `{}` (currently `{live_trunk_sha}`); use `land_quest`",
                                receipt.head_sha
                            ),
                        });
                    }
                    let q5 =
                        Self::probe_git_q5(repo_root).map_err(|e| StateRefusal::GuardFailed {
                            guard: "Q5".into(),
                            reason: format!("probe_git_q5 failed: {e:#}"),
                        })?;
                    if !q5.q5_passed {
                        return Err(StateRefusal::GuardFailed {
                            guard: "Q5".into(),
                            reason: format!(
                                "Q5 git cleanliness failed: clean_working_tree={}, stash_count={}, merged_side_branches={:?}",
                                q5.clean_working_tree, q5.stash_count, q5.merged_side_branches
                            ),
                        });
                    }
                    q.landed_sha = Some(receipt.head_sha.clone());
                    q.verified_receipt_hash = Some(receipt.receipt_hash.clone());
                    q.effective_regime = receipt.achieved_regime.as_str().to_string();
                }
                _ => {
                    return Err(StateRefusal::GuardFailed {
                        guard: "Q5".into(),
                        reason: format!(
                            "quest `{id}` transition `Toothed -> Landed` requires a verified `JudgeReceipt`"
                        ),
                    });
                }
            },
            "Q6" => match &evidence {
                QuestGuardEvidence::Receipt {
                    receipt,
                    repo_root,
                    trunk_branch,
                } => {
                    if q.merged_ungated
                        || q.effective_regime == REGIME_ATTESTED_OVERRIDE
                        || q.origin == ORIGIN_DEMO_SEED
                    {
                        return Err(StateRefusal::GuardFailed {
                            guard: "Q6".into(),
                            reason: format!(
                                "quest `{id}` (`effective_regime={}`, `merged_ungated={}`, `origin={}`) cannot enter `Claimed`",
                                q.effective_regime, q.merged_ungated, q.origin
                            ),
                        });
                    }
                    let changed = Self::verify_candidate_receipt(
                        &q,
                        "Q6",
                        receipt,
                        repo_root,
                        trunk_branch,
                        true,
                    )?;
                    Self::enforce_lease(&q, &changed)?;
                    if let Some(ref landed) = q.landed_sha
                        && landed != &receipt.head_sha
                    {
                        return Err(StateRefusal::GuardFailed {
                            guard: "Q6".into(),
                            reason: format!(
                                "receipt `head_sha` `{}` does not match landed SHA `{landed}`",
                                receipt.head_sha
                            ),
                        });
                    }
                    let lint =
                        run_repo_lints(repo_root).map_err(|e| StateRefusal::GuardFailed {
                            guard: "Q6".into(),
                            reason: format!("Q6 lint failed: {e:#}"),
                        })?;
                    let label_hits: Vec<String> = lint
                        .findings
                        .iter()
                        .filter(|f| f.sink == Some(Sink::Label))
                        .map(|f| format!("{}:{} ({})", f.path, f.line, f.rule_id))
                        .collect();
                    if !label_hits.is_empty() {
                        return Err(StateRefusal::GuardFailed {
                            guard: "Q6".into(),
                            reason: format!("Q6 Label findings remain: {}", label_hits.join(", ")),
                        });
                    }
                    q.effective_regime = receipt.achieved_regime.as_str().to_string();
                }
                _ => {
                    return Err(StateRefusal::GuardFailed {
                        guard: "Q6".into(),
                        reason: format!(
                            "quest `{id}` transition `Landed -> Claimed` requires a verified `JudgeReceipt`"
                        ),
                    });
                }
            },
            "Q7" => match &evidence {
                QuestGuardEvidence::RecordCheck { repo_root, summary } => {
                    if q.merged_ungated
                        || q.effective_regime == REGIME_ATTESTED_OVERRIDE
                        || q.origin == ORIGIN_DEMO_SEED
                    {
                        return Err(StateRefusal::GuardFailed {
                            guard: "Q7".into(),
                            reason: format!(
                                "quest `{id}` (`merged_ungated={}`) cannot be `Recorded` as verified",
                                q.merged_ungated
                            ),
                        });
                    }
                    if summary.trim().is_empty() {
                        return Err(StateRefusal::GuardFailed {
                            guard: "Q7".into(),
                            reason: "Q7 requires a non-empty ledger distillation summary".into(),
                        });
                    }
                    self.verify_ledger_chain()
                        .map_err(|e| StateRefusal::GuardFailed {
                            guard: "Q7".into(),
                            reason: format!("Q7 ledger hash chain verification failed: {e:#}"),
                        })?;
                    let lint =
                        run_repo_lints(repo_root).map_err(|e| StateRefusal::GuardFailed {
                            guard: "Q7".into(),
                            reason: format!("Q7 markdown/navel lint failed: {e:#}"),
                        })?;
                    let doc_errors: Vec<String> = lint
                        .findings
                        .iter()
                        .filter(|f| f.rule_id.starts_with("markdown/"))
                        .map(|f| format!("{}:{} ({})", f.path, f.line, f.rule_id))
                        .collect();
                    if !doc_errors.is_empty() {
                        return Err(StateRefusal::GuardFailed {
                            guard: "Q7".into(),
                            reason: format!("Q7 doc/navel findings: {}", doc_errors.join(", ")),
                        });
                    }
                }
                _ => {
                    return Err(StateRefusal::GuardFailed {
                        guard: "Q7".into(),
                        reason: format!(
                            "quest `{id}` transition `Claimed -> Recorded` requires `RecordCheck` evidence"
                        ),
                    });
                }
            },
            other => {
                return Err(StateRefusal::GuardFailed {
                    guard: other.to_string(),
                    reason: format!("unrecognized quest guard `{other}`"),
                });
            }
        }

        if let Some(tw) = tooth_witness {
            q.tooth_witness = Some(tw.to_string());
        }
        q.state = to_state.to_string();
        q.updated_at = now;
        Self::upsert_quest_in_tx(&tx, &q)?;

        self.append_ledger_or_refuse(
            "quest.transition",
            id,
            &format!(
                "Quest `{id}` moved `{from_state}` -> `{to_state}` [regime={}]",
                q.effective_regime
            ),
            serde_json::to_value(&q).unwrap_or_default(),
        )?;
        tx.commit()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Ok(q)
    }

    // -------------------------------------------------------------------------
    // Composite Authoritative Quest Verbs (`take`, `propose`, `land`, `land_ungated`)
    // -------------------------------------------------------------------------

    /// Take a `Grounded` quest with an exclusive non-overlapping footprint lease pinned to `trunk_branch`.
    #[allow(clippy::too_many_arguments)]
    pub fn take_quest(
        &self,
        quest_id: &str,
        actor: &str,
        deliverable: &str,
        footprint_paths: Vec<String>,
        estimated_swarm_hours: f64,
        repo_root: &Path,
        trunk_branch: &str,
    ) -> std::result::Result<QuestRow, StateRefusal> {
        let base_sha = run_git_ro(
            repo_root,
            &[
                "rev-parse",
                "--verify",
                &format!("{trunk_branch}^{{commit}}"),
            ],
        )
        .map_err(|e| StateRefusal::GuardFailed {
            guard: "Q1".into(),
            reason: format!(
                "failed to resolve trunk `{trunk_branch}` in `{}`: {e:#}",
                repo_root.display()
            ),
        })?
        .trim()
        .to_string();

        self.transition_quest(
            quest_id,
            "Scoped",
            actor,
            None,
            QuestGuardEvidence::ScopeBrief {
                deliverable: deliverable.to_string(),
                footprint_paths,
                estimated_swarm_hours,
                base_sha: Some(base_sha),
            },
        )
    }

    /// Propose a committed candidate with a SHA-bound `JudgeReceipt`, verifying executed `#tooth`,
    /// footprint lease, and trunk `base_sha` freshness, advancing the quest to `Toothed`.
    pub fn propose_quest(
        &self,
        quest_id: &str,
        actor: &str,
        receipt: &JudgeReceipt,
        repo_root: &Path,
        trunk_branch: &str,
    ) -> std::result::Result<QuestRow, StateRefusal> {
        let cur = self
            .get_quest(quest_id)
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?
            .ok_or_else(|| StateRefusal::IllegalTransition {
                machine: "quest".into(),
                id: quest_id.into(),
                from: "<missing>".into(),
                to: "Toothed".into(),
            })?;

        if actor != cur.holder_agent {
            return Err(StateRefusal::GuardFailed {
                guard: "Q4".into(),
                reason: format!(
                    "actor `{actor}` does not hold quest `{quest_id}` (holder is `{}`)",
                    cur.holder_agent
                ),
            });
        }

        // Pre-verify full candidate receipt BEFORE advancing intermediate states (`Built`, `Wired`)
        let changed_paths =
            Self::verify_candidate_receipt(&cur, "Q4", receipt, repo_root, trunk_branch, false)?;
        let outside = Self::paths_outside_lease(&cur, &changed_paths);
        let cur = if outside.is_empty() {
            cur
        } else {
            self.extend_footprint_lease(quest_id, &outside, &receipt.head_sha)?
        };

        // Re-proposing when already `Toothed` (e.g. after rebasing onto an advanced trunk) updates
        // `(base_sha, proposed_head_sha, verified_receipt_hash)` atomically.
        if cur.state == "Toothed" {
            let mut conn = self
                .conn()
                .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?;
            let tx = conn
                .transaction()
                .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
            let mut updated = cur;
            updated.base_sha = Some(receipt.base_sha.clone());
            updated.proposed_head_sha = Some(receipt.head_sha.clone());
            updated.verified_receipt_hash = Some(receipt.receipt_hash.clone());
            updated.updated_at = Utc::now().to_rfc3339();
            Self::upsert_quest_in_tx(&tx, &updated)?;
            self.append_ledger_or_refuse(
                "quest.proposed",
                quest_id,
                &format!(
                    "Quest `{quest_id}` re-proposed on rebased base `{}` -> head `{}`",
                    &receipt.base_sha[..receipt.base_sha.len().min(12)],
                    &receipt.head_sha[..receipt.head_sha.len().min(12)]
                ),
                serde_json::to_value(&updated).unwrap_or_default(),
            )?;
            tx.commit()
                .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
            return Ok(updated);
        }

        // A candidate may delete files; only paths still present are artifacts to check on disk.
        let present: Vec<String> = changed_paths
            .iter()
            .filter(|p| repo_root.join(p).exists())
            .cloned()
            .collect();
        let changed_paths = if present.is_empty() {
            changed_paths
        } else {
            present
        };

        if cur.state == "Scoped" {
            self.transition_quest(
                quest_id,
                "Built",
                actor,
                None,
                QuestGuardEvidence::RepoCheck {
                    repo_root: repo_root.to_path_buf(),
                    artifacts: changed_paths.clone(),
                },
            )?;
        }
        let after_built = self
            .get_quest(quest_id)
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?
            .unwrap();
        if after_built.state == "Built" {
            self.transition_quest(
                quest_id,
                "Wired",
                actor,
                None,
                QuestGuardEvidence::RepoCheck {
                    repo_root: repo_root.to_path_buf(),
                    artifacts: changed_paths,
                },
            )?;
        }

        self.transition_quest(
            quest_id,
            "Toothed",
            actor,
            None,
            QuestGuardEvidence::Receipt {
                receipt: Box::new(receipt.clone()),
                repo_root: repo_root.to_path_buf(),
                trunk_branch: trunk_branch.to_string(),
            },
        )
    }

    /// Land a `Toothed` quest onto `trunk_branch` by re-verifying `receipt` against live trunk
    /// freshness (`StaleBaseSha` if trunk moved!), fast-forwarding `trunk_branch`, deleting any
    /// merged side-branch, checking `probe_git_q5`, and advancing `Toothed -> Landed`.
    pub fn land_quest(
        &self,
        quest_id: &str,
        actor: &str,
        receipt: &JudgeReceipt,
        repo_root: &Path,
        trunk_branch: &str,
    ) -> std::result::Result<QuestRow, StateRefusal> {
        let cur = self
            .get_quest(quest_id)
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?
            .ok_or_else(|| StateRefusal::IllegalTransition {
                machine: "quest".into(),
                id: quest_id.into(),
                from: "<missing>".into(),
                to: "Landed".into(),
            })?;

        if cur.state != "Toothed" {
            return Err(StateRefusal::IllegalTransition {
                machine: "quest".into(),
                id: quest_id.into(),
                from: cur.state,
                to: "Landed".into(),
            });
        }
        if actor != cur.holder_agent {
            return Err(StateRefusal::GuardFailed {
                guard: "Q5".into(),
                reason: format!(
                    "actor `{actor}` does not hold quest `{quest_id}` (holder is `{}`)",
                    cur.holder_agent
                ),
            });
        }

        // Strict TOCTOU check: live `trunk_branch` tip MUST STILL equal `receipt.base_sha`!
        let live_trunk_sha = run_git_ro(
            repo_root,
            &[
                "rev-parse",
                "--verify",
                &format!("{trunk_branch}^{{commit}}"),
            ],
        )
        .map_err(|e| StateRefusal::GuardFailed {
            guard: "Q5".into(),
            reason: format!("failed to resolve `{trunk_branch}`: {e:#}"),
        })?
        .trim()
        .to_string();

        if live_trunk_sha != receipt.base_sha {
            return Err(StateRefusal::StaleBaseSha {
                quest_id: quest_id.to_string(),
                trunk_branch: trunk_branch.to_string(),
                receipt_base_sha: receipt.base_sha.clone(),
                current_trunk_sha: live_trunk_sha,
            });
        }

        // Checked before the fast-forward: a refusal here must not leave trunk already moved.
        let changed =
            Self::verify_candidate_receipt(&cur, "Q5", receipt, repo_root, trunk_branch, true)?;
        Self::enforce_lease(&cur, &changed)?;

        // Fast-forward `trunk_branch` to `receipt.head_sha` and remove merged side branch if any
        let current_branch = run_git_ro(repo_root, &["rev-parse", "--abbrev-ref", "HEAD"])
            .unwrap_or_default()
            .trim()
            .to_string();

        if current_branch != trunk_branch {
            run_git(repo_root, &["checkout", "--quiet", trunk_branch]).map_err(|e| {
                StateRefusal::GuardFailed {
                    guard: "Q5".into(),
                    reason: format!("failed to checkout `{trunk_branch}`: {e:#}"),
                }
            })?;
        }

        run_git(
            repo_root,
            &["merge", "--ff-only", "--quiet", &receipt.head_sha],
        )
        .map_err(|e| StateRefusal::GuardFailed {
            guard: "Q5".into(),
            reason: format!("fast-forward merge onto `{trunk_branch}` failed: {e:#}"),
        })?;

        if !current_branch.is_empty()
            && current_branch != "HEAD"
            && current_branch != trunk_branch
            && !matches!(current_branch.as_str(), "main" | "master" | "dev")
        {
            let _ = run_git(repo_root, &["branch", "-d", &current_branch]);
        }

        self.transition_quest(
            quest_id,
            "Landed",
            actor,
            None,
            QuestGuardEvidence::Receipt {
                receipt: Box::new(receipt.clone()),
                repo_root: repo_root.to_path_buf(),
                trunk_branch: trunk_branch.to_string(),
            },
        )
    }

    /// Emergency operator bypass (`obend-swarm` Finding 14): fast-forwards `head_rev` onto
    /// `trunk_branch` and records the quest in `Landed` with `effective_regime = "AttestedOverride"`
    /// and `merged_ungated = true`, preserving ledger truth without certifying `decided`/`certified`.
    pub fn land_quest_ungated(
        &self,
        quest_id: &str,
        operator: &str,
        reason: &str,
        repo_root: &Path,
        trunk_branch: &str,
        head_rev: &str,
    ) -> std::result::Result<QuestRow, StateRefusal> {
        if operator.trim().is_empty() || reason.trim().is_empty() {
            return Err(StateRefusal::GuardFailed {
                guard: "Q5".into(),
                reason: "land_quest_ungated requires non-empty `operator` and `reason`".into(),
            });
        }
        let head_sha = run_git_ro(
            repo_root,
            &["rev-parse", "--verify", &format!("{head_rev}^{{commit}}")],
        )
        .map_err(|e| StateRefusal::GuardFailed {
            guard: "Q5".into(),
            reason: format!("failed to resolve `{head_rev}`: {e:#}"),
        })?
        .trim()
        .to_string();

        let current_branch = run_git_ro(repo_root, &["rev-parse", "--abbrev-ref", "HEAD"])
            .unwrap_or_default()
            .trim()
            .to_string();
        if current_branch != trunk_branch {
            run_git(repo_root, &["checkout", "--quiet", trunk_branch]).map_err(|e| {
                StateRefusal::GuardFailed {
                    guard: "Q5".into(),
                    reason: format!("failed to checkout `{trunk_branch}`: {e:#}"),
                }
            })?;
        }
        let live_trunk_sha = run_git_ro(repo_root, &["rev-parse", "--verify", "HEAD^{commit}"])
            .unwrap_or_default()
            .trim()
            .to_string();
        if live_trunk_sha != head_sha {
            run_git(repo_root, &["merge", "--ff-only", "--quiet", &head_sha]).map_err(|e| {
                StateRefusal::GuardFailed {
                    guard: "Q5".into(),
                    reason: format!("ungated fast-forward merge failed: {e:#}"),
                }
            })?;
        }
        if !current_branch.is_empty()
            && current_branch != "HEAD"
            && current_branch != trunk_branch
            && !matches!(current_branch.as_str(), "main" | "master" | "dev")
        {
            let _ = run_git(repo_root, &["branch", "-d", &current_branch]);
        }

        // Advance any unreached pre-Landed states with explicit `AttestedOverride` so statechart path stays contiguous
        let intermediate = ["Scoped", "Built", "Wired", "Toothed", "Landed"];
        let mut cur = self
            .get_quest(quest_id)
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?
            .ok_or_else(|| StateRefusal::IllegalTransition {
                machine: "quest".into(),
                id: quest_id.into(),
                from: "<missing>".into(),
                to: "Landed".into(),
            })?;

        let start_idx = match cur.state.as_str() {
            "Grounded" => 0,
            "Scoped" => 1,
            "Built" => 2,
            "Wired" => 3,
            "Toothed" => 4,
            other => {
                return Err(StateRefusal::IllegalTransition {
                    machine: "quest".into(),
                    id: quest_id.into(),
                    from: other.into(),
                    to: "Landed".into(),
                });
            }
        };

        for next_st in &intermediate[start_idx..] {
            cur = self.transition_quest(
                quest_id,
                next_st,
                operator,
                None,
                QuestGuardEvidence::AttestedOverride {
                    operator: operator.to_string(),
                    reason: reason.to_string(),
                    head_sha: Some(head_sha.clone()),
                },
            )?;
        }
        Ok(cur)
    }

    // -------------------------------------------------------------------------
    // Ember Event Queue (`ember_events == ["aim", "decision", "taste"]`)
    // -------------------------------------------------------------------------

    pub fn enqueue_ember_event(
        &self,
        kind: &str,
        subject_id: &str,
        prompt: &str,
    ) -> std::result::Result<EmberEventRow, StateRefusal> {
        if !self.spec.is_valid_ember_event(kind) {
            return Err(StateRefusal::InvalidEmberEvent {
                event: kind.to_string(),
                allowed: self.spec.ember_events.clone(),
            });
        }
        let now = Utc::now().to_rfc3339();
        let mut conn = self
            .conn()
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?;
        let tx = conn
            .transaction()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        tx.execute(
            "INSERT INTO ember_queue (kind, subject_id, prompt, resolved, resolution, created_at)
             VALUES (?1, ?2, ?3, 0, NULL, ?4)",
            params![kind, subject_id, prompt, now],
        )
        .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        let id = tx.last_insert_rowid();
        let row = EmberEventRow {
            id,
            kind: kind.to_string(),
            subject_id: subject_id.to_string(),
            prompt: prompt.to_string(),
            resolved: false,
            resolution: None,
            created_at: now,
        };
        self.append_ledger_or_refuse(
            &format!("ember.{kind}"),
            subject_id,
            prompt,
            serde_json::to_value(&row).unwrap_or_default(),
        )?;
        tx.commit()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Ok(row)
    }

    // -------------------------------------------------------------------------
    // Segment Operations (`obb seg`: `new`, `fork`, `continue`, `distill`, `merge`, `forget`, `adopt`, `compare`, `list`)
    // -------------------------------------------------------------------------

    pub fn seg_new(
        &self,
        id: &str,
        quest_id: &str,
        model_tier: &str,
        host: &str,
        notes: &str,
    ) -> std::result::Result<SegmentRow, StateRefusal> {
        self.enforce_host_headroom(host)?;
        let now = Utc::now().to_rfc3339();
        let initial = self.spec.machines.segment.initial.clone();
        let mut conn = self
            .conn()
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?;
        let tx = conn
            .transaction()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        tx.execute(
            "INSERT OR REPLACE INTO segments
             (id, quest_id, parent_id, state, model_tier, host, token_count, transcript_mode, distill_hash, notes, origin, updated_at)
             VALUES (?1, ?2, NULL, ?3, ?4, ?5, 0, 'full', NULL, ?6, ?7, ?8)",
            params![id, quest_id, initial, model_tier, host, notes, ORIGIN_LIVE, now],
        )
        .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        let row = SegmentRow {
            id: id.to_string(),
            quest_id: quest_id.to_string(),
            parent_id: None,
            state: initial,
            model_tier: model_tier.to_string(),
            host: host.to_string(),
            token_count: 0,
            transcript_mode: "full".to_string(),
            distill_hash: None,
            notes: notes.to_string(),
            origin: ORIGIN_LIVE.to_string(),
            updated_at: now,
        };
        self.append_ledger_or_refuse(
            "segment.new",
            id,
            &format!("Segment `{id}` created on `{host}` ({model_tier})"),
            serde_json::to_value(&row).unwrap_or_default(),
        )?;
        tx.commit()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Ok(row)
    }

    pub fn seg_continue(
        &self,
        id: &str,
        added_tokens: u64,
        notes: &str,
    ) -> std::result::Result<SegmentRow, StateRefusal> {
        let mut seg = self.get_segment(id)?;
        self.enforce_host_headroom(&seg.host)?;

        let new_tokens = seg.token_count + added_tokens;
        let target_state = if new_tokens >= SEGMENT_PRESSURE_TOKEN_CAP {
            "Pressured"
        } else {
            "Working"
        };

        if seg.state != target_state {
            if self
                .spec
                .find_segment_transition(&seg.state, target_state)
                .is_none()
            {
                if seg.state == "Fresh" && target_state == "Pressured" {
                    seg.state = "Pressured".to_string();
                } else {
                    return Err(StateRefusal::IllegalTransition {
                        machine: "segment".into(),
                        id: id.into(),
                        from: seg.state,
                        to: target_state.into(),
                    });
                }
            } else {
                seg.state = target_state.to_string();
            }
        }

        seg.token_count = new_tokens;
        if !notes.is_empty() {
            seg.notes = notes.to_string();
        }
        seg.updated_at = Utc::now().to_rfc3339();
        let mut conn = self
            .conn()
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?;
        let tx = conn
            .transaction()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Self::upsert_segment_in_tx(&tx, &seg)?;
        let ev_prefix = if seg.origin == ORIGIN_DEMO_SEED {
            "demo_seed.segment.continue"
        } else {
            "segment.continue"
        };
        self.append_ledger_or_refuse(
            ev_prefix,
            id,
            &format!(
                "Segment `{id}` continued ({} tokens, state `{}`)",
                seg.token_count, seg.state
            ),
            serde_json::to_value(&seg).unwrap_or_default(),
        )?;
        tx.commit()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Ok(seg)
    }

    pub fn seg_distill(
        &self,
        id: &str,
        distill_artifact_content: &str,
    ) -> std::result::Result<SegmentRow, StateRefusal> {
        let mut seg = self.get_segment(id)?;
        if distill_artifact_content.trim().is_empty() {
            return Err(StateRefusal::GuardFailed {
                guard: "S3".into(),
                reason: "distillation artifact cannot be empty".into(),
            });
        }
        if !matches!(seg.state.as_str(), "Pressured" | "Working" | "Distilled") {
            return Err(StateRefusal::IllegalTransition {
                machine: "segment".into(),
                id: id.into(),
                from: seg.state,
                to: "Distilled".into(),
            });
        }
        let digest = sha256_hex(distill_artifact_content.as_bytes());
        seg.state = "Distilled".to_string();
        seg.distill_hash = Some(digest.clone());
        seg.transcript_mode = "compacted".to_string();
        seg.updated_at = Utc::now().to_rfc3339();
        let mut conn = self
            .conn()
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?;
        let tx = conn
            .transaction()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Self::upsert_segment_in_tx(&tx, &seg)?;
        let ev_prefix = if seg.origin == ORIGIN_DEMO_SEED {
            "demo_seed.segment.distill"
        } else {
            "segment.distill"
        };
        self.append_ledger_or_refuse(
            ev_prefix,
            id,
            &format!("Segment `{id}` distilled (sha256={})", &digest[..12]),
            serde_json::to_value(&seg).unwrap_or_default(),
        )?;
        tx.commit()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Ok(seg)
    }

    pub fn seg_fork(
        &self,
        parent_id: &str,
        child_id: &str,
        child_model_tier: &str,
        child_host: &str,
        handoff_direction: &str,
        transcript_mode: &str,
    ) -> std::result::Result<SegmentRow, StateRefusal> {
        self.enforce_host_headroom(child_host)?;
        let mut parent = self.get_segment(parent_id)?;

        if parent.token_count > SEGMENT_FORK_TOKEN_CAP && parent.state != "Distilled" {
            return Err(StateRefusal::LargeContextFork {
                seg_id: parent.id,
                tokens: parent.token_count,
                cap: SEGMENT_FORK_TOKEN_CAP,
                state: parent.state,
            });
        }

        match handoff_direction {
            "downshift" => {
                if transcript_mode != "full" {
                    return Err(StateRefusal::HandoffDirectionViolation {
                        direction: "downshift".into(),
                        expected_mode: "full".into(),
                        actual_mode: transcript_mode.into(),
                    });
                }
            }
            "escalate" => {
                if transcript_mode != "compacted" {
                    return Err(StateRefusal::HandoffDirectionViolation {
                        direction: "escalate".into(),
                        expected_mode: "compacted".into(),
                        actual_mode: transcript_mode.into(),
                    });
                }
            }
            "peer" => {}
            other => {
                return Err(StateRefusal::GuardFailed {
                    guard: "S5".into(),
                    reason: format!(
                        "unknown handoff direction `{other}` (expected `downshift`, `escalate`, or `peer`)"
                    ),
                });
            }
        }

        parent.state = "Forked".to_string();
        parent.updated_at = Utc::now().to_rfc3339();

        let inherited_tokens = if transcript_mode == "compacted" {
            (parent.token_count / 10).min(8_000)
        } else {
            parent.token_count
        };
        let now = Utc::now().to_rfc3339();
        let child = SegmentRow {
            id: child_id.to_string(),
            quest_id: parent.quest_id.clone(),
            parent_id: Some(parent.id.clone()),
            state: "Working".to_string(),
            model_tier: child_model_tier.to_string(),
            host: child_host.to_string(),
            token_count: inherited_tokens,
            transcript_mode: transcript_mode.to_string(),
            distill_hash: parent.distill_hash.clone(),
            notes: format!("forked ({handoff_direction}) from {}", parent.id),
            origin: parent.origin.clone(),
            updated_at: now,
        };
        let mut conn = self
            .conn()
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?;
        let tx = conn
            .transaction()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Self::upsert_segment_in_tx(&tx, &parent)?;
        Self::upsert_segment_in_tx(&tx, &child)?;
        let ev_prefix = if child.origin == ORIGIN_DEMO_SEED {
            "demo_seed.segment.fork"
        } else {
            "segment.fork"
        };
        self.append_ledger_or_refuse(
            ev_prefix,
            child_id,
            &format!(
                "Segment `{child_id}` forked from `{parent_id}` ({handoff_direction}, mode={transcript_mode})"
            ),
            serde_json::to_value(&child).unwrap_or_default(),
        )?;
        tx.commit()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Ok(child)
    }

    pub fn seg_merge(
        &self,
        id: &str,
        into_id: &str,
    ) -> std::result::Result<SegmentRow, StateRefusal> {
        let mut seg = self.get_segment(id)?;
        let _target = self.get_segment(into_id)?;
        if !matches!(seg.state.as_str(), "Working" | "Distilled" | "Forked") {
            return Err(StateRefusal::IllegalTransition {
                machine: "segment".into(),
                id: id.into(),
                from: seg.state,
                to: "Retired".into(),
            });
        }
        seg.state = "Retired".to_string();
        seg.notes = format!("merged into {into_id} and superseded");
        seg.updated_at = Utc::now().to_rfc3339();
        let mut conn = self
            .conn()
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?;
        let tx = conn
            .transaction()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Self::upsert_segment_in_tx(&tx, &seg)?;
        self.append_ledger_or_refuse(
            "segment.merge",
            id,
            &format!("Segment `{id}` merged into `{into_id}`"),
            serde_json::to_value(&seg).unwrap_or_default(),
        )?;
        tx.commit()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Ok(seg)
    }

    pub fn seg_forget(
        &self,
        id: &str,
        reason: &str,
    ) -> std::result::Result<SegmentRow, StateRefusal> {
        let mut seg = self.get_segment(id)?;
        seg.state = "Retired".to_string();
        seg.transcript_mode = "forgotten-prefix".to_string();
        seg.notes = format!("retired/forgotten: {reason}");
        seg.updated_at = Utc::now().to_rfc3339();
        let mut conn = self
            .conn()
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?;
        let tx = conn
            .transaction()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Self::upsert_segment_in_tx(&tx, &seg)?;
        self.append_ledger_or_refuse(
            "segment.forget",
            id,
            &format!("Segment `{id}` retired (`forget`: {reason})"),
            serde_json::to_value(&seg).unwrap_or_default(),
        )?;
        tx.commit()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Ok(seg)
    }

    pub fn seg_adopt(
        &self,
        id: &str,
        quest_id: &str,
        session_path: &str,
        host: &str,
    ) -> std::result::Result<SegmentRow, StateRefusal> {
        self.enforce_host_headroom(host)?;
        let approx_tokens = fs::metadata(session_path)
            .map(|m| m.len() / 4)
            .unwrap_or(4_000);
        let now = Utc::now().to_rfc3339();
        let row = SegmentRow {
            id: id.to_string(),
            quest_id: quest_id.to_string(),
            parent_id: None,
            state: "Working".to_string(),
            model_tier: "adopted-session".to_string(),
            host: host.to_string(),
            token_count: approx_tokens,
            transcript_mode: "full".to_string(),
            distill_hash: None,
            notes: format!("adopted from {session_path}"),
            origin: ORIGIN_LIVE.to_string(),
            updated_at: now,
        };
        let mut conn = self
            .conn()
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?;
        let tx = conn
            .transaction()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Self::upsert_segment_in_tx(&tx, &row)?;
        self.append_ledger_or_refuse(
            "segment.adopt",
            id,
            &format!("Segment `{id}` adopted from `{session_path}` on `{host}`"),
            serde_json::to_value(&row).unwrap_or_default(),
        )?;
        tx.commit()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Ok(row)
    }

    pub fn seg_compare(&self, seg_a: &str, seg_b: &str) -> Result<serde_json::Value> {
        let a = self
            .get_segment(seg_a)
            .map_err(|e| anyhow::anyhow!(e.to_string()))?;
        let b = self
            .get_segment(seg_b)
            .map_err(|e| anyhow::anyhow!(e.to_string()))?;
        Ok(serde_json::json!({
            "left": a,
            "right": b,
            "same_quest": a.quest_id == b.quest_id,
            "token_delta": (a.token_count as i64) - (b.token_count as i64),
            "shared_distill": a.distill_hash.is_some() && a.distill_hash == b.distill_hash,
        }))
    }

    pub fn list_segments(&self) -> Result<Vec<SegmentRow>> {
        let conn = self.conn()?;
        let mut stmt = conn.prepare(
            "SELECT id, quest_id, parent_id, state, model_tier, host, token_count, transcript_mode, distill_hash, notes, origin, updated_at
             FROM segments ORDER BY updated_at ASC, id ASC",
        )?;
        let rows = stmt
            .query_map([], |r| {
                Ok(SegmentRow {
                    id: r.get(0)?,
                    quest_id: r.get(1)?,
                    parent_id: r.get(2)?,
                    state: r.get(3)?,
                    model_tier: r.get(4)?,
                    host: r.get(5)?,
                    token_count: r.get::<_, i64>(6)? as u64,
                    transcript_mode: r.get(7)?,
                    distill_hash: r.get(8)?,
                    notes: r.get(9)?,
                    origin: r.get(10)?,
                    updated_at: r.get(11)?,
                })
            })?
            .collect::<std::result::Result<Vec<_>, _>>()?;
        Ok(rows)
    }

    fn get_segment(&self, id: &str) -> std::result::Result<SegmentRow, StateRefusal> {
        let conn = self
            .conn()
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?;
        let row = conn
            .query_row(
                "SELECT id, quest_id, parent_id, state, model_tier, host, token_count, transcript_mode, distill_hash, notes, origin, updated_at
                 FROM segments WHERE id = ?1",
                params![id],
                |r| {
                    Ok(SegmentRow {
                        id: r.get(0)?,
                        quest_id: r.get(1)?,
                        parent_id: r.get(2)?,
                        state: r.get(3)?,
                        model_tier: r.get(4)?,
                        host: r.get(5)?,
                        token_count: r.get::<_, i64>(6)? as u64,
                        transcript_mode: r.get(7)?,
                        distill_hash: r.get(8)?,
                        notes: r.get(9)?,
                        origin: r.get(10)?,
                        updated_at: r.get(11)?,
                    })
                },
            )
            .optional()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        row.ok_or_else(|| StateRefusal::IllegalTransition {
            machine: "segment".into(),
            id: id.into(),
            from: "<missing>".into(),
            to: "<any>".into(),
        })
    }

    fn upsert_segment_in_tx(
        tx: &rusqlite::Transaction<'_>,
        s: &SegmentRow,
    ) -> std::result::Result<(), StateRefusal> {
        tx.execute(
            "INSERT OR REPLACE INTO segments
             (id, quest_id, parent_id, state, model_tier, host, token_count, transcript_mode, distill_hash, notes, origin, updated_at)
             VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12)",
            params![
                s.id,
                s.quest_id,
                s.parent_id,
                s.state,
                s.model_tier,
                s.host,
                s.token_count as i64,
                s.transcript_mode,
                s.distill_hash,
                s.notes,
                s.origin,
                s.updated_at
            ],
        )
        .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        Ok(())
    }

    // -------------------------------------------------------------------------
    // Machine Disk Headroom, `cv --frozen`, and Git `Q5` Probes
    // -------------------------------------------------------------------------

    pub fn record_machine_status(&self, m: &MachineStatus) -> Result<()> {
        let conn = self.conn()?;
        conn.execute(
            "INSERT OR REPLACE INTO machines
             (host, reachable, required_for_dispatch, avail_gb, total_gb, load_summary, below_floor, checked_at)
             VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8)",
            params![
                m.host,
                m.reachable as i64,
                m.required_for_dispatch as i64,
                m.avail_gb,
                m.total_gb,
                m.load_summary,
                m.below_floor as i64,
                m.checked_at,
            ],
        )?;
        Ok(())
    }

    fn enforce_host_headroom(&self, host: &str) -> std::result::Result<(), StateRefusal> {
        let conn = self
            .conn()
            .map_err(|e| StateRefusal::StorageError(format!("{e:#}")))?;
        // `below_floor` also covers a local disk that could not be measured at all.
        let row: Option<(i64, f64)> = conn
            .query_row(
                "SELECT below_floor, avail_gb FROM machines WHERE host = ?1",
                params![host],
                |r| Ok((r.get(0)?, r.get(1)?)),
            )
            .optional()
            .map_err(|e| StateRefusal::StorageError(e.to_string()))?;
        if let Some((below_floor, avail_gb)) = row
            && below_floor != 0
        {
            return Err(StateRefusal::DiskHeadroomFloor {
                host: host.to_string(),
                avail_gb,
                floor_gb: DISK_FREE_FLOOR_GB,
            });
        }
        Ok(())
    }

    /// Probe local workspace disk headroom (`df -Pk`) and optionally remote SSH hosts (`hbox`, `bb2`).
    pub fn probe_machines(&self, include_remotes: bool) -> Result<Vec<MachineStatus>> {
        let mut results = Vec::new();
        let now = Utc::now().to_rfc3339();

        let local_status = match Command::new("df")
            .arg("-Pk")
            .arg(&self.workspace_root)
            .output()
        {
            Ok(out) if out.status.success() => {
                let s = String::from_utf8_lossy(&out.stdout);
                // An unreadable `df` is an unknown, never a made-up healthy reading.
                match parse_df_pk(&s) {
                    Some((avail_gb, total_gb)) => MachineStatus {
                        host: "local".to_string(),
                        reachable: true,
                        required_for_dispatch: true,
                        avail_gb,
                        total_gb,
                        load_summary: "local workspace".to_string(),
                        below_floor: avail_gb < DISK_FREE_FLOOR_GB,
                        checked_at: now.clone(),
                    },
                    None => MachineStatus {
                        host: "local".to_string(),
                        reachable: false,
                        required_for_dispatch: true,
                        avail_gb: 0.0,
                        total_gb: 0.0,
                        load_summary: "df output unparsable".to_string(),
                        below_floor: true,
                        checked_at: now.clone(),
                    },
                }
            }
            _ => MachineStatus {
                host: "local".to_string(),
                reachable: false,
                required_for_dispatch: true,
                avail_gb: 0.0,
                total_gb: 0.0,
                load_summary: "df failed".to_string(),
                below_floor: true,
                checked_at: now.clone(),
            },
        };
        self.record_machine_status(&local_status)?;
        results.push(local_status);

        if include_remotes {
            for remote in ["hbox", "bb2"] {
                let out = Command::new("ssh")
                    .args([
                        "-o",
                        "BatchMode=yes",
                        "-o",
                        "ConnectTimeout=3",
                        remote,
                        "df -Pk . && uptime",
                    ])
                    .output();
                let st = match out {
                    Ok(o) if o.status.success() => {
                        let txt = String::from_utf8_lossy(&o.stdout);
                        let (avail_gb, total_gb) = parse_df_pk(&txt).unwrap_or((0.0, 0.0));
                        let load = txt
                            .lines()
                            .last()
                            .map(str::trim)
                            .unwrap_or("ok")
                            .to_string();
                        MachineStatus {
                            host: remote.to_string(),
                            reachable: true,
                            required_for_dispatch: true,
                            avail_gb,
                            total_gb,
                            load_summary: load,
                            below_floor: avail_gb < DISK_FREE_FLOOR_GB,
                            checked_at: now.clone(),
                        }
                    }
                    _ => MachineStatus {
                        host: remote.to_string(),
                        reachable: false,
                        required_for_dispatch: false,
                        avail_gb: 0.0,
                        total_gb: 0.0,
                        load_summary: "unreachable (SSH offline/timeout)".to_string(),
                        below_floor: false,
                        checked_at: now.clone(),
                    },
                };
                self.record_machine_status(&st)?;
                results.push(st);
            }
        }

        Ok(results)
    }

    /// Probe `/Users/ember/.cargo/bin/cv --frozen` for `G1`, `S2`, and `S6`.
    pub fn probe_cv(&self, cv_bin: Option<&Path>) -> CvProbeReport {
        let bin = cv_bin.unwrap_or_else(|| Path::new(DEFAULT_CV_BIN));
        if !bin.is_file() {
            return CvProbeReport {
                cv_bin: bin.to_string_lossy().to_string(),
                available: false,
                g1_whole_read_events: 0,
                s2_doctor_ok: false,
                s6_stranded_lanes: 0,
                deferrals_open: 0,
                summary: format!("cv binary not found at {}", bin.display()),
            };
        }

        let doctor_ok = Command::new(bin)
            .args(["--frozen", "doctor"])
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false);

        let events_count = Command::new(bin)
            .args(["--frozen", "events"])
            .output()
            .map(|o| {
                String::from_utf8_lossy(&o.stdout)
                    .lines()
                    .filter(|l| l.contains("read") || l.contains("Read"))
                    .count()
            })
            .unwrap_or(0);

        let stranded_count = Command::new(bin)
            .args(["--frozen", "lanes", "--stranded"])
            .output()
            .map(|o| {
                String::from_utf8_lossy(&o.stdout)
                    .lines()
                    .filter(|l| !l.trim().is_empty() && !l.to_lowercase().contains("none"))
                    .count()
            })
            .unwrap_or(0);

        let deferrals_count = Command::new(bin)
            .args(["--frozen", "deferrals"])
            .output()
            .map(|o| {
                String::from_utf8_lossy(&o.stdout)
                    .lines()
                    .filter(|l| !l.trim().is_empty() && !l.to_lowercase().contains("none"))
                    .count()
            })
            .unwrap_or(0);

        CvProbeReport {
            cv_bin: bin.to_string_lossy().to_string(),
            available: true,
            g1_whole_read_events: events_count,
            s2_doctor_ok: doctor_ok,
            s6_stranded_lanes: stranded_count,
            deferrals_open: deferrals_count,
            summary: format!(
                "doctor_ok={doctor_ok}, whole_reads={events_count}, stranded={stranded_count}, deferrals={deferrals_count}"
            ),
        }
    }

    /// Probe git repository cleanliness (`Q5`: clean working tree, 0 `git stash` entries, 0 surviving merged side-branches).
    pub fn probe_git_q5(repo_root: &Path) -> Result<GitProbeReport> {
        let mut status_cmd = Command::new("git");
        configure_hermetic_git(&mut status_cmd)
            .args(["--no-optional-locks", "-C"])
            .arg(repo_root)
            .args(["status", "--porcelain"]);
        let status_out = status_cmd
            .output()
            .context("failed to run `git status --porcelain`")?;
        let modified_paths: Vec<String> = String::from_utf8_lossy(&status_out.stdout)
            .lines()
            .map(str::trim)
            .filter(|l| {
                if l.is_empty() {
                    return false;
                }
                let path_part = l.get(3..).unwrap_or(l).trim();
                !(path_part == ".obb-state" || path_part.starts_with(".obb-state/"))
            })
            .map(str::to_string)
            .collect();

        let mut stash_cmd = Command::new("git");
        configure_hermetic_git(&mut stash_cmd)
            .args(["--no-optional-locks", "-C"])
            .arg(repo_root)
            .args(["stash", "list"]);
        let stash_out = stash_cmd
            .output()
            .context("failed to run `git stash list`")?;
        let stash_count = String::from_utf8_lossy(&stash_out.stdout)
            .lines()
            .filter(|l| !l.trim().is_empty())
            .count();

        let mut branch_cmd = Command::new("git");
        configure_hermetic_git(&mut branch_cmd)
            .args(["--no-optional-locks", "-C"])
            .arg(repo_root)
            .args(["rev-parse", "--abbrev-ref", "HEAD"]);
        let branch_out = branch_cmd.output()?;
        let current_branch = String::from_utf8_lossy(&branch_out.stdout)
            .trim()
            .to_string();

        let mut merged_cmd = Command::new("git");
        configure_hermetic_git(&mut merged_cmd)
            .args(["--no-optional-locks", "-C"])
            .arg(repo_root)
            .args(["branch", "--merged", "HEAD", "--format=%(refname:short)"]);
        let merged_out = merged_cmd.output()?;
        let merged_side_branches: Vec<String> = String::from_utf8_lossy(&merged_out.stdout)
            .lines()
            .map(str::trim)
            .filter(|b| {
                !b.is_empty() && *b != current_branch && !matches!(*b, "main" | "master" | "dev")
            })
            .map(str::to_string)
            .collect();

        let clean_working_tree = modified_paths.is_empty();
        let q5_passed = clean_working_tree && stash_count == 0 && merged_side_branches.is_empty();

        Ok(GitProbeReport {
            repo: repo_root.to_string_lossy().to_string(),
            clean_working_tree,
            modified_paths,
            stash_count,
            merged_side_branches,
            current_branch,
            q5_passed,
        })
    }

    pub fn snapshot(&self) -> Result<StateSnapshot> {
        let conn = self.conn()?;

        let mut c_stmt = conn.prepare(
            "SELECT id, title, state, aim_statement, target_repo, origin, updated_at FROM campaigns ORDER BY id",
        )?;
        let campaigns: Vec<CampaignRow> = c_stmt
            .query_map([], |r| {
                Ok(CampaignRow {
                    id: r.get(0)?,
                    title: r.get(1)?,
                    state: r.get(2)?,
                    aim_statement: r.get(3)?,
                    target_repo: r.get(4)?,
                    origin: r.get(5)?,
                    updated_at: r.get(6)?,
                })
            })?
            .collect::<std::result::Result<Vec<_>, _>>()?;

        let mut q_stmt = conn.prepare(
            "SELECT id, campaign_id, title, state, is_sink, prior_state, holder_agent, target_regime,
                    effective_regime, merged_ungated, origin, footprint_json, base_sha,
                    proposed_head_sha, landed_sha, verified_receipt_hash, tooth_witness, updated_at
             FROM quests ORDER BY id",
        )?;
        let quests: Vec<QuestRow> = q_stmt
            .query_map([], Self::map_quest_row)?
            .collect::<std::result::Result<Vec<_>, _>>()?;

        let segments = self.list_segments()?;

        let mut e_stmt = conn.prepare(
            "SELECT id, kind, subject_id, prompt, resolved, resolution, created_at
             FROM ember_queue WHERE resolved = 0 ORDER BY id ASC",
        )?;
        let waiting_on_ember: Vec<EmberEventRow> = e_stmt
            .query_map([], |r| {
                Ok(EmberEventRow {
                    id: r.get(0)?,
                    kind: r.get(1)?,
                    subject_id: r.get(2)?,
                    prompt: r.get(3)?,
                    resolved: r.get::<_, i64>(4)? != 0,
                    resolution: r.get(5)?,
                    created_at: r.get(6)?,
                })
            })?
            .collect::<std::result::Result<Vec<_>, _>>()?;

        let mut m_stmt = conn.prepare(
            "SELECT host, reachable, required_for_dispatch, avail_gb, total_gb, load_summary, below_floor, checked_at
             FROM machines ORDER BY host",
        )?;
        let machines: Vec<MachineStatus> = m_stmt
            .query_map([], |r| {
                Ok(MachineStatus {
                    host: r.get(0)?,
                    reachable: r.get::<_, i64>(1)? != 0,
                    required_for_dispatch: r.get::<_, i64>(2)? != 0,
                    avail_gb: r.get(3)?,
                    total_gb: r.get(4)?,
                    load_summary: r.get(5)?,
                    below_floor: r.get::<_, i64>(6)? != 0,
                    checked_at: r.get(7)?,
                })
            })?
            .collect::<std::result::Result<Vec<_>, _>>()?;

        let mut pause_reasons = Vec::new();
        for m in &machines {
            if m.reachable && m.below_floor {
                pause_reasons.push(format!(
                    "machine `{}` free disk {:.2} GB < {:.1} GB floor",
                    m.host, m.avail_gb, DISK_FREE_FLOOR_GB
                ));
            } else if m.below_floor {
                pause_reasons.push(format!(
                    "machine `{}` free disk could not be measured ({})",
                    m.host, m.load_summary
                ));
            }
        }
        let scheduler_paused = !pause_reasons.is_empty();

        let all_ledger = self.read_ledger()?;
        let demo_seed_event_count = all_ledger.iter().filter(|e| e.is_demo_seed()).count();
        let live_event_count = all_ledger.len().saturating_sub(demo_seed_event_count);
        let live_transition_count = all_ledger.iter().filter(|e| e.is_live_transition()).count();
        let contains_demo_seed = demo_seed_event_count > 0
            || campaigns.iter().any(|c| c.origin == ORIGIN_DEMO_SEED)
            || quests.iter().any(|q| q.origin == ORIGIN_DEMO_SEED);

        let verified_quest_count = quests
            .iter()
            .filter(|q| {
                q.origin == ORIGIN_LIVE
                    && !q.merged_ungated
                    && matches!(q.state.as_str(), "Landed" | "Claimed" | "Recorded")
                    && matches!(q.effective_regime.as_str(), "decided" | "certified")
            })
            .count();

        let ungated_override_count = quests
            .iter()
            .filter(|q| q.merged_ungated || q.effective_regime == REGIME_ATTESTED_OVERRIDE)
            .count();

        let start = all_ledger.len().saturating_sub(25);
        let recent_ledger = all_ledger[start..].to_vec();

        Ok(StateSnapshot {
            workspace_root: self.workspace_root.to_string_lossy().to_string(),
            state_dir: self.state_dir.to_string_lossy().to_string(),
            scheduler_paused,
            pause_reasons,
            contains_demo_seed,
            live_event_count,
            live_transition_count,
            demo_seed_event_count,
            verified_quest_count,
            ungated_override_count,
            campaigns,
            quests,
            segments,
            waiting_on_ember,
            machines,
            recent_ledger,
        })
    }

    /// Seed an explicitly marked `demo_seed` Campaign / Quest / Segment fixture for UI/rendering
    /// inspection (`origin = "demo_seed"`, `effective_regime = "demo_seed"`).
    ///
    /// Seeded rows and `demo_seed.*` ledger events are strictly segregated from live operational
    /// metrics (`live_transition_count == 0`, `verified_quest_count == 0`).
    pub fn seed_obend_campaign(&self, obend_repo: &Path) -> Result<StateSnapshot> {
        let _ = self.probe_machines(false)?;
        let now = Utc::now().to_rfc3339();
        let mut conn = self.conn()?;
        let tx = conn.transaction()?;

        let append_demo = |ev_type: &str,
                           entity: &str,
                           summary: &str,
                           mut val: serde_json::Value|
         -> Result<()> {
            if let Some(obj) = val.as_object_mut() {
                obj.insert("origin".into(), serde_json::json!(ORIGIN_DEMO_SEED));
                obj.insert("regime".into(), serde_json::json!(ORIGIN_DEMO_SEED));
            }
            self.append_ledger(
                &format!("demo_seed.{ev_type}"),
                entity,
                &format!("[DEMO SEED] {summary}"),
                val,
            )?;
            Ok(())
        };

        let camp = CampaignRow {
            id: "C1-obend-reground".into(),
            title: "Obend Epistemic Regrounding & Process Harness [DEMO SEED]".into(),
            state: "Running".into(),
            aim_statement: "Every load-bearing Obend claim has a tooth, an independent spec, and zero cross-language mirrors.".into(),
            target_repo: obend_repo.to_string_lossy().to_string(),
            origin: ORIGIN_DEMO_SEED.into(),
            updated_at: now.clone(),
        };
        tx.execute(
            "INSERT OR REPLACE INTO campaigns (id, title, state, aim_statement, target_repo, origin, updated_at)
             VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7)",
            params![
                camp.id,
                camp.title,
                camp.state,
                camp.aim_statement,
                camp.target_repo,
                ORIGIN_DEMO_SEED,
                camp.updated_at
            ],
        )?;
        append_demo(
            "campaign.created",
            &camp.id,
            "Demo campaign initialized in `Aim`",
            serde_json::to_value(&camp)?,
        )?;
        append_demo(
            "campaign.transition",
            &camp.id,
            "Demo campaign Aim -> Grounded",
            serde_json::json!({"from": "Aim", "to": "Grounded"}),
        )?;
        append_demo(
            "campaign.transition",
            &camp.id,
            "Demo campaign Grounded -> Running",
            serde_json::json!({"from": "Grounded", "to": "Running"}),
        )?;

        type DemoQuest<'a> = (
            &'a str,
            &'a str,
            &'a str,
            &'a str,
            &'a str,
            bool,
            Option<&'a str>,
            &'a [&'a str],
        );
        let demo_quests: &[DemoQuest<'_>] = &[
            (
                "W1-A",
                "Branch Convergence & Stash Elimination in obend",
                "lane-w1a",
                "decided",
                "Scoped",
                false,
                None,
                &["Scoped"],
            ),
            (
                "W1-B",
                "Build `obb` Metaharness (`lint`, `judge`, `state`, `serve`)",
                "lane-w1b",
                "decided",
                "Toothed",
                false,
                None,
                &["Scoped", "Built", "Wired", "Toothed"],
            ),
            (
                "W1-C",
                "Synchronize `DESIGN.md` Term Former & Quantity Tables with `Obend/Core/`",
                "lane-docs",
                "certified",
                "Label",
                true,
                Some("Wired"),
                &["Scoped", "Built", "Wired", "Label"],
            ),
            (
                "W1-D",
                "Eliminate Discarded `z1` Tactics & Tautological `Judge.Meaning`",
                "lane-lean",
                "decided",
                "Theater",
                true,
                Some("Built"),
                &["Scoped", "Built", "Theater"],
            ),
            (
                "W1-E",
                "Replace Python E2E Self-Mocks & Rust Semantic Mirrors with `libobend` FFI",
                "lane-seam",
                "decided",
                "Mirror",
                true,
                Some("Built"),
                &["Scoped", "Built", "Mirror"],
            ),
        ];

        for (qid, title, holder, target_reg, final_state, is_sink, prior, steps) in demo_quests {
            let row = QuestRow {
                id: (*qid).to_string(),
                campaign_id: "C1-obend-reground".into(),
                title: (*title).to_string(),
                state: (*final_state).to_string(),
                is_sink: *is_sink,
                prior_state: prior.map(str::to_string),
                holder_agent: (*holder).to_string(),
                target_regime: (*target_reg).to_string(),
                effective_regime: ORIGIN_DEMO_SEED.into(),
                merged_ungated: false,
                origin: ORIGIN_DEMO_SEED.into(),
                footprint_lease: Vec::new(),
                base_sha: None,
                proposed_head_sha: None,
                landed_sha: None,
                verified_receipt_hash: None,
                tooth_witness: if *qid == "W1-B" {
                    Some("demo-seed-unexecuted".into())
                } else {
                    None
                },
                updated_at: now.clone(),
            };
            Self::upsert_quest_in_tx(&tx, &row).map_err(|e| anyhow::anyhow!(e))?;
            append_demo(
                "quest.created",
                qid,
                &format!("Demo quest `{qid}` created"),
                serde_json::to_value(&row)?,
            )?;
            for st in *steps {
                append_demo(
                    "quest.transition",
                    qid,
                    &format!("Demo quest `{qid}` -> `{st}`"),
                    serde_json::json!({ "quest_id": qid, "to": st }),
                )?;
            }
        }

        let seg_root = SegmentRow {
            id: "seg-root-audit".into(),
            quest_id: "W1-B".into(),
            parent_id: None,
            state: "Forked".into(),
            model_tier: "pro".into(),
            host: "local".into(),
            token_count: 28_000,
            transcript_mode: "compacted".into(),
            distill_hash: Some(sha256_hex(b"demo-seed-distill")),
            notes: "Demo seed audit segment".into(),
            origin: ORIGIN_DEMO_SEED.into(),
            updated_at: now.clone(),
        };
        let seg_child = SegmentRow {
            id: "seg-w1b-impl".into(),
            quest_id: "W1-B".into(),
            parent_id: Some("seg-root-audit".into()),
            state: "Working".into(),
            model_tier: "pro".into(),
            host: "local".into(),
            token_count: 2_800,
            transcript_mode: "compacted".into(),
            distill_hash: seg_root.distill_hash.clone(),
            notes: "Demo seed forked segment".into(),
            origin: ORIGIN_DEMO_SEED.into(),
            updated_at: now.clone(),
        };
        Self::upsert_segment_in_tx(&tx, &seg_root).map_err(|e| anyhow::anyhow!(e))?;
        Self::upsert_segment_in_tx(&tx, &seg_child).map_err(|e| anyhow::anyhow!(e))?;
        append_demo(
            "segment.new",
            "seg-root-audit",
            "Demo segment created",
            serde_json::to_value(&seg_root)?,
        )?;
        append_demo(
            "segment.continue",
            "seg-root-audit",
            "Demo segment continued",
            serde_json::to_value(&seg_root)?,
        )?;
        append_demo(
            "segment.distill",
            "seg-root-audit",
            "Demo segment distilled",
            serde_json::to_value(&seg_root)?,
        )?;
        append_demo(
            "segment.fork",
            "seg-w1b-impl",
            "Demo segment forked",
            serde_json::to_value(&seg_child)?,
        )?;

        tx.execute(
            "INSERT INTO ember_queue (kind, subject_id, prompt, resolved, resolution, created_at)
             VALUES (?1, ?2, ?3, 0, NULL, ?4)",
            params![
                "taste",
                "W1-C",
                "[DEMO SEED] Should `DESIGN.md` §1.1 list only current `Obend/Core/Term.lean` constructors, or generate the table mechanically via `lake exe docs-table`?",
                now
            ],
        )?;
        append_demo(
            "ember.taste",
            "W1-C",
            "Demo taste prompt queued",
            serde_json::json!({"subject_id": "W1-C", "kind": "taste"}),
        )?;

        tx.commit()?;
        self.snapshot()
    }
}

fn table_has_column(conn: &Connection, table: &str, col_name: &str) -> Result<bool> {
    let mut stmt = conn.prepare(&format!("PRAGMA table_info({table})"))?;
    let cols: Vec<String> = stmt
        .query_map([], |r| r.get::<_, String>(1))?
        .collect::<std::result::Result<Vec<_>, _>>()?;
    Ok(cols.iter().any(|c| c == col_name))
}

fn parse_df_pk(df_stdout: &str) -> Option<(f64, f64)> {
    let data_line = df_stdout.lines().nth(1)?;
    let cols: Vec<&str> = data_line.split_whitespace().collect();
    if cols.len() < 4 {
        return None;
    }
    let total_kb = cols[1].parse::<f64>().ok()?;
    let avail_kb = cols[3].parse::<f64>().ok()?;
    let gb_div = 1024.0 * 1024.0;
    Some((avail_kb / gb_div, total_kb / gb_div))
}
