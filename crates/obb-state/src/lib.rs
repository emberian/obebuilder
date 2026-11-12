//! Statechart Supervisor, Segment Tree, Append-Only JSONL Ledger & Live Probes
//! (`PROCESS.md`, `DESIGN.md` §4–5, `spec/process.json`).

use anyhow::{Context, Result, bail};
use chrono::Utc;
use obb_core::{ProcessSpec, sha256_hex};
use obb_judge::SuccessionRecord;
use rusqlite::{Connection, OptionalExtension, params};
use serde::{Deserialize, Serialize};
use std::fs::{self, OpenOptions};
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

pub const DEFAULT_CV_BIN: &str = "/Users/ember/.cargo/bin/cv";
pub const DISK_FREE_FLOOR_GB: f64 = 20.0;
pub const SEGMENT_FORK_TOKEN_CAP: u64 = 64_000;
pub const SEGMENT_PRESSURE_TOKEN_CAP: u64 = 120_000;

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, thiserror::Error)]
pub enum StateRefusal {
    #[error("IllegalTransition: {machine} `{id}` cannot move `{from}` -> `{to}` (not in `spec/process.json`)")]
    IllegalTransition {
        machine: String,
        id: String,
        from: String,
        to: String,
    },

    #[error("SinkExitViolation: quest `{id}` is in sink `{sink}`; leaving requires `{required_exit}` by holder `{holder}` (got actor `{actor}`, action `{action}`)")]
    SinkExitViolation {
        id: String,
        sink: String,
        required_exit: String,
        holder: String,
        actor: String,
        action: String,
    },

    #[error("GuardFailed({guard}): {reason}")]
    GuardFailed { guard: String, reason: String },

    #[error("InvalidEmberEvent: `{event}` is forbidden on ember's channel; allowed events are strictly {allowed:?}")]
    InvalidEmberEvent {
        event: String,
        allowed: Vec<String>,
    },

    #[error("DiskHeadroomFloor: machine `{host}` has {avail_gb:.2} GB free (< {floor_gb:.1} GB floor); scheduling paused")]
    DiskHeadroomFloor {
        host: String,
        avail_gb: f64,
        floor_gb: f64,
    },

    #[error("LargeContextFork(S4): segment `{seg_id}` has {tokens} tokens (> {cap} cap) in state `{state}`; run `obb seg distill` before forking")]
    LargeContextFork {
        seg_id: String,
        tokens: u64,
        cap: u64,
        state: String,
    },

    #[error("HandoffDirectionViolation(S5): `{direction}` handoff requires `{expected_mode}`, got `{actual_mode}`")]
    HandoffDirectionViolation {
        direction: String,
        expected_mode: String,
        actual_mode: String,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CampaignRow {
    pub id: String,
    pub title: String,
    pub state: String,
    pub aim_statement: String,
    pub target_repo: String,
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

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StateSnapshot {
    pub workspace_root: String,
    pub scheduler_paused: bool,
    pub pause_reasons: Vec<String>,
    pub campaigns: Vec<CampaignRow>,
    pub quests: Vec<QuestRow>,
    pub segments: Vec<SegmentRow>,
    pub waiting_on_ember: Vec<EmberEventRow>,
    pub machines: Vec<MachineStatus>,
    pub recent_ledger: Vec<LedgerEvent>,
}

/// Persistent SQLite + JSONL Statechart Supervisor.
pub struct StateStore {
    workspace_root: PathBuf,
    db_path: PathBuf,
    ledger_path: PathBuf,
    pub spec: ProcessSpec,
}

impl StateStore {
    pub fn open(workspace_root: &Path) -> Result<Self> {
        let spec_path = workspace_root.join("spec/process.json");
        let spec = if spec_path.is_file() {
            ProcessSpec::load_from_path(&spec_path)?
        } else {
            ProcessSpec::embedded_default()?
        };

        let obb_dir = workspace_root.join(".obb");
        let ledger_dir = workspace_root.join("ledger");
        fs::create_dir_all(&obb_dir)
            .with_context(|| format!("failed to create {}", obb_dir.display()))?;
        fs::create_dir_all(&ledger_dir)
            .with_context(|| format!("failed to create {}", ledger_dir.display()))?;

        let db_path = obb_dir.join("state.db");
        let ledger_path = ledger_dir.join("events.jsonl");

        let store = Self {
            workspace_root: workspace_root.to_path_buf(),
            db_path,
            ledger_path,
            spec,
        };
        store.init_schema()?;
        Ok(store)
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
        Ok(())
    }

    // -------------------------------------------------------------------------
    // Hash-chained Append-Only JSONL Ledger (`ledger/events.jsonl`)
    // -------------------------------------------------------------------------

    pub fn read_ledger(&self) -> Result<Vec<LedgerEvent>> {
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
        let mut expected_prev = "0".repeat(64);
        for ev in &events {
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

    pub fn append_ledger(
        &self,
        event_type: &str,
        entity_id: &str,
        summary: &str,
        payload: serde_json::Value,
    ) -> Result<LedgerEvent> {
        let existing = self.read_ledger()?;
        let seq = existing.len() + 1;
        let prev_hash = existing
            .last()
            .map(|e| e.event_hash.clone())
            .unwrap_or_else(|| "0".repeat(64));
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

        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.ledger_path)?;
        writeln!(file, "{}", serde_json::to_string(&ev)?)?;
        Ok(ev)
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
        let conn = self.conn()?;
        conn.execute(
            "INSERT OR REPLACE INTO campaigns (id, title, state, aim_statement, target_repo, updated_at)
             VALUES (?1, ?2, ?3, ?4, ?5, ?6)",
            params![id, title, initial, aim_statement, target_repo, now],
        )?;
        let row = CampaignRow {
            id: id.to_string(),
            title: title.to_string(),
            state: initial.clone(),
            aim_statement: aim_statement.to_string(),
            target_repo: target_repo.to_string(),
            updated_at: now,
        };
        self.append_ledger(
            "campaign.created",
            id,
            &format!("Campaign `{title}` initialized in `{initial}`"),
            serde_json::to_value(&row)?,
        )?;
        Ok(row)
    }

    pub fn transition_campaign(
        &self,
        id: &str,
        to_state: &str,
        guard_passed: bool,
        evidence: &str,
    ) -> std::result::Result<CampaignRow, StateRefusal> {
        let conn = self.conn().expect("sqlite connection");
        let cur: Option<(String, String, String, String)> = conn
            .query_row(
                "SELECT title, state, aim_statement, target_repo FROM campaigns WHERE id = ?1",
                params![id],
                |r| Ok((r.get(0)?, r.get(1)?, r.get(2)?, r.get(3)?)),
            )
            .optional()
            .expect("query campaign");

        let Some((title, from_state, aim_statement, target_repo)) = cur else {
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

        if let Some(ref g) = tr.guard {
            if !guard_passed {
                return Err(StateRefusal::GuardFailed {
                    guard: g.clone(),
                    reason: format!("campaign `{id}` transition `{from_state}` -> `{to_state}` requires guard {g}"),
                });
            }
        }

        let now = Utc::now().to_rfc3339();
        conn.execute(
            "UPDATE campaigns SET state = ?1, updated_at = ?2 WHERE id = ?3",
            params![to_state, now, id],
        )
        .expect("update campaign");

        let updated = CampaignRow {
            id: id.to_string(),
            title,
            state: to_state.to_string(),
            aim_statement,
            target_repo,
            updated_at: now,
        };
        let _ = self.append_ledger(
            "campaign.transition",
            id,
            &format!("Campaign `{id}`: `{from_state}` -> `{to_state}` ({evidence})"),
            serde_json::json!({ "from": from_state, "to": to_state, "evidence": evidence }),
        );
        Ok(updated)
    }

    pub fn create_quest(
        &self,
        id: &str,
        campaign_id: &str,
        title: &str,
        holder_agent: &str,
        target_regime: &str,
    ) -> Result<QuestRow> {
        let now = Utc::now().to_rfc3339();
        let initial = self.spec.machines.quest.initial.clone();
        let conn = self.conn()?;
        conn.execute(
            "INSERT OR REPLACE INTO quests
             (id, campaign_id, title, state, is_sink, prior_state, holder_agent, target_regime, tooth_witness, updated_at)
             VALUES (?1, ?2, ?3, ?4, 0, NULL, ?5, ?6, NULL, ?7)",
            params![id, campaign_id, title, initial, holder_agent, target_regime, now],
        )?;
        let row = QuestRow {
            id: id.to_string(),
            campaign_id: campaign_id.to_string(),
            title: title.to_string(),
            state: initial.clone(),
            is_sink: false,
            prior_state: None,
            holder_agent: holder_agent.to_string(),
            target_regime: target_regime.to_string(),
            tooth_witness: None,
            updated_at: now,
        };
        self.append_ledger(
            "quest.created",
            id,
            &format!("Quest `{id}` ({title}) created in `{initial}` [regime={target_regime}]"),
            serde_json::to_value(&row)?,
        )?;
        Ok(row)
    }

    pub fn transition_quest(
        &self,
        id: &str,
        to_state: &str,
        actor: &str,
        remedial_action: Option<&str>,
        tooth_witness: Option<&str>,
        guard_passed: bool,
    ) -> std::result::Result<QuestRow, StateRefusal> {
        let conn = self.conn().expect("sqlite connection");
        let cur: Option<QuestRow> = conn
            .query_row(
                "SELECT id, campaign_id, title, state, is_sink, prior_state, holder_agent, target_regime, tooth_witness, updated_at
                 FROM quests WHERE id = ?1",
                params![id],
                |r| {
                    Ok(QuestRow {
                        id: r.get(0)?,
                        campaign_id: r.get(1)?,
                        title: r.get(2)?,
                        state: r.get(3)?,
                        is_sink: r.get::<_, i64>(4)? != 0,
                        prior_state: r.get(5)?,
                        holder_agent: r.get(6)?,
                        target_regime: r.get(7)?,
                        tooth_witness: r.get(8)?,
                        updated_at: r.get(9)?,
                    })
                },
            )
            .optional()
            .expect("query quest");

        let Some(q) = cur else {
            return Err(StateRefusal::IllegalTransition {
                machine: "quest".into(),
                id: id.into(),
                from: "<missing>".into(),
                to: to_state.into(),
            });
        };

        let now = Utc::now().to_rfc3339();
        let entering_sink = self.spec.machines.quest.sinks.iter().any(|s| s == to_state);

        // Case 1: Entering one of the 18 frustration sinks
        if entering_sink {
            if !self.spec.can_quest_enter_sink(&q.state, to_state) {
                return Err(StateRefusal::IllegalTransition {
                    machine: "quest".into(),
                    id: id.into(),
                    from: q.state,
                    to: to_state.into(),
                });
            }
            let prior = if q.is_sink {
                q.prior_state.clone()
            } else {
                Some(q.state.clone())
            };
            conn.execute(
                "UPDATE quests SET state = ?1, is_sink = 1, prior_state = ?2, updated_at = ?3 WHERE id = ?4",
                params![to_state, prior, now, id],
            )
            .expect("enter sink");
            let out = QuestRow {
                state: to_state.to_string(),
                is_sink: true,
                prior_state: prior,
                updated_at: now,
                ..q
            };
            let _ = self.append_ledger(
                "quest.sink_entered",
                id,
                &format!("Quest `{id}` entered sink `{to_state}`"),
                serde_json::to_value(&out).unwrap_or_default(),
            );
            return Ok(out);
        }

        // Case 2: Exiting a sink (`sink_exit_rule`: holder agent must execute the sink's remedial action)
        if q.is_sink {
            let required_exit = self
                .spec
                .sinks
                .get(&q.state)
                .map(|s| s.exit.clone())
                .unwrap_or_else(|| "remediate".to_string());
            let act = remedial_action.unwrap_or("");
            if actor != q.holder_agent || act.trim().is_empty() {
                return Err(StateRefusal::SinkExitViolation {
                    id: id.to_string(),
                    sink: q.state,
                    required_exit,
                    holder: q.holder_agent,
                    actor: actor.to_string(),
                    action: act.to_string(),
                });
            }
            let valid_target = self.spec.machines.quest.states.iter().any(|s| s == to_state);
            if !valid_target {
                return Err(StateRefusal::IllegalTransition {
                    machine: "quest".into(),
                    id: id.into(),
                    from: q.state,
                    to: to_state.into(),
                });
            }
            conn.execute(
                "UPDATE quests SET state = ?1, is_sink = 0, prior_state = NULL, updated_at = ?2 WHERE id = ?3",
                params![to_state, now, id],
            )
            .expect("exit sink");
            let out = QuestRow {
                state: to_state.to_string(),
                is_sink: false,
                prior_state: None,
                updated_at: now,
                ..q
            };
            let _ = self.append_ledger(
                "quest.sink_exited",
                id,
                &format!("Quest `{id}` exited sink to `{to_state}` via `{act}` by `{actor}`"),
                serde_json::json!({ "to": to_state, "actor": actor, "remedial_action": act }),
            );
            return Ok(out);
        }

        // Case 3: Normal forward progression (`Grounded -> Framed -> Disputed -> Judged -> Toothed -> Built -> Landed -> Recorded`)
        let Some(tr) = self.spec.find_quest_transition(&q.state, to_state) else {
            return Err(StateRefusal::IllegalTransition {
                machine: "quest".into(),
                id: id.into(),
                from: q.state,
                to: to_state.into(),
            });
        };

        if let Some(ref g) = tr.guard {
            if !guard_passed {
                return Err(StateRefusal::GuardFailed {
                    guard: g.clone(),
                    reason: format!(
                        "quest `{id}` transition `{}` -> `{to_state}` failed guard `{g}`",
                        q.state
                    ),
                });
            }
            if g == "Q4" && tooth_witness.is_none() && q.tooth_witness.is_none() {
                return Err(StateRefusal::GuardFailed {
                    guard: "Q4".into(),
                    reason: format!(
                        "quest `{id}` cannot enter `Toothed` without an explicit planted-fault `tooth_witness`"
                    ),
                });
            }
        }

        let merged_tooth = tooth_witness
            .map(str::to_string)
            .or_else(|| q.tooth_witness.clone());
        conn.execute(
            "UPDATE quests SET state = ?1, tooth_witness = ?2, updated_at = ?3 WHERE id = ?4",
            params![to_state, merged_tooth, now, id],
        )
        .expect("update quest");

        let out = QuestRow {
            state: to_state.to_string(),
            tooth_witness: merged_tooth,
            updated_at: now,
            ..q
        };
        let _ = self.append_ledger(
            "quest.transition",
            id,
            &format!("Quest `{id}` moved to `{to_state}`"),
            serde_json::to_value(&out).unwrap_or_default(),
        );
        Ok(out)
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
        let conn = self.conn().expect("sqlite connection");
        conn.execute(
            "INSERT INTO ember_queue (kind, subject_id, prompt, resolved, resolution, created_at)
             VALUES (?1, ?2, ?3, 0, NULL, ?4)",
            params![kind, subject_id, prompt, now],
        )
        .expect("insert ember event");
        let id = conn.last_insert_rowid();
        let row = EmberEventRow {
            id,
            kind: kind.to_string(),
            subject_id: subject_id.to_string(),
            prompt: prompt.to_string(),
            resolved: false,
            resolution: None,
            created_at: now,
        };
        let _ = self.append_ledger(
            &format!("ember.{kind}"),
            subject_id,
            prompt,
            serde_json::to_value(&row).unwrap_or_default(),
        );
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
        let initial = self.spec.machines.segment.initial.clone(); // "Fresh"
        let conn = self.conn().expect("sqlite connection");
        conn.execute(
            "INSERT OR REPLACE INTO segments
             (id, quest_id, parent_id, state, model_tier, host, token_count, transcript_mode, distill_hash, notes, updated_at)
             VALUES (?1, ?2, NULL, ?3, ?4, ?5, 0, 'full', NULL, ?6, ?7)",
            params![id, quest_id, initial, model_tier, host, notes, now],
        )
        .expect("insert segment");
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
            updated_at: now,
        };
        let _ = self.append_ledger(
            "segment.new",
            id,
            &format!("Segment `{id}` created on `{host}` ({model_tier})"),
            serde_json::to_value(&row).unwrap_or_default(),
        );
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
                // If Fresh -> Pressured in one jump, step Fresh -> Working -> Pressured
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
        self.save_segment(&seg);
        let _ = self.append_ledger(
            "segment.continue",
            id,
            &format!("Segment `{id}` continued ({} tokens, state `{}`)", seg.token_count, seg.state),
            serde_json::to_value(&seg).unwrap_or_default(),
        );
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
        // Allow Working -> Pressured -> Distilled or Pressured -> Distilled
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
        self.save_segment(&seg);
        let _ = self.append_ledger(
            "segment.distill",
            id,
            &format!("Segment `{id}` distilled (sha256={})", &digest[..12]),
            serde_json::to_value(&seg).unwrap_or_default(),
        );
        Ok(seg)
    }

    /// Fork segment `parent_id` into `child_id` enforcing `S4` (no large-context fork without distill)
    /// and `S5` (handoff-tax direction: `downshift` keeps `full` transcript; `escalate` requires `compacted` prefix).
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

        // Guard S4: large-context fork prohibited unless Distilled!
        if parent.token_count > SEGMENT_FORK_TOKEN_CAP && parent.state != "Distilled" {
            return Err(StateRefusal::LargeContextFork {
                seg_id: parent.id,
                tokens: parent.token_count,
                cap: SEGMENT_FORK_TOKEN_CAP,
                state: parent.state,
            });
        }

        // Guard S5: handoff-tax direction (`DESIGN.md` §4.2, `PROCESS.md` S5)
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
        self.save_segment(&parent);

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
            updated_at: now,
        };
        self.insert_segment(&child);
        let _ = self.append_ledger(
            "segment.fork",
            child_id,
            &format!(
                "Segment `{child_id}` forked from `{parent_id}` ({handoff_direction}, mode={transcript_mode})"
            ),
            serde_json::to_value(&child).unwrap_or_default(),
        );
        Ok(child)
    }

    pub fn seg_merge(&self, id: &str, into_id: &str) -> std::result::Result<SegmentRow, StateRefusal> {
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
        self.save_segment(&seg);
        let _ = self.append_ledger(
            "segment.merge",
            id,
            &format!("Segment `{id}` merged into `{into_id}`"),
            serde_json::to_value(&seg).unwrap_or_default(),
        );
        Ok(seg)
    }

    pub fn seg_forget(&self, id: &str, reason: &str) -> std::result::Result<SegmentRow, StateRefusal> {
        let mut seg = self.get_segment(id)?;
        seg.state = "Retired".to_string();
        seg.transcript_mode = "forgotten-prefix".to_string();
        seg.notes = format!("retired/forgotten: {reason}");
        seg.updated_at = Utc::now().to_rfc3339();
        self.save_segment(&seg);
        let _ = self.append_ledger(
            "segment.forget",
            id,
            &format!("Segment `{id}` retired (`forget`: {reason})"),
            serde_json::to_value(&seg).unwrap_or_default(),
        );
        Ok(seg)
    }

    pub fn seg_adopt(
        &self,
        id: &str,
        quest_id: &str,
        session_path: &str,
        host: &str,
    ) -> std::result::Result<SegmentRow, StateRefusal> {
        let approx_tokens = fs::metadata(session_path)
            .map(|m| m.len() / 4)
            .unwrap_or(4_000);
        let mut row = self.seg_new(
            id,
            quest_id,
            "adopted-session",
            host,
            &format!("adopted from {session_path}"),
        )?;
        row.state = "Working".to_string();
        row.token_count = approx_tokens;
        self.save_segment(&row);
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
            "SELECT id, quest_id, parent_id, state, model_tier, host, token_count, transcript_mode, distill_hash, notes, updated_at
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
                    updated_at: r.get(10)?,
                })
            })?
            .collect::<std::result::Result<Vec<_>, _>>()?;
        Ok(rows)
    }

    fn get_segment(&self, id: &str) -> std::result::Result<SegmentRow, StateRefusal> {
        let conn = self.conn().expect("sqlite connection");
        let row = conn
            .query_row(
                "SELECT id, quest_id, parent_id, state, model_tier, host, token_count, transcript_mode, distill_hash, notes, updated_at
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
                        updated_at: r.get(10)?,
                    })
                },
            )
            .optional()
            .expect("query segment");
        row.ok_or_else(|| StateRefusal::IllegalTransition {
            machine: "segment".into(),
            id: id.into(),
            from: "<missing>".into(),
            to: "<any>".into(),
        })
    }

    fn insert_segment(&self, s: &SegmentRow) {
        let conn = self.conn().expect("sqlite connection");
        conn.execute(
            "INSERT OR REPLACE INTO segments
             (id, quest_id, parent_id, state, model_tier, host, token_count, transcript_mode, distill_hash, notes, updated_at)
             VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11)",
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
                s.updated_at
            ],
        )
        .expect("insert segment");
    }

    fn save_segment(&self, s: &SegmentRow) {
        self.insert_segment(s);
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
        let conn = self.conn().expect("sqlite connection");
        let row: Option<(i64, f64)> = conn
            .query_row(
                "SELECT reachable, avail_gb FROM machines WHERE host = ?1",
                params![host],
                |r| Ok((r.get(0)?, r.get(1)?)),
            )
            .optional()
            .expect("query machine");
        if let Some((reachable, avail_gb)) = row {
            if reachable != 0 && avail_gb < DISK_FREE_FLOOR_GB {
                return Err(StateRefusal::DiskHeadroomFloor {
                    host: host.to_string(),
                    avail_gb,
                    floor_gb: DISK_FREE_FLOOR_GB,
                });
            }
        }
        Ok(())
    }

    /// Probe local workspace disk headroom (`df -Pk`) and optionally remote SSH hosts (`hbox`, `bb2`).
    pub fn probe_machines(&self, include_remotes: bool) -> Result<Vec<MachineStatus>> {
        let mut results = Vec::new();
        let now = Utc::now().to_rfc3339();

        // 1. Local host
        let local_status = match Command::new("df")
            .arg("-Pk")
            .arg(&self.workspace_root)
            .output()
        {
            Ok(out) if out.status.success() => {
                let s = String::from_utf8_lossy(&out.stdout);
                let (avail_gb, total_gb) = parse_df_pk(&s).unwrap_or((100.0, 500.0));
                MachineStatus {
                    host: "local".to_string(),
                    reachable: true,
                    required_for_dispatch: true,
                    avail_gb,
                    total_gb,
                    load_summary: "local workspace".to_string(),
                    below_floor: avail_gb < DISK_FREE_FLOOR_GB,
                    checked_at: now.clone(),
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

        // 2. Remote build machines (`hbox`, `bb2` per `MACHINES.md`)
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
                    .filter(|l| !l.trim().is_empty())
                    .count()
            })
            .unwrap_or(0);

        let stranded_count = Command::new(bin)
            .args(["--frozen", "lanes", "--stranded"])
            .output()
            .map(|o| {
                String::from_utf8_lossy(&o.stdout)
                    .lines()
                    .filter(|l| !l.trim().is_empty() && !l.to_ascii_lowercase().contains("no stranded"))
                    .count()
            })
            .unwrap_or(0);

        let deferrals_open = Command::new(bin)
            .args(["--frozen", "deferrals"])
            .output()
            .map(|o| {
                String::from_utf8_lossy(&o.stdout)
                    .lines()
                    .filter(|l| !l.trim().is_empty() && !l.to_ascii_lowercase().contains("none"))
                    .count()
            })
            .unwrap_or(0);

        CvProbeReport {
            cv_bin: bin.to_string_lossy().to_string(),
            available: true,
            g1_whole_read_events: events_count,
            s2_doctor_ok: doctor_ok,
            s6_stranded_lanes: stranded_count,
            deferrals_open,
            summary: format!(
                "doctor_ok={doctor_ok}, events={events_count}, stranded_lanes={stranded_count}, deferrals={deferrals_open}"
            ),
        }
    }

    /// Probe git repository cleanliness (`Q5`: clean working tree, 0 `git stash` entries, 0 surviving merged side-branches).
    pub fn probe_git_q5(repo_root: &Path) -> Result<GitProbeReport> {
        let status_out = Command::new("git")
            .args(["--no-optional-locks", "-C"])
            .arg(repo_root)
            .args(["status", "--porcelain"])
            .output()
            .context("failed to run `git status --porcelain`")?;
        let modified_paths: Vec<String> = String::from_utf8_lossy(&status_out.stdout)
            .lines()
            .filter(|l| !l.trim().is_empty())
            .map(|l| l.trim().to_string())
            .collect();

        let stash_out = Command::new("git")
            .args(["--no-optional-locks", "-C"])
            .arg(repo_root)
            .args(["stash", "list"])
            .output()
            .context("failed to run `git stash list`")?;
        let stash_count = String::from_utf8_lossy(&stash_out.stdout)
            .lines()
            .filter(|l| !l.trim().is_empty())
            .count();

        let branch_out = Command::new("git")
            .args(["--no-optional-locks", "-C"])
            .arg(repo_root)
            .args(["rev-parse", "--abbrev-ref", "HEAD"])
            .output()?;
        let current_branch = String::from_utf8_lossy(&branch_out.stdout)
            .trim()
            .to_string();

        let merged_out = Command::new("git")
            .args(["--no-optional-locks", "-C"])
            .arg(repo_root)
            .args(["branch", "--merged", "HEAD", "--format=%(refname:short)"])
            .output()?;
        let merged_side_branches: Vec<String> = String::from_utf8_lossy(&merged_out.stdout)
            .lines()
            .map(str::trim)
            .filter(|b| {
                !b.is_empty()
                    && *b != current_branch
                    && !matches!(*b, "main" | "master" | "dev")
            })
            .map(str::to_string)
            .collect();

        let clean_working_tree = modified_paths.is_empty();
        let q5_passed =
            clean_working_tree && stash_count == 0 && merged_side_branches.is_empty();

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
            "SELECT id, title, state, aim_statement, target_repo, updated_at FROM campaigns ORDER BY id",
        )?;
        let campaigns: Vec<CampaignRow> = c_stmt
            .query_map([], |r| {
                Ok(CampaignRow {
                    id: r.get(0)?,
                    title: r.get(1)?,
                    state: r.get(2)?,
                    aim_statement: r.get(3)?,
                    target_repo: r.get(4)?,
                    updated_at: r.get(5)?,
                })
            })?
            .collect::<std::result::Result<Vec<_>, _>>()?;

        let mut q_stmt = conn.prepare(
            "SELECT id, campaign_id, title, state, is_sink, prior_state, holder_agent, target_regime, tooth_witness, updated_at
             FROM quests ORDER BY id",
        )?;
        let quests: Vec<QuestRow> = q_stmt
            .query_map([], |r| {
                Ok(QuestRow {
                    id: r.get(0)?,
                    campaign_id: r.get(1)?,
                    title: r.get(2)?,
                    state: r.get(3)?,
                    is_sink: r.get::<_, i64>(4)? != 0,
                    prior_state: r.get(5)?,
                    holder_agent: r.get(6)?,
                    target_regime: r.get(7)?,
                    tooth_witness: r.get(8)?,
                    updated_at: r.get(9)?,
                })
            })?
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
            }
        }
        let scheduler_paused = !pause_reasons.is_empty();

        let all_ledger = self.read_ledger()?;
        let start = all_ledger.len().saturating_sub(25);
        let recent_ledger = all_ledger[start..].to_vec();

        Ok(StateSnapshot {
            workspace_root: self.workspace_root.to_string_lossy().to_string(),
            scheduler_paused,
            pause_reasons,
            campaigns,
            quests,
            segments,
            waiting_on_ember,
            machines,
            recent_ledger,
        })
    }

    /// Seed a realistic Campaign / Quest / Segment graph reflecting `obend`'s live situation
    /// (`DESIGN.md` §6 Milestone 1: "Write a static segment tree for obend's current situation by hand; render it").
    pub fn seed_obend_campaign(&self, obend_repo: &Path) -> Result<StateSnapshot> {
        let _ = self.probe_machines(false)?;
        let _ = self.create_campaign(
            "C1-obend-reground",
            "Obend Epistemic Regrounding & Process Harness",
            "Every load-bearing Obend claim has a tooth, an independent spec, and zero cross-language mirrors.",
            &obend_repo.to_string_lossy(),
        )?;
        let _ = self.transition_campaign("C1-obend-reground", "Grounded", true, "G1 whole-read of obend completed");
        let _ = self.transition_campaign("C1-obend-reground", "Running", true, "G2 DESIGN.md + G4 g0-obebuilder active");

        // W1-A: Branch convergence
        let _ = self.create_quest(
            "W1-A",
            "C1-obend-reground",
            "Branch Convergence & Stash Elimination in obend",
            "lane-w1a",
            "decided",
        )?;
        let _ = self.transition_quest("W1-A", "Scoped", "lane-w1a", None, None, true);

        // W1-B: obebuilder harness (this lane!)
        let _ = self.create_quest(
            "W1-B",
            "C1-obend-reground",
            "Build `obb` Metaharness (`lint`, `judge`, `state`, `serve`)",
            "lane-w1b",
            "decided",
        )?;
        let _ = self.transition_quest("W1-B", "Scoped", "lane-w1b", None, None, true);
        let _ = self.transition_quest("W1-B", "Built", "lane-w1b", None, None, true);
        let _ = self.transition_quest("W1-B", "Wired", "lane-w1b", None, None, true);
        let _ = self.transition_quest(
            "W1-B",
            "Toothed",
            "lane-w1b",
            None,
            Some("crates/obb-cli/tests/planted_faults.rs"),
            true,
        );

        // W1-C: DESIGN.md hallucinated constructor cleanup (currently in `Label` sink from `Wired` in obend)
        let _ = self.create_quest(
            "W1-C",
            "C1-obend-reground",
            "Synchronize `DESIGN.md` Term Former & Quantity Tables with `Obend/Core/`",
            "lane-docs",
            "certified",
        )?;
        let _ = self.transition_quest("W1-C", "Scoped", "lane-docs", None, None, true);
        let _ = self.transition_quest("W1-C", "Built", "lane-docs", None, None, true);
        let _ = self.transition_quest("W1-C", "Wired", "lane-docs", None, None, true);
        let _ = self.transition_quest("W1-C", "Label", "lane-docs", None, None, true);

        // W1-D: SiliconElab & Hybrid Judge theatrical proofs (currently in `Theater` sink from `Built` in obend)
        let _ = self.create_quest(
            "W1-D",
            "C1-obend-reground",
            "Eliminate Discarded `z1` Tactics & Tautological `Judge.Meaning`",
            "lane-lean",
            "decided",
        )?;
        let _ = self.transition_quest("W1-D", "Scoped", "lane-lean", None, None, true);
        let _ = self.transition_quest("W1-D", "Built", "lane-lean", None, None, true);
        let _ = self.transition_quest("W1-D", "Theater", "lane-lean", None, None, true);

        // W1-E: Rust/Python E2E semantic mirrors (currently in `Mirror` sink from `Built` in obend)
        let _ = self.create_quest(
            "W1-E",
            "C1-obend-reground",
            "Replace Python E2E Self-Mocks & Rust Semantic Mirrors with `libobend` FFI",
            "lane-seam",
            "decided",
        )?;
        let _ = self.transition_quest("W1-E", "Scoped", "lane-seam", None, None, true);
        let _ = self.transition_quest("W1-E", "Built", "lane-seam", None, None, true);
        let _ = self.transition_quest("W1-E", "Mirror", "lane-seam", None, None, true);

        // Segments
        let _ = self.seg_new("seg-root-audit", "W1-B", "pro", "local", "Whole-read audit of obend corpus");
        let _ = self.seg_continue("seg-root-audit", 28_000, "Indexed SiliconElab, Hybrid, DESIGN.md, E2E mocks");
        let _ = self.seg_distill("seg-root-audit", "Distilled 5 defect families into obb-lint & judge.json");
        let _ = self.seg_fork(
            "seg-root-audit",
            "seg-w1b-impl",
            "pro",
            "local",
            "escalate",
            "compacted",
        );

        // One legitimate taste question queued for ember
        let _ = self.enqueue_ember_event(
            "taste",
            "W1-C",
            "Should `DESIGN.md` §1.1 list only current `Obend/Core/Term.lean` constructors, or generate the table mechanically via `lake exe docs-table`?",
        );

        self.snapshot()
    }
}

fn parse_df_pk(df_stdout: &str) -> Option<(f64, f64)> {
    // `df -Pk` line 2: Filesystem 1024-blocks Used Available Capacity Mounted-on
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
