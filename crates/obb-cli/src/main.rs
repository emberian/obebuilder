//! `obb` — Process Supervisor, Mechanical Anti-Slop Linter & Non-Regression Judge (`DESIGN.md` §6).

use anyhow::{Result, bail};
use clap::{Parser, Subcommand};
use obb_cli::serve::run_server;
use obb_judge::{
    Gate, TrustBase, check_revert_clean, check_succeed, check_well_formed, evaluate_gate,
};
use obb_lint::spec_check::run_spec_sensitivity_check;
use obb_lint::{filter_report_by_rule, run_repo_lints};
use obb_state::StateStore;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

#[derive(Parser, Debug)]
#[command(
    name = "obb",
    version,
    about = "Obebuilder metaharness: anti-slop linter, genealogy judge, process statechart & visualizer"
)]
struct Cli {
    /// Workspace root containing `judge.json`, `spec/process.json`, `.obb/`, and `ledger/`
    #[arg(long, global = true, default_value = ".")]
    workspace: PathBuf,

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

        #[command(subcommand)]
        sub: Option<LintSubcommand>,
    },

    /// Process Judge as a Value & machine-checked G4 non-regression (`JUDGE.md`)
    Judge {
        #[command(subcommand)]
        sub: JudgeSubcommand,
    },

    /// Campaign & Quest statechart supervisor + live `cv` / disk / git guards (`PROCESS.md`)
    State {
        #[command(subcommand)]
        sub: StateSubcommand,
    },

    /// First-class Segment lifecycle (`new`, `fork`, `continue`, `distill`, `merge`, `forget`, `adopt`, `compare`, `list`)
    Seg {
        #[command(subcommand)]
        sub: SegSubcommand,
    },

    /// Append-only hash-chained JSONL ledger (`ledger/events.jsonl`)
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
enum JudgeSubcommand {
    /// Evaluate current `judge.json` floors against `--repo` (read-only)
    Check {
        #[arg(long)]
        judge: Option<PathBuf>,

        #[arg(long, default_value = ".")]
        repo: PathBuf,

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

        /// Replace `<judge>` on disk and record `LobCost` to `ledger/events.jsonl` if accepted
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
    /// Initialize `.obb/state.db` and `ledger/events.jsonl`
    Init,

    /// Seed the realistic `obend` Campaign/Quest/Segment tree (`DESIGN.md` §6 Milestone 1)
    SeedObend {
        #[arg(long, default_value = "/Users/ember/dev/obend")]
        repo: PathBuf,
    },

    /// Show full Campaign, Quest, Segment, Ember-Queue, and Machine headroom snapshot
    Status {
        #[arg(long)]
        json: bool,
    },

    /// Create or transition a Campaign
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
    },

    /// Create or transition a Quest (enforcing `spec/process.json` + 18 sinks + `sink_exit_rule`)
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

    /// Verify SHA-256 hash chain integrity of `ledger/events.jsonl`
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
            sub,
        } => {
            if let Some(LintSubcommand::SpecCheck {
                lean_root,
                changed,
                transport_bin,
                json: spec_json,
            }) = sub
            {
                let res = run_spec_sensitivity_check(
                    &lean_root,
                    &changed,
                    transport_bin.as_deref(),
                )?;
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

            let mut report = run_repo_lints(&repo)?;
            if let Some(ref flt) = rule {
                report = filter_report_by_rule(report, flt);
            }

            if json {
                println!("{}", serde_json::to_string_pretty(&report)?);
            } else {
                print_human_lint_report(&report);
            }

            if strict && report.errors > 0 {
                Ok(ExitCode::from(2))
            } else {
                Ok(ExitCode::SUCCESS)
            }
        }

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

            JudgeSubcommand::Check { judge, repo, json } => {
                let jpath = resolve_judge_path(&cli.workspace, judge);
                let gate = Gate::load_from_path(&jpath)?;
                let rep = evaluate_gate(&gate, &repo)?;
                if json {
                    println!("{}", serde_json::to_string_pretty(&rep)?);
                } else {
                    println!(
                        "obb judge check: gate=`{}` repo=`{}` all_passed={}",
                        rep.judge_name, rep.repo_root, rep.all_passed
                    );
                    for ev in &rep.evaluations {
                        let tag = if ev.passed { "PASS" } else { "FAIL" };
                        println!(
                            "  [{tag}] {:<36} measured={:<4} bound={:<12} ({})",
                            ev.floor, ev.measured, ev.bound, ev.detail
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
                            let store = StateStore::open(&cli.workspace)?;
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
            let store = StateStore::open(&cli.workspace)?;
            match sub {
                StateSubcommand::Init => {
                    let _ = store.probe_machines(false)?;
                    println!(
                        "Initialized `.obb/state.db` and `ledger/events.jsonl` in {}",
                        cli.workspace.display()
                    );
                    Ok(ExitCode::SUCCESS)
                }
                StateSubcommand::SeedObend { repo } => {
                    let snap = store.seed_obend_campaign(&repo)?;
                    println!(
                        "Seeded campaign ({} quests, {} segments, {} ember events)",
                        snap.quests.len(),
                        snap.segments.len(),
                        snap.waiting_on_ember.len()
                    );
                    Ok(ExitCode::SUCCESS)
                }
                StateSubcommand::Status { json } => {
                    let snap = store.snapshot()?;
                    if json {
                        println!("{}", serde_json::to_string_pretty(&snap)?);
                    } else {
                        println!(
                            "Workspace: {} | scheduler_paused={}",
                            snap.workspace_root, snap.scheduler_paused
                        );
                        println!("Campaigns ({}):", snap.campaigns.len());
                        for c in &snap.campaigns {
                            println!("  - {} [{}]: {}", c.id, c.state, c.title);
                        }
                        println!("Quests ({}):", snap.quests.len());
                        for q in &snap.quests {
                            let sink_tag = if q.is_sink { " (SINK)" } else { "" };
                            println!(
                                "  - {} [{}{}] regime={} holder={}: {}",
                                q.id, q.state, sink_tag, q.target_regime, q.holder_agent, q.title
                            );
                        }
                        println!("Segments ({}):", snap.segments.len());
                        for s in &snap.segments {
                            println!(
                                "  - {} (quest={}, parent={}) [{}] tokens={} mode={} host={}",
                                s.id,
                                s.quest_id,
                                s.parent_id.as_deref().unwrap_or("-"),
                                s.state,
                                s.token_count,
                                s.transcript_mode,
                                s.host
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
                } => {
                    if let Some(target) = to {
                        let row = store
                            .transition_campaign(&id, &target, true, &evidence)
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
                } => {
                    if let Some(target) = to {
                        let row = store
                            .transition_quest(
                                &id,
                                &target,
                                &actor,
                                remedial_action.as_deref(),
                                tooth.as_deref(),
                                true,
                            )
                            .map_err(|e| anyhow::anyhow!(e.to_string()))?;
                        println!(
                            "Quest `{}` -> `{}` (sink={})",
                            row.id, row.state, row.is_sink
                        );
                    } else {
                        let row = store.create_quest(&id, &campaign, &title, &actor, &regime)?;
                        println!("Created quest `{}` in `{}`", row.id, row.state);
                    }
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
                    println!("Queued ember `{}` event #{} on `{}`", row.kind, row.id, row.subject_id);
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
                                m.host, m.reachable, m.avail_gb, m.total_gb, m.below_floor, m.load_summary
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
            let store = StateStore::open(&cli.workspace)?;
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
            let store = StateStore::open(&cli.workspace)?;
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
                                &ev.event_hash[..12]
                            );
                        }
                    }
                }
                LedgerSubcommand::Verify => {
                    let count = store.verify_ledger_chain()?;
                    println!("PASS ledger hash-chain verified ({count} event(s))");
                }
            }
            Ok(ExitCode::SUCCESS)
        }

        Commands::Serve { host, port, repo } => {
            let jpath = resolve_judge_path(&cli.workspace, None);
            if !jpath.is_file() {
                bail!("judge.json not found at {}", jpath.display());
            }
            run_server(&host, port, &cli.workspace, &repo, &jpath).await?;
            Ok(ExitCode::SUCCESS)
        }
    }
}

fn resolve_judge_path(workspace: &Path, explicit: Option<PathBuf>) -> PathBuf {
    explicit.unwrap_or_else(|| workspace.join("judge.json"))
}

fn print_human_lint_report(rep: &obb_core::LintReport) {
    println!(
        "obb lint: repo={} files_scanned={} lean_decls={} lean_inductives={}",
        rep.repo_root, rep.files_scanned, rep.lean_declarations_indexed, rep.lean_inductives_indexed
    );
    println!(
        "totals: {} findings ({} errors, {} warnings)",
        rep.total_findings, rep.errors, rep.warnings
    );

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
        let sink_str = f
            .sink
            .map(|s| format!(" sink={s}"))
            .unwrap_or_default();
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
