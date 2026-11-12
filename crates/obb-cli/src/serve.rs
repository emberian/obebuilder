//! Lightweight localhost visualizer (`obb serve`) for Campaign/Quest/Segment trees,
//! `judge.json` floors, machine disk headroom, and `obb lint` findings (`DESIGN.md` §5, `PROCESS.md` §5).

use anyhow::{Context, Result};
use axum::extract::State;
use axum::response::sse::{Event, KeepAlive, Sse};
use axum::response::{Html, IntoResponse, Json};
use axum::routing::get;
use axum::Router;
use obb_core::LintReport;
use obb_judge::{Gate, evaluate_gate};
use obb_lint::run_repo_lints;
use obb_state::StateStore;
use std::convert::Infallible;
use std::path::{Path, PathBuf};
use std::sync::{Arc, RwLock};
use std::time::Duration;
use tokio_stream::StreamExt;
use tokio_stream::wrappers::IntervalStream;

#[derive(Clone)]
pub struct ServeConfig {
    pub workspace_root: PathBuf,
    pub state_dir: Option<PathBuf>,
    pub target_repo: PathBuf,
    pub judge_path: PathBuf,
    pub cached_lint: Arc<RwLock<Option<LintReport>>>,
}

impl ServeConfig {
    pub fn new(workspace_root: PathBuf, target_repo: PathBuf, judge_path: PathBuf) -> Self {
        // Pre-load `reports/obend-baseline.json` if available so `/api/lints` is instant
        let baseline_path = workspace_root.join("reports/obend-baseline.json");
        let initial_lint = std::fs::read_to_string(&baseline_path)
            .ok()
            .and_then(|s| serde_json::from_str::<LintReport>(&s).ok());
        Self {
            workspace_root,
            state_dir: None,
            target_repo,
            judge_path,
            cached_lint: Arc::new(RwLock::new(initial_lint)),
        }
    }

    pub fn with_state_dir(mut self, state_dir: Option<PathBuf>) -> Self {
        self.state_dir = state_dir;
        self
    }
}

pub fn build_router(cfg: ServeConfig) -> Router {
    Router::new()
        .route("/", get(index_html))
        .route("/api/status", get(api_status))
        .route("/api/lints", get(api_lints))
        .route("/api/judge", get(api_judge))
        .route("/events", get(sse_events))
        .with_state(cfg)
}

pub async fn run_server(
    host: &str,
    port: u16,
    workspace_root: &Path,
    target_repo: &Path,
    judge_path: &Path,
) -> Result<()> {
    run_server_with_state_dir(host, port, workspace_root, None, target_repo, judge_path).await
}

pub async fn run_server_with_state_dir(
    host: &str,
    port: u16,
    workspace_root: &Path,
    state_dir: Option<&Path>,
    target_repo: &Path,
    judge_path: &Path,
) -> Result<()> {
    let store = StateStore::open_with_state_dir(workspace_root, state_dir)?;
    let snap = store.snapshot()?;
    if snap.campaigns.is_empty() {
        let _ = store.seed_obend_campaign(target_repo)?;
    }

    let cfg = ServeConfig::new(
        workspace_root.to_path_buf(),
        target_repo.to_path_buf(),
        judge_path.to_path_buf(),
    )
    .with_state_dir(state_dir.map(Path::to_path_buf));
    let app = build_router(cfg);
    let addr = format!("{host}:{port}");
    let listener = tokio::net::TcpListener::bind(&addr)
        .await
        .with_context(|| format!("failed to bind http://{addr}"))?;
    println!("obb serve listening on http://{addr}");
    axum::serve(listener, app).await?;
    Ok(())
}

async fn api_status(State(cfg): State<ServeConfig>) -> impl IntoResponse {
    match StateStore::open_with_state_dir(&cfg.workspace_root, cfg.state_dir.as_deref())
        .and_then(|s| s.snapshot())
    {
        Ok(snap) => Json(serde_json::to_value(snap).unwrap_or_default()),
        Err(e) => Json(serde_json::json!({ "error": e.to_string() })),
    }
}

async fn api_lints(State(cfg): State<ServeConfig>) -> impl IntoResponse {
    if let Some(cached) = cfg.cached_lint.read().unwrap().clone() {
        return Json(serde_json::to_value(cached).unwrap_or_default());
    }
    match run_repo_lints(&cfg.target_repo) {
        Ok(rep) => {
            *cfg.cached_lint.write().unwrap() = Some(rep.clone());
            Json(serde_json::to_value(rep).unwrap_or_default())
        }
        Err(e) => Json(serde_json::json!({ "error": e.to_string() })),
    }
}

async fn api_judge(State(cfg): State<ServeConfig>) -> impl IntoResponse {
    match Gate::load_from_path(&cfg.judge_path) {
        Ok(gate) => match evaluate_gate(&gate, &cfg.workspace_root) {
            Ok(eval) => Json(serde_json::json!({
                "gate": gate,
                "evaluation": eval,
            })),
            Err(e) => Json(serde_json::json!({
                "gate": gate,
                "evaluation_error": e.to_string(),
            })),
        },
        Err(e) => Json(serde_json::json!({ "error": e.to_string() })),
    }
}

async fn sse_events(
    State(cfg): State<ServeConfig>,
) -> Sse<impl tokio_stream::Stream<Item = std::result::Result<Event, Infallible>>> {
    let stream = IntervalStream::new(tokio::time::interval(Duration::from_secs(5))).map(move |_| {
        let payload = StateStore::open_with_state_dir(&cfg.workspace_root, cfg.state_dir.as_deref())
            .and_then(|s| s.snapshot())
            .map(|snap| serde_json::to_string(&snap).unwrap_or_else(|_| "{}".to_string()))
            .unwrap_or_else(|e| serde_json::json!({ "error": e.to_string() }).to_string());
        Ok(Event::default().event("status").data(payload))
    });
    Sse::new(stream).keep_alive(KeepAlive::default())
}

async fn index_html() -> Html<&'static str> {
    Html(DASHBOARD_HTML)
}

const DASHBOARD_HTML: &str = r#"<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <title>obb — Obebuilder Process & Epistemic Harness</title>
  <style>
    :root {
      --bg: #0d1117;
      --panel: #161b22;
      --border: #30363d;
      --fg: #e6edf3;
      --muted: #8b949e;
      --green: #3fb950;
      --amber: #d29922;
      --red: #f85149;
      --blue: #58a6ff;
      --purple: #bc8cff;
    }
    * { box-sizing: border-box; }
    body {
      margin: 0; padding: 20px 28px;
      background: var(--bg); color: var(--fg);
      font: 13px/1.5 ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace;
    }
    header {
      display: flex; justify-content: space-between; align-items: center;
      border-bottom: 1px solid var(--border); padding-bottom: 12px; margin-bottom: 18px;
    }
    h1 { font-size: 16px; margin: 0; letter-spacing: 0.4px; }
    h2 { font-size: 13px; text-transform: uppercase; color: var(--muted); margin: 0 0 10px 0; }
    .grid { display: grid; grid-template-columns: 1fr 1fr; gap: 16px; margin-bottom: 16px; }
    .card {
      background: var(--panel); border: 1px solid var(--border);
      border-radius: 6px; padding: 14px;
    }
    .badge {
      display: inline-block; padding: 1px 7px; border-radius: 12px;
      font-size: 11px; font-weight: 600; border: 1px solid var(--border);
    }
    .ok { color: var(--green); border-color: var(--green); }
    .sink, .err { color: var(--red); border-color: var(--red); }
    .warn { color: var(--amber); border-color: var(--amber); }
    .info { color: var(--blue); border-color: var(--blue); }
    table { width: 100%; border-collapse: collapse; font-size: 12px; }
    th, td { text-align: left; padding: 5px 8px; border-bottom: 1px solid var(--border); }
    th { color: var(--muted); font-weight: 600; }
    .muted { color: var(--muted); }
  </style>
</head>
<body>
  <header>
    <div>
      <h1>obb // Process Statechart, Genealogy Judge &amp; Anti-Slop Census</h1>
      <span class="muted" id="subtitle">connecting...</span>
    </div>
    <div id="sched-badge"></div>
  </header>

  <div class="grid">
    <div class="card">
      <h2>Waiting on ember (aim / decision / taste ONLY)</h2>
      <div id="ember-box">loading...</div>
    </div>
    <div class="card">
      <h2>Machine Disk &amp; Load Guard (20 GB Floor)</h2>
      <div id="machines-box">loading...</div>
    </div>
  </div>

  <div class="grid">
    <div class="card">
      <h2>Campaign &amp; Quests (PROCESS.md Statechart)</h2>
      <div id="quests-box">loading...</div>
    </div>
    <div class="card">
      <h2>Segment Tree (S4 Distill &amp; S5 Handoff Direction)</h2>
      <div id="segments-box">loading...</div>
    </div>
  </div>

  <div class="grid">
    <div class="card">
      <h2>Process Judge Floors &amp; Löb Basis (judge.json)</h2>
      <div id="judge-box">loading...</div>
    </div>
    <div class="card">
      <h2>obb lint Summary by Rule &amp; Directory</h2>
      <div id="lints-box">loading...</div>
    </div>
  </div>

  <script>
    function esc(s) {
      return String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
    }
    function renderStatus(snap) {
      document.getElementById('subtitle').textContent = `workspace: ${snap.workspace_root}`;
      const sb = document.getElementById('sched-badge');
      sb.innerHTML = snap.scheduler_paused
        ? `<span class="badge err">SCHEDULER PAUSED: ${esc(snap.pause_reasons.join('; '))}</span>`
        : `<span class="badge ok">SCHEDULER READY</span>`;

      const eb = document.getElementById('ember-box');
      if (!snap.waiting_on_ember || snap.waiting_on_ember.length === 0) {
        eb.innerHTML = '<span class="muted">0 open items for ember.</span>';
      } else {
        eb.innerHTML = '<table><tr><th>Kind</th><th>Subject</th><th>Prompt</th></tr>' +
          snap.waiting_on_ember.map(e =>
            `<tr><td><span class="badge warn">${esc(e.kind)}</span></td><td>${esc(e.subject_id)}</td><td>${esc(e.prompt)}</td></tr>`
          ).join('') + '</table>';
      }

      const mb = document.getElementById('machines-box');
      mb.innerHTML = '<table><tr><th>Host</th><th>Free GB</th><th>Status</th><th>Detail</th></tr>' +
        (snap.machines || []).map(m => {
          const cls = !m.reachable ? 'warn' : (m.below_floor ? 'err' : 'ok');
          const lbl = !m.reachable ? 'OFFLINE' : (m.below_floor ? '< 20 GB FLOOR' : 'OK');
          return `<tr><td>${esc(m.host)}</td><td>${m.avail_gb.toFixed(1)} / ${m.total_gb.toFixed(1)}</td><td><span class="badge ${cls}">${lbl}</span></td><td class="muted">${esc(m.load_summary)}</td></tr>`;
        }).join('') + '</table>';

      const qb = document.getElementById('quests-box');
      qb.innerHTML = '<table><tr><th>Quest</th><th>State</th><th>Regime</th><th>Holder</th><th>Title</th></tr>' +
        (snap.quests || []).map(q => {
          const cls = q.is_sink ? 'sink' : 'ok';
          return `<tr><td>${esc(q.id)}</td><td><span class="badge ${cls}">${esc(q.state)}</span></td><td><span class="badge info">${esc(q.target_regime)}</span></td><td>${esc(q.holder_agent)}</td><td>${esc(q.title)}</td></tr>`;
        }).join('') + '</table>';

      const sgb = document.getElementById('segments-box');
      sgb.innerHTML = '<table><tr><th>Segment</th><th>Quest</th><th>Parent</th><th>State</th><th>Tokens</th><th>Mode</th></tr>' +
        (snap.segments || []).map(s =>
          `<tr><td>${esc(s.id)}</td><td>${esc(s.quest_id)}</td><td class="muted">${esc(s.parent_id || '—')}</td><td><span class="badge info">${esc(s.state)}</span></td><td>${s.token_count}</td><td>${esc(s.transcript_mode)}</td></tr>`
        ).join('') + '</table>';
    }

    async function refreshAll() {
      const [st, jd, ln] = await Promise.all([
        fetch('/api/status').then(r => r.json()),
        fetch('/api/judge').then(r => r.json()),
        fetch('/api/lints').then(r => r.json())
      ]);
      if (!st.error) renderStatus(st);

      const jb = document.getElementById('judge-box');
      if (jd.evaluation) {
        jb.innerHTML = `<div style="margin-bottom:8px">Gate <b>${esc(jd.gate.name)}</b> | Basis: <code>${esc(jd.gate.basis.join(', '))}</code></div>` +
          '<table><tr><th>Floor</th><th>Measured</th><th>Bound</th><th>Pass</th></tr>' +
          jd.evaluation.evaluations.map(ev =>
            `<tr><td><code>${esc(ev.floor)}</code></td><td>${ev.measured}</td><td>${esc(ev.bound)}</td><td><span class="badge ${ev.passed ? 'ok' : 'err'}">${ev.passed ? 'PASS' : 'FAIL'}</span></td></tr>`
          ).join('') + '</table>';
      }

      const lb = document.getElementById('lints-box');
      if (ln && ln.by_rule) {
        const rules = Object.entries(ln.by_rule).sort((a,b) => b[1] - a[1]);
        lb.innerHTML = `<div style="margin-bottom:8px">Target: <code>${esc(ln.repo_root)}</code> — <b>${ln.total_findings}</b> findings (${ln.errors} errors, ${ln.warnings} warnings) across ${ln.files_scanned} files</div>` +
          '<table><tr><th>Rule</th><th>Count</th></tr>' +
          rules.map(([r, c]) => `<tr><td><code>${esc(r)}</code></td><td>${c}</td></tr>`).join('') +
          '</table>';
      }
    }

    refreshAll();
    const es = new EventSource('/events');
    es.addEventListener('status', ev => {
      try { renderStatus(JSON.parse(ev.data)); } catch (_) {}
    });
  </script>
</body>
</html>
"#;
