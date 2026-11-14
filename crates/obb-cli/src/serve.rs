//! Lightweight localhost visualizer (`obb serve`) for Campaign/Quest/Segment trees,
//! `judge.json` floors, machine disk headroom, and `obb lint` findings (`DESIGN.md` §5, `PROCESS.md` §5).

use anyhow::{Context, Result};
use axum::Router;
use axum::extract::{Request, State};
use axum::http::{Method, StatusCode, header};
use axum::middleware::{self, Next};
use axum::response::Response;
use axum::response::sse::{Event, KeepAlive, Sse};
use axum::response::{Html, IntoResponse, Json};
use axum::routing::get;
use obb_core::LintReport;
use obb_judge::{Gate, JudgeClock, evaluate_gate_on};
use obb_lint::run_repo_lints;
use obb_state::StateStore;
use sha2::{Digest, Sha256};
use std::convert::Infallible;
use std::path::{Path, PathBuf};
use std::time::Duration;
use subtle::ConstantTimeEq;
use tokio_stream::StreamExt;
use tokio_stream::wrappers::IntervalStream;

#[derive(Clone)]
pub struct ServeConfig {
    pub workspace_root: PathBuf,
    pub state_dir: Option<PathBuf>,
    pub target_repo: PathBuf,
    pub judge_path: PathBuf,
    bearer_digest: Option<[u8; 32]>,
}

impl ServeConfig {
    pub fn new(workspace_root: PathBuf, target_repo: PathBuf, judge_path: PathBuf) -> Self {
        Self {
            workspace_root,
            state_dir: None,
            target_repo,
            judge_path,
            bearer_digest: None,
        }
    }

    pub fn with_bearer_token(mut self, token: &str) -> Self {
        self.bearer_digest = if token.is_empty() {
            None
        } else {
            Some(Sha256::digest(token.as_bytes()).into())
        };
        self
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
        .layer(middleware::from_fn_with_state(
            cfg.clone(),
            validate_request,
        ))
        .with_state(cfg)
}

/// Bound every body, including chunked bodies, before invoking any application handler.
pub const MAX_BODY_BYTES: usize = 64 * 1024;

async fn validate_request(
    State(cfg): State<ServeConfig>,
    request: Request,
    next: Next,
) -> Response {
    if !matches!(*request.method(), Method::GET | Method::HEAD) {
        return (
            StatusCode::METHOD_NOT_ALLOWED,
            [(header::ALLOW, "GET, HEAD")],
        )
            .into_response();
    }
    // The HTML shell is public; repository/state data and SSE require a bearer token.
    if request.uri().path() != "/" {
        let Some(expected) = cfg.bearer_digest else {
            return StatusCode::SERVICE_UNAVAILABLE.into_response();
        };
        let mut values = request.headers().get_all(header::AUTHORIZATION).iter();
        let token = values
            .next()
            .and_then(|h| h.to_str().ok())
            .and_then(|h| h.strip_prefix("Bearer "));
        let valid = token
            .map(|t| {
                let actual: [u8; 32] = Sha256::digest(t.as_bytes()).into();
                bool::from(actual.ct_eq(&expected))
            })
            .unwrap_or(false);
        if !valid || values.next().is_some() {
            return (
                StatusCode::UNAUTHORIZED,
                [(header::WWW_AUTHENTICATE, "Bearer")],
            )
                .into_response();
        }
    }
    let mut types = request.headers().get_all(header::CONTENT_TYPE).iter();
    if let Some(value) = types.next()
        && (types.next().is_some()
            || value.to_str().ok().is_none_or(|v| {
                !matches!(
                    v.to_ascii_lowercase().as_str(),
                    "application/json" | "application/json; charset=utf-8"
                )
            }))
    {
        return StatusCode::UNSUPPORTED_MEDIA_TYPE.into_response();
    }
    if request
        .headers()
        .get(header::CONTENT_LENGTH)
        .and_then(|v| v.to_str().ok())
        .and_then(|v| v.parse::<usize>().ok())
        .is_some_and(|n| n > MAX_BODY_BYTES)
    {
        return StatusCode::PAYLOAD_TOO_LARGE.into_response();
    }
    let (parts, body) = request.into_parts();
    let bytes = match axum::body::to_bytes(body, MAX_BODY_BYTES).await {
        Ok(bytes) => bytes,
        Err(_) => return StatusCode::PAYLOAD_TOO_LARGE.into_response(),
    };
    if !bytes.is_empty() {
        return StatusCode::BAD_REQUEST.into_response();
    }
    next.run(Request::from_parts(parts, axum::body::Body::empty()))
        .await
}

pub async fn run_server(
    host: &str,
    port: u16,
    workspace_root: &Path,
    target_repo: &Path,
    judge_path: &Path,
) -> Result<()> {
    run_server_with_options(
        host,
        port,
        workspace_root,
        None,
        target_repo,
        judge_path,
        false,
    )
    .await
}

pub async fn run_server_with_state_dir(
    host: &str,
    port: u16,
    workspace_root: &Path,
    state_dir: Option<&Path>,
    target_repo: &Path,
    judge_path: &Path,
) -> Result<()> {
    run_server_with_options(
        host,
        port,
        workspace_root,
        state_dir,
        target_repo,
        judge_path,
        false,
    )
    .await
}

pub async fn run_server_with_options(
    host: &str,
    port: u16,
    workspace_root: &Path,
    state_dir: Option<&Path>,
    target_repo: &Path,
    judge_path: &Path,
    seed_demo: bool,
) -> Result<()> {
    let token = std::env::var("OBB_SERVE_TOKEN")
        .context("set OBB_SERVE_TOKEN to access the dashboard API")?;
    anyhow::ensure!(
        !token.trim().is_empty(),
        "OBB_SERVE_TOKEN must not be empty"
    );
    let store = StateStore::open_with_state_dir(workspace_root, state_dir)?;
    if seed_demo {
        let snap = store.snapshot()?;
        if snap.campaigns.is_empty() {
            let _ = store.seed_obend_campaign(target_repo)?;
        }
    }

    let cfg = ServeConfig::new(
        workspace_root.to_path_buf(),
        target_repo.to_path_buf(),
        judge_path.to_path_buf(),
    )
    .with_state_dir(state_dir.map(Path::to_path_buf))
    .with_bearer_token(&token);
    let app = build_router(cfg);
    let addr = format!("{host}:{port}");
    let listener = tokio::net::TcpListener::bind(&addr)
        .await
        .with_context(|| format!("failed to bind http://{addr}"))?;
    println!("obb serve listening on http://{addr}");
    axum::serve(listener, app).await?;
    Ok(())
}

/// Run filesystem / SQLite / git work off the async executor so one slow scan cannot stall
/// every other request and the SSE stream.
async fn blocking_json<F>(work: F) -> Json<serde_json::Value>
where
    F: FnOnce() -> serde_json::Value + Send + 'static,
{
    Json(
        tokio::task::spawn_blocking(work)
            .await
            .unwrap_or_else(|e| serde_json::json!({ "error": e.to_string() })),
    )
}

async fn api_status(State(cfg): State<ServeConfig>) -> impl IntoResponse {
    blocking_json(move || {
        match StateStore::open_with_state_dir(&cfg.workspace_root, cfg.state_dir.as_deref())
            .and_then(|s| s.snapshot())
        {
            Ok(snap) => serde_json::to_value(snap).unwrap_or_default(),
            Err(e) => serde_json::json!({ "error": e.to_string() }),
        }
    })
    .await
}

async fn api_lints(State(cfg): State<ServeConfig>) -> impl IntoResponse {
    blocking_json(move || {
        if !cfg.target_repo.is_dir() {
            return serde_json::json!({ "error": "lint target directory is unavailable", "source": "live" });
        }
        // Scan the target on every request, including dirty/untracked files. The baseline is
        // comparison data only; neither a committed report nor an old scan substitutes for it.
        match run_repo_lints(&cfg.target_repo) {
            Ok(rep) => {
                let baseline = [
                    cfg.target_repo.join("reports/obend-baseline.json"),
                    cfg.workspace_root.join("reports/obend-baseline.json"),
                ]
                .into_iter()
                .find_map(|path| {
                    let report: LintReport =
                        serde_json::from_slice(&std::fs::read(path).ok()?).ok()?;
                    let baseline_repo = Path::new(&report.repo_root).canonicalize().ok()?;
                    (Some(baseline_repo) == cfg.target_repo.canonicalize().ok()).then_some(report)
                });
                let delta = baseline.as_ref().map(|base| {
                    let rules: std::collections::BTreeSet<_> =
                        base.by_rule.keys().chain(rep.by_rule.keys()).collect();
                    let by_rule: std::collections::BTreeMap<_, _> = rules
                        .into_iter()
                        .map(|rule| {
                            (
                                rule,
                                *rep.by_rule.get(rule).unwrap_or(&0) as i128
                                    - *base.by_rule.get(rule).unwrap_or(&0) as i128,
                            )
                        })
                        .collect();
                    serde_json::json!({
                        "baseline_generated_at": base.generated_at,
                        "total_findings": rep.total_findings as i128 - base.total_findings as i128,
                        "errors": rep.errors as i128 - base.errors as i128,
                        "warnings": rep.warnings as i128 - base.warnings as i128,
                        "by_rule": by_rule,
                    })
                });
                let mut response = serde_json::to_value(&rep).unwrap_or_default();
                response["source"] = serde_json::json!("live");
                response["scanned_at"] = serde_json::json!(rep.generated_at);
                response["delta"] = serde_json::json!(delta);
                response
            }
            Err(e) => serde_json::json!({ "error": e.to_string(), "source": "live" }),
        }
    })
    .await
}

/// The dashboard polls this, so it runs on the construction clock: static floors only, with
/// executed teeth and revert merges listed under `deferred_floors` instead of re-run per poll.
async fn api_judge(State(cfg): State<ServeConfig>) -> impl IntoResponse {
    blocking_json(move || match Gate::load_from_path(&cfg.judge_path) {
        Ok(gate) => match evaluate_gate_on(&gate, &cfg.workspace_root, JudgeClock::Construction) {
            Ok(eval) => serde_json::json!({
                "gate": gate,
                "evaluation": eval,
            }),
            Err(e) => serde_json::json!({
                "gate": gate,
                "evaluation_error": e.to_string(),
            }),
        },
        Err(e) => serde_json::json!({ "error": e.to_string() }),
    })
    .await
}

async fn sse_events(
    State(cfg): State<ServeConfig>,
) -> Sse<impl tokio_stream::Stream<Item = std::result::Result<Event, Infallible>>> {
    let stream =
        IntervalStream::new(tokio::time::interval(Duration::from_secs(5))).map(move |_| {
            let payload =
                StateStore::open_with_state_dir(&cfg.workspace_root, cfg.state_dir.as_deref())
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
  <label>API token <input id="token" type="password" autocomplete="off" /></label> <button id="connect">Connect</button>
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
      document.getElementById('subtitle').textContent =
        `workspace: ${snap.workspace_root} | live_transitions=${snap.live_transition_count ?? 0} verified_quests=${snap.verified_quest_count ?? 0} demo_seed_events=${snap.demo_seed_event_count ?? 0}`;
      const sb = document.getElementById('sched-badge');
      const demoTag = snap.contains_demo_seed ? ' <span class="badge warn">DEMO SEED PRESENT</span>' : '';
      sb.innerHTML = (snap.scheduler_paused
        ? `<span class="badge err">SCHEDULER PAUSED: ${esc(snap.pause_reasons.join('; '))}</span>`
        : `<span class="badge ok">SCHEDULER READY</span>`) + demoTag;

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
      qb.innerHTML = '<table><tr><th>Quest</th><th>State</th><th>Effective</th><th>Target</th><th>Holder</th><th>Title</th></tr>' +
        (snap.quests || []).map(q => {
          const cls = q.is_sink ? 'sink' : (q.merged_ungated ? 'warn' : 'ok');
          const effCls = q.origin === 'demo_seed' || q.merged_ungated ? 'warn' : 'info';
          return `<tr><td>${esc(q.id)}</td><td><span class="badge ${cls}">${esc(q.state)}</span></td><td><span class="badge ${effCls}">${esc(q.effective_regime)}</span></td><td><span class="badge info">${esc(q.target_regime)}</span></td><td>${esc(q.holder_agent)}</td><td>${esc(q.title)}</td></tr>`;
        }).join('') + '</table>';

      const sgb = document.getElementById('segments-box');
      sgb.innerHTML = '<table><tr><th>Segment</th><th>Quest</th><th>Parent</th><th>State</th><th>Tokens</th><th>Mode</th></tr>' +
        (snap.segments || []).map(s =>
          `<tr><td>${esc(s.id)}</td><td>${esc(s.quest_id)}</td><td class="muted">${esc(s.parent_id || '—')}</td><td><span class="badge info">${esc(s.state)}</span></td><td>${s.token_count}</td><td>${esc(s.transcript_mode)}</td></tr>`
        ).join('') + '</table>';
    }

    let bearer = '';
    async function api(path) {
      const response = await fetch(path, {headers: {Authorization: `Bearer ${bearer}`}});
      if (!response.ok) throw new Error(`Request failed (${response.status})`);
      return response.json();
    }
    async function refreshAll() {
      const [st, jd, ln] = await Promise.all([
        api('/api/status'),
        api('/api/judge'),
        api('/api/lints')
      ]);
      if (st.error) document.getElementById('subtitle').textContent = `state unavailable: ${st.error}`;
      else renderStatus(st);

      const jb = document.getElementById('judge-box');
      if (jd.error || jd.evaluation_error) {
        jb.innerHTML = `<span class="badge err">JUDGE UNAVAILABLE</span> ${esc(jd.error || jd.evaluation_error)}`;
      } else if (jd.evaluation) {
        const deferred = jd.evaluation.deferred_floors || [];
        const deferredNote = deferred.length
          ? `<div class="muted" style="margin-bottom:8px">Not run here (convergence only, <code>obb judge check</code>): <code>${esc(deferred.join(', '))}</code></div>`
          : '';
        jb.innerHTML = `<div style="margin-bottom:8px">Gate <b>${esc(jd.gate.name)}</b> | Achieved: <span class="badge info">${esc(jd.evaluation.achieved_regime)}</span> | Basis: <code>${esc(jd.gate.basis.join(', '))}</code></div>` + deferredNote +
          '<table><tr><th>Floor</th><th>Regime</th><th>Measured</th><th>Bound</th><th>Pass</th></tr>' +
          jd.evaluation.evaluations.map(ev =>
            `<tr><td><code>${esc(ev.floor)}</code></td><td><span class="badge info">${esc(ev.regime)}</span></td><td>${ev.measured}</td><td>${esc(ev.bound)}</td><td><span class="badge ${ev.passed ? 'ok' : 'err'}">${ev.passed ? 'PASS' : 'FAIL'}</span></td></tr>`
          ).join('') + '</table>';
      }

      const lb = document.getElementById('lints-box');
      if (ln && ln.error) {
        lb.innerHTML = `<span class="badge err">LINT UNAVAILABLE</span> ${esc(ln.error)}`;
      } else if (ln && ln.by_rule) {
        const rules = Object.entries(ln.by_rule).sort((a,b) => b[1] - a[1]);
        lb.innerHTML = `<div style="margin-bottom:8px">Target: <code>${esc(ln.repo_root)}</code> — <b>${ln.total_findings}</b> findings (${ln.errors} errors, ${ln.warnings} warnings) across ${ln.files_scanned} files <span class="muted">(live scan ${esc(ln.scanned_at)})${ln.delta ? `; findings delta ${ln.delta.total_findings >= 0 ? '+' : ''}${ln.delta.total_findings} since ${esc(ln.delta.baseline_generated_at)}` : '; no matching baseline'}</span></div>` +
          '<table><tr><th>Rule</th><th>Count</th></tr>' +
          rules.map(([r, c]) => `<tr><td><code>${esc(r)}</code></td><td>${c}</td></tr>`).join('') +
          '</table>';
      }
    }

    document.getElementById('connect').onclick = async () => {
      bearer = document.getElementById('token').value;
      document.getElementById('token').value = '';
      try { await refreshAll(); } catch (error) { document.getElementById('subtitle').textContent = error.message; }
    };
    setInterval(() => { if (bearer) refreshAll().catch(() => {}); }, 5000);
  </script>
</body>
</html>
"#;
