//! `obb-broker` — Remote `hbox` + `bb2` Health Prober, Git-Tree-Keyed `.olean` Hardlink Seed Pool,
//! Target-Aware Router & Memory/Time-Bounded `lake build` Batcher.

use anyhow::{Context, Result, bail};
use chrono::Utc;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::io::Read;
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::Mutex;
use std::thread;
use std::time::{Duration, Instant};

/// Processes older than 30 minutes (1,800s) on `hbox`/`bb2` are flagged as lingering runaways.
pub const RUNAWAY_AGE_SECS: u64 = 1800;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RemoteCmdOutput {
    pub exit_code: i32,
    pub stdout: String,
    pub stderr: String,
    pub duration_ms: u64,
}

/// Pluggable SSH execution trait so `obb broker` runs against real `hbox`/`bb2` in production
/// and against deterministic in-memory mocks in `< 1ms` unit tests.
pub trait RemoteExecutor: Send + Sync {
    fn run_ssh(&self, host: &str, remote_script: &str, timeout_secs: u64) -> Result<RemoteCmdOutput>;
}

/// Production OpenSSH executor with non-interactive `BatchMode=yes`, `ConnectTimeout=5`,
/// and hard wall-clock deadline reaping.
#[derive(Debug, Default, Clone)]
pub struct SshExecutor;

impl RemoteExecutor for SshExecutor {
    fn run_ssh(&self, host: &str, remote_script: &str, timeout_secs: u64) -> Result<RemoteCmdOutput> {
        let t0 = Instant::now();
        let mut child = Command::new("ssh")
            .args([
                "-o",
                "BatchMode=yes",
                "-o",
                "ConnectTimeout=5",
                host,
                "bash",
                "-s",
            ])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .with_context(|| format!("failed to spawn `ssh {host}`"))?;

        if let Some(mut stdin) = child.stdin.take() {
            use std::io::Write;
            let _ = stdin.write_all(remote_script.as_bytes());
        }

        let mut stdout_pipe = child.stdout.take();
        let mut stderr_pipe = child.stderr.take();
        let out_handle = thread::spawn(move || {
            let mut buf = String::new();
            if let Some(ref mut r) = stdout_pipe {
                let _ = r.read_to_string(&mut buf);
            }
            buf
        });
        let err_handle = thread::spawn(move || {
            let mut buf = String::new();
            if let Some(ref mut r) = stderr_pipe {
                let _ = r.read_to_string(&mut buf);
            }
            buf
        });

        let deadline = Duration::from_secs(timeout_secs.max(1));
        let status = loop {
            if let Some(st) = child.try_wait()? {
                break Some(st);
            }
            if t0.elapsed() >= deadline {
                let _ = child.kill();
                let _ = child.wait();
                break None;
            }
            thread::sleep(Duration::from_millis(25));
        };

        let stdout = out_handle.join().unwrap_or_default();
        let stderr = err_handle.join().unwrap_or_default();
        let duration_ms = t0.elapsed().as_millis() as u64;

        match status {
            Some(st) => Ok(RemoteCmdOutput {
                exit_code: st.code().unwrap_or(1),
                stdout,
                stderr,
                duration_ms,
            }),
            None => Ok(RemoteCmdOutput {
                exit_code: 124,
                stdout,
                stderr: format!(
                    "{stderr}\nssh command to `{host}` timed out after {timeout_secs}s"
                )
                .trim()
                .to_string(),
                duration_ms,
            }),
        }
    }
}

/// Deterministic offline mock SSH executor for fast unit & integration tests.
#[derive(Default)]
pub struct MockSshExecutor {
    responses: HashMap<String, RemoteCmdOutput>,
    pub calls: Mutex<Vec<(String, String)>>,
}

impl MockSshExecutor {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_host_output(mut self, host: &str, output: RemoteCmdOutput) -> Self {
        self.responses.insert(host.to_string(), output);
        self
    }

    pub fn recorded_calls(&self) -> Vec<(String, String)> {
        self.calls.lock().unwrap().clone()
    }
}

impl RemoteExecutor for MockSshExecutor {
    fn run_ssh(&self, host: &str, remote_script: &str, _timeout_secs: u64) -> Result<RemoteCmdOutput> {
        self.calls
            .lock()
            .unwrap()
            .push((host.to_string(), remote_script.to_string()));
        if let Some(resp) = self.responses.get(host) {
            Ok(resp.clone())
        } else {
            Ok(RemoteCmdOutput {
                exit_code: 255,
                stdout: String::new(),
                stderr: format!("mock: host `{host}` unreachable"),
                duration_ms: 1,
            })
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RunawayProcess {
    pub pid: u32,
    pub elapsed_secs: u64,
    pub rss_mib: u64,
    pub comm: String,
    pub args: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HostProbe {
    pub host: String,
    pub reachable: bool,
    pub dry_run: bool,
    pub cpu_cores: u32,
    pub load_1m: f64,
    pub load_5m: f64,
    pub load_15m: f64,
    pub mem_total_gib: f64,
    pub mem_free_gib: f64,
    pub zfs_arc_reclaimable_gib: f64,
    pub disk_free_gib: f64,
    pub active_lean_lake_procs: usize,
    pub runaway_procs: Vec<RunawayProcess>,
    pub has_swarm_build: bool,
    pub health_score: f64,
    pub note: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BrokerProbeReport {
    pub checked_at: String,
    pub dry_run: bool,
    pub probe_script: String,
    pub recommended_general_host: Option<String>,
    pub hosts: Vec<HostProbe>,
}

/// Generate the single-roundtrip remote POSIX/bash telemetry script (including ZFS ARC accounting
/// for `hbox` per `~/swarm/MACHINES.md` and `> 30 min` runaway `lean`/`lake` detection).
pub fn build_probe_script() -> String {
    r#"set -u
CORES=$(nproc 2>/dev/null || getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)
LOAD=$(awk '{print $1, $2, $3}' /proc/loadavg 2>/dev/null || echo "0.0 0.0 0.0")
MEM_KB=$(awk '
  /^MemTotal:/ { tot=$2 }
  /^MemAvailable:/ { avail=$2 }
  END { printf "%d %d", tot+0, avail+0 }
' /proc/meminfo 2>/dev/null || echo "0 0")
ZFS_RECLAIM_BYTES=0
if [ -r /proc/spl/kstat/zfs/arcstats ]; then
  ZFS_RECLAIM_BYTES=$(awk '
    $1 == "size" { sz=$3 }
    $1 == "c_min" { cmin=$3 }
    END { d = sz - cmin; if (d > 0) printf "%.0f", d; else print 0 }
  ' /proc/spl/kstat/zfs/arcstats 2>/dev/null || echo 0)
fi
DISK_KB=$(df -Pk . 2>/dev/null | awk 'NR==2 {print $4+0}')
HAS_SWARM=$(command -v swarm-build >/dev/null 2>&1 && echo 1 || echo 0)
echo "OBB_META|$CORES|$LOAD|$MEM_KB|$ZFS_RECLAIM_BYTES|${DISK_KB:-0}|$HAS_SWARM"
ps -eo pid=,etimes=,rss=,comm=,args= 2>/dev/null | awk '
  $4 ~ /^(lean|lake|verilator|verilator_bin|yosys|obend)$/ || $5 ~ /(^|\/)(lean|lake)(\s|$)/ {
    cmd=""
    for (i=5; i<=NF; i++) cmd = cmd (i==5 ? "" : " ") $i
    printf "OBB_PROC|%s|%s|%s|%s|%s\n", $1, $2, $3, $4, substr(cmd, 1, 160)
  }
'
"#
    .to_string()
}

fn round2(v: f64) -> f64 {
    (v * 100.0).round() / 100.0
}

pub fn parse_probe_stdout(host: &str, stdout: &str) -> Result<HostProbe> {
    let mut cpu_cores = 1u32;
    let mut load_1m = 0.0f64;
    let mut load_5m = 0.0f64;
    let mut load_15m = 0.0f64;
    let mut mem_total_gib = 0.0f64;
    let mut mem_free_gib = 0.0f64;
    let mut zfs_arc_reclaimable_gib = 0.0f64;
    let mut disk_free_gib = 0.0f64;
    let mut has_swarm_build = false;
    let mut saw_meta = false;

    let mut active_lean_lake_procs = 0usize;
    let mut runaway_procs = Vec::new();

    for raw_line in stdout.lines() {
        let line = raw_line.trim();
        if let Some(rest) = line.strip_prefix("OBB_META|") {
            let cols: Vec<&str> = rest.split('|').collect();
            if cols.len() >= 6 {
                saw_meta = true;
                cpu_cores = cols[0].trim().parse::<u32>().unwrap_or(1).max(1);
                let loads: Vec<f64> = cols[1]
                    .split_whitespace()
                    .filter_map(|s| s.parse::<f64>().ok())
                    .collect();
                load_1m = loads.first().copied().unwrap_or(0.0);
                load_5m = loads.get(1).copied().unwrap_or(0.0);
                load_15m = loads.get(2).copied().unwrap_or(0.0);

                let mems: Vec<u64> = cols[2]
                    .split_whitespace()
                    .filter_map(|s| s.parse::<u64>().ok())
                    .collect();
                let tot_kb = mems.first().copied().unwrap_or(0);
                let avail_kb = mems.get(1).copied().unwrap_or(0);
                let zfs_bytes = cols[3].trim().parse::<u64>().unwrap_or(0);
                let disk_kb = cols[4].trim().parse::<u64>().unwrap_or(0);
                has_swarm_build = cols[5].trim() == "1";

                mem_total_gib = round2((tot_kb as f64) / (1024.0 * 1024.0));
                let base_avail_gib = (avail_kb as f64) / (1024.0 * 1024.0);
                zfs_arc_reclaimable_gib =
                    round2((zfs_bytes as f64) / (1024.0 * 1024.0 * 1024.0));
                // Linux MemAvailable excludes ZFS ARC (`MACHINES.md`); add reclaimable ARC capped at MemTotal
                let eff_free = (base_avail_gib + zfs_arc_reclaimable_gib).min(mem_total_gib.max(base_avail_gib));
                mem_free_gib = round2(eff_free);
                disk_free_gib = round2((disk_kb as f64) / (1024.0 * 1024.0));
            }
        } else if let Some(rest) = line.strip_prefix("OBB_PROC|") {
            let cols: Vec<&str> = rest.splitn(5, '|').collect();
            if cols.len() == 5 {
                let pid = cols[0].trim().parse::<u32>().unwrap_or(0);
                let elapsed_secs = cols[1].trim().parse::<u64>().unwrap_or(0);
                let rss_kb = cols[2].trim().parse::<u64>().unwrap_or(0);
                let comm = cols[3].trim().to_string();
                let args = cols[4].trim().to_string();

                if comm.contains("lean") || comm.contains("lake") || args.contains("lean") || args.contains("lake") {
                    active_lean_lake_procs += 1;
                }
                if elapsed_secs > RUNAWAY_AGE_SECS {
                    runaway_procs.push(RunawayProcess {
                        pid,
                        elapsed_secs,
                        rss_mib: rss_kb / 1024,
                        comm,
                        args,
                    });
                }
            }
        }
    }

    if !saw_meta {
        bail!("host `{host}` returned malformed telemetry output");
    }

    let health_score = compute_health_score(
        host,
        cpu_cores,
        load_1m,
        mem_free_gib,
        disk_free_gib,
        active_lean_lake_procs,
        runaway_procs.len(),
    );

    let note = if !runaway_procs.is_empty() {
        format!(
            "{} lingering process(es) > 30m detected (oldest {}s)",
            runaway_procs.len(),
            runaway_procs
                .iter()
                .map(|p| p.elapsed_secs)
                .max()
                .unwrap_or(0)
        )
    } else {
        "healthy".to_string()
    };

    Ok(HostProbe {
        host: host.to_string(),
        reachable: true,
        dry_run: false,
        cpu_cores,
        load_1m,
        load_5m,
        load_15m,
        mem_total_gib,
        mem_free_gib,
        zfs_arc_reclaimable_gib,
        disk_free_gib,
        active_lean_lake_procs,
        runaway_procs,
        has_swarm_build,
        health_score,
        note,
    })
}

fn compute_health_score(
    host: &str,
    cpu_cores: u32,
    load_1m: f64,
    mem_free_gib: f64,
    disk_free_gib: f64,
    active_lean_lake_procs: usize,
    runaway_count: usize,
) -> f64 {
    if disk_free_gib < 10.0 || mem_free_gib < 8.0 {
        return 5.0;
    }
    let load_ratio = load_1m / (cpu_cores.max(1) as f64);
    let cpu_score = (40.0 * (1.0 - load_ratio.min(1.2) / 1.2)).max(0.0);
    let mem_score = (40.0 * (mem_free_gib / 80.0).min(1.0)).max(0.0);
    let compiler_penalty = (active_lean_lake_procs as f64) * 1.5;
    let runaway_penalty = (runaway_count as f64) * 12.0;
    // Slight tie-breaker (+2.0) for `hbox` when up, matching `MACHINES.md` ("prefer hbox for obend when hbox is up")
    let affinity_bonus = if host.starts_with("hbox") { 2.0 } else { 0.0 };
    round2(
        (20.0 + cpu_score + mem_score + affinity_bonus - compiler_penalty - runaway_penalty)
            .clamp(1.0, 100.0),
    )
}

/// Probe remote hosts (`bb2`, `hbox`) via `executor` (or emit synthetic dry-run descriptors when `dry_run == true`).
pub fn probe_hosts(
    hosts: &[String],
    executor: &dyn RemoteExecutor,
    dry_run: bool,
) -> BrokerProbeReport {
    let script = build_probe_script();
    let mut results = Vec::with_capacity(hosts.len());

    for host in hosts {
        if dry_run {
            let (cores, mem_tot, mem_free) = if host.starts_with("bb2") {
                (32, 122.0, 96.0)
            } else {
                (24, 123.0, 92.0)
            };
            let score = compute_health_score(host, cores, 2.0, mem_free, 80.0, 0, 0);
            results.push(HostProbe {
                host: host.clone(),
                reachable: true,
                dry_run: true,
                cpu_cores: cores,
                load_1m: 2.0,
                load_5m: 2.0,
                load_15m: 2.0,
                mem_total_gib: mem_tot,
                mem_free_gib: mem_free,
                zfs_arc_reclaimable_gib: 0.0,
                disk_free_gib: 80.0,
                active_lean_lake_procs: 0,
                runaway_procs: Vec::new(),
                has_swarm_build: true,
                health_score: score,
                note: "dry-run synthetic baseline (no SSH executed)".to_string(),
            });
            continue;
        }

        match executor.run_ssh(host, &script, 8) {
            Ok(out) if out.exit_code == 0 => match parse_probe_stdout(host, &out.stdout) {
                Ok(hp) => results.push(hp),
                Err(e) => results.push(unreachable_probe(host, &e.to_string())),
            },
            Ok(out) => {
                let err_msg = if out.stderr.trim().is_empty() {
                    format!("ssh exited with code {}", out.exit_code)
                } else {
                    out.stderr.lines().next().unwrap_or("ssh error").to_string()
                };
                results.push(unreachable_probe(host, &err_msg));
            }
            Err(e) => results.push(unreachable_probe(host, &e.to_string())),
        }
    }

    let recommended_general_host = results
        .iter()
        .filter(|h| h.reachable)
        .max_by(|a, b| {
            a.health_score
                .partial_cmp(&b.health_score)
                .unwrap_or(std::cmp::Ordering::Equal)
        })
        .map(|h| h.host.clone());

    BrokerProbeReport {
        checked_at: Utc::now().to_rfc3339(),
        dry_run,
        probe_script: script,
        recommended_general_host,
        hosts: results,
    }
}

fn unreachable_probe(host: &str, reason: &str) -> HostProbe {
    HostProbe {
        host: host.to_string(),
        reachable: false,
        dry_run: false,
        cpu_cores: 0,
        load_1m: 0.0,
        load_5m: 0.0,
        load_15m: 0.0,
        mem_total_gib: 0.0,
        mem_free_gib: 0.0,
        zfs_arc_reclaimable_gib: 0.0,
        disk_free_gib: 0.0,
        active_lean_lake_procs: 0,
        runaway_procs: Vec::new(),
        has_swarm_build: false,
        health_score: 0.0,
        note: format!("unreachable: {reason}"),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum HostChoice {
    Auto,
    Bb2,
    Hbox,
}

impl HostChoice {
    pub fn parse_str(s: &str) -> Result<Self> {
        match s.trim().to_ascii_lowercase().as_str() {
            "auto" => Ok(Self::Auto),
            "bb2" => Ok(Self::Bb2),
            "hbox" => Ok(Self::Hbox),
            other => bail!("unsupported `--host {other}`; expected `auto`, `bb2`, or `hbox`"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TargetWorkloadClass {
    /// GPU / RDNA2 / WGSL / Litmus memory-model workloads -> routed to `hbox`.
    GpuRdna2Litmus,
    /// Yosys / Verilator / FABulous / FPGA / EDA synthesis & RTL workloads -> routed to `bb2`.
    YosysVerilatorEda,
    /// Pure Lean 4 elaboration / proof / CLI targets -> routed to the healthier host.
    GeneralLean,
}

impl fmt::Display for TargetWorkloadClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::GpuRdna2Litmus => f.write_str("gpu_rdna2_litmus"),
            Self::YosysVerilatorEda => f.write_str("yosys_verilator_eda"),
            Self::GeneralLean => f.write_str("general_lean"),
        }
    }
}

/// Classify a build target into `GpuRdna2Litmus`, `YosysVerilatorEda`, or `GeneralLean`.
pub fn classify_build_target(target: &str) -> TargetWorkloadClass {
    let lower = target.to_ascii_lowercase();
    if lower.contains("rdna2")
        || lower.contains("litmus")
        || lower.contains("emitgpu")
        || lower.contains("emit-gpu")
        || lower.contains(".gpu")
        || lower.contains("/gpu/")
        || lower.ends_with("gpu")
        || lower.contains("wgsl")
        || lower.contains("rocm")
    {
        return TargetWorkloadClass::GpuRdna2Litmus;
    }

    if lower.contains("yosys")
        || lower.contains("verilat")
        || lower.contains("fabulous")
        || lower.contains("agenticeda")
        || lower.contains("tapeout")
        || lower.contains("emitsv")
        || lower.contains("emit-sv")
        || lower.ends_with(".sv")
        || lower.ends_with(".v")
        || lower.contains("/fpga/")
        || lower.contains("/eda/")
    {
        return TargetWorkloadClass::YosysVerilatorEda;
    }

    TargetWorkloadClass::GeneralLean
}

/// Normalize a caller-provided target (e.g. `lean/Obend/Vault/Replay.lean` or `Obend.Vault.Replay`)
/// into a `lake build` target identifier.
pub fn normalize_lake_target(raw: &str) -> String {
    let trimmed = raw.trim();
    if let Some(no_lean_ext) = trimmed.strip_suffix(".lean") {
        let no_prefix = no_lean_ext.strip_prefix("lean/").unwrap_or(no_lean_ext);
        return no_prefix.replace('/', ".");
    }
    trimmed.to_string()
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TargetRoutingDecision {
    pub raw_target: String,
    pub lake_target: String,
    pub workload_class: TargetWorkloadClass,
    pub assigned_host: String,
    pub reason: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BatchExecutionOutcome {
    pub executed: bool,
    pub exit_code: i32,
    pub duration_ms: u64,
    pub stdout_tail: String,
    pub stderr_tail: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HostBuildBatch {
    pub host: String,
    pub lake_targets: Vec<String>,
    pub workload_classes: Vec<TargetWorkloadClass>,
    pub seed_key: String,
    pub seed_pool_dir: String,
    pub timeout_secs: u64,
    pub max_rss_gb: u64,
    pub batched_lake_command: String,
    pub remote_recipe: String,
    pub execution: Option<BatchExecutionOutcome>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildPlanOptions {
    pub host_choice: HostChoice,
    pub timeout_secs: u64,
    pub max_rss_gb: u64,
    pub dry_run: bool,
    pub exec: bool,
    pub repo_root: Option<std::path::PathBuf>,
    pub remote_seed_root: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildPlanReport {
    pub generated_at: String,
    pub host_choice: HostChoice,
    pub seed_key: String,
    pub timeout_secs: u64,
    pub max_rss_gb: u64,
    pub total_targets: usize,
    pub total_batches: usize,
    pub routing: Vec<TargetRoutingDecision>,
    pub batches: Vec<HostBuildBatch>,
    pub warnings: Vec<String>,
}

fn resolve_git_seed_key(repo_root: Option<&Path>) -> String {
    let Some(root) = repo_root else {
        return "head-default".to_string();
    };
    // Prefer `HEAD:lean` tree SHA so pure docs/Rust edits reuse the exact same warm `.olean` seed!
    for rev in ["HEAD:lean", "HEAD"] {
        if let Ok(out) = Command::new("git")
            .arg("--no-optional-locks")
            .arg("-C")
            .arg(root)
            .args(["rev-parse", rev])
            .output()
        {
            if out.status.success() {
                let sha = String::from_utf8_lossy(&out.stdout).trim().to_string();
                if sha.len() >= 12 {
                    return sha;
                }
            }
        }
    }
    "head-default".to_string()
}

fn default_seed_pool_for_host(host: &str) -> String {
    if host.starts_with("hbox") {
        "/othersys/obb-seeds/obend".to_string()
    } else {
        "$HOME/obend/obb-seeds".to_string()
    }
}

/// Emit the safe remote execution recipe for one host batch:
/// 1. Isolated per-invocation worktree + PID file
/// 2. `EXIT INT TERM` process-tree reaper (`pkill -TERM/-KILL -P $$`)
/// 3. Git-tree-keyed hardlink `.olean` + `.ir` seeding (`cp -al`)
/// 4. `timeout --kill-after=10s <timeout>s` + `SWARM_MEM_MAX=<N>G swarm-build` (with `ulimit -v` fallback)
/// 5. Atomic refresh of warm `.olean` seed cache on green exit
pub fn render_safe_remote_recipe(
    host: &str,
    lake_targets: &[String],
    seed_key: &str,
    seed_pool_dir: &str,
    timeout_secs: u64,
    max_rss_gb: u64,
) -> (String, String) {
    let joined_targets = lake_targets.join(" ");
    let batched_lake_cmd = format!("lake build {joined_targets}");
    let ulimit_kb = max_rss_gb.saturating_mul(1_048_576);
    let short_key = &seed_key[..seed_key.len().min(12)];
    let base_repo = "$HOME/obend/repo";

    let recipe = format!(
        r#"set -euo pipefail
# Host: {host} | Seed key: {seed_key}
SEED_POOL="{seed_pool_dir}"
SEED_KEY="{seed_key}"
BASE_REPO="{base_repo}"
WORK_ROOT="${{OBB_WORK_ROOT:-/tmp/obb-worktrees}}"
mkdir -p "$WORK_ROOT" "$SEED_POOL"
WT_DIR="$WORK_ROOT/wt-{short_key}-$$"
PID_FILE="$WT_DIR/.obb-build.pid"

cleanup_obb_build() {{
  local ec=$?
  trap - EXIT INT TERM
  pkill -TERM -P $$ 2>/dev/null || true
  sleep 0.2 || true
  pkill -KILL -P $$ 2>/dev/null || true
  rm -f "$PID_FILE" 2>/dev/null || true
  if [ -d "$BASE_REPO/.git" ] && [ -d "$WT_DIR" ]; then
    git -C "$BASE_REPO" worktree remove --force "$WT_DIR" 2>/dev/null || rm -rf "$WT_DIR"
  else
    rm -rf "$WT_DIR" 2>/dev/null || true
  fi
  exit "$ec"
}}
trap cleanup_obb_build EXIT INT TERM

if [ -d "$BASE_REPO/.git" ]; then
  git -C "$BASE_REPO" worktree add --detach "$WT_DIR" HEAD >/dev/null
else
  mkdir -p "$WT_DIR/lean"
fi
mkdir -p "$WT_DIR/lean/.lake/build"
echo "$$" > "$PID_FILE"

# Hardlink-seed (`cp -al`) warm `.lake/build/{{lib,ir}}` from git-tree-keyed cache (fallback to `latest`)
SEED_SRC=""
if [ -d "$SEED_POOL/$SEED_KEY/.lake/build/lib" ]; then
  SEED_SRC="$SEED_POOL/$SEED_KEY/.lake/build"
elif [ -d "$SEED_POOL/latest/.lake/build/lib" ]; then
  SEED_SRC="$SEED_POOL/latest/.lake/build"
fi
if [ -n "$SEED_SRC" ]; then
  for sub in lib ir; do
    if [ -d "$SEED_SRC/$sub" ]; then
      cp -al "$SEED_SRC/$sub" "$WT_DIR/lean/.lake/build/"
    fi
  done
fi

cd "$WT_DIR/lean"
if command -v swarm-build >/dev/null 2>&1; then
  SWARM_MEM_MAX="{max_rss_gb}G" swarm-build timeout --kill-after=10s {timeout_secs}s {batched_lake_cmd}
else
  ( ulimit -v {ulimit_kb}; exec timeout --kill-after=10s {timeout_secs}s {batched_lake_cmd} )
fi

# Refresh git-tree-keyed `.olean` seed pool atomically for downstream swarm lanes
STAGE_SEED="$SEED_POOL/.stage-$SEED_KEY-$$"
rm -rf "$STAGE_SEED"
mkdir -p "$STAGE_SEED/.lake/build"
for sub in lib ir; do
  if [ -d "$WT_DIR/lean/.lake/build/$sub" ]; then
    cp -al "$WT_DIR/lean/.lake/build/$sub" "$STAGE_SEED/.lake/build/"
  fi
done
if [ ! -d "$SEED_POOL/$SEED_KEY" ]; then
  mv "$STAGE_SEED" "$SEED_POOL/$SEED_KEY" 2>/dev/null || rm -rf "$STAGE_SEED"
else
  rm -rf "$STAGE_SEED"
fi
ln -sfn "$SEED_POOL/$SEED_KEY" "$SEED_POOL/latest"
"#
    );

    (batched_lake_cmd, recipe)
}

fn tail_lines(s: &str, max_lines: usize) -> String {
    let lines: Vec<&str> = s.lines().collect();
    let start = lines.len().saturating_sub(max_lines);
    lines[start..].join("\n")
}

/// Plan (and optionally execute with `opts.exec == true`) target-routed, batched remote Lean builds.
pub fn plan_build(
    targets: &[String],
    opts: &BuildPlanOptions,
    executor: &dyn RemoteExecutor,
) -> Result<BuildPlanReport> {
    if targets.is_empty() {
        bail!("`obb broker plan-build` requires at least one build target");
    }

    let probe_hosts_list = vec!["bb2".to_string(), "hbox".to_string()];
    // When `--host auto` is requested (and not `--dry-run`), probe `bb2` and `hbox` once to pick the healthier host
    let probe = if opts.host_choice == HostChoice::Auto {
        Some(probe_hosts(&probe_hosts_list, executor, opts.dry_run))
    } else {
        None
    };

    let mut warnings = Vec::new();
    let reachable_map: HashMap<String, &HostProbe> = probe
        .as_ref()
        .map(|p| {
            p.hosts
                .iter()
                .filter(|h| h.reachable)
                .map(|h| (h.host.clone(), h))
                .collect()
        })
        .unwrap_or_default();

    let healthiest_general = probe
        .as_ref()
        .and_then(|p| p.recommended_general_host.clone())
        .unwrap_or_else(|| {
            warnings.push(
                "Neither `hbox` nor `bb2` answered live SSH probe; defaulting general Lean plan to `hbox`."
                    .to_string(),
            );
            "hbox".to_string()
        });

    let mut routing = Vec::with_capacity(targets.len());
    // Group batches deterministically in host order while preserving target order per host
    let mut grouped: BTreeMap<String, (Vec<String>, Vec<TargetWorkloadClass>)> = BTreeMap::new();

    for raw in targets {
        let class = classify_build_target(raw);
        let lake_target = normalize_lake_target(raw);

        let (assigned_host, reason) = match opts.host_choice {
            HostChoice::Bb2 => ("bb2".to_string(), "pinned via `--host bb2`".to_string()),
            HostChoice::Hbox => ("hbox".to_string(), "pinned via `--host hbox`".to_string()),
            HostChoice::Auto => match class {
                TargetWorkloadClass::GpuRdna2Litmus => {
                    if opts.dry_run || reachable_map.contains_key("hbox") || reachable_map.is_empty() {
                        (
                            "hbox".to_string(),
                            "GPU/RDNA2/Litmus target affinity -> `hbox`".to_string(),
                        )
                    } else {
                        warnings.push(format!(
                            "GPU/RDNA2/Litmus target `{raw}` prefers `hbox`, which is unreachable; falling back to `bb2` for pure Lean elaboration only"
                        ));
                        (
                            "bb2".to_string(),
                            "GPU/RDNA2/Litmus prefers `hbox` (unreachable) -> fallback `bb2`"
                                .to_string(),
                        )
                    }
                }
                TargetWorkloadClass::YosysVerilatorEda => {
                    if opts.dry_run || reachable_map.contains_key("bb2") || reachable_map.is_empty() {
                        (
                            "bb2".to_string(),
                            "Yosys/Verilator/EDA target affinity -> `bb2`".to_string(),
                        )
                    } else {
                        warnings.push(format!(
                            "Yosys/Verilator/EDA target `{raw}` prefers `bb2`, which is unreachable; falling back to `hbox`"
                        ));
                        (
                            "hbox".to_string(),
                            "Yosys/Verilator/EDA prefers `bb2` (unreachable) -> fallback `hbox`"
                                .to_string(),
                        )
                    }
                }
                TargetWorkloadClass::GeneralLean => {
                    let score_note = reachable_map
                        .get(&healthiest_general)
                        .map(|h| format!("health_score={:.1}, free={:.1}GiB", h.health_score, h.mem_free_gib))
                        .unwrap_or_else(|| "offline default".to_string());
                    (
                        healthiest_general.clone(),
                        format!("healthier general Lean host -> `{healthiest_general}` ({score_note})"),
                    )
                }
            },
        };

        let entry = grouped.entry(assigned_host.clone()).or_default();
        if !entry.0.contains(&lake_target) {
            entry.0.push(lake_target.clone());
        }
        if !entry.1.contains(&class) {
            entry.1.push(class);
        }

        routing.push(TargetRoutingDecision {
            raw_target: raw.clone(),
            lake_target,
            workload_class: class,
            assigned_host,
            reason,
        });
    }

    let seed_key = resolve_git_seed_key(opts.repo_root.as_deref());
    let mut batches = Vec::with_capacity(grouped.len());

    for (host, (lake_targets, workload_classes)) in grouped {
        let seed_pool_dir = opts
            .remote_seed_root
            .clone()
            .unwrap_or_else(|| default_seed_pool_for_host(&host));
        let (batched_lake_command, remote_recipe) = render_safe_remote_recipe(
            &host,
            &lake_targets,
            &seed_key,
            &seed_pool_dir,
            opts.timeout_secs,
            opts.max_rss_gb,
        );

        let execution = if opts.exec && !opts.dry_run {
            let out = executor.run_ssh(&host, &remote_recipe, opts.timeout_secs.saturating_add(30))?;
            Some(BatchExecutionOutcome {
                executed: true,
                exit_code: out.exit_code,
                duration_ms: out.duration_ms,
                stdout_tail: tail_lines(&out.stdout, 40),
                stderr_tail: tail_lines(&out.stderr, 40),
            })
        } else {
            None
        };

        batches.push(HostBuildBatch {
            host,
            lake_targets,
            workload_classes,
            seed_key: seed_key.clone(),
            seed_pool_dir,
            timeout_secs: opts.timeout_secs,
            max_rss_gb: opts.max_rss_gb,
            batched_lake_command,
            remote_recipe,
            execution,
        });
    }

    Ok(BuildPlanReport {
        generated_at: Utc::now().to_rfc3339(),
        host_choice: opts.host_choice,
        seed_key,
        timeout_secs: opts.timeout_secs,
        max_rss_gb: opts.max_rss_gb,
        total_targets: targets.len(),
        total_batches: batches.len(),
        routing,
        batches,
        warnings,
    })
}
