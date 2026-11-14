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
    fn run_ssh(
        &self,
        host: &str,
        remote_script: &str,
        timeout_secs: u64,
    ) -> Result<RemoteCmdOutput>;
}

/// Production OpenSSH executor with non-interactive `BatchMode=yes`, `ConnectTimeout=5`,
/// and hard wall-clock deadline reaping.
#[derive(Debug, Default, Clone)]
pub struct SshExecutor;

impl RemoteExecutor for SshExecutor {
    fn run_ssh(
        &self,
        host: &str,
        remote_script: &str,
        timeout_secs: u64,
    ) -> Result<RemoteCmdOutput> {
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
: "${HOME:=/tmp}"
export PATH="${PATH:-/usr/bin:/bin}:$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:/usr/local/bin"
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
                zfs_arc_reclaimable_gib = round2((zfs_bytes as f64) / (1024.0 * 1024.0 * 1024.0));
                // Linux MemAvailable excludes ZFS ARC (`MACHINES.md`); add reclaimable ARC capped at MemTotal
                let eff_free = (base_avail_gib + zfs_arc_reclaimable_gib)
                    .min(mem_total_gib.max(base_avail_gib));
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

                if comm.contains("lean")
                    || comm.contains("lake")
                    || args.contains("lean")
                    || args.contains("lake")
                {
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
    #[serde(default)]
    pub target_commit: Option<String>,
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
    #[serde(default)]
    pub target_commit: Option<String>,
    pub remote_seed_root: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildPlanReport {
    pub generated_at: String,
    pub host_choice: HostChoice,
    #[serde(default)]
    pub target_commit: Option<String>,
    pub seed_key: String,
    pub timeout_secs: u64,
    pub max_rss_gb: u64,
    pub total_targets: usize,
    pub total_batches: usize,
    pub routing: Vec<TargetRoutingDecision>,
    pub batches: Vec<HostBuildBatch>,
    pub warnings: Vec<String>,
}

#[derive(Debug, Clone)]
struct ResolvedGitRevisions {
    target_commit: Option<String>,
    seed_key: String,
    dirty_warning: Option<String>,
}

fn git_rev_parse(root: &Path, rev: &str) -> Option<String> {
    let out = Command::new("git")
        .arg("--no-optional-locks")
        .arg("-C")
        .arg(root)
        .args(["rev-parse", "--verify", rev])
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let sha = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if sha.len() >= 12 { Some(sha) } else { None }
}

fn resolve_git_revisions(
    repo_root: Option<&Path>,
    explicit_commit: Option<&str>,
) -> Result<ResolvedGitRevisions> {
    let cleaned_explicit = explicit_commit.map(str::trim).filter(|s| !s.is_empty());

    if let Some(root) = repo_root {
        let rev_base = cleaned_explicit.unwrap_or("HEAD");
        let commit_sha = git_rev_parse(root, &format!("{rev_base}^{{commit}}"));
        if let Some(exp) = cleaned_explicit
            && commit_sha.is_none()
        {
            bail!(
                "explicit `--commit {exp}` could not be resolved in local repository `{}`",
                root.display()
            );
        }
        // Prefer `<rev>:lean` tree SHA so pure docs/Rust edits reuse the exact same warm `.olean` seed!
        let seed_key = git_rev_parse(root, &format!("{rev_base}:lean"))
            .or_else(|| commit_sha.clone())
            .unwrap_or_else(|| "head-default".to_string());

        let dirty_warning = if cleaned_explicit.is_none() && commit_sha.is_some() {
            Command::new("git")
                .arg("--no-optional-locks")
                .arg("-C")
                .arg(root)
                .args(["status", "--porcelain"])
                .output()
                .ok()
                .filter(|o| o.status.success())
                .and_then(|o| {
                    let s = String::from_utf8_lossy(&o.stdout);
                    if s.lines().any(|l| !l.trim().is_empty()) {
                        Some(format!(
                            "Local worktree `{}` has uncommitted modifications; remote recipe checks out exact commit `{}` (commit & push changes first so remote matches local edits).",
                            root.display(),
                            commit_sha.as_deref().unwrap_or("HEAD")
                        ))
                    } else {
                        None
                    }
                })
        } else {
            None
        };

        return Ok(ResolvedGitRevisions {
            target_commit: commit_sha,
            seed_key,
            dirty_warning,
        });
    }

    if let Some(exp) = cleaned_explicit {
        if !exp.chars().all(|c| c.is_ascii_hexdigit()) || exp.len() < 7 {
            bail!(
                "explicit `--commit {exp}` without `--repo` must be a hexadecimal commit SHA (>= 7 chars)"
            );
        }
        return Ok(ResolvedGitRevisions {
            target_commit: Some(exp.to_string()),
            seed_key: exp.to_string(),
            dirty_warning: None,
        });
    }

    Ok(ResolvedGitRevisions {
        target_commit: None,
        seed_key: "head-default".to_string(),
        dirty_warning: None,
    })
}

fn default_seed_pool_for_host(host: &str) -> String {
    if host.starts_with("hbox") {
        "/othersys/obb-seeds/obend".to_string()
    } else {
        "$HOME/obend/obb-seeds".to_string()
    }
}

/// Backwards-compatible wrapper around [`render_safe_remote_recipe_for_commit`] without an explicit commit pin.
pub fn render_safe_remote_recipe(
    host: &str,
    lake_targets: &[String],
    seed_key: &str,
    seed_pool_dir: &str,
    timeout_secs: u64,
    max_rss_gb: u64,
) -> (String, String) {
    render_safe_remote_recipe_for_commit(
        host,
        lake_targets,
        None,
        seed_key,
        seed_pool_dir,
        timeout_secs,
        max_rss_gb,
    )
}

pub fn is_valid_lake_target(t: &str) -> bool {
    !t.is_empty()
        && t.len() <= 256
        && !t.starts_with('-')
        && t.bytes().all(|b| {
            b.is_ascii_alphanumeric() || matches!(b, b'.' | b'_' | b'-' | b'/' | b'@' | b'+' | b':')
        })
}

fn is_safe_remote_path(p: &str) -> bool {
    if p.is_empty() || p.len() > 512 || !(p.starts_with('/') || p.starts_with("$HOME/")) {
        return false;
    }
    let after_home = p.strip_prefix("$HOME/").unwrap_or(p);
    if after_home.contains('$') {
        return false;
    }
    !p.bytes().any(|b| {
        b <= 0x20
            || b == 0x7f
            || matches!(
                b,
                b'"' | b'\'' | b'`' | b';' | b'|' | b'&' | b'(' | b')' | b'<' | b'>' | b'\\'
            )
    }) && !Path::new(p)
        .components()
        .any(|c| matches!(c, std::path::Component::ParentDir))
}

fn sanitize_shell_token(raw: &str, allow_slash_dollar: bool) -> String {
    raw.chars()
        .filter(|&c| {
            c.is_ascii_alphanumeric()
                || matches!(c, '.' | '_' | '-' | '@' | '+' | ':')
                || (allow_slash_dollar && (c == '/' || c == '$'))
        })
        .collect()
}

/// Emit the safe remote execution recipe for one host batch:
/// 1. Isolated per-invocation worktree (`0700` user-owned `WORK_ROOT`) + external PID file
/// 2. `EXIT INT TERM` process-group & session reaper (`setsid` PGID + `kill -- -$$` + `pkill -P $$`)
/// 3. Exact target commit sync (`git fetch` + `git checkout --detach <exact_sha>`) & `HEAD:lean` tree verification
/// 4. Safe CoW/copied `.olean` + `.ir` seeding (`cp -R --reflink=auto`, never shared writable `cp -al` inodes!)
/// 5. `timeout --kill-after=10s <timeout>s` + `swarm-build` / `systemd-run --user --scope` / `setsid` `ulimit -v`
/// 6. Read-only sealed (`chmod -R a-w`) atomic refresh of warm `.olean` seed cache on green exit
pub fn render_safe_remote_recipe_for_commit(
    host: &str,
    lake_targets: &[String],
    target_commit: Option<&str>,
    seed_key: &str,
    seed_pool_dir: &str,
    timeout_secs: u64,
    max_rss_gb: u64,
) -> (String, String) {
    let safe_targets: Vec<String> = lake_targets
        .iter()
        .map(|t| sanitize_shell_token(t, true))
        .filter(|t| !t.is_empty() && !t.starts_with('-'))
        .collect();
    let joined_targets = safe_targets.join(" ");
    let batched_lake_cmd = format!("lake build {joined_targets}");
    let ulimit_kb = max_rss_gb.saturating_mul(1_048_576);
    let safe_host = sanitize_shell_token(host, false);
    let safe_seed_key = sanitize_shell_token(seed_key, false);
    let short_key = &safe_seed_key[..safe_seed_key.len().min(12)];
    let base_repo = "$HOME/obend/repo";
    let safe_seed_pool = sanitize_shell_token(seed_pool_dir, true);
    let commit_pin: String = target_commit
        .unwrap_or("")
        .chars()
        .filter(|c| c.is_ascii_hexdigit())
        .collect();

    let recipe = format!(
        r#"set -euo pipefail
# Host: {safe_host} | Target commit: {commit_pin} | Seed key: {safe_seed_key}
: "${{HOME:=/tmp}}"
export PATH="${{PATH:-/usr/bin:/bin}}:$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:/usr/local/bin"
SEED_POOL="{safe_seed_pool}"
SEED_KEY="{safe_seed_key}"
TARGET_COMMIT="{commit_pin}"
BASE_REPO=""
if [ -n "${{OBB_BASE_REPO:-}}" ]; then
  BASE_REPO="$OBB_BASE_REPO"
else
  if [ -n "$TARGET_COMMIT" ]; then
    for cand in "$HOME/obend/repo" "$HOME/obend/dev" "$HOME/obend"; do
      if [ -e "$cand/.git" ] && git -C "$cand" cat-file -e "${{TARGET_COMMIT}}^{{commit}}" 2>/dev/null; then
        BASE_REPO="$cand"
        break
      fi
    done
  fi
  if [ -z "$BASE_REPO" ]; then
    for cand in "$HOME/obend/repo" "$HOME/obend/dev" "$HOME/obend"; do
      if [ -e "$cand/.git" ]; then
        BASE_REPO="$cand"
        break
      fi
    done
  fi
  if [ -z "$BASE_REPO" ]; then
    BASE_REPO="{base_repo}"
  fi
fi
WORK_ROOT="${{OBB_WORK_ROOT:-${{XDG_RUNTIME_DIR:-$HOME/.cache}}/obb-worktrees}}"
mkdir -p -m 700 "$WORK_ROOT"
chmod 700 "$WORK_ROOT" 2>/dev/null || true
if [ -L "$WORK_ROOT" ] || [ ! -O "$WORK_ROOT" ] || [ ! -w "$WORK_ROOT" ]; then
  echo "ERROR: unsafe or unwritable WORK_ROOT: $WORK_ROOT" >&2
  exit 68
fi
use_seed_pool() {{
  [ -n "$1" ] && mkdir -p -m 700 "$1" 2>/dev/null && (chmod 700 "$1" 2>/dev/null || true) && [ ! -L "$1" ] && [ -O "$1" ] && [ -w "$1" ]
}}
if ! use_seed_pool "$SEED_POOL"; then
  OBB_USER="$(id -un 2>/dev/null || echo "${{USER:-obb}}")"
  if [ -d "/othersys/lanes" ] && [ -w "/othersys/lanes" ] && use_seed_pool "/othersys/lanes/obb-seeds-$OBB_USER/obend"; then
    SEED_POOL="/othersys/lanes/obb-seeds-$OBB_USER/obend"
  elif use_seed_pool "$HOME/obend/obb-seeds"; then
    SEED_POOL="$HOME/obend/obb-seeds"
  else
    echo "ERROR: no writable user-owned SEED_POOL available" >&2
    exit 67
  fi
fi
INV_DIR="$(mktemp -d "$WORK_ROOT/obb-{short_key}-XXXXXXXX")"
WT_DIR="$INV_DIR/wt"
PID_FILE="$INV_DIR/build.pid"
BUILD_PGID=""
echo "$$" > "$PID_FILE"

cleanup_obb_build() {{
  local ec=$?
  trap '' INT TERM
  trap - EXIT
  if [ -n "${{BUILD_PGID:-}}" ]; then
    kill -TERM -- "-$BUILD_PGID" 2>/dev/null || true
  fi
  kill -TERM -- -$$ 2>/dev/null || true
  pkill -TERM -P $$ 2>/dev/null || true
  sleep 0.2 || true
  if [ -n "${{BUILD_PGID:-}}" ]; then
    kill -KILL -- "-$BUILD_PGID" 2>/dev/null || true
  fi
  pkill -KILL -P $$ 2>/dev/null || true
  rm -f "$PID_FILE" 2>/dev/null || true
  if [ -d "$WT_DIR" ]; then
    chmod -R u+w "$WT_DIR" 2>/dev/null || true
    if [ -e "$BASE_REPO/.git" ]; then
      git -C "$BASE_REPO" worktree remove --force "$WT_DIR" 2>/dev/null || rm -rf "$WT_DIR"
    else
      rm -rf "$WT_DIR" 2>/dev/null || true
    fi
  fi
  rm -rf "$INV_DIR" 2>/dev/null || true
  exit "$ec"
}}
trap cleanup_obb_build EXIT INT TERM

if [ -e "$BASE_REPO/.git" ]; then
  if [ -n "$TARGET_COMMIT" ]; then
    if ! git -C "$BASE_REPO" cat-file -e "${{TARGET_COMMIT}}^{{commit}}" 2>/dev/null; then
      git -C "$BASE_REPO" fetch --no-tags --quiet --all --prune
    fi
    if ! git -C "$BASE_REPO" cat-file -e "${{TARGET_COMMIT}}^{{commit}}" 2>/dev/null; then
      echo "ERROR: target commit $TARGET_COMMIT is missing on remote {safe_host} after git fetch; push exact SHA before building." >&2
      exit 65
    fi
    git -C "$BASE_REPO" worktree add --detach "$WT_DIR" "$TARGET_COMMIT" >/dev/null
    git -C "$WT_DIR" checkout --detach --force "$TARGET_COMMIT" >/dev/null
  else
    git -C "$BASE_REPO" fetch --no-tags --quiet --all --prune 2>/dev/null || true
    ORIGIN_SHA="$(git -C "$BASE_REPO" rev-parse --verify origin/HEAD^{{commit}} 2>/dev/null \
      || git -C "$BASE_REPO" rev-parse --verify origin/dev^{{commit}} 2>/dev/null \
      || git -C "$BASE_REPO" rev-parse --verify origin/main^{{commit}} 2>/dev/null \
      || git -C "$BASE_REPO" rev-parse --verify FETCH_HEAD^{{commit}} 2>/dev/null \
      || git -C "$BASE_REPO" rev-parse --verify HEAD^{{commit}})"
    git -C "$BASE_REPO" worktree add --detach "$WT_DIR" "$ORIGIN_SHA" >/dev/null
    git -C "$WT_DIR" checkout --detach --force "$ORIGIN_SHA" >/dev/null
  fi
  if [ "$SEED_KEY" != "head-default" ] && [ "$SEED_KEY" != "$TARGET_COMMIT" ]; then
    REMOTE_TREE="$(git -C "$WT_DIR" rev-parse --verify HEAD:lean 2>/dev/null || git -C "$WT_DIR" rev-parse --verify HEAD^{{commit}})"
    if [ "$REMOTE_TREE" != "$SEED_KEY" ]; then
      echo "ERROR: remote checkout tree ($REMOTE_TREE) does not match local seed_key ($SEED_KEY)" >&2
      exit 66
    fi
  fi
else
  mkdir -p "$WT_DIR/lean"
fi
mkdir -p "$WT_DIR/lean/.lake/build"

# Safe CoW/copy `.lake/build/{{lib,ir}}` from immutable git-tree-keyed seed pool (never shared writable hardlink inodes)
SEED_SRC=""
if [ -d "$SEED_POOL/$SEED_KEY/.lake/build/lib" ]; then
  SEED_SRC="$SEED_POOL/$SEED_KEY/.lake/build"
elif [ -d "$SEED_POOL/latest/.lake/build/lib" ]; then
  SEED_SRC="$SEED_POOL/latest/.lake/build"
fi
if [ -n "$SEED_SRC" ]; then
  for sub in lib ir; do
    if [ -d "$SEED_SRC/$sub" ]; then
      cp -R --reflink=auto --preserve=timestamps "$SEED_SRC/$sub" "$WT_DIR/lean/.lake/build/" 2>/dev/null \
        || cp -R "$SEED_SRC/$sub" "$WT_DIR/lean/.lake/build/"
      chmod -R u+w "$WT_DIR/lean/.lake/build/$sub"
    fi
  done
fi

cd "$WT_DIR/lean"
if command -v swarm-build >/dev/null 2>&1; then
  if command -v setsid >/dev/null 2>&1; then
    setsid bash -c 'SWARM_MEM_MAX="{max_rss_gb}G" exec swarm-build timeout --kill-after=10s {timeout_secs}s {batched_lake_cmd}' &
    BUILD_PGID=$!
    wait "$BUILD_PGID"
  else
    set -m
    ( SWARM_MEM_MAX="{max_rss_gb}G" exec swarm-build timeout --kill-after=10s {timeout_secs}s {batched_lake_cmd} ) &
    BUILD_PGID=$!
    set +m
    wait "$BUILD_PGID"
  fi
elif command -v systemd-run >/dev/null 2>&1 && systemd-run --user --scope true >/dev/null 2>&1; then
  if command -v setsid >/dev/null 2>&1; then
    setsid systemd-run --user --scope --quiet -p MemoryMax={max_rss_gb}G timeout --kill-after=10s {timeout_secs}s {batched_lake_cmd} &
    BUILD_PGID=$!
    wait "$BUILD_PGID"
  else
    systemd-run --user --scope --quiet -p MemoryMax={max_rss_gb}G timeout --kill-after=10s {timeout_secs}s {batched_lake_cmd}
  fi
elif command -v setsid >/dev/null 2>&1; then
  setsid bash -c "ulimit -v {ulimit_kb} 2>/dev/null || true; exec timeout --kill-after=10s {timeout_secs}s {batched_lake_cmd}" &
  BUILD_PGID=$!
  wait "$BUILD_PGID"
else
  set -m
  ( ulimit -v {ulimit_kb} 2>/dev/null || true; if command -v timeout >/dev/null 2>&1; then exec timeout --kill-after=10s {timeout_secs}s {batched_lake_cmd}; else exec {batched_lake_cmd}; fi ) &
  BUILD_PGID=$!
  set +m
  wait "$BUILD_PGID"
fi

# Refresh git-tree-keyed `.olean` seed pool atomically with read-only sealed artifacts
STAGE_SEED="$SEED_POOL/.stage-$SEED_KEY-$$"
rm -rf "$STAGE_SEED"
mkdir -p "$STAGE_SEED/.lake/build"
for sub in lib ir; do
  if [ -d "$WT_DIR/lean/.lake/build/$sub" ]; then
    cp -R --reflink=auto --preserve=timestamps "$WT_DIR/lean/.lake/build/$sub" "$STAGE_SEED/.lake/build/" 2>/dev/null \
      || cp -R "$WT_DIR/lean/.lake/build/$sub" "$STAGE_SEED/.lake/build/"
  fi
done
chmod -R a-w "$STAGE_SEED/.lake/build" 2>/dev/null || true
if [ ! -d "$SEED_POOL/$SEED_KEY" ]; then
  mv "$STAGE_SEED" "$SEED_POOL/$SEED_KEY" 2>/dev/null || (chmod -R u+w "$STAGE_SEED" 2>/dev/null || true; rm -rf "$STAGE_SEED")
else
  chmod -R u+w "$STAGE_SEED" 2>/dev/null || true
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
        if !is_valid_lake_target(&lake_target) {
            bail!(
                "invalid or unsafe `lake build` target `{raw}` (normalized `{lake_target}`): targets must be non-empty alphanumeric/dot/slash/dash identifiers and must not start with `-`"
            );
        }

        let (assigned_host, reason) = match opts.host_choice {
            HostChoice::Bb2 => ("bb2".to_string(), "pinned via `--host bb2`".to_string()),
            HostChoice::Hbox => ("hbox".to_string(), "pinned via `--host hbox`".to_string()),
            HostChoice::Auto => match class {
                TargetWorkloadClass::GpuRdna2Litmus => {
                    if opts.dry_run
                        || reachable_map.contains_key("hbox")
                        || reachable_map.is_empty()
                    {
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
                    if opts.dry_run || reachable_map.contains_key("bb2") || reachable_map.is_empty()
                    {
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
                        .map(|h| {
                            format!(
                                "health_score={:.1}, free={:.1}GiB",
                                h.health_score, h.mem_free_gib
                            )
                        })
                        .unwrap_or_else(|| "offline default".to_string());
                    (
                        healthiest_general.clone(),
                        format!(
                            "healthier general Lean host -> `{healthiest_general}` ({score_note})"
                        ),
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

    let resolved = resolve_git_revisions(opts.repo_root.as_deref(), opts.target_commit.as_deref())?;
    if let Some(dw) = resolved.dirty_warning {
        warnings.push(dw);
    }
    let seed_key = resolved.seed_key;
    let target_commit = resolved.target_commit;
    let mut batches = Vec::with_capacity(grouped.len());

    for (host, (lake_targets, workload_classes)) in grouped {
        let seed_pool_dir = opts
            .remote_seed_root
            .clone()
            .unwrap_or_else(|| default_seed_pool_for_host(&host));
        if !is_safe_remote_path(&seed_pool_dir) {
            bail!(
                "unsafe `--remote-seed-root` path `{seed_pool_dir}`: must start with `/` or `$HOME/` and contain no `..` or shell metacharacters"
            );
        }
        let (batched_lake_command, remote_recipe) = render_safe_remote_recipe_for_commit(
            &host,
            &lake_targets,
            target_commit.as_deref(),
            &seed_key,
            &seed_pool_dir,
            opts.timeout_secs,
            opts.max_rss_gb,
        );

        let execution = if opts.exec && !opts.dry_run {
            let out =
                executor.run_ssh(&host, &remote_recipe, opts.timeout_secs.saturating_add(30))?;
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
            target_commit: target_commit.clone(),
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
        target_commit,
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
