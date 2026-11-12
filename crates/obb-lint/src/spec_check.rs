//! Spec-sensitivity hook invoking `lean-transport` (`--no-repair`) in an isolated shadow directory
//! to verify that mutating a specification actually breaks downstream theorems (`DESIGN.md` §3, §6.1).

use anyhow::{Context, Result, bail};
use obb_core::{ArtifactKind, Finding, Regime, Severity, Sink};
use serde::{Deserialize, Serialize};
use std::path::Path;
use std::process::Command;

pub const DEFAULT_TRANSPORT_BIN: &str =
    "/Users/ember/dev/lean-transport/.lake/build/bin/transport";

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BrokenDecl {
    pub file: String,
    pub line: usize,
    pub decl_name: String,
    pub kind: String,
    pub message: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpecSensitivityResult {
    pub lean_root: String,
    pub changed_file: String,
    pub transport_bin: String,
    pub total_downstream_decls: usize,
    pub intact_decls: usize,
    pub broken_decls: usize,
    pub spec_sensitive: bool,
    pub broken_details: Vec<BrokenDecl>,
    pub findings: Vec<Finding>,
}

/// Parse `census.json` emitted by `lean-transport run --no-repair --out <dir>`.
pub fn parse_transport_census_json(
    raw_json: &str,
    changed_file: &str,
) -> Result<SpecSensitivityResult> {
    let val: serde_json::Value =
        serde_json::from_str(raw_json).context("failed to parse lean-transport census.json")?;

    let mut total = val
        .get("total")
        .or_else(|| val.get("totalDecls"))
        .and_then(|v| v.as_u64())
        .unwrap_or(0) as usize;
    let mut intact = val
        .get("intact")
        .or_else(|| val.get("intactDecls"))
        .and_then(|v| v.as_u64())
        .unwrap_or(0) as usize;
    let mut broken = val
        .get("broken")
        .or_else(|| val.get("brokenDecls"))
        .and_then(|v| v.as_u64())
        .unwrap_or(0) as usize;

    let mut broken_details = Vec::new();
    if let Some(arr) = val
        .get("declarations")
        .or_else(|| val.get("entries"))
        .or_else(|| val.get("failures"))
        .and_then(|v| v.as_array())
    {
        if total == 0 {
            total = arr.len();
        }
        for item in arr {
            let status = item
                .get("status")
                .and_then(|s| s.as_str())
                .unwrap_or("broken");
            let is_broken = status != "intact" && status != "ok";
            if is_broken {
                broken_details.push(BrokenDecl {
                    file: item
                        .get("file")
                        .and_then(|s| s.as_str())
                        .unwrap_or("")
                        .to_string(),
                    line: item.get("line").and_then(|n| n.as_u64()).unwrap_or(1) as usize,
                    decl_name: item
                        .get("decl")
                        .or_else(|| item.get("name"))
                        .and_then(|s| s.as_str())
                        .unwrap_or("<decl>")
                        .to_string(),
                    kind: item
                        .get("kind")
                        .and_then(|s| s.as_str())
                        .unwrap_or("type_mismatch")
                        .to_string(),
                    message: item
                        .get("error")
                        .or_else(|| item.get("message"))
                        .and_then(|s| s.as_str())
                        .unwrap_or("")
                        .to_string(),
                });
            }
        }
        if broken == 0 && !broken_details.is_empty() {
            broken = broken_details.len();
            if total >= broken && intact == 0 {
                intact = total - broken;
            }
        }
    }

    let spec_sensitive = broken > 0;
    let mut findings = Vec::new();
    if !spec_sensitive {
        findings.push(Finding {
            rule_id: "lean/spec-insensitive-change".to_string(),
            severity: Severity::Error,
            artifact_kind: ArtifactKind::S,
            max_regime: Regime::Attested,
            sink: Some(Sink::Theater),
            path: changed_file.to_string(),
            line: 1,
            column: 1,
            symbol: None,
            message: format!(
                "Spec mutation in `{changed_file}` broke 0 downstream declarations across {total} checked declarations (`lean-transport --no-repair` stayed completely green)"
            ),
            remediation: "Downstream proofs are disconnected from this specification! Tighten downstream theorems so they depend on the actual specification fields/predicates.".to_string(),
        });
    }

    Ok(SpecSensitivityResult {
        lean_root: String::new(),
        changed_file: changed_file.to_string(),
        transport_bin: String::new(),
        total_downstream_decls: total,
        intact_decls: intact,
        broken_decls: broken,
        spec_sensitive,
        broken_details,
        findings,
    })
}

/// Invoke `lean-transport run --root <lean_root> --changed <changed_file> --no-repair --out <temp_dir>`
/// without modifying `<lean_root>`.
pub fn run_spec_sensitivity_check(
    lean_root: &Path,
    changed_file: &Path,
    transport_bin: Option<&Path>,
) -> Result<SpecSensitivityResult> {
    let bin = transport_bin.unwrap_or_else(|| Path::new(DEFAULT_TRANSPORT_BIN));
    if !bin.is_file() {
        bail!(
            "lean-transport binary not found at {}; build it first or pass `--transport-bin`",
            bin.display()
        );
    }
    if !lean_root.is_dir() {
        bail!("lean root directory does not exist: {}", lean_root.display());
    }

    let shadow_out = tempfile::tempdir().context("failed to create temporary output dir")?;
    let out_dir = shadow_out.path().join("transport-out");

    // Run under `lake env` in `lean_root` only if `lakefile.lean`/`lakefile.toml` is present,
    // writing strictly to `out_dir` inside tmp (`--no-repair` only elaborates in memory + writes census).
    let output = Command::new("lake")
        .arg("env")
        .arg(bin)
        .arg("run")
        .arg("--root")
        .arg(lean_root)
        .arg("--changed")
        .arg(changed_file)
        .arg("--no-repair")
        .arg("--out")
        .arg(&out_dir)
        .current_dir(lean_root)
        .output()
        .with_context(|| format!("failed to execute `lake env {}`", bin.display()))?;

    let census_path = out_dir.join("census.json");
    if census_path.is_file() {
        let raw = std::fs::read_to_string(&census_path)
            .with_context(|| format!("failed to read {}", census_path.display()))?;
        let mut res = parse_transport_census_json(&raw, &changed_file.to_string_lossy())?;
        res.lean_root = lean_root.to_string_lossy().to_string();
        res.transport_bin = bin.to_string_lossy().to_string();
        return Ok(res);
    }

    // Fallback: parse stdout/stderr summary if `lean-transport` reported directly on stdout
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    if !output.status.success() && stdout.trim().is_empty() {
        bail!(
            "lean-transport exited with {}: {}",
            output.status,
            stderr.trim()
        );
    }

    // Extract `broken: N` / `intact: M` if printed in text mode
    let mut broken = 0usize;
    let mut intact = 0usize;
    for tok_line in stdout.lines().chain(stderr.lines()) {
        let lower = tok_line.to_ascii_lowercase();
        if let Some(idx) = lower.find("broken") {
            for word in lower[idx..].split(|c: char| !c.is_ascii_digit()) {
                if let Ok(n) = word.parse::<usize>() {
                    broken = n;
                    break;
                }
            }
        }
        if let Some(idx) = lower.find("intact") {
            for word in lower[idx..].split(|c: char| !c.is_ascii_digit()) {
                if let Ok(n) = word.parse::<usize>() {
                    intact = n;
                    break;
                }
            }
        }
    }

    let synth_json = serde_json::json!({
        "total": broken + intact,
        "intact": intact,
        "broken": broken,
    })
    .to_string();
    let mut res = parse_transport_census_json(&synth_json, &changed_file.to_string_lossy())?;
    res.lean_root = lean_root.to_string_lossy().to_string();
    res.transport_bin = bin.to_string_lossy().to_string();
    Ok(res)
}
