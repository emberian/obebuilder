//! `obb-quarry`: Donor History Namespace Manager (`refs/quarry/<donor>/*`) & 6-Gate Pre-Uptake
//! Surgery Auditor for the Cathedral + Quarry Monorepo architecture.
//!
//! Guarantees:
//! - `sync_quarry` fetches donor branches strictly into `refs/quarry/<donor>/<branch>` with
//!   `--no-tags --no-write-fetch-head`, never touching `HEAD`, `.git/index`, `FETCH_HEAD`,
//!   `refs/heads/*`, `refs/tags/*`, or the working tree.
//! - `status_quarry` audits all tracked entries across `uptaken`, `queued_for_upgrade`,
//!   `idea_only`, and `retired_slop`, verifying that every `uptaken` entry records a donor
//!   `source_path`, non-empty `audit_notes`, and an existing `destination_path` in the target repo.
//! - `inspect_quarry_target` stages `<donor>:<path>` (either from `refs/quarry/<donor>/*` git
//!   objects or read-only from `--donor-path` / donor root) into an isolated scratch directory and
//!   runs `obb-lint` + the 6-Gate Quarry Surgery Checklist.

use anyhow::{Context, Result, bail};
use chrono::Utc;
use obb_core::{ArtifactKind, Finding, ModularityReport, Regime, Severity, Sink, sha256_hex};
use obb_lint::lean_index::build_lean_index;
use obb_lint::run_repo_lints;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt;
use std::path::{Path, PathBuf};
use std::process::Command;
use walkdir::WalkDir;

pub const DEFAULT_QUARRY_MANIFEST_REL: &str = "quarry/obend-quarry.toml";

/// Lifecycle state of an excavated donor subsystem in `quarry.toml`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum QuarryState {
    Uptaken,
    QueuedForUpgrade,
    IdeaOnly,
    RetiredSlop,
}

impl QuarryState {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Uptaken => "uptaken",
            Self::QueuedForUpgrade => "queued_for_upgrade",
            Self::IdeaOnly => "idea_only",
            Self::RetiredSlop => "retired_slop",
        }
    }

    pub fn parse_filter(raw: &str) -> Result<Self> {
        match raw.trim().to_ascii_lowercase().as_str() {
            "uptaken" => Ok(Self::Uptaken),
            "queued_for_upgrade" | "queued" => Ok(Self::QueuedForUpgrade),
            "idea_only" | "idea" => Ok(Self::IdeaOnly),
            "retired_slop" | "retired" | "slop" => Ok(Self::RetiredSlop),
            other => bail!(
                "unknown quarry state `{other}` (expected one of: uptaken, queued_for_upgrade, idea_only, retired_slop)"
            ),
        }
    }
}

impl fmt::Display for QuarryState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Donor repository specification in `quarry.toml`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DonorSpec {
    pub path: PathBuf,
    pub branches: Vec<String>,
    #[serde(default)]
    pub default_branch: Option<String>,
    #[serde(default)]
    pub language: String,
    #[serde(default)]
    pub summary: String,
}

impl DonorSpec {
    pub fn primary_branch(&self) -> &str {
        self.default_branch
            .as_deref()
            .or_else(|| self.branches.first().map(String::as_str))
            .unwrap_or("main")
    }
}

fn default_target_repo_label() -> String {
    "obend".to_string()
}

/// Tracked donor module/subsystem entry in `quarry.toml`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QuarryEntry {
    pub id: String,
    pub donor: String,
    pub source_path: String,
    pub state: QuarryState,
    #[serde(default = "default_target_repo_label")]
    pub target_repo: String,
    #[serde(default)]
    pub destination_path: Option<String>,
    pub audit_notes: String,
    #[serde(default)]
    pub required_cures: Vec<String>,
}

/// Parsed `quarry.toml` manifest.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QuarryManifest {
    pub version: u32,
    #[serde(default = "default_target_repo_label")]
    pub target_name: String,
    #[serde(default)]
    pub default_target_repo: Option<PathBuf>,
    pub donors: BTreeMap<String, DonorSpec>,
    pub entries: Vec<QuarryEntry>,
}

impl QuarryManifest {
    pub fn load_from_path(path: &Path) -> Result<Self> {
        let raw = std::fs::read_to_string(path)
            .with_context(|| format!("failed to read quarry manifest at {}", path.display()))?;
        Self::parse_toml_str(&raw)
            .with_context(|| format!("failed to parse quarry manifest TOML at {}", path.display()))
    }

    pub fn parse_toml_str(raw: &str) -> Result<Self> {
        let manifest: Self = toml::from_str(raw)?;
        if manifest.version == 0 {
            bail!("quarry manifest `version` must be >= 1");
        }
        for (donor_name, spec) in &manifest.donors {
            if donor_name.trim().is_empty() || donor_name.contains('/') || donor_name.contains(':')
            {
                bail!("invalid donor key `{donor_name}`");
            }
            if spec.branches.is_empty() {
                bail!("donor `{donor_name}` must list at least one branch in `branches`");
            }
        }
        for entry in &manifest.entries {
            if !manifest.donors.contains_key(&entry.donor) {
                bail!(
                    "quarry entry `{}` references undeclared donor `{}`",
                    entry.id,
                    entry.donor
                );
            }
        }
        Ok(manifest)
    }
}

/// Per-ref action planned or executed by `obb quarry sync`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RefSyncAction {
    pub donor: String,
    pub donor_path: String,
    pub branch: String,
    pub source_sha: String,
    pub target_ref: String,
    pub previous_target_sha: Option<String>,
    pub new_target_sha: String,
    pub refspec: String,
    pub command_preview: String,
    pub updated: bool,
}

/// Structured report from `obb quarry sync`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QuarrySyncReport {
    pub target_repo: String,
    pub dry_run: bool,
    pub synced_at: String,
    pub head_before: Option<String>,
    pub head_after: Option<String>,
    pub head_unchanged: bool,
    pub index_unchanged: bool,
    pub worktree_unchanged: bool,
    pub actions: Vec<RefSyncAction>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RepoSafetySnapshot {
    head_symref_or_sha: Option<String>,
    head_commit: Option<String>,
    index_digest: Option<String>,
    fetch_head_digest: Option<String>,
    branches_digest: String,
    tags_digest: String,
    status_porcelain: String,
}

fn capture_repo_safety_snapshot(repo_root: &Path) -> Result<RepoSafetySnapshot> {
    let git_dir_raw = run_git_ro(repo_root, &["rev-parse", "--git-dir"])?;
    let git_dir = {
        let p = Path::new(git_dir_raw.trim());
        if p.is_absolute() {
            p.to_path_buf()
        } else {
            repo_root.join(p)
        }
    };

    let head_symref_or_sha = std::fs::read_to_string(git_dir.join("HEAD"))
        .ok()
        .map(|s| s.trim().to_string());
    let head_commit = run_git_ro_opt(repo_root, &["rev-parse", "--verify", "HEAD^{commit}"]);
    let index_digest = std::fs::read(git_dir.join("index"))
        .ok()
        .map(|b| sha256_hex(&b));
    let fetch_head_digest = std::fs::read(git_dir.join("FETCH_HEAD"))
        .ok()
        .map(|b| sha256_hex(&b));
    let branches_raw = run_git_ro(
        repo_root,
        &[
            "for-each-ref",
            "--format=%(refname) %(objectname)",
            "refs/heads",
        ],
    )?;
    let tags_raw = run_git_ro(
        repo_root,
        &[
            "for-each-ref",
            "--format=%(refname) %(objectname)",
            "refs/tags",
        ],
    )?;
    let status_porcelain = run_git_ro(
        repo_root,
        &["status", "--porcelain", "--untracked-files=normal"],
    )?;

    Ok(RepoSafetySnapshot {
        head_symref_or_sha,
        head_commit,
        index_digest,
        fetch_head_digest,
        branches_digest: sha256_hex(branches_raw.as_bytes()),
        tags_digest: sha256_hex(tags_raw.as_bytes()),
        status_porcelain,
    })
}

/// Sync all donor branches declared in `manifest` into `refs/quarry/<donor>/<branch>` inside
/// `target_repo` (`--no-tags --no-write-fetch-head`), or preview without touching `target_repo`
/// when `dry_run` is `true`.
pub fn sync_quarry(
    manifest: &QuarryManifest,
    target_repo: &Path,
    dry_run: bool,
) -> Result<QuarrySyncReport> {
    let canon_target = target_repo
        .canonicalize()
        .with_context(|| format!("target repo does not exist: {}", target_repo.display()))?;

    let before = capture_repo_safety_snapshot(&canon_target)?;
    let mut actions = Vec::new();

    for (donor_name, donor) in &manifest.donors {
        let canon_donor = donor.path.canonicalize().with_context(|| {
            format!(
                "donor `{donor_name}` path does not exist: {}",
                donor.path.display()
            )
        })?;

        for branch in &donor.branches {
            let src_ref = format!("refs/heads/{branch}");
            let source_sha = run_git_ro(
                &canon_donor,
                &["rev-parse", "--verify", &format!("{src_ref}^{{commit}}")],
            )
            .with_context(|| {
                format!(
                    "donor `{donor_name}` ({}) has no branch `{branch}`",
                    canon_donor.display()
                )
            })?
            .trim()
            .to_string();

            let target_ref = format!("refs/quarry/{donor_name}/{branch}");
            let previous_target_sha = run_git_ro_opt(
                &canon_target,
                &["rev-parse", "--verify", &format!("{target_ref}^{{commit}}")],
            );
            let refspec = format!("+{src_ref}:{target_ref}");
            let command_preview = format!(
                "git -C {} fetch --no-tags --no-write-fetch-head {} {}",
                canon_target.display(),
                canon_donor.display(),
                refspec
            );

            let updated = previous_target_sha.as_deref() != Some(source_sha.as_str());

            if !dry_run {
                let out = Command::new("git")
                    .arg("-C")
                    .arg(&canon_target)
                    .arg("fetch")
                    .arg("--quiet")
                    .arg("--no-tags")
                    .arg("--no-write-fetch-head")
                    .arg(&canon_donor)
                    .arg(&refspec)
                    .output()
                    .with_context(|| format!("failed to run `{command_preview}`"))?;
                if !out.status.success() {
                    bail!(
                        "`{command_preview}` failed: {}",
                        String::from_utf8_lossy(&out.stderr).trim()
                    );
                }

                let verified = run_git_ro(
                    &canon_target,
                    &["rev-parse", "--verify", &format!("{target_ref}^{{commit}}")],
                )?
                .trim()
                .to_string();
                if verified != source_sha {
                    bail!(
                        "quarry ref verification mismatch for `{target_ref}`: expected {source_sha}, got {verified}"
                    );
                }
            }

            actions.push(RefSyncAction {
                donor: donor_name.clone(),
                donor_path: canon_donor.to_string_lossy().to_string(),
                branch: branch.clone(),
                source_sha: source_sha.clone(),
                target_ref,
                previous_target_sha,
                new_target_sha: source_sha,
                refspec,
                command_preview,
                updated,
            });
        }
    }

    let after = capture_repo_safety_snapshot(&canon_target)?;
    let head_unchanged = before.head_symref_or_sha == after.head_symref_or_sha
        && before.head_commit == after.head_commit
        && before.branches_digest == after.branches_digest
        && before.tags_digest == after.tags_digest
        && before.fetch_head_digest == after.fetch_head_digest;
    let index_unchanged = before.index_digest == after.index_digest;
    let worktree_unchanged = before.status_porcelain == after.status_porcelain;

    if !head_unchanged || !index_unchanged || !worktree_unchanged {
        bail!(
            "quarry safety invariant violated on {}: head_unchanged={head_unchanged}, index_unchanged={index_unchanged}, worktree_unchanged={worktree_unchanged}",
            canon_target.display()
        );
    }

    Ok(QuarrySyncReport {
        target_repo: canon_target.to_string_lossy().to_string(),
        dry_run,
        synced_at: Utc::now().to_rfc3339(),
        head_before: before.head_commit,
        head_after: after.head_commit,
        head_unchanged,
        index_unchanged,
        worktree_unchanged,
        actions,
    })
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct DonorStatusSummary {
    pub donor: String,
    pub donor_path: String,
    pub donor_reachable: bool,
    pub branches: Vec<String>,
    pub synced_quarry_refs: BTreeMap<String, String>,
    pub total_entries: usize,
    pub by_state: BTreeMap<String, usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UptakeViolation {
    pub entry_id: String,
    pub donor: String,
    pub reason: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QuarryEntryStatus {
    pub id: String,
    pub donor: String,
    pub source_path: String,
    pub source_exists: Option<bool>,
    pub state: QuarryState,
    pub target_repo: String,
    pub destination_path: Option<String>,
    pub destination_exists: Option<bool>,
    pub audit_notes: String,
    pub required_cures: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QuarryStatusReport {
    pub target_repo: Option<String>,
    pub generated_at: String,
    pub state_filter: Option<String>,
    pub total_entries: usize,
    pub by_state: BTreeMap<String, usize>,
    pub donors: Vec<DonorStatusSummary>,
    pub all_uptaken_verified: bool,
    pub uptake_violations: Vec<UptakeViolation>,
    pub entries: Vec<QuarryEntryStatus>,
}

/// Audit `manifest` across donor states (`uptaken`, `queued_for_upgrade`, `idea_only`, `retired_slop`),
/// verifying destination existence and audit notes for every `uptaken` entry.
pub fn status_quarry(
    manifest: &QuarryManifest,
    target_repo_override: Option<&Path>,
    state_filter: Option<QuarryState>,
) -> Result<QuarryStatusReport> {
    let resolved_target: Option<PathBuf> = target_repo_override
        .map(Path::to_path_buf)
        .or_else(|| manifest.default_target_repo.clone())
        .map(|p| p.canonicalize().unwrap_or(p));

    let target_is_git = resolved_target
        .as_deref()
        .is_some_and(|p| p.is_dir() && run_git_ro_opt(p, &["rev-parse", "--git-dir"]).is_some());

    let mut donors_out = Vec::new();
    for (donor_name, spec) in &manifest.donors {
        let reachable = spec.path.exists();
        let mut synced_quarry_refs = BTreeMap::new();
        if target_is_git && let Some(ref trepo) = resolved_target {
            for br in &spec.branches {
                let qref = format!("refs/quarry/{donor_name}/{br}");
                if let Some(sha) = run_git_ro_opt(
                    trepo,
                    &["rev-parse", "--verify", &format!("{qref}^{{commit}}")],
                ) {
                    synced_quarry_refs.insert(br.clone(), sha);
                }
            }
        }

        let mut d_by_state = BTreeMap::new();
        let mut d_total = 0usize;
        for e in &manifest.entries {
            if &e.donor == donor_name {
                d_total += 1;
                *d_by_state.entry(e.state.as_str().to_string()).or_insert(0) += 1;
            }
        }

        donors_out.push(DonorStatusSummary {
            donor: donor_name.clone(),
            donor_path: spec.path.to_string_lossy().to_string(),
            donor_reachable: reachable,
            branches: spec.branches.clone(),
            synced_quarry_refs,
            total_entries: d_total,
            by_state: d_by_state,
        });
    }

    let mut by_state: BTreeMap<String, usize> = BTreeMap::new();
    for st in [
        QuarryState::Uptaken,
        QuarryState::QueuedForUpgrade,
        QuarryState::IdeaOnly,
        QuarryState::RetiredSlop,
    ] {
        by_state.insert(st.as_str().to_string(), 0);
    }

    let mut uptake_violations = Vec::new();
    let mut entries_out = Vec::new();

    for entry in &manifest.entries {
        *by_state
            .entry(entry.state.as_str().to_string())
            .or_insert(0) += 1;

        let donor_spec = manifest.donors.get(&entry.donor);
        let source_exists = donor_spec.and_then(|d| {
            if d.path.exists() {
                Some(d.path.join(&entry.source_path).exists())
            } else {
                None
            }
        });

        let checks_this_target =
            entry.target_repo == manifest.target_name || entry.target_repo == "obend";
        let destination_exists = match (&resolved_target, &entry.destination_path) {
            (Some(trepo), Some(dest)) if checks_this_target && trepo.exists() => {
                Some(trepo.join(dest).exists())
            }
            _ => None,
        };

        if entry.state == QuarryState::Uptaken {
            if entry.source_path.trim().is_empty() {
                uptake_violations.push(UptakeViolation {
                    entry_id: entry.id.clone(),
                    donor: entry.donor.clone(),
                    reason: "`uptaken` entry has empty `source_path`".to_string(),
                });
            }
            if entry.audit_notes.trim().is_empty() {
                uptake_violations.push(UptakeViolation {
                    entry_id: entry.id.clone(),
                    donor: entry.donor.clone(),
                    reason: "`uptaken` entry is missing `audit_notes`".to_string(),
                });
            }
            match &entry.destination_path {
                None => {
                    uptake_violations.push(UptakeViolation {
                        entry_id: entry.id.clone(),
                        donor: entry.donor.clone(),
                        reason: "`uptaken` entry has no `destination_path`".to_string(),
                    });
                }
                Some(dest) if dest.trim().is_empty() => {
                    uptake_violations.push(UptakeViolation {
                        entry_id: entry.id.clone(),
                        donor: entry.donor.clone(),
                        reason: "`uptaken` entry has blank `destination_path`".to_string(),
                    });
                }
                Some(dest) => {
                    if destination_exists == Some(false) {
                        uptake_violations.push(UptakeViolation {
                            entry_id: entry.id.clone(),
                            donor: entry.donor.clone(),
                            reason: format!(
                                "`uptaken` destination `{dest}` does not exist inside target repo `{}`",
                                resolved_target
                                    .as_ref()
                                    .map(|p| p.display().to_string())
                                    .unwrap_or_default()
                            ),
                        });
                    }
                }
            }
            if source_exists == Some(false) {
                uptake_violations.push(UptakeViolation {
                    entry_id: entry.id.clone(),
                    donor: entry.donor.clone(),
                    reason: format!(
                        "donor source_path `{}` does not exist in `{}`",
                        entry.source_path, entry.donor
                    ),
                });
            }
        }

        if state_filter.is_none_or(|flt| flt == entry.state) {
            entries_out.push(QuarryEntryStatus {
                id: entry.id.clone(),
                donor: entry.donor.clone(),
                source_path: entry.source_path.clone(),
                source_exists,
                state: entry.state,
                target_repo: entry.target_repo.clone(),
                destination_path: entry.destination_path.clone(),
                destination_exists,
                audit_notes: entry.audit_notes.clone(),
                required_cures: entry.required_cures.clone(),
            });
        }
    }

    let all_uptaken_verified = uptake_violations.is_empty();

    Ok(QuarryStatusReport {
        target_repo: resolved_target.map(|p| p.to_string_lossy().to_string()),
        generated_at: Utc::now().to_rfc3339(),
        state_filter: state_filter.map(|s| s.as_str().to_string()),
        total_entries: manifest.entries.len(),
        by_state,
        donors: donors_out,
        all_uptaken_verified,
        uptake_violations,
        entries: entries_out,
    })
}

/// Evaluation of one of the 6 Pre-Uptake Quarry Surgery Gates.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SurgeryGateResult {
    pub gate_id: String,
    pub title: String,
    pub passed: bool,
    pub defect_count: usize,
    pub summary: String,
}

/// Complete report from `obb quarry inspect <donor>:<path>`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QuarryInspectReport {
    pub spec: String,
    pub donor: String,
    pub donor_subpath: String,
    pub resolution_source: String,
    pub inspected_at: String,
    pub files_inspected: usize,
    pub ready_for_uptake: bool,
    pub matched_manifest_entries: Vec<QuarryEntry>,
    pub gates: Vec<SurgeryGateResult>,
    pub total_defects: usize,
    pub errors: usize,
    pub warnings: usize,
    pub modularity: ModularityReport,
    pub findings: Vec<Finding>,
}

/// Parse `<donor>:<path>` spec string.
pub fn parse_donor_path_spec(spec: &str) -> Result<(String, String)> {
    let Some((donor, raw_path)) = spec.split_once(':') else {
        bail!(
            "invalid quarry target `{spec}`: expected `<donor>:<path>` (e.g. `breadstuffs:orb/Crypto.lean`)"
        );
    };
    let donor = donor.trim();
    let clean_path = raw_path.trim().trim_matches('/');
    if donor.is_empty() || clean_path.is_empty() {
        bail!("invalid quarry target `{spec}`: both `<donor>` and `<path>` must be non-empty");
    }
    if clean_path.split('/').any(|seg| seg == "..") {
        bail!("invalid quarry target `{spec}`: parent traversal (`..`) is forbidden");
    }
    Ok((donor.to_string(), clean_path.to_string()))
}

#[derive(Debug)]
struct ExtractedFile {
    donor_rel_path: String,
    bytes: Vec<u8>,
}

fn extract_from_quarry_git_ref(
    target_repo: &Path,
    git_ref: &str,
    subpath: &str,
) -> Result<Option<(String, Vec<ExtractedFile>)>> {
    let Some(commit_sha) = run_git_ro_opt(
        target_repo,
        &["rev-parse", "--verify", &format!("{git_ref}^{{commit}}")],
    ) else {
        return Ok(None);
    };

    // Check if `commit_sha:subpath` exists and whether it is a `blob` or `tree`
    let Some(obj_type) = run_git_ro_opt(
        target_repo,
        &["cat-file", "-t", &format!("{commit_sha}:{subpath}")],
    ) else {
        bail!(
            "path `{subpath}` does not exist inside synced quarry ref `{git_ref}` ({commit_sha})"
        );
    };

    let mut out_files = Vec::new();
    match obj_type.trim() {
        "blob" => {
            let bytes = run_git_ro_bytes(
                target_repo,
                &["cat-file", "blob", &format!("{commit_sha}:{subpath}")],
            )?;
            out_files.push(ExtractedFile {
                donor_rel_path: subpath.to_string(),
                bytes,
            });
        }
        "tree" => {
            let ls_bytes = run_git_ro_bytes(
                target_repo,
                &["ls-tree", "-r", "-z", &commit_sha, "--", subpath],
            )?;
            for entry_bytes in ls_bytes.split(|b| *b == 0) {
                if entry_bytes.is_empty() {
                    continue;
                }
                let line = String::from_utf8_lossy(entry_bytes);
                let Some((meta, rel_p)) = line.split_once('\t') else {
                    continue;
                };
                let parts: Vec<&str> = meta.split_whitespace().collect();
                if parts.len() >= 3 && parts[1] == "blob" {
                    let blob_oid = parts[2];
                    let bytes = run_git_ro_bytes(target_repo, &["cat-file", "blob", blob_oid])?;
                    out_files.push(ExtractedFile {
                        donor_rel_path: rel_p.to_string(),
                        bytes,
                    });
                }
            }
        }
        other => {
            bail!("unsupported git object type `{other}` at `{git_ref}:{subpath}`");
        }
    }

    Ok(Some((
        format!("git:{git_ref}@{}", &commit_sha[..12.min(commit_sha.len())]),
        out_files,
    )))
}

fn extract_from_filesystem_ro(
    donor_root: &Path,
    subpath: &str,
) -> Result<(String, Vec<ExtractedFile>)> {
    let canon_root = donor_root
        .canonicalize()
        .with_context(|| format!("donor directory does not exist: {}", donor_root.display()))?;
    let target = canon_root.join(subpath);
    if !target.exists() {
        bail!(
            "path `{subpath}` does not exist under donor directory {}",
            canon_root.display()
        );
    }

    let mut out_files = Vec::new();
    if target.is_file() {
        let bytes = std::fs::read(&target)
            .with_context(|| format!("failed to read donor file {}", target.display()))?;
        out_files.push(ExtractedFile {
            donor_rel_path: subpath.to_string(),
            bytes,
        });
    } else {
        for entry in WalkDir::new(&target)
            .into_iter()
            .filter_entry(|e| {
                let name = e.file_name().to_string_lossy();
                !matches!(
                    name.as_ref(),
                    ".git" | ".lake" | "target" | "node_modules" | "__pycache__"
                )
            })
            .flatten()
        {
            if entry.file_type().is_file() {
                let rel = entry
                    .path()
                    .strip_prefix(&canon_root)
                    .unwrap_or(entry.path())
                    .to_string_lossy()
                    .replace('\\', "/");
                let bytes = std::fs::read(entry.path())?;
                out_files.push(ExtractedFile {
                    donor_rel_path: rel,
                    bytes,
                });
            }
        }
    }

    out_files.sort_by(|a, b| a.donor_rel_path.cmp(&b.donor_rel_path));
    Ok((format!("dir:{}", canon_root.display()), out_files))
}

fn staged_rel_path_for(donor_rel: &str) -> String {
    if donor_rel.ends_with(".lean") {
        // Stage donor `.lean` modules under `lean/Obend/...` in scratch dir so full library gates bite!
        let stripped = donor_rel
            .strip_prefix("lean/Obend/")
            .or_else(|| donor_rel.strip_prefix("lean/"))
            .unwrap_or(donor_rel);
        format!("lean/Obend/{stripped}")
    } else if donor_rel.ends_with(".rs")
        && !donor_rel.contains("/src/")
        && !donor_rel.starts_with("src/")
    {
        format!("crates/donor/src/{donor_rel}")
    } else {
        donor_rel.to_string()
    }
}

fn scan_donor_extra_surgery_hazards(donor_rel: &str, src: &str, findings: &mut Vec<Finding>) {
    // 1. HOL4 `.sml` / OCaml `.ml` cheat / oracle / axiom checks (`svenvs` uptake gate)
    if donor_rel.ends_with(".sml") || donor_rel.ends_with(".ml") {
        let mut in_sml_comment = 0usize;
        for (idx, line) in src.lines().enumerate() {
            let lno = idx + 1;
            let bytes = line.as_bytes();
            let mut clean = String::new();
            let mut k = 0usize;
            while k < bytes.len() {
                if k + 1 < bytes.len() && bytes[k] == b'(' && bytes[k + 1] == b'*' {
                    in_sml_comment += 1;
                    k += 2;
                    continue;
                }
                if k + 1 < bytes.len() && bytes[k] == b'*' && bytes[k + 1] == b')' {
                    in_sml_comment = in_sml_comment.saturating_sub(1);
                    k += 2;
                    continue;
                }
                if in_sml_comment == 0 {
                    clean.push(bytes[k] as char);
                }
                k += 1;
            }

            for bad_tok in ["cheat", "new_axiom", "mk_oracle_thm", "mk_thm"] {
                if contains_word(&clean, bad_tok) {
                    findings.push(Finding {
                        rule_id: "hol4/cheat-or-axiom".to_string(),
                        severity: Severity::Error,
                        artifact_kind: ArtifactKind::P,
                        max_regime: Regime::Attested,
                        sink: Some(Sink::Theater),
                        path: donor_rel.to_string(),
                        line: lno,
                        column: 1,
                        symbol: Some(bad_tok.to_string()),
                        message: format!(
                            "Donor HOL4/ML script invokes `{bad_tok}`, bypassing kernel proof checking"
                        ),
                        remediation: "Translate into a constructive Lean 4 kernel theorem with zero `sorry`/`axiom`.".to_string(),
                    });
                }
            }
        }
    }

    // 2. 2026 Cryptographic Literature Landmines (`ePrint 2026/1838`, `2026/2424`, `2026/2546`)
    if donor_rel.ends_with(".lean") || donor_rel.ends_with(".rs") {
        let lower_all = src.to_ascii_lowercase();

        // (a) Fenzi 2026/1838: Fiat-Shamir challenge-0 squeezed before absorbing statement/circuit descriptor
        if (lower_all.contains("fiatshamir") || lower_all.contains("transcript"))
            && (lower_all.contains("challenge0") || lower_all.contains("squeeze_challenge(0)"))
            && !lower_all.contains("descriptor")
            && !lower_all.contains("vk_digest")
            && !lower_all.contains("domain_sep")
            && !lower_all.contains("circuit_id")
        {
            findings.push(Finding {
                rule_id: "crypto/unbound-fs-challenge0".to_string(),
                severity: Severity::Warning,
                artifact_kind: ArtifactKind::S,
                max_regime: Regime::Attested,
                sink: Some(Sink::Miscalibrated),
                path: donor_rel.to_string(),
                line: 1,
                column: 1,
                symbol: None,
                message: "Fiat-Shamir transcript derives initial challenge without visible circuit/statement descriptor absorption (`ePrint 2026/1838` challenge-0 attack surface)".to_string(),
                remediation: "Absorb `(protocol_id, circuit_descriptor_digest, public_statement)` into the transcript sponge before squeezing challenge 0.".to_string(),
            });
        }

        // (b) Diamond-Gruen-Crites-Stewart 2026/2424: Binary Reed-Solomon / Ligerito unique-decoding / capacity proximity claim above Johnson bound
        if (lower_all.contains("ligerito")
            || lower_all.contains("binaryreedsolomon")
            || lower_all.contains("binary_rs"))
            && (lower_all.contains("capacity")
                || lower_all.contains("beyond_johnson")
                || lower_all.contains("1 - rate"))
        {
            findings.push(Finding {
                rule_id: "crypto/binary-rs-beyond-johnson".to_string(),
                severity: Severity::Error,
                artifact_kind: ArtifactKind::W,
                max_regime: Regime::Attested,
                sink: Some(Sink::Miscalibrated),
                path: donor_rel.to_string(),
                line: 1,
                column: 1,
                symbol: None,
                message: "Binary Reed-Solomon / Ligerito proximity parameter references capacity / beyond-Johnson regime, refuted by `ePrint 2026/2424`".to_string(),
                remediation: "Cap binary linear/RS proximity strictly below the proven Johnson / list-decoding bound (`1 - sqrt(rate)`).".to_string(),
            });
        }
    }
}

fn contains_word(haystack: &str, word: &str) -> bool {
    haystack
        .split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .any(|tok| tok == word)
}

/// Inspect `<donor>:<path>` against `obb lint` and the 6-Gate Pre-Uptake Quarry Surgery Checklist.
pub fn inspect_quarry_target(
    spec: &str,
    target_repo: Option<&Path>,
    donor_path_override: Option<&Path>,
    manifest: Option<&QuarryManifest>,
    branch_override: Option<&str>,
) -> Result<QuarryInspectReport> {
    let (donor, subpath) = parse_donor_path_spec(spec)?;

    let donor_spec = manifest.and_then(|m| m.donors.get(&donor));
    let branch = branch_override
        .or_else(|| donor_spec.map(DonorSpec::primary_branch))
        .unwrap_or("main");

    let (resolution_source, extracted_files) = if let Some(explicit_dir) = donor_path_override {
        extract_from_filesystem_ro(explicit_dir, &subpath)?
    } else {
        let mut from_git = None;
        if let Some(trepo) = target_repo
            && trepo.is_dir()
            && run_git_ro_opt(trepo, &["rev-parse", "--git-dir"]).is_some()
        {
            let qref = format!("refs/quarry/{donor}/{branch}");
            from_git = extract_from_quarry_git_ref(trepo, &qref, &subpath)?;
        }
        if let Some(found) = from_git {
            found
        } else if let Some(dspec) = donor_spec {
            extract_from_filesystem_ro(&dspec.path, &subpath)?
        } else {
            bail!(
                "cannot resolve `{spec}`: pass `--donor-path <dir>`, sync `refs/quarry/{donor}/{branch}` in `--repo`, or supply `--manifest <quarry.toml>`"
            );
        }
    };

    if extracted_files.is_empty() {
        bail!("`{spec}` resolved via `{resolution_source}`, but contained 0 files");
    }

    // Stage into isolated temporary directory
    let stage_dir = tempfile::tempdir().context("failed to create temporary quarry stage dir")?;
    let mut staged_to_donor: BTreeMap<String, String> = BTreeMap::new();
    let mut extra_findings: Vec<Finding> = Vec::new();

    for ef in &extracted_files {
        let staged_rel = staged_rel_path_for(&ef.donor_rel_path);
        let full_path = stage_dir.path().join(&staged_rel);
        if let Some(parent) = full_path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(&full_path, &ef.bytes)?;
        staged_to_donor.insert(staged_rel, ef.donor_rel_path.clone());

        if let Ok(utf8) = std::str::from_utf8(&ef.bytes) {
            scan_donor_extra_surgery_hazards(&ef.donor_rel_path, utf8, &mut extra_findings);
        }
    }

    let mut lint_report = run_repo_lints(stage_dir.path())?;
    let lean_idx = build_lean_index(stage_dir.path());

    // Flag `set_option maxHeartbeats > 400_000` in staged donor Lean files for Gate 6
    for lf in &lean_idx.files {
        let orig_path = staged_to_donor
            .get(&lf.rel_path)
            .or_else(|| staged_to_donor.get(&format!("lean/{}", lf.rel_path)))
            .cloned()
            .unwrap_or_else(|| lf.rel_path.clone());
        for (hb, line) in &lf.max_heartbeats {
            if *hb > 400_000 {
                extra_findings.push(Finding {
                    rule_id: "lean/heartbeat-cap".to_string(),
                    severity: Severity::Warning,
                    artifact_kind: ArtifactKind::P,
                    max_regime: Regime::Decided,
                    sink: Some(Sink::Slow),
                    path: orig_path.clone(),
                    line: *line,
                    column: 1,
                    symbol: None,
                    message: format!(
                        "`set_option maxHeartbeats {hb}` exceeds the 400,000 elaboration budget cap"
                    ),
                    remediation:
                        "Decompose proof into smaller lemmas instead of inflating `maxHeartbeats`."
                            .to_string(),
                });
            }
        }
    }

    // Normalize staged paths back to clean donor-relative paths
    for f in &mut lint_report.findings {
        let old_path = f.path.clone();
        if let Some(orig) = staged_to_donor
            .get(&old_path)
            .or_else(|| staged_to_donor.get(&format!("lean/{old_path}")))
        {
            f.path = orig.clone();
            if old_path != f.path {
                f.message = f.message.replace(&old_path, &f.path);
                f.remediation = f.remediation.replace(&old_path, &f.path);
            }
        } else if let Some(stripped) = old_path.strip_prefix("lean/Obend/") {
            f.path = stripped.to_string();
            f.message = f.message.replace(&old_path, &f.path);
            f.remediation = f.remediation.replace(&old_path, &f.path);
        }
    }
    for m in &mut lint_report.modularity.monolithic_modules {
        if let Some(orig) = staged_to_donor
            .get(&m.path)
            .or_else(|| staged_to_donor.get(&format!("lean/{}", m.path)))
        {
            m.path = orig.clone();
        }
    }
    if let Some(ref mut max_p) = lint_report.modularity.max_module_path
        && let Some(orig) = staged_to_donor
            .get(max_p)
            .or_else(|| staged_to_donor.get(&format!("lean/{max_p}")))
    {
        *max_p = orig.clone();
    }

    // Attach matching `quarry.toml` entries (overlap on `source_path`)
    let mut matched_manifest_entries = Vec::new();
    if let Some(m) = manifest {
        for entry in &m.entries {
            if entry.donor == donor {
                let ep = entry.source_path.trim_matches('/');
                if ep == subpath
                    || subpath.starts_with(&format!("{ep}/"))
                    || ep.starts_with(&format!("{subpath}/"))
                {
                    if entry.state == QuarryState::RetiredSlop {
                        extra_findings.push(Finding {
                            rule_id: "quarry/retired-slop-blocked".to_string(),
                            severity: Severity::Error,
                            artifact_kind: ArtifactKind::M,
                            max_regime: Regime::Attested,
                            sink: Some(Sink::Scar),
                            path: entry.source_path.clone(),
                            line: 1,
                            column: 1,
                            symbol: Some(entry.id.clone()),
                            message: format!(
                                "Manifest marks `{}` (`{}:{}`) as `retired_slop`: {}",
                                entry.id, entry.donor, entry.source_path, entry.audit_notes
                            ),
                            remediation: "Do not uptake `retired_slop` code into `obend`; keep quarantined in `refs/quarry/*` for historical reference only.".to_string(),
                        });
                    }
                    matched_manifest_entries.push(entry.clone());
                }
            }
        }
    }

    let mut findings = lint_report.findings;
    findings.extend(extra_findings);
    findings.sort_by(|a, b| {
        a.path
            .cmp(&b.path)
            .then_with(|| a.line.cmp(&b.line))
            .then_with(|| a.column.cmp(&b.column))
            .then_with(|| a.rule_id.cmp(&b.rule_id))
    });

    let count_rules = |rule_ids: &[&str]| -> usize {
        findings
            .iter()
            .filter(|f| rule_ids.iter().any(|r| f.rule_id == *r))
            .count()
    };

    // Evaluate the 6-Gate Pre-Uptake Quarry Surgery Checklist
    let g1_defects = count_rules(&[
        "lean/sorry-or-axiom",
        "lean/native-decide-in-proof",
        "hol4/cheat-or-axiom",
        "quarry/retired-slop-blocked",
    ]);
    let g2_defects = count_rules(&[
        "lean/closed-soundness-claim",
        "lean/trivial-conclusion",
        "lean/unused-param",
        "lean/tautological-judge-meaning",
        "lean/discarded-tactic-binding",
        "obend/tautological-law",
        "obend/claim-restates-method",
    ]);
    let g3_defects = count_rules(&[
        "lean/narrow-digest-weld",
        "crypto/unbound-fs-challenge0",
        "crypto/binary-rs-beyond-johnson",
    ]);
    let g4_defects = count_rules(&["lean/uninhabited-premise-risk"]);
    let g5_defects = count_rules(&[
        "lean/hardcoded-wire-decoder",
        "lean/cosplay-naming",
        "rust/mock-backend-in-src",
        "rust/obend-semantic-mirror",
        "python/e2e-mock-bridge",
        "python/e2e-self-mock",
    ]);
    let g6_defects = count_rules(&["lean/monolithic-module", "lean/heartbeat-cap"]);

    let gates = vec![
        SurgeryGateResult {
            gate_id: "G1-kernel-purity".to_string(),
            title: "Kernel & Axiom Purity (0 sorry, 0 axiom, 0 cheat, 0 native_decide/ofReduceBool)".to_string(),
            passed: g1_defects == 0,
            defect_count: g1_defects,
            summary: format!("{g1_defects} kernel-purity/trust-bypass defect(s)"),
        },
        SurgeryGateResult {
            gate_id: "G2-universal-anti-vacuity".to_string(),
            title: "Universal Soundness & Anti-Vacuity (∀ quantification, non-tautological Meaning, used params)".to_string(),
            passed: g2_defects == 0,
            defect_count: g2_defects,
            summary: format!("{g2_defects} vacuity/tautology/closed-claim defect(s)"),
        },
        SurgeryGateResult {
            gate_id: "G3-crypto-full-width-binding".to_string(),
            title: "Full-Width >=256-Bit Cryptographic Binding & 2026 Parameter Floors".to_string(),
            passed: g3_defects == 0,
            defect_count: g3_defects,
            summary: format!("{g3_defects} narrow-digest/2026-crypto defect(s)"),
        },
        SurgeryGateResult {
            gate_id: "G4-hypothesis-ledger-inhabited".to_string(),
            title: "Inhabited-Premise & HypothesisLedger Anti-Vacuity Witness".to_string(),
            passed: g4_defects == 0,
            defect_count: g4_defects,
            summary: format!("{g4_defects} unwitnessed `_sound` premise(s)"),
        },
        SurgeryGateResult {
            gate_id: "G5-executable-spine-no-mocks".to_string(),
            title: "Single Executable Spine (no hardcoded wire decoders, mocks, or cosplay poles)".to_string(),
            passed: g5_defects == 0,
            defect_count: g5_defects,
            summary: format!("{g5_defects} mock/wire-shortcut/cosplay defect(s)"),
        },
        SurgeryGateResult {
            gate_id: "G6-compositional-modularity".to_string(),
            title: "Compositional Modularity & Elaboration Budget (<=4,000 lines, maxHeartbeats <=400k)".to_string(),
            passed: g6_defects == 0,
            defect_count: g6_defects,
            summary: format!(
                "{g6_defects} modularity/budget violation(s) (max_lines={}, compositionality_index={:.1})",
                lint_report.modularity.max_module_lines,
                lint_report.modularity.compositionality_index
            ),
        },
    ];

    let errors = findings
        .iter()
        .filter(|f| f.severity == Severity::Error)
        .count();
    let warnings = findings
        .iter()
        .filter(|f| f.severity == Severity::Warning)
        .count();
    let ready_for_uptake = gates.iter().all(|g| g.passed) && errors == 0;

    Ok(QuarryInspectReport {
        spec: spec.to_string(),
        donor,
        donor_subpath: subpath,
        resolution_source,
        inspected_at: Utc::now().to_rfc3339(),
        files_inspected: extracted_files.len(),
        ready_for_uptake,
        matched_manifest_entries,
        gates,
        total_defects: findings.len(),
        errors,
        warnings,
        modularity: lint_report.modularity,
        findings,
    })
}

fn run_git_ro(repo_root: &Path, args: &[&str]) -> Result<String> {
    let bytes = run_git_ro_bytes(repo_root, args)?;
    Ok(String::from_utf8_lossy(&bytes).to_string())
}

fn run_git_ro_opt(repo_root: &Path, args: &[&str]) -> Option<String> {
    run_git_ro(repo_root, args)
        .ok()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
}

fn run_git_ro_bytes(repo_root: &Path, args: &[&str]) -> Result<Vec<u8>> {
    let out = Command::new("git")
        .arg("--no-optional-locks")
        .arg("-C")
        .arg(repo_root)
        .args(args)
        .output()
        .with_context(|| {
            format!(
                "failed to execute git {:?} in {}",
                args,
                repo_root.display()
            )
        })?;
    if !out.status.success() {
        bail!(
            "git {:?} failed in {}: {}",
            args,
            repo_root.display(),
            String::from_utf8_lossy(&out.stderr).trim()
        );
    }
    Ok(out.stdout)
}
