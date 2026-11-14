//! Opt-in reuse of authenticated verdicts for clean, committed input cones.

use crate::{receipt_auth, run_git_ro, should_skip_sandbox_entry};
use anyhow::{Context, Result, bail};
use obb_core::sha256_hex;
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use std::io::Write;
use std::path::{Component, Path, PathBuf};
use std::sync::OnceLock;

/// `core.fsmonitor` is repository configuration, so a candidate could point it at a hook that
/// reports "nothing changed". Status is always computed by git itself.
const STATUS: [&str; 6] = [
    "-c",
    "core.fsmonitor=false",
    "status",
    "--porcelain",
    "-z",
    "--untracked-files=all",
];

pub(crate) fn clean_for_cache(repo: &Path) -> Result<bool> {
    let status = run_git_ro(repo, &STATUS)?;
    Ok(status
        .split('\0')
        .filter(|s| !s.is_empty())
        .all(is_runtime_status_entry)
        && hidden_index_entries(repo)?.is_empty())
}

/// Exempt only untracked judge/vault metadata, never tracked source modifications.
pub fn is_runtime_status_entry(entry: &str) -> bool {
    entry.strip_prefix("?? ").is_some_and(|path| {
        path == ".obb/receipt.key"
            || path.starts_with(".obb/cache/")
            || path.starts_with(".obb/ledger/")
            || path.starts_with(".obb-state/")
    })
}

/// Index entries whose working-tree content `git status` does not compare with `HEAD`:
/// `assume-unchanged` (lowercase tag) and `skip-worktree` (`S`). Each is returned as
/// `<tag> <path>`. A tree carrying any of them is not known to equal its commit.
pub fn hidden_index_entries(repo: &Path) -> Result<Vec<String>> {
    Ok(run_git_ro(repo, &["ls-files", "-v", "-z"])?
        .split('\0')
        .filter(|entry| !entry.is_empty() && !entry.starts_with("H "))
        .map(str::to_string)
        .collect())
}

/// Ignored paths a check could still read. Status never reports their content and the tree
/// digest does not cover it, so a cone that reaches one of them is not reusable.
fn ignored_paths(repo: &Path) -> Result<Vec<String>> {
    let mut args = STATUS.to_vec();
    args.push("--ignored=matching");
    let mut ignored: Vec<String> = run_git_ro(repo, &args)?
        .split('\0')
        .filter_map(|entry| entry.strip_prefix("!! "))
        .filter(|path| {
            // Judge metadata, and directories neither the sandbox copy nor the scanners enter.
            let mut components = path.trim_end_matches('/').split('/');
            components.clone().next() != Some(".obb") && !components.any(should_skip_sandbox_entry)
        })
        .map(str::to_string)
        .collect();
    ignored.sort();
    Ok(ignored)
}

/// Whether an ignored path is selected by `pattern`, or is a directory that could hold
/// something `pattern` selects. Errs toward "yes".
fn ignored_in_cone(pattern: &str, ignored: &str) -> bool {
    let path = ignored.trim_end_matches('/');
    if matches_input(pattern, path) {
        return true;
    }
    if !ignored.ends_with('/') {
        return false;
    }
    let dir = format!("{path}/");
    match pattern.find(['*', '?']) {
        None => pattern.starts_with(&dir),
        Some(wildcard) => {
            let literal = &pattern[..wildcard];
            literal.starts_with(&dir) || dir.starts_with(literal)
        }
    }
}

#[derive(Serialize, Deserialize)]
struct Entry<T> {
    digest: String,
    value: T,
    mac: String,
}

pub(crate) struct ConeCache<'a> {
    repo: &'a Path,
    tree: String,
    entries: Vec<String>,
    ignored: Vec<String>,
    key: Option<Vec<u8>>,
}

impl<'a> ConeCache<'a> {
    pub(crate) fn open(repo: &'a Path, enabled: bool, signing_key: Option<&[u8]>) -> Result<Self> {
        let mut cache = Self {
            repo,
            tree: String::new(),
            entries: Vec::new(),
            ignored: Vec::new(),
            key: None,
        };
        // Non-git and dirty construction workspaces always execute checks, never reuse HEAD.
        if !enabled || !clean_for_cache(repo).unwrap_or(false) {
            return Ok(cache);
        }
        // A repository without a commit has no tree to bind a verdict to.
        let Ok(tree) = run_git_ro(repo, &["rev-parse", "--verify", "HEAD^{tree}"]) else {
            return Ok(cache);
        };
        cache.tree = tree.trim().into();
        // List the tree that was resolved, not whatever `HEAD` names by the time this runs.
        cache.entries = run_git_ro(
            repo,
            &["ls-tree", "-r", "-t", "-z", "--full-tree", &cache.tree],
        )?
        .split('\0')
        .filter(|s| !s.is_empty())
        .map(str::to_string)
        .collect();
        cache.entries.sort();
        cache.ignored = ignored_paths(repo)?;
        cache.key = Some(match signing_key {
            Some(key) => key.to_vec(),
            None => receipt_auth::ensure_receipt_key(None, repo)?,
        });
        Ok(cache)
    }

    /// `None` means "execute the check": reuse is off, or the tree entries cannot stand in
    /// for everything the declared cone covers.
    pub(crate) fn digest<T: Serialize>(
        &self,
        inputs: &[String],
        definition: &T,
        extra: &[String],
    ) -> Result<Option<String>> {
        if self.key.is_none() || inputs.is_empty() {
            return Ok(None);
        }
        let mut patterns = inputs.to_vec();
        for pattern in &mut patterns {
            if pattern.is_empty()
                || Path::new(pattern).components().any(|c| {
                    matches!(
                        c,
                        Component::ParentDir | Component::RootDir | Component::Prefix(_)
                    )
                })
            {
                bail!("input cone must use nonempty repository-relative paths: {pattern:?}");
            }
            *pattern = pattern
                .trim_start_matches("./")
                .trim_end_matches('/')
                .to_string();
            if pattern.is_empty() {
                *pattern = ".".into();
            }
        }
        patterns.sort();
        patterns.dedup();
        let mut matched = vec![false; patterns.len()];
        let mut selected = Vec::new();
        for entry in &self.entries {
            let Some((meta, path)) = entry.split_once('\t') else {
                continue;
            };
            let mut hit = false;
            for (pattern, seen) in patterns.iter().zip(&mut matched) {
                if matches_input(pattern, path) {
                    *seen = true;
                    hit = true;
                }
            }
            if !hit {
                continue;
            }
            // A symlink's blob is only its target text, and a gitlink pins a commit without
            // saying what the submodule checkout holds. Neither binds the bytes a check reads.
            if meta.starts_with("120000 ") || meta.starts_with("160000 ") {
                return Ok(None);
            }
            selected.push(entry);
        }
        // A pattern selecting nothing (a typo, a path not committed yet) would leave the digest
        // constant across every later change to the files it was meant to name.
        if matched.contains(&false)
            || self.ignored.iter().any(|ignored| {
                patterns
                    .iter()
                    .any(|pattern| ignored_in_cone(pattern, ignored))
            })
        {
            return Ok(None);
        }
        // The executable binds reuse to the implementation, including linked linter/runner code.
        static RUNNER: OnceLock<String> = OnceLock::new();
        let runner = if let Some(digest) = RUNNER.get() {
            digest.clone()
        } else {
            let digest = sha256_hex(&std::fs::read(std::env::current_exe()?)?);
            RUNNER.get_or_init(|| digest).clone()
        };
        Ok(Some(sha256_hex(&serde_json::to_vec(&(
            "obb-cone-v1",
            runner,
            patterns,
            definition,
            extra,
            selected,
        ))?)))
    }

    /// `.obb/cache/cones`, unless a symlinked component would carry cache reads and writes
    /// out of the repository.
    fn cones_dir(&self) -> Option<PathBuf> {
        let mut dir = self.repo.to_path_buf();
        for component in [".obb", "cache", "cones"] {
            dir.push(component);
            if dir
                .symlink_metadata()
                .is_ok_and(|meta| meta.file_type().is_symlink())
            {
                return None;
            }
        }
        Some(dir)
    }

    pub(crate) fn read<T: DeserializeOwned + Serialize>(
        &self,
        digest: Option<&str>,
    ) -> Result<Option<T>> {
        let (Some(digest), Some(key), Some(dir)) = (digest, &self.key, self.cones_dir()) else {
            return Ok(None);
        };
        let Ok(bytes) = std::fs::read(dir.join(format!("{digest}.json"))) else {
            return Ok(None);
        };
        let Ok(entry) = serde_json::from_slice::<Entry<T>>(&bytes) else {
            return Ok(None);
        };
        let message = serde_json::to_vec(&(&entry.digest, &entry.value))?;
        if entry.digest != digest
            || !receipt_auth::verify_mac(key, receipt_auth::CONE_CONTEXT, &message, &entry.mac)
        {
            return Ok(None);
        }
        Ok(Some(entry.value))
    }

    pub(crate) fn write<T: Serialize>(&self, digest: Option<&str>, value: &T) -> Result<()> {
        let (Some(digest), Some(key), Some(dir)) = (digest, &self.key, self.cones_dir()) else {
            return Ok(());
        };
        // The verdict was computed from the working tree; it is recorded against `tree` only
        // if the two still agree after the check ran.
        if !clean_for_cache(self.repo)?
            || run_git_ro(self.repo, &["rev-parse", "--verify", "HEAD^{tree}"])?.trim()
                != self.tree
            || ignored_paths(self.repo)? != self.ignored
        {
            return Ok(());
        }
        std::fs::create_dir_all(&dir)?;
        let mac = receipt_auth::mac_hex(
            key,
            receipt_auth::CONE_CONTEXT,
            &serde_json::to_vec(&(digest, value))?,
        );
        let entry = Entry {
            digest: digest.to_string(),
            value,
            mac,
        };
        let mut file = tempfile::NamedTempFile::new_in(&dir)?;
        serde_json::to_writer(&mut file, &entry)?;
        file.flush()?;
        file.persist(dir.join(format!("{digest}.json")))
            .context("persisting cone verdict")?;
        Ok(())
    }
}

/// Literal paths include descendants; glob syntax supports `*`, `?`, and recursive `**`.
fn matches_input(pattern: &str, path: &str) -> bool {
    if pattern == "."
        || path == pattern
        || path
            .strip_prefix(pattern)
            .is_some_and(|tail| tail.starts_with('/'))
    {
        return true;
    }
    if !pattern.contains(['*', '?']) {
        return false;
    }
    let pattern = pattern.as_bytes();
    let path = path.as_bytes();
    let mut rows = vec![vec![false; path.len() + 1]; pattern.len() + 1];
    rows[pattern.len()][path.len()] = true;
    for i in (0..pattern.len()).rev() {
        for j in (0..=path.len()).rev() {
            rows[i][j] = match pattern[i] {
                b'*' => {
                    let recursive =
                        pattern.get(i + 1) == Some(&b'*') || (i > 0 && pattern[i - 1] == b'*');
                    rows[i + 1][j]
                        || (j < path.len() && (recursive || path[j] != b'/') && rows[i][j + 1])
                        || (recursive && pattern.get(i + 1) == Some(&b'/') && rows[i + 2][j])
                }
                b'?' => j < path.len() && path[j] != b'/' && rows[i + 1][j + 1],
                byte => j < path.len() && byte == path[j] && rows[i + 1][j + 1],
            };
        }
    }
    rows[0][0]
}
