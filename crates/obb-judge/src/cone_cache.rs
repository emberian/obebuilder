//! Opt-in reuse of authenticated verdicts for clean, committed input cones.

use crate::{receipt_auth, run_git_ro};
use anyhow::{Context, Result, bail};
use obb_core::sha256_hex;
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use std::io::Write;
use std::path::{Component, Path};
use std::sync::OnceLock;

pub(crate) fn clean_for_cache(repo: &Path) -> Result<bool> {
    let status = run_git_ro(
        repo,
        &["status", "--porcelain", "-z", "--untracked-files=all"],
    )?;
    Ok(status
        .split('\0')
        .filter(|s| !s.is_empty())
        .all(is_runtime_status_entry))
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
    key: Option<Vec<u8>>,
}

impl<'a> ConeCache<'a> {
    pub(crate) fn open(repo: &'a Path, enabled: bool, signing_key: Option<&[u8]>) -> Result<Self> {
        let mut cache = Self {
            repo,
            tree: String::new(),
            entries: Vec::new(),
            key: None,
        };
        // Non-git and dirty construction workspaces always execute checks, never reuse HEAD.
        if !enabled || !clean_for_cache(repo).unwrap_or(false) {
            return Ok(cache);
        }
        cache.tree = run_git_ro(repo, &["rev-parse", "HEAD^{tree}"])?
            .trim()
            .into();
        cache.entries = run_git_ro(repo, &["ls-tree", "-r", "-t", "-z", "--full-tree", "HEAD"])?
            .split('\0')
            .filter(|s| !s.is_empty())
            .map(str::to_string)
            .collect();
        cache.entries.sort();
        cache.key = Some(match signing_key {
            Some(key) => key.to_vec(),
            None => receipt_auth::ensure_receipt_key(None, repo)?,
        });
        Ok(cache)
    }

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
        let selected: Vec<_> = self
            .entries
            .iter()
            .filter(|entry| {
                let Some((_, path)) = entry.split_once('\t') else {
                    return false;
                };
                patterns.iter().any(|pattern| matches_input(pattern, path))
            })
            .collect();
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

    pub(crate) fn read<T: DeserializeOwned + Serialize>(
        &self,
        digest: Option<&str>,
    ) -> Result<Option<T>> {
        let (Some(digest), Some(key)) = (digest, &self.key) else {
            return Ok(None);
        };
        let path = self
            .repo
            .join(".obb/cache/cones")
            .join(format!("{digest}.json"));
        let Ok(bytes) = std::fs::read(path) else {
            return Ok(None);
        };
        let Ok(entry) = serde_json::from_slice::<Entry<T>>(&bytes) else {
            return Ok(None);
        };
        let message = serde_json::to_vec(&(&entry.digest, &entry.value))?;
        if entry.digest != digest || !receipt_auth::verify_mac(key, &message, &entry.mac) {
            return Ok(None);
        }
        Ok(Some(entry.value))
    }

    pub(crate) fn write<T: Serialize>(&self, digest: Option<&str>, value: &T) -> Result<()> {
        let (Some(digest), Some(key)) = (digest, &self.key) else {
            return Ok(());
        };
        if !clean_for_cache(self.repo)?
            || run_git_ro(self.repo, &["rev-parse", "HEAD^{tree}"])?.trim() != self.tree
        {
            return Ok(());
        }
        let dir = self.repo.join(".obb/cache/cones");
        std::fs::create_dir_all(&dir)?;
        let mac = receipt_auth::mac_hex(key, &serde_json::to_vec(&(digest, value))?);
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
