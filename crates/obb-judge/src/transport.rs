//! Wire-v2 pass transport for command floors evaluated on exact, committed file views.
use super::{Floor, Gate, JudgeCheckReport, JudgeReceipt, configure_hermetic_git, run_git_ro};
use anyhow::{Context, Result, bail, ensure};
use obb_core::sha256_hex;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::os::unix::fs::PermissionsExt;
use std::path::Path;
use std::process::Command;
use std::sync::OnceLock;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TransportCone {
    pub cone_blobs: BTreeMap<String, String>,
    pub cone_oids: BTreeMap<String, String>,
    pub cone_modes: BTreeMap<String, String>,
    pub cone_merkle_root: String,
    pub toolchain_sha256: String,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
pub enum Transport {
    Transported,
    Invalidated { changed_paths: Vec<String> },
}

fn executable_digest() -> Result<String> {
    static DIGEST: OnceLock<String> = OnceLock::new();
    if let Some(digest) = DIGEST.get() {
        return Ok(digest.clone());
    }
    let digest = sha256_hex(&serde_json::to_vec(&(
        "obb-runtime-v2",
        sha256_hex(&std::fs::read(std::env::current_exe()?)?),
        sha256_hex(&std::fs::read("/bin/sh")?),
        std::env::var("OBB_RUNTIME_ID").unwrap_or_default(),
    ))?);
    Ok(DIGEST.get_or_init(|| digest).clone())
}

fn literal(path: &str) -> bool {
    !path.contains(['*', '?', '[', '\0'])
        && path.len() <= 4096
        && path
            .split('/')
            .all(|p| !matches!(p, "" | "." | "..") && !p.eq_ignore_ascii_case(".git"))
}

fn command_inputs(floor: &Floor) -> Option<&[String]> {
    match floor {
        Floor::Configured {
            command: Some(_),
            inputs,
            ..
        } if !inputs.is_empty() && inputs.iter().all(|p| literal(p)) => Some(inputs),
        _ => None,
    }
}

pub(super) fn check_unit(gate: &Gate) -> Result<()> {
    ensure!(
        !gate.floors.is_empty() && gate.teeth.is_empty(),
        "cone-unit requires file command floors"
    );
    for floor in &gate.floors {
        ensure!(
            command_inputs(floor).is_some()
                && matches!(floor.core(), Floor::Named(_))
                && gate.method_for("cone-unit@1", floor)
                    == Some(&super::Method::Eval(super::TrustBase::External(
                        "shell".into()
                    )))
                && gate
                    .basis
                    .contains(&super::TrustBase::External("shell".into())),
            "invalid cone-unit command or method"
        );
    }
    Ok(())
}

fn entries(repo: &Path, tree: &str, paths: &[&str]) -> Result<BTreeMap<String, (String, String)>> {
    ensure!(
        matches!(tree.len(), 40 | 64) && tree.bytes().all(|b| b.is_ascii_hexdigit()),
        "expected full tree OID"
    );
    ensure!(
        run_git_ro(repo, &["--no-replace-objects", "cat-file", "-t", tree])?.trim() == "tree",
        "expected tree object"
    );
    let mut found = BTreeMap::new();
    for chunk in paths.chunks(64) {
        let mut args = vec![
            "--no-replace-objects",
            "--literal-pathspecs",
            "ls-tree",
            "--full-tree",
            "-z",
            tree,
            "--",
        ];
        args.extend_from_slice(chunk);
        for record in run_git_ro(repo, &args)?
            .split('\0')
            .filter(|r| !r.is_empty())
        {
            let (header, path) = record.split_once('\t').context("malformed ls-tree entry")?;
            let fields: Vec<_> = header.split(' ').collect();
            if let [mode @ ("100644" | "100755"), "blob", oid] = fields.as_slice() {
                found.insert(path.to_owned(), (mode.to_string(), oid.to_string()));
            }
        }
    }
    Ok(found)
}

fn blob(repo: &Path, oid: &str) -> Result<Vec<u8>> {
    let out = configure_hermetic_git(&mut Command::new("git"))
        .arg("-C")
        .arg(repo)
        .args(["--no-replace-objects", "cat-file", "blob", oid])
        .output()?;
    ensure!(out.status.success(), "could not read committed blob");
    Ok(out.stdout)
}

/// Use the same immutable file view for evaluation and receipt issuance. Other
/// floor shapes keep their existing evaluator and produce tree-bound evidence.
pub(super) fn project(repo: &Path, tree: &str, floor: &Floor, dest: &Path) -> Result<()> {
    let inputs = command_inputs(floor).context("invalid unit inputs")?;
    let paths: Vec<_> = inputs.iter().map(String::as_str).collect();
    let files = entries(repo, tree.trim(), &paths)?;
    ensure!(
        paths.iter().all(|p| files.contains_key(*p)),
        "cone-unit requires committed regular files"
    );
    for (path, (mode, oid)) in files {
        let file = dest.join(path);
        std::fs::create_dir_all(file.parent().context("missing parent")?)?;
        std::fs::write(&file, blob(repo, &oid)?)?;
        std::fs::set_permissions(
            file,
            std::fs::Permissions::from_mode(if mode == "100755" { 0o755 } else { 0o644 }),
        )?;
    }
    Ok(())
}

impl TransportCone {
    fn root(&self) -> Result<String> {
        ensure!(
            self.cone_blobs.keys().eq(self.cone_modes.keys())
                && self.cone_blobs.keys().eq(self.cone_oids.keys()),
            "inconsistent cone modes"
        );
        let mut nodes = Vec::new();
        for (path, hash) in &self.cone_blobs {
            ensure!(literal(path), "invalid cone path");
            nodes.push(sha256_hex(&serde_json::to_vec(&(
                "obb-cone-leaf-v2",
                path,
                &self.cone_modes[path],
                hash,
            ))?));
        }
        while nodes.len() > 1 {
            nodes = nodes
                .chunks(2)
                .map(|pair| {
                    sha256_hex(
                        format!("obb-cone-node-v2\0{}{}", pair[0], pair.last().unwrap()).as_bytes(),
                    )
                })
                .collect();
        }
        Ok(nodes
            .pop()
            .unwrap_or_else(|| sha256_hex(b"obb-cone-empty-v2")))
    }
}

pub(super) fn issue(
    gate: &Gate,
    repo: &Path,
    tree: &str,
    report: &JudgeCheckReport,
    clean: bool,
) -> Result<TransportCone> {
    let mut cone = TransportCone {
        cone_blobs: BTreeMap::new(),
        cone_modes: BTreeMap::new(),
        cone_oids: BTreeMap::new(),
        cone_merkle_root: String::new(),
        toolchain_sha256: executable_digest()?,
    };
    if gate.formats == ["cone-unit@1"]
        && clean
        && report.all_passed
        && report.teeth_report.total == 0
        && !gate.floors.is_empty()
        && gate.floors.iter().all(|f| command_inputs(f).is_some())
    {
        let paths: std::collections::BTreeSet<_> = gate
            .floors
            .iter()
            .flat_map(Floor::inputs)
            .map(String::as_str)
            .collect();
        let files = entries(repo, tree, &paths.iter().copied().collect::<Vec<_>>())?;
        if files.keys().map(String::as_str).eq(paths) {
            for (path, (mode, oid)) in files {
                cone.cone_blobs
                    .insert(path.clone(), sha256_hex(&blob(repo, &oid)?));
                cone.cone_oids.insert(path.clone(), oid);
                cone.cone_modes.insert(path, mode);
            }
        }
    }
    cone.cone_merkle_root = cone.root()?;
    Ok(cone)
}

impl JudgeReceipt {
    /// Authenticate before touching Git. Missing paths, content and mode changes
    /// are returned in bytewise path order. Only the selected blobs are read.
    pub fn verify_transport(&self, key: &[u8], repo: &Path, target: &str) -> Result<Transport> {
        self.verify_transport_with_toolchain(key, repo, target, &executable_digest()?)
    }

    /// Verify with the issuer toolchain pinned by an embedding application.
    pub fn verify_transport_with_toolchain(
        &self,
        key: &[u8],
        repo: &Path,
        target: &str,
        expected_toolchain: &str,
    ) -> Result<Transport> {
        self.verify_authenticated(key)?;
        let cone = self
            .transport
            .as_ref()
            .context("v1 receipts have no transport evidence")?;
        ensure!(
            self.all_passed && self.clean_working_tree,
            "requires a clean passing receipt"
        );
        ensure!(cone.root()? == cone.cone_merkle_root, "invalid cone root");
        ensure!(
            cone.toolchain_sha256 == expected_toolchain,
            "different judge executable"
        );
        if cone.cone_blobs.is_empty() {
            bail!("gate has no transportable file view")
        }
        let paths: Vec<_> = cone.cone_blobs.keys().map(String::as_str).collect();
        let found = entries(repo, target, &paths)?;
        let mut changed_paths = Vec::new();
        for (p, hash) in &cone.cone_blobs {
            if let Some((mode, oid)) = found.get(p)
                && mode == &cone.cone_modes[p]
                && (oid == &cone.cone_oids[p]
                    || (oid.len() != cone.cone_oids[p].len()
                        && sha256_hex(&blob(repo, oid)?) == *hash))
            {
                continue;
            }
            changed_paths.push(p.clone());
        }
        Ok(if changed_paths.is_empty() {
            Transport::Transported
        } else {
            Transport::Invalidated { changed_paths }
        })
    }
}
