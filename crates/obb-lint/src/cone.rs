//! `obb cone` — Sub-50ms Lean 4.35 `module` Public/Private Import Cone Analyzer,
//! Blast-Radius Calculator, Critical-Path DAG Depth & Disjoint Swarm Shard Planner
//! (`LAW-M1`, `LAW-M2`, `LAW-M6`).

use crate::lean_index::LeanIndex;
use crate::lean_rules::{FILE_WIDE_EXPOSE_LINE_THRESHOLD, is_allowed_public_meta_import_path};
use anyhow::{Result, bail};
use obb_core::ConeHubSummary;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::Path;
use std::time::Instant;

pub const HUB_FAN_IN_THRESHOLD: usize = 25;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HeaderImport {
    pub module: String,
    pub is_public: bool,
    pub is_meta: bool,
    pub is_all: bool,
    pub line: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModuleConeNode {
    pub module: String,
    pub rel_path: String,
    pub subsystem: String,
    pub lines: usize,
    pub has_module_kw: bool,
    pub has_file_wide_expose: bool,
    pub public_imports: Vec<String>,
    pub private_imports: Vec<String>,
    pub meta_imports: Vec<String>,
    pub public_meta_imports: Vec<String>,
    /// Transitive `public import` importers (`U -pub*-> self`).
    pub public_fan_in: usize,
    /// Total downstream `.olean`s that rebuild if `self`'s public header changes.
    pub blast_radius: usize,
    /// Longest outgoing intra-repo `public import` chain length starting from `self`.
    pub public_cone_depth: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PublicMetaLeak {
    pub module: String,
    pub rel_path: String,
    pub imported: String,
    pub line: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConeDepthViolation {
    pub module: String,
    pub rel_path: String,
    pub depth: usize,
    pub max_allowed: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofConeLeak {
    pub importer_module: String,
    pub importer_path: String,
    pub proof_module: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConeReport {
    pub repo_root: String,
    pub scan_ms: f64,
    pub total_modules: usize,
    pub module_system_files: usize,
    pub legacy_non_module_files: usize,
    pub total_public_imports: usize,
    pub total_private_imports: usize,
    pub total_meta_imports: usize,
    pub file_wide_expose_modules: usize,
    pub max_public_cone_depth: usize,
    pub max_depth_limit: Option<usize>,
    pub critical_path: Vec<String>,
    pub high_blast_radius_hubs: Vec<ConeHubSummary>,
    pub public_meta_import_leaks: Vec<PublicMetaLeak>,
    pub proof_cone_leaks: Vec<ProofConeLeak>,
    pub depth_violations: Vec<ConeDepthViolation>,
    pub modules: Vec<ModuleConeNode>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProposedShard {
    pub name: String,
    pub files: Vec<String>,
    #[serde(default)]
    pub barrier: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PlannedShard {
    pub name: String,
    pub subsystem_groups: Vec<String>,
    pub module_count: usize,
    pub total_lines: usize,
    pub max_blast_radius: usize,
    pub files: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShardOverlap {
    pub path: String,
    pub shards: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HubContentionWarning {
    pub shard: String,
    pub module: String,
    pub rel_path: String,
    pub public_fan_in: usize,
    pub blast_radius: usize,
    pub message: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConePlanReport {
    pub repo_root: String,
    pub requested_shards: usize,
    pub mode: String,
    pub disjoint_write_slices: bool,
    pub hub_threshold: usize,
    pub barrier_hubs: Vec<ConeHubSummary>,
    pub overlapping_assignments: Vec<ShardOverlap>,
    pub hub_warnings: Vec<HubContentionWarning>,
    pub shards: Vec<PlannedShard>,
}

struct RawModuleHeader {
    module: String,
    rel_path: String,
    subsystem: String,
    lines: usize,
    has_module_kw: bool,
    has_file_wide_expose: bool,
    imports: Vec<HeaderImport>,
}

/// Normalize a repository-relative `.lean` path into its canonical Lean module name.
pub fn module_name_for_rel_path(rel_path: &str) -> String {
    let trimmed = rel_path.strip_prefix("lean/").unwrap_or(rel_path);
    let without_ext = trimmed.strip_suffix(".lean").unwrap_or(trimmed);
    if let Some(test_sub) = without_ext.strip_prefix("tests/") {
        return format!("Tests.{}", test_sub.replace('/', "."));
    }
    if let Some(tool_sub) = without_ext.strip_prefix("tools/")
        && let Some((_dir, root_mod)) = tool_sub.rsplit_once('/')
    {
        return format!("tools.{root_mod}");
    }
    without_ext.replace('/', ".")
}

fn subsystem_for_rel_path(rel_path: &str) -> String {
    let trimmed = rel_path.strip_prefix("lean/").unwrap_or(rel_path);
    let parts: Vec<&str> = trimmed.split('/').collect();
    if parts.first() == Some(&"Obend") && parts.len() >= 3 {
        format!("Obend/{}", parts[1])
    } else if parts.first() == Some(&"Obend") {
        "Obend/Root".to_string()
    } else if parts.len() >= 2 {
        parts[0].to_string()
    } else {
        "root".to_string()
    }
}

/// Fast single-pass header scanner for a `.lean` file: counts lines, parses `module` + all
/// `[public] [meta] [private] import [all] <Mod>` directives in the header, and detects top-level
/// `@[expose] public section` without tokenizing proof/definition bodies.
fn fast_scan_lean_header(rel_path: &str, src: &str) -> RawModuleHeader {
    let bytes = src.as_bytes();
    let len = bytes.len();
    let mut lines = 0usize;
    for &b in bytes {
        if b == b'\n' {
            lines += 1;
        }
    }
    if len > 0 && bytes[len - 1] != b'\n' {
        lines += 1;
    }

    let mut has_module_kw = false;
    let mut has_file_wide_expose = false;
    let mut imports = Vec::new();

    let mut i = 0usize;
    let mut cur_line = 1usize;
    let mut block_comment_depth = 0usize;
    let mut header_done = false;
    let mut pending_expose_attr = false;
    let mut mods: Vec<&str> = Vec::new();

    // Helper: scan header tokens until we hit the first declaration/body command past `public section` / `namespace`.
    while i < len {
        let b = bytes[i];
        // Handle nested `/- ... -/` block comments
        if block_comment_depth > 0 {
            if b == b'/' && i + 1 < len && bytes[i + 1] == b'-' {
                block_comment_depth += 1;
                i += 2;
                continue;
            }
            if b == b'-' && i + 1 < len && bytes[i + 1] == b'/' {
                block_comment_depth -= 1;
                i += 2;
                continue;
            }
            if b == b'\n' {
                cur_line += 1;
            }
            i += 1;
            continue;
        }

        // Whitespace
        if b == b' ' || b == b'\t' || b == b'\r' {
            i += 1;
            continue;
        }
        if b == b'\n' {
            cur_line += 1;
            i += 1;
            continue;
        }

        // Line comment `-- ...`
        if b == b'-' && i + 1 < len && bytes[i + 1] == b'-' {
            i += 2;
            while i < len && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }

        // Block comment `/- ... -/`
        if b == b'/' && i + 1 < len && bytes[i + 1] == b'-' {
            block_comment_depth = 1;
            i += 2;
            continue;
        }

        // Attribute `@[...]` (to detect `@[expose] public section` near top of file)
        if b == b'@' && i + 1 < len && bytes[i + 1] == b'[' {
            let start = i + 2;
            let mut d = 1usize;
            i += 2;
            while i < len && d > 0 {
                if bytes[i] == b'\n' {
                    cur_line += 1;
                } else if bytes[i] == b'[' {
                    d += 1;
                } else if bytes[i] == b']' {
                    d -= 1;
                }
                i += 1;
            }
            let end = i.saturating_sub(1);
            if start <= end && end <= len {
                let inside = &src[start..end];
                if inside
                    .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                    .any(|w| w == "expose")
                {
                    pending_expose_attr = true;
                }
            }
            continue;
        }

        // Identifier / keyword
        if b.is_ascii_alphabetic() || b == b'_' {
            let start = i;
            i += 1;
            while i < len
                && (bytes[i].is_ascii_alphanumeric()
                    || bytes[i] == b'_'
                    || bytes[i] == b'.'
                    || bytes[i] == b'\'')
            {
                i += 1;
            }
            let word = &src[start..i];
            match word {
                "module" if !header_done && mods.is_empty() => {
                    has_module_kw = true;
                    pending_expose_attr = false;
                }
                "public" | "private" | "meta" | "scoped" | "local" | "noncomputable"
                | "partial" | "unsafe" | "protected" => {
                    mods.push(word);
                }
                "import" if !header_done => {
                    let imp_line = cur_line;
                    let is_public = mods.contains(&"public");
                    let is_meta = mods.contains(&"meta");
                    mods.clear();
                    pending_expose_attr = false;

                    // Parse `all` (optional) + module name(s) on the same logical line
                    let mut is_all = false;
                    let mut first_word = true;
                    while i < len && bytes[i] != b'\n' {
                        if bytes[i] == b' ' || bytes[i] == b'\t' || bytes[i] == b'\r' {
                            i += 1;
                            continue;
                        }
                        if bytes[i] == b'-' && i + 1 < len && bytes[i + 1] == b'-' {
                            while i < len && bytes[i] != b'\n' {
                                i += 1;
                            }
                            break;
                        }
                        if bytes[i] == b'/' && i + 1 < len && bytes[i + 1] == b'-' {
                            block_comment_depth = 1;
                            i += 2;
                            break;
                        }
                        let mstart = i;
                        while i < len
                            && !bytes[i].is_ascii_whitespace()
                            && !(bytes[i] == b'-' && i + 1 < len && bytes[i + 1] == b'-')
                            && !(bytes[i] == b'/' && i + 1 < len && bytes[i + 1] == b'-')
                        {
                            i += 1;
                        }
                        let tok = &src[mstart..i];
                        if first_word && tok == "all" {
                            is_all = true;
                            first_word = false;
                            continue;
                        }
                        first_word = false;
                        if !tok.is_empty() {
                            imports.push(HeaderImport {
                                module: tok.to_string(),
                                is_public,
                                is_meta,
                                is_all,
                                line: imp_line,
                            });
                        }
                    }
                }
                "namespace" | "open" | "set_option" | "universe" => {
                    header_done = true;
                    mods.clear();
                    pending_expose_attr = false;
                    // Skip rest of line
                    while i < len && bytes[i] != b'\n' {
                        if bytes[i] == b'/' && i + 1 < len && bytes[i + 1] == b'-' {
                            block_comment_depth = 1;
                            i += 2;
                            break;
                        }
                        i += 1;
                    }
                }
                "section" => {
                    if pending_expose_attr && mods.contains(&"public") {
                        has_file_wide_expose = true;
                    }
                    break;
                }
                _ => {
                    // First real declaration (`def`, `theorem`, `structure`, `inductive`, `class`, etc.)
                    // ends the header + top-level section prologue scan immediately!
                    break;
                }
            }
            continue;
        }

        // Any other non-header token (`#guard`, syntax, etc.) ends header scan
        break;
    }

    RawModuleHeader {
        module: module_name_for_rel_path(rel_path),
        rel_path: rel_path.to_string(),
        subsystem: subsystem_for_rel_path(rel_path),
        lines,
        has_module_kw,
        has_file_wide_expose: has_file_wide_expose && lines > FILE_WIDE_EXPOSE_LINE_THRESHOLD,
        imports,
    }
}

/// Scan all `.lean` module headers in `repo_root` and compute the full import cone & blast-radius
/// graph in `< 50ms` (typically `5–15ms` on 750+ modules).
pub fn scan_repo_cone(repo_root: &Path, max_depth: Option<usize>) -> Result<ConeReport> {
    let t0 = Instant::now();
    let canon = repo_root
        .canonicalize()
        .unwrap_or_else(|_| repo_root.to_path_buf());

    let walk_root = if canon.join("lean/lakefile.toml").is_file()
        || canon.join("lean/lakefile.lean").is_file()
    {
        canon.join("lean")
    } else {
        canon.clone()
    };

    let mut lean_paths: Vec<std::path::PathBuf> = Vec::new();
    for entry in walkdir::WalkDir::new(&walk_root)
        .into_iter()
        .filter_entry(|e| {
            let name = e.file_name().to_str().unwrap_or("");
            if e.depth() > 0 && e.file_type().is_dir() && name.starts_with('.') {
                return false;
            }
            !matches!(
                name,
                "target" | "node_modules" | "astra" | "crates" | "dist" | "vendor"
            )
        })
        .flatten()
    {
        if entry.file_type().is_file()
            && entry.path().extension().and_then(|e| e.to_str()) == Some("lean")
        {
            lean_paths.push(entry.path().to_path_buf());
        }
    }
    lean_paths.sort();

    let n_files = lean_paths.len();
    let workers = std::thread::available_parallelism()
        .map(|p| p.get())
        .unwrap_or(4)
        .clamp(1, 8);

    let raw_headers: Vec<RawModuleHeader> = if n_files <= 16 || workers == 1 {
        let mut out = Vec::with_capacity(n_files);
        for abs in &lean_paths {
            if let Ok(rel) = abs.strip_prefix(&canon)
                && let Ok(src) = std::fs::read_to_string(abs)
            {
                let rel_str = rel.to_string_lossy().replace('\\', "/");
                out.push(fast_scan_lean_header(&rel_str, &src));
            }
        }
        out
    } else {
        let chunk_sz = n_files.div_ceil(workers);
        std::thread::scope(|s| {
            let mut handles = Vec::new();
            for chunk in lean_paths.chunks(chunk_sz) {
                let canon_ref = &canon;
                handles.push(s.spawn(move || {
                    let mut local = Vec::with_capacity(chunk.len());
                    for abs in chunk {
                        if let Ok(rel) = abs.strip_prefix(canon_ref)
                            && let Ok(src) = std::fs::read_to_string(abs)
                        {
                            let rel_str = rel.to_string_lossy().replace('\\', "/");
                            local.push(fast_scan_lean_header(&rel_str, &src));
                        }
                    }
                    local
                }));
            }
            let mut merged = Vec::with_capacity(n_files);
            for h in handles {
                if let Ok(part) = h.join() {
                    merged.extend(part);
                }
            }
            merged
        })
    };

    let elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
    Ok(assemble_cone_report(
        &canon.to_string_lossy(),
        raw_headers,
        max_depth,
        elapsed_ms,
    ))
}

/// Compute `ConeReport` directly from an already-built `LeanIndex` (zero extra file I/O).
pub fn compute_cone_from_index(
    repo_root: &str,
    index: &LeanIndex,
    max_depth: Option<usize>,
) -> ConeReport {
    let t0 = Instant::now();
    let raw_headers: Vec<RawModuleHeader> = index
        .files
        .iter()
        .map(|f| RawModuleHeader {
            module: module_name_for_rel_path(&f.rel_path),
            rel_path: f.rel_path.clone(),
            subsystem: subsystem_for_rel_path(&f.rel_path),
            lines: f.line_count,
            has_module_kw: f.has_module_kw,
            has_file_wide_expose: !f.expose_public_sections.is_empty()
                && f.line_count > FILE_WIDE_EXPOSE_LINE_THRESHOLD,
            imports: f
                .imports
                .iter()
                .map(|imp| HeaderImport {
                    module: imp.module.clone(),
                    is_public: imp.is_public,
                    is_meta: imp.is_meta,
                    is_all: imp.is_all,
                    line: imp.line,
                })
                .collect(),
        })
        .collect();
    let elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
    assemble_cone_report(repo_root, raw_headers, max_depth, elapsed_ms)
}

fn is_test_only_rel_path(rel_path: &str) -> bool {
    rel_path.contains("/tests/")
        || rel_path.starts_with("tests/")
        || rel_path.starts_with("lean/tests/")
        || rel_path.ends_with("Test.lean")
}

fn is_proof_module_name(mod_name: &str) -> bool {
    mod_name.contains(".Proofs.") || mod_name.ends_with(".Proofs")
}

fn assemble_cone_report(
    repo_root: &str,
    headers: Vec<RawModuleHeader>,
    max_depth: Option<usize>,
    initial_ms: f64,
) -> ConeReport {
    let t_graph = Instant::now();
    let n = headers.len();
    let mut mod_to_idx: HashMap<String, usize> = HashMap::with_capacity(n * 2);
    for (idx, h) in headers.iter().enumerate() {
        mod_to_idx.insert(h.module.clone(), idx);
    }

    let mut total_public_imports = 0usize;
    let mut total_private_imports = 0usize;
    let mut total_meta_imports = 0usize;
    let mut module_system_files = 0usize;
    let mut legacy_non_module_files = 0usize;
    let mut file_wide_expose_modules = 0usize;

    let mut public_meta_import_leaks = Vec::new();
    let mut proof_cone_leaks = Vec::new();

    // Directed adjacency lists on module indices `0..n`
    let mut pub_out: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut pub_rev: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut any_rev: Vec<Vec<usize>> = vec![Vec::new(); n];

    let mut pub_names_per_node: Vec<Vec<String>> = vec![Vec::new(); n];
    let mut priv_names_per_node: Vec<Vec<String>> = vec![Vec::new(); n];
    let mut meta_names_per_node: Vec<Vec<String>> = vec![Vec::new(); n];
    let mut pub_meta_names_per_node: Vec<Vec<String>> = vec![Vec::new(); n];

    for (u, h) in headers.iter().enumerate() {
        if h.has_module_kw {
            module_system_files += 1;
        } else {
            legacy_non_module_files += 1;
        }
        if h.has_file_wide_expose && !is_test_only_rel_path(&h.rel_path) {
            file_wide_expose_modules += 1;
        }

        let importer_is_proof_or_test = is_proof_module_name(&h.module)
            || is_test_only_rel_path(&h.rel_path)
            || h.rel_path.contains("/Teeth/")
            || h.rel_path.ends_with("/Census.lean");

        for imp in &h.imports {
            // Effective public visibility: in Lean 4.35 `module` files only `public import`
            // re-exports headers; in legacy non-`module` files, plain `import` re-exports publicly.
            let effective_public = if h.has_module_kw {
                imp.is_public
            } else {
                !imp.is_meta
            };

            if imp.is_public && imp.is_meta {
                total_public_imports += 1;
                total_meta_imports += 1;
                pub_meta_names_per_node[u].push(imp.module.clone());
                if !is_test_only_rel_path(&h.rel_path)
                    && !is_allowed_public_meta_import_path(&h.rel_path)
                    && (imp.module == "Lean" || imp.module.starts_with("Lean."))
                {
                    public_meta_import_leaks.push(PublicMetaLeak {
                        module: h.module.clone(),
                        rel_path: h.rel_path.clone(),
                        imported: imp.module.clone(),
                        line: imp.line,
                    });
                }
            } else if effective_public {
                total_public_imports += 1;
                pub_names_per_node[u].push(imp.module.clone());
            } else if imp.is_meta {
                total_meta_imports += 1;
                meta_names_per_node[u].push(imp.module.clone());
            } else {
                total_private_imports += 1;
                priv_names_per_node[u].push(imp.module.clone());
            }

            if !importer_is_proof_or_test
                && h.module != "Obend"
                && is_proof_module_name(&imp.module)
            {
                proof_cone_leaks.push(ProofConeLeak {
                    importer_module: h.module.clone(),
                    importer_path: h.rel_path.clone(),
                    proof_module: imp.module.clone(),
                });
            }

            if let Some(&v) = mod_to_idx.get(&imp.module)
                && u != v
            {
                any_rev[v].push(u);
                if effective_public {
                    pub_out[u].push(v);
                    pub_rev[v].push(u);
                }
            }
        }
    }

    for v in 0..n {
        pub_out[v].sort_unstable();
        pub_out[v].dedup();
        pub_rev[v].sort_unstable();
        pub_rev[v].dedup();
        any_rev[v].sort_unstable();
        any_rev[v].dedup();
    }

    // Compute longest `public import` chain depth + next-pointer for critical path (cycle-safe)
    let mut state = vec![0u8; n]; // 0 = unvisited, 1 = visiting, 2 = done
    let mut depth_memo = vec![0usize; n];
    let mut next_on_crit: Vec<Option<usize>> = vec![None; n];

    fn dfs_depth(
        u: usize,
        pub_out: &[Vec<usize>],
        state: &mut [u8],
        depth_memo: &mut [usize],
        next_on_crit: &mut [Option<usize>],
    ) -> usize {
        if state[u] == 2 {
            return depth_memo[u];
        }
        if state[u] == 1 {
            // Break cycle deterministically
            return 0;
        }
        state[u] = 1;
        let mut best = 0usize;
        let mut best_child = None;
        for &v in &pub_out[u] {
            let cand = 1 + dfs_depth(v, pub_out, state, depth_memo, next_on_crit);
            if cand > best {
                best = cand;
                best_child = Some(v);
            }
        }
        state[u] = 2;
        depth_memo[u] = best;
        next_on_crit[u] = best_child;
        best
    }

    let mut max_public_cone_depth = 0usize;
    let mut crit_start: Option<usize> = None;
    for u in 0..n {
        let d = dfs_depth(u, &pub_out, &mut state, &mut depth_memo, &mut next_on_crit);
        if d > max_public_cone_depth || (crit_start.is_none() && n > 0) {
            max_public_cone_depth = d;
            crit_start = Some(u);
        }
    }

    let mut critical_path = Vec::new();
    if let Some(mut cur) = crit_start {
        let mut seen = HashSet::new();
        while seen.insert(cur) {
            critical_path.push(headers[cur].module.clone());
            match next_on_crit[cur] {
                Some(nxt) => cur = nxt,
                None => break,
            }
        }
    }

    // Compute `public_fan_in` and `blast_radius` per module
    let mut visited = vec![0u32; n];
    let mut rebuild_mark = vec![0u32; n];
    let mut epoch = 1u32;

    let mut nodes = Vec::with_capacity(n);
    let mut high_blast_radius_hubs = Vec::new();
    let mut depth_violations = Vec::new();

    for v in 0..n {
        // 1. Reverse BFS on `pub_rev`: all modules `w` that transitively `public import` `v`
        let pub_tag = epoch;
        epoch += 1;
        visited[v] = pub_tag;
        let mut stack = vec![v];
        let mut pub_importers = Vec::new();
        while let Some(cur) = stack.pop() {
            for &imp_u in &pub_rev[cur] {
                if visited[imp_u] != pub_tag {
                    visited[imp_u] = pub_tag;
                    pub_importers.push(imp_u);
                    stack.push(imp_u);
                }
            }
        }
        let public_fan_in = pub_importers.len();

        // 2. Blast radius: any module `z != v` that directly imports `v` OR directly imports any `u` in `pub_importers`
        let blast_tag = epoch;
        epoch += 1;
        rebuild_mark[v] = blast_tag;
        let mut blast_radius = 0usize;
        for &src_hub in std::iter::once(&v).chain(pub_importers.iter()) {
            for &z in &any_rev[src_hub] {
                if rebuild_mark[z] != blast_tag {
                    rebuild_mark[z] = blast_tag;
                    blast_radius += 1;
                }
            }
        }

        let public_cone_depth = depth_memo[v];
        if let Some(limit) = max_depth
            && public_cone_depth > limit
        {
            depth_violations.push(ConeDepthViolation {
                module: headers[v].module.clone(),
                rel_path: headers[v].rel_path.clone(),
                depth: public_cone_depth,
                max_allowed: limit,
            });
        }

        if blast_radius > HUB_FAN_IN_THRESHOLD || public_fan_in > HUB_FAN_IN_THRESHOLD {
            high_blast_radius_hubs.push(ConeHubSummary {
                module: headers[v].module.clone(),
                path: headers[v].rel_path.clone(),
                public_fan_in,
                blast_radius,
            });
        }

        nodes.push(ModuleConeNode {
            module: headers[v].module.clone(),
            rel_path: headers[v].rel_path.clone(),
            subsystem: headers[v].subsystem.clone(),
            lines: headers[v].lines,
            has_module_kw: headers[v].has_module_kw,
            has_file_wide_expose: headers[v].has_file_wide_expose,
            public_imports: pub_names_per_node[v].clone(),
            private_imports: priv_names_per_node[v].clone(),
            meta_imports: meta_names_per_node[v].clone(),
            public_meta_imports: pub_meta_names_per_node[v].clone(),
            public_fan_in,
            blast_radius,
            public_cone_depth,
        });
    }

    high_blast_radius_hubs.sort_by(|a, b| {
        b.blast_radius
            .cmp(&a.blast_radius)
            .then_with(|| b.public_fan_in.cmp(&a.public_fan_in))
            .then_with(|| a.module.cmp(&b.module))
    });
    depth_violations.sort_by(|a, b| b.depth.cmp(&a.depth).then_with(|| a.module.cmp(&b.module)));

    let total_ms =
        ((initial_ms + t_graph.elapsed().as_secs_f64() * 1000.0) * 100.0).round() / 100.0;

    ConeReport {
        repo_root: repo_root.to_string(),
        scan_ms: total_ms,
        total_modules: n,
        module_system_files,
        legacy_non_module_files,
        total_public_imports,
        total_private_imports,
        total_meta_imports,
        file_wide_expose_modules,
        max_public_cone_depth,
        max_depth_limit: max_depth,
        critical_path,
        high_blast_radius_hubs,
        public_meta_import_leaks,
        proof_cone_leaks,
        depth_violations,
        modules: nodes,
    }
}

/// Partition library modules into `shards_k` disjoint write slices (isolating `fan_in > 25` hubs
/// behind a barrier slice), OR validate a caller-supplied list of `proposed_shards` for disjointness
/// and high-blast-radius hub contention.
pub fn plan_cone_shards(
    cone: &ConeReport,
    shards_k: usize,
    proposed_shards: &[ProposedShard],
) -> Result<ConePlanReport> {
    if shards_k == 0 && proposed_shards.is_empty() {
        bail!("`--shards <K>` requires K >= 1 when no proposed shard specs are provided");
    }

    let mut by_path: HashMap<&str, &ModuleConeNode> = HashMap::new();
    let mut by_mod: HashMap<&str, &ModuleConeNode> = HashMap::new();
    for node in &cone.modules {
        by_path.insert(node.rel_path.as_str(), node);
        if let Some(stripped) = node.rel_path.strip_prefix("lean/") {
            by_path.insert(stripped, node);
        }
        by_mod.insert(node.module.as_str(), node);
    }

    // Mode A: Validate explicit proposed shard write slices
    if !proposed_shards.is_empty() {
        let mut file_owners: BTreeMap<String, Vec<String>> = BTreeMap::new();
        let mut planned_shards = Vec::with_capacity(proposed_shards.len());
        let mut hub_warnings = Vec::new();
        let parallel_workers = proposed_shards.iter().filter(|s| !s.barrier).count();

        for prop in proposed_shards {
            let mut norm_files = Vec::new();
            let mut subsystems = BTreeSet::new();
            let mut lines = 0usize;
            let mut max_blast = 0usize;

            for raw_entry in &prop.files {
                let entry = raw_entry.trim();
                if entry.is_empty() {
                    continue;
                }
                let resolved_node = by_path
                    .get(entry)
                    .copied()
                    .or_else(|| by_mod.get(entry).copied());

                let canonical_key = resolved_node
                    .map(|n| n.rel_path.clone())
                    .unwrap_or_else(|| entry.to_string());

                file_owners
                    .entry(canonical_key.clone())
                    .or_default()
                    .push(prop.name.clone());
                norm_files.push(canonical_key);

                if let Some(node) = resolved_node {
                    subsystems.insert(node.subsystem.clone());
                    lines += node.lines;
                    max_blast = max_blast.max(node.blast_radius);

                    if !prop.barrier
                        && parallel_workers > 1
                        && (node.blast_radius > HUB_FAN_IN_THRESHOLD
                            || node.public_fan_in > HUB_FAN_IN_THRESHOLD)
                    {
                        hub_warnings.push(HubContentionWarning {
                            shard: prop.name.clone(),
                            module: node.module.clone(),
                            rel_path: node.rel_path.clone(),
                            public_fan_in: node.public_fan_in,
                            blast_radius: node.blast_radius,
                            message: format!(
                                "Worker shard `{}` writes high-blast-radius hub `{}` (blast_radius={}, public_fan_in={} > {} cap) outside a barrier slice; editing its public header invalidates {} downstream `.olean`s!",
                                prop.name,
                                node.module,
                                node.blast_radius,
                                node.public_fan_in,
                                HUB_FAN_IN_THRESHOLD,
                                node.blast_radius
                            ),
                        });
                    }
                }
            }

            norm_files.sort();
            norm_files.dedup();
            planned_shards.push(PlannedShard {
                name: prop.name.clone(),
                subsystem_groups: subsystems.into_iter().collect(),
                module_count: norm_files.len(),
                total_lines: lines,
                max_blast_radius: max_blast,
                files: norm_files,
            });
        }

        let mut overlapping_assignments = Vec::new();
        for (path, mut owners) in file_owners {
            owners.sort();
            owners.dedup();
            if owners.len() > 1 {
                overlapping_assignments.push(ShardOverlap {
                    path,
                    shards: owners,
                });
            }
        }

        return Ok(ConePlanReport {
            repo_root: cone.repo_root.clone(),
            requested_shards: proposed_shards.len(),
            mode: "validate_proposed".to_string(),
            disjoint_write_slices: overlapping_assignments.is_empty(),
            hub_threshold: HUB_FAN_IN_THRESHOLD,
            barrier_hubs: cone.high_blast_radius_hubs.clone(),
            overlapping_assignments,
            hub_warnings,
            shards: planned_shards,
        });
    }

    // Mode B: Automatic K-way disjoint shard partitioner (isolating `fan_in > 25` hubs into the barrier)
    let mut barrier_hubs = Vec::new();
    let mut sub_buckets: BTreeMap<String, Vec<&ModuleConeNode>> = BTreeMap::new();

    for node in &cone.modules {
        if is_test_only_rel_path(&node.rel_path) || node.rel_path.contains("/Teeth/") {
            continue;
        }
        if node.blast_radius > HUB_FAN_IN_THRESHOLD || node.public_fan_in > HUB_FAN_IN_THRESHOLD {
            barrier_hubs.push(ConeHubSummary {
                module: node.module.clone(),
                path: node.rel_path.clone(),
                public_fan_in: node.public_fan_in,
                blast_radius: node.blast_radius,
            });
        } else {
            sub_buckets
                .entry(node.subsystem.clone())
                .or_default()
                .push(node);
        }
    }

    barrier_hubs.sort_by(|a, b| {
        b.blast_radius
            .cmp(&a.blast_radius)
            .then_with(|| a.module.cmp(&b.module))
    });

    // Build cohesive subsystem chunks (splitting any giant subsystem > ceil(total/K) into sub-slices
    // while keeping every file in at most 1 chunk so write slices are 100% disjoint).
    let total_non_hub_lines: usize = sub_buckets
        .values()
        .flat_map(|v| v.iter())
        .map(|n| n.lines.max(1))
        .sum();
    let target_lines_per_shard = (total_non_hub_lines / shards_k.max(1)).max(400);

    let mut work_units: Vec<(String, usize, Vec<&ModuleConeNode>)> = Vec::new();
    for (sub, mut mods) in sub_buckets {
        mods.sort_by(|a, b| a.rel_path.cmp(&b.rel_path));
        let sub_lines: usize = mods.iter().map(|m| m.lines.max(1)).sum();
        if sub_lines <= target_lines_per_shard * 3 / 2 || shards_k == 1 || mods.len() <= 1 {
            work_units.push((sub, sub_lines, mods));
        } else {
            // Split large subsystem (e.g. `Obend/Hardware` or `Obend/Core`) into balanced sub-slices
            let mut cur_mods = Vec::new();
            let mut cur_lines = 0usize;
            let mut part_idx = 1usize;
            for m in mods {
                if !cur_mods.is_empty() && cur_lines + m.lines > target_lines_per_shard {
                    work_units.push((format!("{sub}#{part_idx}"), cur_lines, cur_mods));
                    cur_mods = Vec::new();
                    cur_lines = 0;
                    part_idx += 1;
                }
                cur_lines += m.lines.max(1);
                cur_mods.push(m);
            }
            if !cur_mods.is_empty() {
                work_units.push((format!("{sub}#{part_idx}"), cur_lines, cur_mods));
            }
        }
    }

    // LPT greedy bin-packing across `shards_k` shards
    work_units.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));

    let mut bins: Vec<(BTreeSet<String>, usize, usize, Vec<String>)> =
        vec![(BTreeSet::new(), 0, 0, Vec::new()); shards_k];

    for (group_label, lines, mods) in work_units {
        let best_bin = bins
            .iter()
            .enumerate()
            .min_by_key(|(idx, (_, cur_lines, _, files))| (*cur_lines, files.len(), *idx))
            .map(|(idx, _)| idx)
            .unwrap_or(0);
        let entry = &mut bins[best_bin];
        entry.0.insert(group_label);
        entry.1 += lines;
        for m in mods {
            entry.2 = entry.2.max(m.blast_radius);
            entry.3.push(m.rel_path.clone());
        }
    }

    let mut shards = Vec::with_capacity(shards_k);
    for (idx, (groups, lines, max_blast, mut files)) in bins.into_iter().enumerate() {
        files.sort();
        shards.push(PlannedShard {
            name: format!("shard-{}", idx + 1),
            subsystem_groups: groups.into_iter().collect(),
            module_count: files.len(),
            total_lines: lines,
            max_blast_radius: max_blast,
            files,
        });
    }

    Ok(ConePlanReport {
        repo_root: cone.repo_root.clone(),
        requested_shards: shards_k,
        mode: "auto_partition".to_string(),
        disjoint_write_slices: true,
        hub_threshold: HUB_FAN_IN_THRESHOLD,
        barrier_hubs,
        overlapping_assignments: Vec::new(),
        hub_warnings: Vec::new(),
        shards,
    })
}
