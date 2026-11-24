//! `obb apex` — Whole-System Compositional Assurance & Anti-Leaf-Island Engine.
//!
//! Resolves registered `[apex]` composition theorems in the Lean index, verifies `0 sorry` and
//! `0` custom `axiom` across their transitive dependency cone, computes per-subsystem
//! **Apex Compositional Coverage %** (`Core`, `Leaf`, `Vault`, `Judge`, `Hardware`, `Analysis`,
//! `Lower`, `Consensus`), and identifies unwired leaf-island modules in `lean/Obend/`.

use crate::cone::module_name_for_rel_path;
use crate::lean_index::{DeclKind, LeanIndex, ParsedLeanDecl, build_lean_index};
use crate::lean_lexer::{LeanToken, LeanTokenKind};
use anyhow::{Context, Result, bail};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::Path;

pub const DEFAULT_APEX_MANIFEST_REL: &str = "quarry/obend-apex.toml";

/// Repository-root manifest name; takes precedence over every `quarry/` manifest.
pub const REPO_ROOT_APEX_MANIFEST_REL: &str = "obb-apex.toml";

/// Pattern for target-named manifests under `quarry/`, used when exactly one file matches.
pub const QUARRY_APEX_MANIFEST_PATTERN: &str = "quarry/*-apex.toml";

/// Where a target repository declares its own Apex manifest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ApexManifestDiscovery {
    /// No `obb-apex.toml`, `quarry/obend-apex.toml` or `quarry/*-apex.toml` exists.
    Absent,
    /// The authoritative manifest, relative to the repository root.
    Found { rel_path: String },
    /// Several `quarry/*-apex.toml` files exist and none is authoritative (sorted, repo-relative).
    Ambiguous { candidates: Vec<String> },
}

/// Locate the repository's Apex manifest: `obb-apex.toml`, then `quarry/obend-apex.toml`, then the
/// only `quarry/*-apex.toml`. Several `quarry/*-apex.toml` files without one of the first two
/// names are reported as [`ApexManifestDiscovery::Ambiguous`] rather than resolved by a guess.
pub fn discover_repo_apex_manifest(repo_root: &Path) -> Result<ApexManifestDiscovery> {
    for rel in [REPO_ROOT_APEX_MANIFEST_REL, DEFAULT_APEX_MANIFEST_REL] {
        match std::fs::symlink_metadata(repo_root.join(rel)) {
            Ok(_) => {
                return Ok(ApexManifestDiscovery::Found {
                    rel_path: rel.into(),
                });
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => return Err(e).with_context(|| format!("cannot inspect `{rel}`")),
        }
    }
    let quarry_dir = repo_root.join("quarry");
    match std::fs::symlink_metadata(&quarry_dir) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            return Ok(ApexManifestDiscovery::Absent);
        }
        result => {
            result.context("cannot inspect `quarry/`")?;
        }
    }
    let mut candidates = Vec::new();
    for entry in std::fs::read_dir(&quarry_dir).context("cannot list `quarry/`")? {
        let name = entry?.file_name();
        if name.as_encoded_bytes().ends_with(b"-apex.toml") {
            let name = name
                .to_str()
                .context("Apex manifest name in `quarry/` is not UTF-8")?;
            candidates.push(format!("quarry/{name}"));
        }
    }
    candidates.sort();
    Ok(match candidates.len() {
        0 => ApexManifestDiscovery::Absent,
        1 => ApexManifestDiscovery::Found {
            rel_path: candidates.remove(0),
        },
        _ => ApexManifestDiscovery::Ambiguous { candidates },
    })
}

pub const CANONICAL_SUBSYSTEMS: &[&str] = &[
    "Core",
    "Leaf",
    "Vault",
    "Judge",
    "Hardware",
    "Analysis",
    "Lower",
    "Consensus",
];

fn default_subsystems() -> Vec<String> {
    CANONICAL_SUBSYSTEMS
        .iter()
        .map(|s| (*s).to_string())
        .collect()
}

fn default_entry_points() -> Vec<String> {
    vec![
        "lean/Obend/Main.lean".to_string(),
        "lean/Obend/FFI.lean".to_string(),
        "lean/Obend/FFI/Bridge.lean".to_string(),
        "lean/tools/emitsv/EmitSv.lean".to_string(),
        "lean/tools/emitcam/EmitCam.lean".to_string(),
        "lean/tools/emithvm/EmitHvm.lean".to_string(),
        "lean/tools/emitgpu/EmitGpu.lean".to_string(),
        "lean/tools/rdna2/Rdna2.lean".to_string(),
        "lean/tools/litmuscheck/LitmusCheck.lean".to_string(),
        "lean/tools/journal/Main.lean".to_string(),
    ]
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApexEntry {
    pub id: String,
    pub subsystem: String,
    pub module: String,
    pub theorem: String,
    pub description: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PlannedApexEntry {
    pub id: String,
    pub pillar: String,
    pub subsystem: String,
    pub target_module: String,
    pub target_theorem: String,
    pub wave: String,
    pub description: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApexManifest {
    pub version: u32,
    pub target_name: String,
    #[serde(default)]
    pub default_target_repo: Option<String>,
    #[serde(default = "default_subsystems")]
    pub subsystems: Vec<String>,
    #[serde(default = "default_entry_points")]
    pub entry_points: Vec<String>,
    #[serde(default)]
    pub max_unwired_islands: Option<usize>,
    #[serde(default)]
    pub apex: Vec<ApexEntry>,
    #[serde(default)]
    pub planned_apex: Vec<PlannedApexEntry>,
}

impl ApexManifest {
    pub fn load_from_path(path: &Path) -> Result<Self> {
        if !std::fs::metadata(path)
            .with_context(|| format!("cannot inspect apex manifest {}", path.display()))?
            .is_file()
        {
            bail!("apex manifest {} must be a regular file", path.display());
        }
        let raw = std::fs::read_to_string(path)
            .with_context(|| format!("failed to read apex manifest {}", path.display()))?;
        let parsed: Self = toml::from_str(&raw)
            .with_context(|| format!("failed to parse apex manifest TOML {}", path.display()))?;
        if parsed.apex.is_empty() {
            bail!(
                "apex manifest {} registers zero `[[apex]]` theorems",
                path.display()
            );
        }
        Ok(parsed)
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct ApexCheckOptions {
    pub strict_islands: bool,
    pub max_islands: Option<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerifiedApexTheorem {
    pub id: String,
    pub subsystem: String,
    pub module: String,
    pub rel_path: Option<String>,
    pub theorem: String,
    pub resolved_fq_name: Option<String>,
    pub line: Option<usize>,
    pub exists: bool,
    pub sorry_count: usize,
    pub custom_axiom_count: usize,
    pub offenders: Vec<String>,
    pub cone_modules: usize,
    pub cone_declarations: usize,
    pub valid: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PlannedApexStatus {
    pub id: String,
    pub pillar: String,
    pub subsystem: String,
    pub target_module: String,
    pub target_theorem: String,
    pub wave: String,
    pub materialized: bool,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SubsystemApexCoverage {
    pub subsystem: String,
    pub registered_apex_theorems: usize,
    pub total_modules: usize,
    pub apex_covered_modules: usize,
    pub apex_coverage_pct: f64,
    pub wired_modules: usize,
    pub wired_coverage_pct: f64,
    pub total_declarations: usize,
    pub apex_reachable_declarations: usize,
    pub unwired_islands: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeafIsland {
    pub subsystem: String,
    pub module: String,
    pub rel_path: String,
    pub lines: usize,
    pub theorems: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApexReport {
    pub repo_root: String,
    pub manifest_target: String,
    pub registered_apex_count: usize,
    pub valid_apex_count: usize,
    pub all_apex_valid: bool,
    pub planned_apex_count: usize,
    pub planned_materialized_count: usize,
    pub total_library_modules: usize,
    pub apex_covered_library_modules: usize,
    pub overall_apex_coverage_pct: f64,
    pub wired_library_modules: usize,
    pub overall_wired_coverage_pct: f64,
    pub total_library_declarations: usize,
    pub apex_reachable_declarations: usize,
    pub unwired_island_count: usize,
    pub check_passed: bool,
    pub failure_reasons: Vec<String>,
    pub apex_theorems: Vec<VerifiedApexTheorem>,
    pub planned_apex: Vec<PlannedApexStatus>,
    pub subsystem_coverage: Vec<SubsystemApexCoverage>,
    pub unwired_leaf_islands: Vec<LeafIsland>,
}

fn round1(v: f64) -> f64 {
    (v * 10.0).round() / 10.0
}

fn is_excluded_library_module(rel_path: &str) -> bool {
    let norm = rel_path.strip_prefix("lean/").unwrap_or(rel_path);
    if !norm.starts_with("Obend/") {
        return true;
    }
    norm.starts_with("Obend/Teeth/")
        || norm.starts_with("Obend/Apps/")
        || matches!(
            norm,
            "Obend/Census.lean"
                | "Obend/Stdlib.lean"
                | "Obend/AssertAxioms.lean"
                | "Obend/AssertCompiled.lean"
        )
}

fn subsystem_of_obend_rel(rel_path: &str, known_subsystems: &HashSet<String>) -> String {
    let norm = rel_path.strip_prefix("lean/").unwrap_or(rel_path);
    let parts: Vec<&str> = norm.split('/').collect();
    if parts.first() == Some(&"Obend") {
        if parts.len() >= 3 {
            return parts[1].to_string();
        }
        if parts.len() == 2 {
            let stem = parts[1].strip_suffix(".lean").unwrap_or(parts[1]);
            if known_subsystems.contains(stem) {
                return stem.to_string();
            }
            return "Core".to_string();
        }
    }
    "Other".to_string()
}

fn collect_decl_idents(decl: &ParsedLeanDecl, out: &mut Vec<String>) {
    let mut push_toks = |toks: &[LeanToken]| {
        for tok in toks {
            match &tok.kind {
                LeanTokenKind::Ident(id) | LeanTokenKind::DoubleBacktickConst(id) => {
                    out.push(id.clone());
                }
                _ => {}
            }
        }
    };
    for b in &decl.binders {
        push_toks(&b.type_tokens);
    }
    push_toks(&decl.type_tokens);
    push_toks(&decl.body_tokens);
    for wf in &decl.where_fields {
        push_toks(&wf.rhs_tokens);
    }
    for sf in &decl.struct_fields {
        push_toks(&sf.type_tokens);
    }
}

pub fn evaluate_apex(
    repo_root: &Path,
    manifest: &ApexManifest,
    options: ApexCheckOptions,
) -> Result<ApexReport> {
    let canon = repo_root
        .canonicalize()
        .unwrap_or_else(|_| repo_root.to_path_buf());
    let index = build_lean_index(&canon);
    Ok(evaluate_apex_with_index(
        &canon.to_string_lossy(),
        &index,
        manifest,
        options,
    ))
}

pub fn evaluate_apex_with_index(
    repo_root: &str,
    index: &LeanIndex,
    manifest: &ApexManifest,
    options: ApexCheckOptions,
) -> ApexReport {
    let n_files = index.files.len();
    let mut lookup_file: HashMap<String, usize> = HashMap::with_capacity(n_files * 3);
    let mut file_mod_names: Vec<String> = Vec::with_capacity(n_files);

    for (f_idx, f) in index.files.iter().enumerate() {
        let mod_name = module_name_for_rel_path(&f.rel_path);
        lookup_file.insert(mod_name.clone(), f_idx);
        lookup_file.insert(f.rel_path.clone(), f_idx);
        if let Some(stripped) = f.rel_path.strip_prefix("lean/") {
            lookup_file.insert(stripped.to_string(), f_idx);
            let bare_mod = stripped
                .strip_suffix(".lean")
                .unwrap_or(stripped)
                .replace('/', ".");
            lookup_file.insert(bare_mod, f_idx);
        }
        file_mod_names.push(mod_name);
    }

    // Build outgoing import graph `mod_imports[u]`
    let mut mod_imports: Vec<Vec<usize>> = vec![Vec::new(); n_files];
    for (u, f) in index.files.iter().enumerate() {
        for imp in &f.imports {
            if let Some(&v) = lookup_file.get(&imp.module)
                && u != v
            {
                mod_imports[u].push(v);
            }
        }
        mod_imports[u].sort_unstable();
        mod_imports[u].dedup();
    }

    let compute_mod_cone = |seed: usize| -> BTreeSet<usize> {
        let mut seen = BTreeSet::new();
        let mut stack = vec![seed];
        while let Some(cur) = stack.pop() {
            if seen.insert(cur) {
                for &dep in &mod_imports[cur] {
                    if !seen.contains(&dep) {
                        stack.push(dep);
                    }
                }
            }
        }
        seen
    };

    // Index all declarations globally by `fq_name` and `short_name` for fast declaration-cone walk
    let mut by_fq: HashMap<&str, Vec<(usize, usize)>> = HashMap::new();
    let mut by_short: HashMap<&str, Vec<(usize, usize)>> = HashMap::new();
    for (f_idx, f) in index.files.iter().enumerate() {
        for (d_idx, d) in f.declarations.iter().enumerate() {
            by_fq
                .entry(d.fq_name.as_str())
                .or_default()
                .push((f_idx, d_idx));
            by_short
                .entry(d.name.as_str())
                .or_default()
                .push((f_idx, d_idx));
        }
    }

    let mut global_apex_mod_cone: HashSet<usize> = HashSet::new();
    let mut global_apex_decl_cone: HashSet<(usize, usize)> = HashSet::new();
    let mut apex_theorems = Vec::with_capacity(manifest.apex.len());
    let mut failure_reasons = Vec::new();
    let mut apex_count_by_sub: BTreeMap<String, usize> = BTreeMap::new();

    for entry in &manifest.apex {
        *apex_count_by_sub
            .entry(entry.subsystem.clone())
            .or_insert(0) += 1;

        let Some(&f_idx) = lookup_file.get(&entry.module) else {
            let reason = format!(
                "Apex `{}`: module `{}` not found in repository",
                entry.id, entry.module
            );
            failure_reasons.push(reason);
            apex_theorems.push(VerifiedApexTheorem {
                id: entry.id.clone(),
                subsystem: entry.subsystem.clone(),
                module: entry.module.clone(),
                rel_path: None,
                theorem: entry.theorem.clone(),
                resolved_fq_name: None,
                line: None,
                exists: false,
                sorry_count: 0,
                custom_axiom_count: 0,
                offenders: Vec::new(),
                cone_modules: 0,
                cone_declarations: 0,
                valid: false,
            });
            continue;
        };

        let file = &index.files[f_idx];
        let matched_decl = file.declarations.iter().enumerate().find(|(_, d)| {
            d.kind == DeclKind::Theorem
                && (d.name == entry.theorem
                    || d.fq_name == entry.theorem
                    || d.fq_name.ends_with(&format!(".{}", entry.theorem)))
        });

        let Some((d_idx, root_decl)) = matched_decl else {
            let reason = format!(
                "Apex `{}`: theorem `{}` not found in `{}`",
                entry.id, entry.theorem, file.rel_path
            );
            failure_reasons.push(reason);
            apex_theorems.push(VerifiedApexTheorem {
                id: entry.id.clone(),
                subsystem: entry.subsystem.clone(),
                module: entry.module.clone(),
                rel_path: Some(file.rel_path.clone()),
                theorem: entry.theorem.clone(),
                resolved_fq_name: None,
                line: None,
                exists: false,
                sorry_count: 0,
                custom_axiom_count: 0,
                offenders: Vec::new(),
                cone_modules: 0,
                cone_declarations: 0,
                valid: false,
            });
            continue;
        };

        let mod_cone = compute_mod_cone(f_idx);

        // Walk declaration dependency cone restricted to `mod_cone`
        let mut decl_cone: HashSet<(usize, usize)> = HashSet::new();
        let mut d_stack = vec![(f_idx, d_idx)];
        let mut scratch_idents = Vec::new();
        while let Some((cf, cd)) = d_stack.pop() {
            if !decl_cone.insert((cf, cd)) {
                continue;
            }
            scratch_idents.clear();
            collect_decl_idents(&index.files[cf].declarations[cd], &mut scratch_idents);
            for ident in &scratch_idents {
                if let Some(targets) = by_fq.get(ident.as_str()) {
                    for &(tf, td) in targets {
                        if mod_cone.contains(&tf) && !decl_cone.contains(&(tf, td)) {
                            d_stack.push((tf, td));
                        }
                    }
                } else {
                    let short = ident.rsplit('.').next().unwrap_or(ident.as_str());
                    if let Some(targets) = by_short.get(short) {
                        for &(tf, td) in targets {
                            if mod_cone.contains(&tf) && !decl_cone.contains(&(tf, td)) {
                                d_stack.push((tf, td));
                            }
                        }
                    }
                }
            }
        }

        // Audit cone for `sorry` / `sorryAx` and declared `axiom`
        let mut sorry_count = 0usize;
        let mut custom_axiom_count = 0usize;
        let mut offenders = BTreeSet::new();

        // Check module-level sorry/axioms across `mod_cone` as well as `decl_cone`
        for &mf in &mod_cone {
            let mfile = &index.files[mf];
            for (line, col, token) in &mfile.raw_sorry_sites {
                sorry_count += 1;
                offenders.insert(format!("{token} ({}:{line}:{col})", mfile.rel_path));
            }
            for md in &mfile.declarations {
                if md.kind == DeclKind::Axiom {
                    custom_axiom_count += 1;
                    offenders.insert(format!("axiom {} ({})", md.fq_name, mfile.rel_path));
                }
            }
        }

        let single_turn_issue = crate::lean_rules::single_turn_apex_violation(file, root_decl);
        if single_turn_issue.is_some() {
            offenders.insert(format!(
                "single-sequence-harness in {} ({})",
                root_decl.fq_name, file.rel_path
            ));
        }

        let valid = sorry_count == 0 && custom_axiom_count == 0 && single_turn_issue.is_none();
        if sorry_count > 0 || custom_axiom_count > 0 {
            failure_reasons.push(format!(
                "Apex `{}` (`{}`) cone contains {} sorry site(s) and {} custom axiom(s)",
                entry.id, root_decl.fq_name, sorry_count, custom_axiom_count
            ));
        }
        if let Some(ref st_msg) = single_turn_issue {
            failure_reasons.push(format!(
                "Apex `{}` (`{}`): {}",
                entry.id, root_decl.fq_name, st_msg
            ));
        }
        if valid {
            global_apex_mod_cone.extend(mod_cone.iter().copied());
            global_apex_decl_cone.extend(decl_cone.iter().copied());
        }

        apex_theorems.push(VerifiedApexTheorem {
            id: entry.id.clone(),
            subsystem: entry.subsystem.clone(),
            module: entry.module.clone(),
            rel_path: Some(file.rel_path.clone()),
            theorem: entry.theorem.clone(),
            resolved_fq_name: Some(root_decl.fq_name.clone()),
            line: Some(root_decl.line),
            exists: true,
            sorry_count,
            custom_axiom_count,
            offenders: offenders.into_iter().collect(),
            cone_modules: mod_cone.len(),
            cone_declarations: decl_cone.len(),
            valid,
        });
    }

    // Executable / FFI entry-point cone (explicitly skipping `Obend.lean` umbrella barrel)
    let mut entry_mod_cone: HashSet<usize> = HashSet::new();
    for ep in &manifest.entry_points {
        if ep == "Obend" || ep.ends_with("/Obend.lean") || ep == "Obend.lean" {
            continue;
        }
        if let Some(&ep_idx) = lookup_file.get(ep) {
            entry_mod_cone.extend(compute_mod_cone(ep_idx));
        }
    }

    let mut known_subs: HashSet<String> = index.subsystems.clone();
    for s in &manifest.subsystems {
        known_subs.insert(s.clone());
    }

    // Evaluate `[planned_apex]` materialization
    let mut planned_statuses = Vec::with_capacity(manifest.planned_apex.len());
    let mut planned_materialized_count = 0usize;
    for p in &manifest.planned_apex {
        let materialized = lookup_file.get(&p.target_module).is_some_and(|&f_idx| {
            index.files[f_idx].declarations.iter().any(|d| {
                d.kind == DeclKind::Theorem
                    && (d.name == p.target_theorem
                        || d.fq_name == p.target_theorem
                        || d.fq_name.ends_with(&format!(".{}", p.target_theorem)))
            })
        });
        if materialized {
            planned_materialized_count += 1;
        }
        planned_statuses.push(PlannedApexStatus {
            id: p.id.clone(),
            pillar: p.pillar.clone(),
            subsystem: p.subsystem.clone(),
            target_module: p.target_module.clone(),
            target_theorem: p.target_theorem.clone(),
            wave: p.wave.clone(),
            materialized,
        });
    }

    // Aggregate per-subsystem compositional coverage & unwired leaf islands
    #[derive(Default)]
    struct SubTally {
        total_mods: usize,
        apex_mods: usize,
        wired_mods: usize,
        total_decls: usize,
        apex_decls: usize,
        islands: usize,
    }

    let mut sub_tallies: BTreeMap<String, SubTally> = BTreeMap::new();
    for s in &manifest.subsystems {
        sub_tallies.entry(s.clone()).or_default();
    }

    let mut total_library_modules = 0usize;
    let mut apex_covered_library_modules = 0usize;
    let mut wired_library_modules = 0usize;
    let mut total_library_declarations = 0usize;
    let mut apex_reachable_library_declarations = 0usize;
    let mut unwired_leaf_islands = Vec::new();

    for (f_idx, f) in index.files.iter().enumerate() {
        if is_excluded_library_module(&f.rel_path) {
            continue;
        }
        let sub = subsystem_of_obend_rel(&f.rel_path, &known_subs);
        let tally = sub_tallies.entry(sub.clone()).or_default();

        total_library_modules += 1;
        tally.total_mods += 1;

        let in_apex = global_apex_mod_cone.contains(&f_idx);
        let in_wired = in_apex || entry_mod_cone.contains(&f_idx);

        if in_apex {
            apex_covered_library_modules += 1;
            tally.apex_mods += 1;
        }
        if in_wired {
            wired_library_modules += 1;
            tally.wired_mods += 1;
        } else {
            tally.islands += 1;
            let thms = f
                .declarations
                .iter()
                .filter(|d| d.kind == DeclKind::Theorem)
                .count();
            unwired_leaf_islands.push(LeafIsland {
                subsystem: sub,
                module: file_mod_names[f_idx].clone(),
                rel_path: f.rel_path.clone(),
                lines: f.line_count,
                theorems: thms,
            });
        }

        let f_decls = f.declarations.len();
        total_library_declarations += f_decls;
        tally.total_decls += f_decls;
        for d_idx in 0..f_decls {
            if global_apex_decl_cone.contains(&(f_idx, d_idx)) {
                apex_reachable_library_declarations += 1;
                tally.apex_decls += 1;
            }
        }
    }

    unwired_leaf_islands.sort_by(|a, b| {
        a.subsystem
            .cmp(&b.subsystem)
            .then_with(|| a.rel_path.cmp(&b.rel_path))
    });

    // Order canonical subsystems first, followed by any additional subsystems in `Obend/`
    let mut ordered_subs: Vec<String> = manifest.subsystems.clone();
    for k in sub_tallies.keys() {
        if !ordered_subs.iter().any(|s| s == k) {
            ordered_subs.push(k.clone());
        }
    }

    let mut subsystem_coverage = Vec::with_capacity(ordered_subs.len());
    for sub in ordered_subs {
        let t = sub_tallies.remove(&sub).unwrap_or_default();
        let apex_pct = if t.total_mods == 0 {
            100.0
        } else {
            round1(100.0 * (t.apex_mods as f64) / (t.total_mods as f64))
        };
        let wired_pct = if t.total_mods == 0 {
            100.0
        } else {
            round1(100.0 * (t.wired_mods as f64) / (t.total_mods as f64))
        };
        subsystem_coverage.push(SubsystemApexCoverage {
            registered_apex_theorems: *apex_count_by_sub.get(&sub).unwrap_or(&0),
            subsystem: sub,
            total_modules: t.total_mods,
            apex_covered_modules: t.apex_mods,
            apex_coverage_pct: apex_pct,
            wired_modules: t.wired_mods,
            wired_coverage_pct: wired_pct,
            total_declarations: t.total_decls,
            apex_reachable_declarations: t.apex_decls,
            unwired_islands: t.islands,
        });
    }

    let valid_apex_count = apex_theorems.iter().filter(|a| a.valid).count();
    let all_apex_valid = !apex_theorems.is_empty() && valid_apex_count == apex_theorems.len();

    let effective_island_cap = if options.strict_islands {
        Some(0usize)
    } else {
        options.max_islands.or(manifest.max_unwired_islands)
    };

    if let Some(cap) = effective_island_cap
        && unwired_leaf_islands.len() > cap
    {
        failure_reasons.push(format!(
            "Unwired leaf islands ({}) exceed allowed cap ({})",
            unwired_leaf_islands.len(),
            cap
        ));
    }

    let check_passed = all_apex_valid && failure_reasons.is_empty();

    let overall_apex_coverage_pct = if total_library_modules == 0 {
        100.0
    } else {
        round1(100.0 * (apex_covered_library_modules as f64) / (total_library_modules as f64))
    };
    let overall_wired_coverage_pct = if total_library_modules == 0 {
        100.0
    } else {
        round1(100.0 * (wired_library_modules as f64) / (total_library_modules as f64))
    };

    ApexReport {
        repo_root: repo_root.to_string(),
        manifest_target: manifest.target_name.clone(),
        registered_apex_count: apex_theorems.len(),
        valid_apex_count,
        all_apex_valid,
        planned_apex_count: planned_statuses.len(),
        planned_materialized_count,
        total_library_modules,
        apex_covered_library_modules,
        overall_apex_coverage_pct,
        wired_library_modules,
        overall_wired_coverage_pct,
        total_library_declarations,
        apex_reachable_declarations: apex_reachable_library_declarations,
        unwired_island_count: unwired_leaf_islands.len(),
        check_passed,
        failure_reasons,
        apex_theorems,
        planned_apex: planned_statuses,
        subsystem_coverage,
        unwired_leaf_islands,
    }
}
