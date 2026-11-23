//! Modularity & Compositionality Index (`obb lint --modularity`).
//!
//! Measures algebraic interface density (`structure` + `class` + `instance`) versus isolated
//! leaf theorems (theorems never referenced by any downstream proof or definition), and flags
//! giant >4,000-line monolithic `.lean` modules that risk elaboration RSS blowups.

use crate::lean_index::{DeclKind, LeanIndex, ParsedLeanDecl};
use crate::lean_lexer::{LeanToken, LeanTokenKind};
use obb_core::{DirectoryModularity, ModularityReport, MonolithicModule};
use std::collections::{BTreeMap, HashSet};

pub const MONOLITHIC_LINE_THRESHOLD: usize = 4000;

fn collect_decl_referenced_idents(decl: &ParsedLeanDecl, out: &mut HashSet<String>) {
    let mut local_seen = HashSet::new();
    let mut scan = |toks: &[LeanToken]| {
        for tok in toks {
            match &tok.kind {
                LeanTokenKind::Ident(id) | LeanTokenKind::DoubleBacktickConst(id) => {
                    local_seen.insert(id.clone());
                    if let Some(short) = id.rsplit('.').next() {
                        local_seen.insert(short.to_string());
                    }
                }
                _ => {}
            }
        }
    };

    for b in &decl.binders {
        scan(&b.type_tokens);
    }
    scan(&decl.type_tokens);
    scan(&decl.body_tokens);
    for wf in &decl.where_fields {
        scan(&wf.rhs_tokens);
    }
    for sf in &decl.struct_fields {
        scan(&sf.type_tokens);
    }

    // Remove self-references so recursive/self-named references don't masquerade as downstream reuse
    local_seen.remove(&decl.name);
    local_seen.remove(&decl.fq_name);
    out.extend(local_seen);
}

fn round4(v: f64) -> f64 {
    (v * 10_000.0).round() / 10_000.0
}

fn round2(v: f64) -> f64 {
    (v * 100.0).round() / 100.0
}

pub fn compute_modularity_report(index: &LeanIndex) -> ModularityReport {
    let mut referenced_by_others: HashSet<String> = HashSet::new();

    for file in &index.files {
        for decl in &file.declarations {
            collect_decl_referenced_idents(decl, &mut referenced_by_others);
        }
        for (_, gtoks) in &file.guard_tokens {
            for tok in gtoks {
                if let LeanTokenKind::Ident(id) = &tok.kind {
                    referenced_by_others.insert(id.clone());
                    if let Some(short) = id.rsplit('.').next() {
                        referenced_by_others.insert(short.to_string());
                    }
                }
            }
        }
    }

    let mut lean_files = 0usize;
    let mut total_lean_lines = 0usize;
    let mut max_module_lines = 0usize;
    let mut max_module_path: Option<String> = None;
    let mut structures = 0usize;
    let mut classes = 0usize;
    let mut instances = 0usize;
    let mut inductives = 0usize;
    let mut total_theorems = 0usize;
    let mut composed_theorems = 0usize;
    let mut isolated_leaf_theorems = 0usize;
    let mut monolithic_modules: Vec<MonolithicModule> = Vec::new();
    let mut dir_map: BTreeMap<String, DirectoryModularity> = BTreeMap::new();

    for file in &index.files {
        lean_files += 1;
        total_lean_lines += file.line_count;
        if file.line_count > max_module_lines {
            max_module_lines = file.line_count;
            max_module_path = Some(file.rel_path.clone());
        }

        let dir_entry = dir_map
            .entry(file.directory_bucket.clone())
            .or_insert_with(|| DirectoryModularity {
                directory: file.directory_bucket.clone(),
                ..Default::default()
            });
        dir_entry.files += 1;
        dir_entry.total_lines += file.line_count;
        if file.line_count > dir_entry.max_lines {
            dir_entry.max_lines = file.line_count;
        }

        let mut file_thms = 0usize;
        let mut file_structs_classes = 0usize;

        for decl in &file.declarations {
            match decl.kind {
                DeclKind::Structure => {
                    structures += 1;
                    file_structs_classes += 1;
                    dir_entry.structures_and_classes += 1;
                }
                DeclKind::Class => {
                    classes += 1;
                    file_structs_classes += 1;
                    dir_entry.structures_and_classes += 1;
                }
                DeclKind::Instance => {
                    instances += 1;
                    dir_entry.instances += 1;
                }
                DeclKind::Inductive => {
                    inductives += 1;
                }
                DeclKind::Theorem => {
                    total_theorems += 1;
                    file_thms += 1;
                    dir_entry.total_theorems += 1;
                    let reused = referenced_by_others.contains(&decl.name)
                        || referenced_by_others.contains(&decl.fq_name);
                    if reused {
                        composed_theorems += 1;
                        dir_entry.composed_theorems += 1;
                    } else {
                        isolated_leaf_theorems += 1;
                        dir_entry.isolated_leaf_theorems += 1;
                    }
                }
                _ => {}
            }
        }

        if file.line_count > MONOLITHIC_LINE_THRESHOLD {
            monolithic_modules.push(MonolithicModule {
                path: file.rel_path.clone(),
                lines: file.line_count,
                declarations: file.declarations.len(),
                theorems: file_thms,
                structures_and_classes: file_structs_classes,
            });
        }
    }

    monolithic_modules.sort_by(|a, b| b.lines.cmp(&a.lines).then_with(|| a.path.cmp(&b.path)));

    for d in dir_map.values_mut() {
        d.carrier_to_leaf_ratio =
            round4((d.structures_and_classes as f64) / (d.isolated_leaf_theorems.max(1) as f64));
    }

    let carriers = structures + classes;
    let carrier_to_leaf_ratio = round4((carriers as f64) / (isolated_leaf_theorems.max(1) as f64));
    let theorem_reuse_ratio = if total_theorems == 0 {
        1.0
    } else {
        round4((composed_theorems as f64) / (total_theorems as f64))
    };

    let reuse_score = 50.0 * theorem_reuse_ratio;
    let interface_score = if (total_theorems == 0 && carriers == 0) || isolated_leaf_theorems == 0 {
        30.0
    } else {
        30.0 * (carrier_to_leaf_ratio / (carrier_to_leaf_ratio + 0.25))
    };
    let hygiene_score = if lean_files == 0 {
        20.0
    } else {
        20.0 * (1.0 - (monolithic_modules.len() as f64 / lean_files as f64)).clamp(0.0, 1.0)
    };
    let compositionality_index =
        round2((reuse_score + interface_score + hygiene_score).clamp(0.0, 100.0));

    let cone = crate::cone::compute_cone_from_index("", index, None);

    ModularityReport {
        monolithic_line_threshold: MONOLITHIC_LINE_THRESHOLD,
        lean_files,
        total_lean_lines,
        max_module_lines,
        max_module_path,
        structures,
        classes,
        instances,
        inductives,
        total_theorems,
        composed_theorems,
        isolated_leaf_theorems,
        carrier_to_leaf_ratio,
        theorem_reuse_ratio,
        compositionality_index,
        max_public_cone_depth: cone.max_public_cone_depth,
        critical_path: cone.critical_path,
        high_blast_radius_hubs: cone.high_blast_radius_hubs,
        file_wide_expose_modules: cone.file_wide_expose_modules,
        public_meta_import_leaks: cone.public_meta_import_leaks.len(),
        monolithic_modules,
        by_directory: dir_map.into_values().collect(),
    }
}
