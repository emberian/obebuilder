//! Complete Markdown architecture-doc symbol, module-path, `inductive` constructor table,
//! and `Navel` confession-prose verifier (`DESIGN.md` §2.6, closing `DocsCensus.lean`'s blind spots).

use crate::lean_index::LeanIndex;
use obb_core::{ArtifactKind, Finding, Regime, Severity, Sink};
use std::collections::{BTreeSet, HashSet};
use std::path::Path;

fn is_lean_stdlib_prefix(prefix: &str) -> bool {
    matches!(
        prefix,
        "Nat"
            | "Int"
            | "Bool"
            | "String"
            | "Substring"
            | "Char"
            | "UInt8"
            | "UInt16"
            | "UInt32"
            | "UInt64"
            | "USize"
            | "Float"
            | "BitVec"
            | "Fin"
            | "List"
            | "Array"
            | "ByteArray"
            | "Option"
            | "Except"
            | "IO"
            | "EIO"
            | "BaseIO"
            | "System"
            | "FilePath"
            | "Lean"
            | "Elab"
            | "Meta"
            | "Tactic"
            | "Syntax"
            | "TSyntax"
            | "Name"
            | "Expr"
            | "Level"
            | "Environment"
            | "ConstantInfo"
            | "Json"
            | "ToJson"
            | "FromJson"
            | "Std"
            | "Prod"
            | "Sum"
            | "Sigma"
            | "PSigma"
            | "Subtype"
            | "Decidable"
            | "DecidableEq"
            | "BEq"
            | "Hashable"
            | "Repr"
            | "ToString"
            | "Inhabited"
            | "Nonempty"
            | "Ord"
            | "Iff"
            | "And"
            | "Or"
            | "Eq"
            | "HEq"
            | "True"
            | "False"
            | "Task"
            | "Promise"
            | "HashMap"
            | "HashSet"
            | "RBMap"
            | "RBTree"
    )
}

fn is_common_non_lean_snake_case(tok: &str) -> bool {
    matches!(
        tok,
        "snake_case"
            | "camel_case"
            | "cargo_test"
            | "git_status"
            | "merge_tree"
            | "obend_ffi"
            | "libobend_ffi"
            | "step_one_cycle"
            | "sim_backend"
            | "sovereign_drex_cluster"
            | "test_tier1"
            | "no_sorry_ax"
            | "no_declared_axiom"
            | "tier1_module_sec_cap"
            | "docs_symbols_exist"
            | "no_tautological_judge_meaning"
            | "no_discarded_tactic_result"
            | "planted_fault_red"
            | "home_revert_clean"
            | "max_heartbeats"
            | "assert_compiled"
            | "fixture_kept"
            | "run_cmd"
            | "set_option"
            | "termination_by"
            | "decreasing_by"
            | "native_decide"
    )
}

fn should_scan_markdown_path(rel_path: &str) -> bool {
    // Skip historical audit logs, archived scratchpads, and build outputs
    if rel_path.starts_with("review/")
        || rel_path.starts_with("archive/")
        || rel_path.starts_with("reports/")
        || rel_path.starts_with("ledger/")
        || rel_path.starts_with("vault/")
        || rel_path.contains("/review/")
        || rel_path.contains("/archive/")
    {
        return false;
    }
    let fname = Path::new(rel_path)
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("");
    !matches!(
        fname,
        "CHANGELOG.md" | "FINDINGS.md" | "VAULT.md" | "AGENTS.md" | "GEMINI.md" | "CLAUDE.md"
    )
}

/// Extract backticked code spans from a single markdown line: `(content, col_1_based)`.
fn extract_inline_code_spans(line: &str) -> Vec<(String, usize)> {
    let chars: Vec<char> = line.chars().collect();
    let n = chars.len();
    let mut i = 0usize;
    let mut out = Vec::new();

    while i < n {
        if chars[i] == '`' {
            let start_col = i + 1;
            let mut ticks = 0usize;
            while i < n && chars[i] == '`' {
                ticks += 1;
                i += 1;
            }
            let content_start = i;
            let mut found_end = None;
            while i < n {
                if chars[i] == '`' {
                    let close_start = i;
                    let mut cticks = 0usize;
                    while i < n && chars[i] == '`' {
                        cticks += 1;
                        i += 1;
                    }
                    if cticks == ticks {
                        found_end = Some(close_start);
                        break;
                    }
                } else {
                    i += 1;
                }
            }
            if let Some(end_idx) = found_end {
                let text: String = chars[content_start..end_idx].iter().collect();
                out.push((text, start_col));
            }
        } else {
            i += 1;
        }
    }
    out
}

/// Extract bare `Foo.lean` filenames outside backticks (e.g. `(RTL.lean, Sim.lean, Verify.lean)`).
fn extract_bare_lean_filenames(line: &str) -> Vec<(String, usize)> {
    let chars: Vec<char> = line.chars().collect();
    let n = chars.len();
    let mut out = Vec::new();
    let mut in_ticks = false;
    let mut i = 0usize;

    while i < n {
        if chars[i] == '`' {
            in_ticks = !in_ticks;
            i += 1;
            continue;
        }
        if in_ticks {
            i += 1;
            continue;
        }
        if chars[i].is_ascii_alphabetic() {
            let start = i;
            while i < n && (chars[i].is_ascii_alphanumeric() || chars[i] == '_' || chars[i] == '/') {
                i += 1;
            }
            if i + 5 <= n {
                let tail: String = chars[i..i + 5].iter().collect();
                if tail == ".lean" {
                    let full: String = chars[start..i + 5].iter().collect();
                    out.push((full, start + 1));
                    i += 5;
                    continue;
                }
            }
        } else {
            i += 1;
        }
    }
    out
}

fn split_pipe_row(line: &str) -> Vec<String> {
    let trimmed = line.trim();
    if !trimmed.starts_with('|') || !trimmed.ends_with('|') {
        return Vec::new();
    }
    let inner = &trimmed[1..trimmed.len() - 1];
    inner.split('|').map(|c| c.trim().to_string()).collect()
}

fn is_separator_row(cells: &[String]) -> bool {
    !cells.is_empty()
        && cells.iter().all(|c| {
            let clean = c.trim();
            !clean.is_empty() && clean.chars().all(|ch| matches!(ch, '-' | ':' | ' '))
        })
}

fn is_ident_token(s: &str) -> bool {
    !s.is_empty()
        && s.chars()
            .next()
            .map(|c| c.is_ascii_alphabetic() || c == '_')
            .unwrap_or(false)
        && s.chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '\'')
}

/// Resolve which Lean `inductive` a Markdown heading + table header refers to, if any.
fn resolve_table_target_inductive(
    heading_text: &str,
    header_cells: &[String],
    index: &LeanIndex,
) -> Option<(String, BTreeSet<String>, Option<usize>)> {
    // Identify which column holds constructors (`Constructors`, `Constructor`, `Former`, `Formers`, or exact inductive name)
    let mut ctor_col: Option<usize> = None;
    for (col_idx, h) in header_cells.iter().enumerate() {
        let h_clean = h.trim_matches('*').trim_matches('`').trim();
        let h_low = h_clean.to_ascii_lowercase();
        if matches!(
            h_low.as_str(),
            "constructor" | "constructors" | "former" | "formers" | "lean constructor" | "variant" | "variants"
        ) {
            ctor_col = Some(col_idx);
            break;
        }
        if index.inductives.contains_key(h_clean) {
            if let Some(ctors) = index.inductives.get(h_clean) {
                return Some((h_clean.to_string(), ctors.clone(), Some(col_idx)));
            }
        }
    }

    let ctor_col = ctor_col?;

    // Check if heading cites a specific `Obend/.../*.lean` module
    for (span, _) in extract_inline_code_spans(heading_text) {
        let clean = span.trim();
        let norm = clean.strip_prefix("lean/").unwrap_or(clean);
        if let Some(mod_inds) = index.module_inductives.get(norm) {
            if mod_inds.len() == 1 {
                let (ind_name, ctors) = mod_inds.iter().next().unwrap();
                return Some((ind_name.clone(), ctors.clone(), Some(ctor_col)));
            }
            // Match heading words against inductive names in that module (e.g. `Term Former Table`)
            for word in heading_text
                .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                .filter(|w| !w.is_empty())
            {
                if let Some(ctors) = mod_inds.get(word) {
                    return Some((word.to_string(), ctors.clone(), Some(ctor_col)));
                }
            }
        }
        if let Some(ctors) = index.inductives.get(clean) {
            return Some((clean.to_string(), ctors.clone(), Some(ctor_col)));
        }
    }

    // Fallback: check Capitalized identifiers in heading against unique `index.inductives`
    for word in heading_text
        .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .filter(|w| w.chars().next().map(|c| c.is_ascii_uppercase()).unwrap_or(false))
    {
        if let Some(ctors) = index.inductives.get(word) {
            return Some((word.to_string(), ctors.clone(), Some(ctor_col)));
        }
    }

    None
}

/// Lint a single Markdown document against `LeanIndex` and `PROCESS.md` `Navel` prose rules.
pub fn lint_markdown_file(
    rel_path: &str,
    src: &str,
    index: &LeanIndex,
    repo_root: Option<&Path>,
) -> Vec<Finding> {
    let mut findings = Vec::new();
    let has_lean_corpus = !index.files.is_empty();
    let lines: Vec<&str> = src.lines().collect();

    let mut in_fence = false;
    let mut fence_lang = String::new();
    let mut fence_start_line = 1usize;
    let mut fence_buf = String::new();

    let mut current_heading = String::new();
    let mut seen_missing_on_file: HashSet<(String, usize)> = HashSet::new();

    let mut i = 0usize;
    while i < lines.len() {
        let line = lines[i];
        let line_no = i + 1;
        let trimmed = line.trim_start();

        // Fenced code blocks ```...
        if let Some(after_ticks) = trimmed.strip_prefix("```") {
            if !in_fence {
                in_fence = true;
                fence_lang = after_ticks
                    .split_whitespace()
                    .next()
                    .unwrap_or("")
                    .to_ascii_lowercase();
                fence_start_line = line_no;
                fence_buf.clear();
            } else {
                if has_lean_corpus && (fence_lang == "lean" || fence_lang == "lean4" || fence_lang.is_empty())
                {
                    check_fenced_inductive_blocks(
                        rel_path,
                        fence_start_line,
                        &fence_buf,
                        index,
                        &mut findings,
                    );
                }
                in_fence = false;
                fence_lang.clear();
                fence_buf.clear();
            }
            i += 1;
            continue;
        }

        if in_fence {
            fence_buf.push_str(line);
            fence_buf.push('\n');
            i += 1;
            continue;
        }

        // Track headings (`# ...`)
        if trimmed.starts_with('#') {
            current_heading = trimmed.trim_start_matches('#').trim().to_string();
        }

        // Navel / confession prose check (`PROCESS.md` sink `Navel`: self-audit/confession in architecture docs)
        check_navel_prose(rel_path, line_no, line, &mut findings);

        // Pipe table constructor check (e.g. `DESIGN.md` §1.1 `Term Former Table` & §1.2 `Quantities`)
        if has_lean_corpus && trimmed.starts_with('|') && i + 1 < lines.len() {
            let header_cells = split_pipe_row(line);
            let sep_cells = split_pipe_row(lines[i + 1]);
            if !header_cells.is_empty() && is_separator_row(&sep_cells) {
                if let Some((ind_name, actual_ctors, Some(ctor_col))) =
                    resolve_table_target_inductive(&current_heading, &header_cells, index)
                {
                    let mut row_i = i + 2;
                    while row_i < lines.len() && lines[row_i].trim_start().starts_with('|') {
                        let row_cells = split_pipe_row(lines[row_i]);
                        if let Some(cell) = row_cells.get(ctor_col) {
                            for (span, _) in extract_inline_code_spans(cell) {
                                let clean_span = span.trim();
                                let first_tok = clean_span
                                    .split_whitespace()
                                    .next()
                                    .unwrap_or("")
                                    .trim_end_matches(|c: char| matches!(c, ',' | ';' | ')' | ':'));
                                let ctor_candidate = first_tok
                                    .strip_prefix(&format!("{ind_name}."))
                                    .or_else(|| first_tok.strip_prefix('.'))
                                    .unwrap_or(first_tok);
                                if is_ident_token(ctor_candidate)
                                    && !actual_ctors.contains(ctor_candidate)
                                {
                                    let actual_list: Vec<&str> =
                                        actual_ctors.iter().map(String::as_str).collect();
                                    findings.push(Finding {
                                        rule_id: "markdown/hallucinated-constructor".to_string(),
                                        severity: Severity::Error,
                                        artifact_kind: ArtifactKind::S,
                                        max_regime: Regime::Attested,
                                        sink: Some(Sink::Label),
                                        path: rel_path.to_string(),
                                        line: row_i + 1,
                                        column: 1,
                                        symbol: Some(format!("{ind_name}.{ctor_candidate}")),
                                        message: format!(
                                            "Markdown table claims constructor `{ctor_candidate}` on `inductive {ind_name}`, which does not exist in Lean source (actual: [{}])",
                                            actual_list.join(", ")
                                        ),
                                        remediation: format!(
                                            "Update the `{ind_name}` table in `{rel_path}` to match the actual Lean `inductive {ind_name}` declaration, or generate constructor tables from Lean."
                                        ),
                                    });
                                }
                            }
                        }
                        row_i += 1;
                    }
                }
            }
        }

        if !has_lean_corpus {
            i += 1;
            continue;
        }

        // Inline backticked spans
        for (raw_span, col) in extract_inline_code_spans(line) {
            let span = raw_span.trim();
            if span.is_empty() {
                continue;
            }

            // 1. `review/*.md` citations
            if span.starts_with("review/") && span.ends_with(".md") && !span.contains('*') {
                let exists = index.review_paths.contains(span)
                    || repo_root.map(|r| r.join(span).is_file()).unwrap_or(false);
                if !exists && seen_missing_on_file.insert((span.to_string(), line_no)) {
                    findings.push(Finding {
                        rule_id: "markdown/missing-cited-file".to_string(),
                        severity: Severity::Warning,
                        artifact_kind: ArtifactKind::S,
                        max_regime: Regime::Attested,
                        sink: Some(Sink::Navel),
                        path: rel_path.to_string(),
                        line: line_no,
                        column: col,
                        symbol: Some(span.to_string()),
                        message: format!("Markdown cites `{span}`, which does not exist on disk"),
                        remediation: "Remove stale review citations from architecture docs (keep live invariants only).".to_string(),
                    });
                }
                continue;
            }

            // 2. Lean file / directory paths (`Obend/.../*.lean`, `lean/Obend/...`, or bare `Foo.lean`)
            if (span.ends_with(".lean") || (span.starts_with("Obend/") && span.ends_with('/')))
                && !span.contains(' ')
                && !span.contains('*')
            {
                let norm = span.strip_prefix("lean/").unwrap_or(span);
                if let Some(dir_sub) = norm.strip_prefix("Obend/").and_then(|s| s.strip_suffix('/'))
                {
                    let top_sub = dir_sub.split('/').next().unwrap_or(dir_sub);
                    let dir_exists = index.subsystems.contains(top_sub)
                        || repo_root
                            .map(|r| r.join("lean").join(norm).is_dir())
                            .unwrap_or(false);
                    if !dir_exists && seen_missing_on_file.insert((span.to_string(), line_no)) {
                        findings.push(Finding {
                            rule_id: "markdown/missing-lean-file".to_string(),
                            severity: Severity::Error,
                            artifact_kind: ArtifactKind::S,
                            max_regime: Regime::Attested,
                            sink: Some(Sink::Label),
                            path: rel_path.to_string(),
                            line: line_no,
                            column: col,
                            symbol: Some(span.to_string()),
                            message: format!(
                                "Markdown cites Lean subsystem directory `{span}`, which does not exist under `lean/Obend/`"
                            ),
                            remediation: "Point to the real `lean/Obend/` directory or delete aspirational directory citations.".to_string(),
                        });
                    }
                } else if norm.starts_with("Obend/") {
                    if !index.lean_rel_paths.contains(norm)
                        && seen_missing_on_file.insert((span.to_string(), line_no))
                    {
                        findings.push(Finding {
                            rule_id: "markdown/missing-lean-file".to_string(),
                            severity: Severity::Error,
                            artifact_kind: ArtifactKind::S,
                            max_regime: Regime::Attested,
                            sink: Some(Sink::Label),
                            path: rel_path.to_string(),
                            line: line_no,
                            column: col,
                            symbol: Some(span.to_string()),
                            message: format!(
                                "Markdown cites Lean module `{span}`, which does not exist in `lean/Obend/`"
                            ),
                            remediation: "Update the path to the actual `.lean` module or remove unimplemented roadmap module names.".to_string(),
                        });
                    }
                } else if !norm.contains('/') {
                    let exists_in_lean_root = repo_root
                        .map(|r| r.join("lean").join(norm).is_file() || r.join(norm).is_file())
                        .unwrap_or(false);
                    if !index.by_basename.contains_key(norm)
                        && !exists_in_lean_root
                        && norm != "lakefile.lean"
                        && seen_missing_on_file.insert((span.to_string(), line_no))
                    {
                        findings.push(Finding {
                            rule_id: "markdown/missing-lean-file".to_string(),
                            severity: Severity::Error,
                            artifact_kind: ArtifactKind::S,
                            max_regime: Regime::Attested,
                            sink: Some(Sink::Label),
                            path: rel_path.to_string(),
                            line: line_no,
                            column: col,
                            symbol: Some(span.to_string()),
                            message: format!(
                                "Markdown cites Lean file `{span}`, which matches no `.lean` file in the repository"
                            ),
                            remediation: "Replace bare filename with an existing `Obend/.../*.lean` module or move aspirational items out of present-tense docs.".to_string(),
                        });
                    }
                }
                continue;
            }

            // Extract leading symbol token if span is `Sym.member arg1 arg2` or exact symbol
            let first_word = span
                .split(|c: char| c.is_whitespace() || matches!(c, '(' | ')' | ',' | ';'))
                .find(|s| !s.is_empty())
                .unwrap_or("");

            // 3. Explicit `Obend.*` constant citations
            if first_word.starts_with("Obend.")
                && first_word
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '\''))
            {
                if !index.has_symbol(first_word)
                    && seen_missing_on_file.insert((first_word.to_string(), line_no))
                {
                    findings.push(Finding {
                        rule_id: "markdown/missing-lean-symbol".to_string(),
                        severity: Severity::Error,
                        artifact_kind: ArtifactKind::S,
                        max_regime: Regime::Attested,
                        sink: Some(Sink::Label),
                        path: rel_path.to_string(),
                        line: line_no,
                        column: col,
                        symbol: Some(first_word.to_string()),
                        message: format!(
                            "Markdown cites Lean constant `{first_word}`, which does not exist in `lean/Obend/`"
                        ),
                        remediation: "Replace with the actual Lean declaration name or delete the phantom reference.".to_string(),
                    });
                }
                continue;
            }

            // 4. Qualified `Type.member` citations (`Quantity.zero`, `Term.brand`, `Judge.accepts`, `Code.encode`)
            if let Some((lhs, rhs)) = first_word.split_once('.') {
                let valid_shape = lhs
                    .chars()
                    .next()
                    .map(|c| c.is_ascii_uppercase())
                    .unwrap_or(false)
                    && lhs.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
                    && !rhs.is_empty()
                    && !rhs.contains('.')
                    && rhs
                        .chars()
                        .next()
                        .map(|c| c.is_ascii_alphabetic() || c == '_')
                        .unwrap_or(false)
                    && rhs
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '\'');
                // Exclude file extensions (`Cargo.toml`, `Foo.rs`, `Bar.py`, `Baz.json`, `Qux.obend`, `X.v`, `Y.sv`)
                let looks_like_filename = matches!(
                    rhs,
                    "lean"
                        | "rs"
                        | "py"
                        | "md"
                        | "json"
                        | "toml"
                        | "yaml"
                        | "yml"
                        | "obend"
                        | "v"
                        | "sv"
                        | "c"
                        | "h"
                        | "sh"
                        | "txt"
                        | "jsonl"
                        | "db"
                );
                if valid_shape && !looks_like_filename && !is_lean_stdlib_prefix(lhs) {
                    // Check if `lhs` is a known Lean type/namespace/subsystem in `LeanIndex`
                    let lhs_known_in_lean = index.has_symbol(lhs)
                        || index.inductives.contains_key(lhs)
                        || index.subsystems.contains(lhs);
                    if lhs_known_in_lean
                        && !index.has_symbol(first_word)
                        && seen_missing_on_file.insert((first_word.to_string(), line_no))
                    {
                        findings.push(Finding {
                            rule_id: "markdown/missing-lean-symbol".to_string(),
                            severity: Severity::Error,
                            artifact_kind: ArtifactKind::S,
                            max_regime: Regime::Attested,
                            sink: Some(Sink::Label),
                            path: rel_path.to_string(),
                            line: line_no,
                            column: col,
                            symbol: Some(first_word.to_string()),
                            message: format!(
                                "Markdown cites `{first_word}`, which is not declared on `{lhs}` in `lean/Obend/`"
                            ),
                            remediation: format!(
                                "Update `{first_word}` to an existing constructor/declaration of `{lhs}` or implement it in Lean."
                            ),
                        });
                    }
                }
                continue;
            }

            // 5. Bare `snake_case` theorem claims (`step_conserves_linear`, `dated_sound`, `accepts_cited_sound`)
            let is_single_token = !span.contains(char::is_whitespace)
                && !span.contains('/')
                && !span.contains('.')
                && !span.contains('-')
                && !span.contains(':');
            if is_single_token
                && span.contains('_')
                && span
                    .chars()
                    .next()
                    .map(|c| c.is_ascii_lowercase())
                    .unwrap_or(false)
                && span
                    .chars()
                    .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_')
                && !is_common_non_lean_snake_case(span)
            {
                let sounds_like_lean_theorem = span.ends_with("_sound")
                    || span.ends_with("_complete")
                    || span.ends_with("_binds")
                    || span.ends_with("_conserves")
                    || span.contains("_conserves_")
                    || span.ends_with("_preserves")
                    || span.contains("_preserves_")
                    || span.ends_with("_iff")
                    || span.ends_with("_thm")
                    || span.ends_with("_lemma")
                    || span.ends_with("_inv")
                    || span.ends_with("_deterministic");
                if sounds_like_lean_theorem
                    && !index.has_symbol(span)
                    && seen_missing_on_file.insert((span.to_string(), line_no))
                {
                    findings.push(Finding {
                        rule_id: "markdown/missing-lean-symbol".to_string(),
                        severity: Severity::Error,
                        artifact_kind: ArtifactKind::S,
                        max_regime: Regime::Attested,
                        sink: Some(Sink::Label),
                        path: rel_path.to_string(),
                        line: line_no,
                        column: col,
                        symbol: Some(span.to_string()),
                        message: format!(
                            "Markdown claims Lean theorem `{span}`, which does not exist in `lean/Obend/`"
                        ),
                        remediation: "Prove and name the theorem in Lean, or replace the prose claim with the actual proved theorem identifier.".to_string(),
                    });
                }
            }
        }

        // 6. Bare `(RTL.lean, Sim.lean, ...)` filenames outside backticks
        for (bare_lean, col) in extract_bare_lean_filenames(line) {
            let norm = bare_lean.strip_prefix("lean/").unwrap_or(&bare_lean);
            let found = if norm.contains('/') {
                index.lean_rel_paths.contains(norm)
                    || repo_root.map(|r| r.join(norm).is_file()).unwrap_or(false)
            } else {
                index.by_basename.contains_key(norm)
                    || repo_root
                        .map(|r| r.join("lean").join(norm).is_file() || r.join(norm).is_file())
                        .unwrap_or(false)
                    || norm == "lakefile.lean"
            };
            if !found && seen_missing_on_file.insert((bare_lean.clone(), line_no)) {
                findings.push(Finding {
                    rule_id: "markdown/missing-lean-file".to_string(),
                    severity: Severity::Error,
                    artifact_kind: ArtifactKind::S,
                    max_regime: Regime::Attested,
                    sink: Some(Sink::Label),
                    path: rel_path.to_string(),
                    line: line_no,
                    column: col,
                    symbol: Some(bare_lean.clone()),
                    message: format!(
                        "Markdown cites Lean file `{bare_lean}` outside code ticks, which does not exist in the repository"
                    ),
                    remediation: "Remove nonexistent `.lean` module names from present-tense architecture prose.".to_string(),
                });
            }
        }

        i += 1;
    }

    findings
}

fn check_fenced_inductive_blocks(
    rel_path: &str,
    fence_start_line: usize,
    fence_src: &str,
    index: &LeanIndex,
    findings: &mut Vec<Finding>,
) {
    let mut current_ind: Option<(String, Option<BTreeSet<String>>, usize)> = None;

    for (offset, line) in fence_src.lines().enumerate() {
        let line_no = fence_start_line + 1 + offset;
        let trimmed = line.trim();

        if let Some(rest) = trimmed.strip_prefix("inductive ") {
            let ind_name = rest
                .split(|c: char| c.is_whitespace() || matches!(c, '(' | '{' | '[' | ':'))
                .find(|s| !s.is_empty())
                .unwrap_or("");
            if is_ident_token(ind_name) {
                let known = index.inductives.get(ind_name).cloned();
                if known.is_none() && !index.has_symbol(ind_name) {
                    findings.push(Finding {
                        rule_id: "markdown/missing-lean-symbol".to_string(),
                        severity: Severity::Error,
                        artifact_kind: ArtifactKind::S,
                        max_regime: Regime::Attested,
                        sink: Some(Sink::Label),
                        path: rel_path.to_string(),
                        line: line_no,
                        column: 1,
                        symbol: Some(ind_name.to_string()),
                        message: format!(
                            "Fenced code block declares `inductive {ind_name}`, which does not exist in `lean/Obend/`"
                        ),
                        remediation: "Keep fenced `inductive` specifications synchronized with real Lean definitions.".to_string(),
                    });
                }
                current_ind = Some((ind_name.to_string(), known, line_no));
            }
            continue;
        }

        // End of inductive block on unindented non-`|` command
        if !trimmed.is_empty()
            && !line.starts_with(' ')
            && !line.starts_with('\t')
            && !trimmed.starts_with('|')
            && !trimmed.starts_with("--")
        {
            current_ind = None;
        }

        if let Some((ref ind_name, Some(ref actual_ctors), _)) = current_ind {
            if let Some(after_pipe) = trimmed.strip_prefix('|') {
                let ctor = after_pipe
                    .trim_start()
                    .trim_start_matches('.')
                    .split(|c: char| c.is_whitespace() || matches!(c, '(' | '{' | '[' | ':'))
                    .find(|s| !s.is_empty())
                    .unwrap_or("");
                if is_ident_token(ctor) && ctor != "..." && !actual_ctors.contains(ctor) {
                    let actual_list: Vec<&str> = actual_ctors.iter().map(String::as_str).collect();
                    findings.push(Finding {
                        rule_id: "markdown/hallucinated-constructor".to_string(),
                        severity: Severity::Error,
                        artifact_kind: ArtifactKind::S,
                        max_regime: Regime::Attested,
                        sink: Some(Sink::Label),
                        path: rel_path.to_string(),
                        line: line_no,
                        column: 1,
                        symbol: Some(format!("{ind_name}.{ctor}")),
                        message: format!(
                            "Fenced `inductive {ind_name}` lists constructor `{ctor}`, which does not exist in Lean source (actual: [{}])",
                            actual_list.join(", ")
                        ),
                        remediation: format!(
                            "Align fenced `inductive {ind_name}` constructors with the Lean definition."
                        ),
                    });
                }
            }
        }
    }
}

fn check_navel_prose(rel_path: &str, line_no: usize, line: &str, findings: &mut Vec<Finding>) {
    let lower = line.to_ascii_lowercase();
    let trigger = if lower.contains("deleted on 202") || lower.contains("removed on 202") {
        Some("historical deletion diary (`deleted/removed on 202...`) inside live architecture doc")
    } else if lower.contains("until 2026-") || lower.contains("prior to 2026-") {
        Some("dated historical confession (`until/prior to 2026-...`) inside live architecture doc")
    } else if (lower.contains("0 sorryax") || lower.contains("zero sorryax") || lower.contains("zero sorry"))
        && !lower.contains("floor")
        && !lower.contains("no_sorry_ax")
        && !lower.contains("rule")
        && !lower.contains("detector")
    {
        Some("self-congratulatory `0 sorryAx` prose assertion (put mechanical checks in `obb judge`, not prose)")
    } else {
        None
    };

    if let Some(reason) = trigger {
        findings.push(Finding {
            rule_id: "markdown/navel-prose".to_string(),
            severity: Severity::Warning,
            artifact_kind: ArtifactKind::S,
            max_regime: Regime::Attested,
            sink: Some(Sink::Navel),
            path: rel_path.to_string(),
            line: line_no,
            column: 1,
            symbol: None,
            message: format!("`Navel` confession/self-audit prose in `{rel_path}`: {reason}"),
            remediation: "State only live invariants in architecture docs; move history to git commits and self-checks to `obb lint` / `obb judge`.".to_string(),
        });
    }
}

pub fn scan_markdown_files(repo_root: &Path, index: &LeanIndex) -> (usize, Vec<Finding>) {
    let mut count = 0usize;
    let mut findings = Vec::new();
    let mut md_paths = Vec::new();

    for entry in walkdir::WalkDir::new(repo_root)
        .into_iter()
        .filter_entry(|e| {
            let name = e.file_name().to_str().unwrap_or("");
            if e.depth() > 0 && e.file_type().is_dir() && name.starts_with('.') {
                return false;
            }
            !matches!(name, "target" | "node_modules" | "astra")
        })
        .flatten()
    {
        if entry.file_type().is_file()
            && entry.path().extension().and_then(|e| e.to_str()) == Some("md")
        {
            md_paths.push(entry.path().to_path_buf());
        }
    }
    md_paths.sort();

    for p in md_paths {
        let Ok(rel) = p.strip_prefix(repo_root) else {
            continue;
        };
        let rel_str = rel.to_string_lossy().replace('\\', "/");
        if !should_scan_markdown_path(&rel_str) {
            continue;
        }
        if let Ok(src) = std::fs::read_to_string(&p) {
            count += 1;
            findings.extend(lint_markdown_file(&rel_str, &src, index, Some(repo_root)));
        }
    }

    (count, findings)
}
