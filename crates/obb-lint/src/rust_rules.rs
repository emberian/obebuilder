//! Lexical & structural analyzer for Rust crates (`MockBackend` & hardcoded `.obend` semantic mirror detectors).

use obb_core::{ArtifactKind, Finding, Regime, Severity, Sink};
use std::path::Path;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RsTokKind {
    Ident(String),
    StrLit(String),
    NumLit(String),
    DocOrLineComment(String),
    Symbol(String),
}

#[derive(Debug, Clone)]
pub struct RsTok {
    pub kind: RsTokKind,
    pub line: usize,
    pub col: usize,
}

pub fn tokenize_rust(src: &str) -> Vec<RsTok> {
    let chars: Vec<char> = src.chars().collect();
    let n = chars.len();
    let mut i = 0usize;
    let mut line = 1usize;
    let mut col = 1usize;
    let mut out = Vec::new();

    while i < n {
        let c = chars[i];
        if c == '\n' {
            line += 1;
            col = 1;
            i += 1;
            continue;
        }
        if c.is_whitespace() {
            col += 1;
            i += 1;
            continue;
        }

        let sline = line;
        let scol = col;

        // Line comment `//...`
        if c == '/' && i + 1 < n && chars[i + 1] == '/' {
            i += 2;
            col += 2;
            let mut text = String::new();
            while i < n && chars[i] != '\n' {
                text.push(chars[i]);
                i += 1;
                col += 1;
            }
            out.push(RsTok {
                kind: RsTokKind::DocOrLineComment(text),
                line: sline,
                col: scol,
            });
            continue;
        }

        // Nested block comment `/* ... */`
        if c == '/' && i + 1 < n && chars[i + 1] == '*' {
            i += 2;
            col += 2;
            let mut depth = 1usize;
            while i < n && depth > 0 {
                if chars[i] == '/' && i + 1 < n && chars[i + 1] == '*' {
                    depth += 1;
                    i += 2;
                    col += 2;
                } else if chars[i] == '*' && i + 1 < n && chars[i + 1] == '/' {
                    depth -= 1;
                    i += 2;
                    col += 2;
                } else if chars[i] == '\n' {
                    line += 1;
                    col = 1;
                    i += 1;
                } else {
                    i += 1;
                    col += 1;
                }
            }
            continue;
        }

        // Raw string literal `r#"..."#` or `r"..."`
        if c == 'r' && i + 1 < n && (chars[i + 1] == '#' || chars[i + 1] == '"') {
            let mut hashes = 0usize;
            let mut j = i + 1;
            while j < n && chars[j] == '#' {
                hashes += 1;
                j += 1;
            }
            if j < n && chars[j] == '"' {
                col += (j - i) + 1;
                i = j + 1;
                let mut s = String::new();
                while i < n {
                    if chars[i] == '"' {
                        let mut h = 0usize;
                        while i + 1 + h < n && h < hashes && chars[i + 1 + h] == '#' {
                            h += 1;
                        }
                        if h == hashes {
                            i += 1 + hashes;
                            col += 1 + hashes;
                            break;
                        }
                    }
                    if chars[i] == '\n' {
                        line += 1;
                        col = 1;
                    } else {
                        col += 1;
                    }
                    s.push(chars[i]);
                    i += 1;
                }
                out.push(RsTok {
                    kind: RsTokKind::StrLit(s),
                    line: sline,
                    col: scol,
                });
                continue;
            }
        }

        // Normal string literal `"..."`
        if c == '"' {
            i += 1;
            col += 1;
            let mut s = String::new();
            while i < n && chars[i] != '"' {
                if chars[i] == '\\' && i + 1 < n {
                    s.push(chars[i + 1]);
                    if chars[i + 1] == '\n' {
                        line += 1;
                        col = 1;
                    } else {
                        col += 2;
                    }
                    i += 2;
                    continue;
                }
                if chars[i] == '\n' {
                    line += 1;
                    col = 1;
                } else {
                    col += 1;
                }
                s.push(chars[i]);
                i += 1;
            }
            if i < n && chars[i] == '"' {
                i += 1;
                col += 1;
            }
            out.push(RsTok {
                kind: RsTokKind::StrLit(s),
                line: sline,
                col: scol,
            });
            continue;
        }

        // Char literal / lifetime `'a` or `'x'`
        if c == '\'' {
            if i + 2 < n && chars[i + 1] != '\\' && chars[i + 2] == '\'' {
                i += 3;
                col += 3;
                continue;
            } else if i + 3 < n && chars[i + 1] == '\\' && chars[i + 3] == '\'' {
                i += 4;
                col += 4;
                continue;
            }
            i += 1;
            col += 1;
            while i < n && (chars[i].is_alphanumeric() || chars[i] == '_') {
                i += 1;
                col += 1;
            }
            continue;
        }

        // Numeric literal
        if c.is_ascii_digit() {
            let mut num = String::new();
            while i < n && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                num.push(chars[i]);
                i += 1;
                col += 1;
            }
            out.push(RsTok {
                kind: RsTokKind::NumLit(num),
                line: sline,
                col: scol,
            });
            continue;
        }

        // Identifier
        if c.is_alphabetic() || c == '_' {
            let mut id = String::new();
            while i < n && (chars[i].is_alphanumeric() || chars[i] == '_') {
                id.push(chars[i]);
                i += 1;
                col += 1;
            }
            out.push(RsTok {
                kind: RsTokKind::Ident(id),
                line: sline,
                col: scol,
            });
            continue;
        }

        if i + 1 < n {
            let two = format!("{}{}", c, chars[i + 1]);
            if matches!(two.as_str(), "::" | "->" | "=>" | "==" | "!=" | "<=" | ">=" | "#[") {
                i += 2;
                col += 2;
                out.push(RsTok {
                    kind: RsTokKind::Symbol(two),
                    line: sline,
                    col: scol,
                });
                continue;
            }
        }

        i += 1;
        col += 1;
        out.push(RsTok {
            kind: RsTokKind::Symbol(c.to_string()),
            line: sline,
            col: scol,
        });
    }

    out
}

pub fn lint_rust_file(rel_path: &str, src: &str) -> Vec<Finding> {
    let mut findings = Vec::new();
    let is_test_path = rel_path.contains("/tests/") || rel_path.ends_with("_test.rs");
    if is_test_path {
        return findings;
    }

    let toks = tokenize_rust(src);
    let n = toks.len();

    // Truncate before `#[cfg(test)]` module if present at brace depth 0
    let mut effective_len = n;
    let mut brace_depth = 0isize;
    for idx in 0..n {
        match &toks[idx].kind {
            RsTokKind::Symbol(s) if s == "{" => brace_depth += 1,
            RsTokKind::Symbol(s) if s == "}" => brace_depth = (brace_depth - 1).max(0),
            RsTokKind::Symbol(s) if s == "#[" && brace_depth == 0 => {
                if idx + 4 < n
                    && matches!(&toks[idx + 1].kind, RsTokKind::Ident(id) if id == "cfg")
                    && matches!(&toks[idx + 3].kind, RsTokKind::Ident(id) if id == "test")
                {
                    effective_len = idx;
                    break;
                }
            }
            _ => {}
        }
    }

    let prod_toks = &toks[..effective_len];
    let uses_obend_ffi = prod_toks.iter().any(|t| {
        matches!(
            &t.kind,
            RsTokKind::Ident(id)
                if id == "obend_ffi" || id == "ObendSession" || id.starts_with("obend_session_")
        )
    });

    // 1. Detect `struct Mock*` / `struct Dummy*` / `struct *SimBackend*` in non-test crate `src/`
    for (idx, tok) in prod_toks.iter().enumerate() {
        if matches!(&tok.kind, RsTokKind::Ident(kw) if kw == "struct" || kw == "enum") {
            if let Some(RsTok {
                kind: RsTokKind::Ident(type_name),
                line,
                col,
            }) = prod_toks.get(idx + 1)
            {
                let lower = type_name.to_ascii_lowercase();
                if lower.starts_with("mock")
                    || lower.starts_with("dummy")
                    || lower.ends_with("mock")
                    || lower.contains("simbackend")
                {
                    findings.push(Finding {
                        rule_id: "rust/mock-backend-in-src".to_string(),
                        severity: Severity::Error,
                        artifact_kind: ArtifactKind::P,
                        max_regime: Regime::Attested,
                        sink: Some(Sink::Theater),
                        path: rel_path.to_string(),
                        line: *line,
                        column: *col,
                        symbol: Some(type_name.clone()),
                        message: format!(
                            "Production crate module `{rel_path}` defines software mock/simulation type `{type_name}` on the load-bearing path"
                        ),
                        remediation: "Replace in-process Rust mock backend with IPC/FFI calls to the real Verilated RTL binary or `obend_ffi` session, or gate mocks strictly under `#[cfg(test)]`.".to_string(),
                    });
                }
            }
        }
    }

    // 2. Detect Rust semantic mirrors:
    //    (a) `*SpecEvaluation` struct or function claiming `.obend` spec evaluation via hardcoded Rust numbers without `obend_ffi`!
    //    (b) Functions whose comments/strings reference `.obend` files and perform hardcoded arithmetic/substring checks without `obend_ffi`!
    if !uses_obend_ffi {
        let mut references_obend_source = false;
        let mut first_obend_str_loc: Option<(String, usize, usize)> = None;
        for tok in prod_toks {
            if let RsTokKind::StrLit(s) = &tok.kind {
                if s.ends_with(".obend") || s.contains(".obend") || s.contains("edition ObjectiveBend") {
                    references_obend_source = true;
                    if first_obend_str_loc.is_none() {
                        first_obend_str_loc = Some((s.clone(), tok.line, tok.col));
                    }
                }
            }
        }

        // Check for `*SpecEvaluation` structs or functions computing hardcoded numeric mirrors of `.obend`
        for (idx, tok) in prod_toks.iter().enumerate() {
            if let RsTokKind::Ident(id) = &tok.kind {
                if id.ends_with("SpecEvaluation") && idx > 0 && matches!(&prod_toks[idx - 1].kind, RsTokKind::Ident(kw) if kw == "struct") {
                    findings.push(Finding {
                        rule_id: "rust/obend-semantic-mirror".to_string(),
                        severity: Severity::Error,
                        artifact_kind: ArtifactKind::P,
                        max_regime: Regime::Attested,
                        sink: Some(Sink::Mirror),
                        path: rel_path.to_string(),
                        line: tok.line,
                        column: tok.col,
                        symbol: Some(id.clone()),
                        message: format!(
                            "`{id}` in `{rel_path}` mirrors `.obend` specification evaluation in Rust with zero calls to `obend_ffi` (`PROCESS.md` sink `Mirror`)"
                        ),
                        remediation: "Evaluate `.obend` modules through `obend_ffi::session::ObendSession` or load Lean-emitted artifacts instead of re-computing `.obend` formulas in Rust.".to_string(),
                    });
                }
            }
        }

        // Also check functions like `step_one_cycle` that claim `.obend` core evaluation in comments while computing hardcoded `wrapping_mul`/`wrapping_add` constants
        for (idx, tok) in prod_toks.iter().enumerate() {
            if matches!(&tok.kind, RsTokKind::Ident(kw) if kw == "fn") {
                if let Some(RsTok {
                    kind: RsTokKind::Ident(fn_name),
                    line,
                    col,
                }) = prod_toks.get(idx + 1)
                {
                    // Scan function body until matching `}`
                    if let Some((body_start, body_end)) = find_fn_body_bounds(prod_toks, idx + 2) {
                        let fn_body = &prod_toks[body_start..body_end];
                        let body_mentions_obend_eval = fn_body.iter().any(|t| match &t.kind {
                            RsTokKind::DocOrLineComment(c) => {
                                let cl = c.to_ascii_lowercase();
                                cl.contains(".obend")
                                    && (cl.contains("evaluate") || cl.contains("semantics"))
                            }
                            _ => false,
                        });
                        let num_count = fn_body
                            .iter()
                            .filter(|t| matches!(&t.kind, RsTokKind::NumLit(_)))
                            .count();

                        if body_mentions_obend_eval && num_count >= 6 {
                            findings.push(Finding {
                                rule_id: "rust/obend-semantic-mirror".to_string(),
                                severity: Severity::Error,
                                artifact_kind: ArtifactKind::P,
                                max_regime: Regime::Attested,
                                sink: Some(Sink::Mirror),
                                path: rel_path.to_string(),
                                line: *line,
                                column: *col,
                                symbol: Some(fn_name.clone()),
                                message: format!(
                                    "Function `{fn_name}` claims to evaluate `.obend` semantics using {num_count} hardcoded numeric literals in Rust without calling `obend_ffi` or RTL"
                                ),
                                remediation: "Delegate `.obend` evaluation to `obend_ffi` or a compiled/Verilated artifact emitted by Lean (`Obend/Leaf/Emit.lean`).".to_string(),
                            });
                        }
                    }
                }
            }
        }

        let _ = (references_obend_source, first_obend_str_loc);
    }

    findings
}

fn find_fn_body_bounds(toks: &[RsTok], start: usize) -> Option<(usize, usize)> {
    let mut i = start;
    while i < toks.len() {
        if matches!(&toks[i].kind, RsTokKind::Symbol(s) if s == "{") {
            let body_start = i + 1;
            let mut depth = 1usize;
            i += 1;
            while i < toks.len() && depth > 0 {
                match &toks[i].kind {
                    RsTokKind::Symbol(s) if s == "{" => depth += 1,
                    RsTokKind::Symbol(s) if s == "}" => depth -= 1,
                    _ => {}
                }
                i += 1;
            }
            return Some((body_start, i.saturating_sub(1)));
        }
        if matches!(&toks[i].kind, RsTokKind::Symbol(s) if s == ";") {
            return None;
        }
        i += 1;
    }
    None
}

pub fn scan_rust_files(repo_root: &Path) -> (usize, Vec<Finding>) {
    let mut count = 0usize;
    let mut findings = Vec::new();
    let mut rs_paths = Vec::new();

    for entry in walkdir::WalkDir::new(repo_root)
        .into_iter()
        .filter_entry(|e| {
            let name = e.file_name().to_str().unwrap_or("");
            if e.depth() > 0 && e.file_type().is_dir() && name.starts_with('.') {
                return false;
            }
            !matches!(name, "target" | "astra")
        })
        .flatten()
    {
        if entry.file_type().is_file()
            && entry.path().extension().and_then(|e| e.to_str()) == Some("rs")
        {
            rs_paths.push(entry.path().to_path_buf());
        }
    }
    rs_paths.sort();

    for p in rs_paths {
        let Ok(rel) = p.strip_prefix(repo_root) else {
            continue;
        };
        let rel_str = rel.to_string_lossy().replace('\\', "/");
        if let Ok(src) = std::fs::read_to_string(&p) {
            count += 1;
            findings.extend(lint_rust_file(&rel_str, &src));
        }
    }

    (count, findings)
}
