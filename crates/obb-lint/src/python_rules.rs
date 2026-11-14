//! Lexical & structural analyzer for Python test suites (`tests/e2e/` self-mocking theater detector).

use obb_core::{ArtifactKind, Finding, Regime, Severity, Sink};
use std::collections::HashSet;
use std::path::Path;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PyTokKind {
    Ident(String),
    StrLit(String),
    Symbol(char),
    Newline,
}

#[derive(Debug, Clone)]
pub struct PyTok {
    pub kind: PyTokKind,
    pub line: usize,
    pub col: usize,
}

pub fn tokenize_python(src: &str) -> Vec<PyTok> {
    let chars: Vec<char> = src.chars().collect();
    let n = chars.len();
    let mut i = 0usize;
    let mut line = 1usize;
    let mut col = 1usize;
    let mut out = Vec::new();

    while i < n {
        let c = chars[i];
        if c == '\n' {
            out.push(PyTok {
                kind: PyTokKind::Newline,
                line,
                col,
            });
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
        // Comment `# ...`
        if c == '#' {
            while i < n && chars[i] != '\n' {
                i += 1;
                col += 1;
            }
            continue;
        }

        let sline = line;
        let scol = col;

        // String literal (including raw/f-string prefixes and triple quotes `"""` / `'''`)
        let quote_opt = if c == '"' || c == '\'' {
            Some((c, 0usize))
        } else if matches!(c, 'r' | 'f' | 'b' | 'u' | 'R' | 'F' | 'B')
            && i + 1 < n
            && (chars[i + 1] == '"' || chars[i + 1] == '\'')
        {
            Some((chars[i + 1], 1usize))
        } else {
            None
        };

        if let Some((q, prefix_len)) = quote_opt {
            i += prefix_len;
            col += prefix_len;
            let is_triple = i + 2 < n && chars[i + 1] == q && chars[i + 2] == q;
            let mut s = String::new();
            if is_triple {
                i += 3;
                col += 3;
                while i < n {
                    if i + 2 < n && chars[i] == q && chars[i + 1] == q && chars[i + 2] == q {
                        i += 3;
                        col += 3;
                        break;
                    }
                    if chars[i] == '\\' && i + 1 < n {
                        s.push(chars[i + 1]);
                        i += 2;
                        col += 2;
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
            } else {
                i += 1;
                col += 1;
                while i < n && chars[i] != q && chars[i] != '\n' {
                    if chars[i] == '\\' && i + 1 < n {
                        s.push(chars[i + 1]);
                        i += 2;
                        col += 2;
                        continue;
                    }
                    s.push(chars[i]);
                    i += 1;
                    col += 1;
                }
                if i < n && chars[i] == q {
                    i += 1;
                    col += 1;
                }
            }
            out.push(PyTok {
                kind: PyTokKind::StrLit(s),
                line: sline,
                col: scol,
            });
            continue;
        }

        if c.is_alphabetic() || c == '_' {
            let mut id = String::new();
            while i < n && (chars[i].is_alphanumeric() || chars[i] == '_') {
                id.push(chars[i]);
                i += 1;
                col += 1;
            }
            out.push(PyTok {
                kind: PyTokKind::Ident(id),
                line: sline,
                col: scol,
            });
            continue;
        }

        out.push(PyTok {
            kind: PyTokKind::Symbol(c),
            line: sline,
            col: scol,
        });
        i += 1;
        col += 1;
    }

    out
}

#[derive(Debug, Default)]
struct PyFileFacts {
    rel_path: String,
    has_real_subprocess_or_ffi_call: bool,
    references_obend_binary_or_lib: bool,
    mock_classes: Vec<(String, usize, usize)>,
    test_fn_count: usize,
    imported_local_modules: HashSet<String>,
}

fn analyze_py_file(rel_path: &str, src: &str) -> PyFileFacts {
    let toks = tokenize_python(src);
    let mut facts = PyFileFacts {
        rel_path: rel_path.to_string(),
        ..Default::default()
    };

    let n = toks.len();
    let mut i = 0usize;
    while i < n {
        match &toks[i].kind {
            PyTokKind::Ident(kw) if kw == "class" => {
                if let Some(PyTok {
                    kind: PyTokKind::Ident(cname),
                    line,
                    col,
                }) = toks.get(i + 1)
                {
                    let lower = cname.to_ascii_lowercase();
                    if lower.contains("mock") || lower.contains("stub") || lower.contains("fake") {
                        facts.mock_classes.push((cname.clone(), *line, *col));
                    }
                }
            }
            PyTokKind::Ident(kw) if kw == "def" => {
                if let Some(PyTok {
                    kind: PyTokKind::Ident(fname),
                    ..
                }) = toks.get(i + 1)
                    && (fname.starts_with("test_") || fname.starts_with("run_all_"))
                {
                    facts.test_fn_count += 1;
                }
            }
            PyTokKind::Ident(kw) if kw == "from" => {
                if let Some(PyTok {
                    kind: PyTokKind::Ident(mod_name),
                    ..
                }) = toks.get(i + 1)
                {
                    facts.imported_local_modules.insert(mod_name.clone());
                }
            }
            PyTokKind::Ident(id) if id == "subprocess" => {
                // Must be an actual call `subprocess.run(...)`, `subprocess.Popen(...)`, `subprocess.check_output(...)`, etc., NOT `import subprocess`!
                if i + 3 < n
                    && matches!(&toks[i + 1].kind, PyTokKind::Symbol('.'))
                    && matches!(
                        &toks[i + 2].kind,
                        PyTokKind::Ident(m)
                            if matches!(
                                m.as_str(),
                                "run" | "Popen" | "check_output" | "check_call" | "call"
                            )
                    )
                    && matches!(&toks[i + 3].kind, PyTokKind::Symbol('('))
                {
                    facts.has_real_subprocess_or_ffi_call = true;
                }
            }
            PyTokKind::Ident(id) if id == "ctypes" || id == "cffi" => {
                if i + 2 < n && matches!(&toks[i + 1].kind, PyTokKind::Symbol('.')) {
                    facts.has_real_subprocess_or_ffi_call = true;
                }
            }
            PyTokKind::StrLit(s) => {
                let lower = s.to_ascii_lowercase();
                if lower.contains("libobend")
                    || lower.contains("obend_ffi")
                    || lower.ends_with("/obend")
                    || lower == "obend"
                    || lower.contains("lake exe obend")
                {
                    facts.references_obend_binary_or_lib = true;
                }
            }
            _ => {}
        }
        i += 1;
    }

    facts
}

pub fn scan_python_files(repo_root: &Path) -> (usize, Vec<Finding>) {
    let mut count = 0usize;
    let mut findings = Vec::new();
    let mut py_paths = Vec::new();

    for entry in walkdir::WalkDir::new(repo_root)
        .into_iter()
        .filter_entry(|e| {
            let name = e.file_name().to_str().unwrap_or("");
            if e.depth() > 0 && e.file_type().is_dir() && name.starts_with('.') {
                return false;
            }
            !matches!(name, "target" | "__pycache__" | "astra")
        })
        .flatten()
    {
        if entry.file_type().is_file()
            && entry.path().extension().and_then(|e| e.to_str()) == Some("py")
        {
            py_paths.push(entry.path().to_path_buf());
        }
    }
    py_paths.sort();

    let mut e2e_facts: Vec<PyFileFacts> = Vec::new();

    for p in py_paths {
        let Ok(rel) = p.strip_prefix(repo_root) else {
            continue;
        };
        let rel_str = rel.to_string_lossy().replace('\\', "/");
        if p.file_name().and_then(|s| s.to_str()) == Some("__init__.py") {
            continue;
        }
        let Ok(src) = std::fs::read_to_string(&p) else {
            continue;
        };
        count += 1;

        if rel_str.starts_with("tests/e2e/") || rel_str.contains("/tests/e2e/") {
            e2e_facts.push(analyze_py_file(&rel_str, &src));
        }
    }

    // Check if ANY file in `tests/e2e/` actually invokes `subprocess.*` or `ctypes`/`cffi`
    let suite_has_any_real_bridge = e2e_facts
        .iter()
        .any(|f| f.has_real_subprocess_or_ffi_call && f.references_obend_binary_or_lib);

    for f in &e2e_facts {
        // Flag mock bridge classes inside `tests/e2e/`
        for (cname, line, col) in &f.mock_classes {
            findings.push(Finding {
                rule_id: "python/e2e-mock-bridge".to_string(),
                severity: Severity::Error,
                artifact_kind: ArtifactKind::P,
                max_regime: Regime::Attested,
                sink: Some(Sink::Theater),
                path: f.rel_path.clone(),
                line: *line,
                column: *col,
                symbol: Some(cname.clone()),
                message: format!(
                    "E2E harness `{}` defines mock class `{cname}` instead of calling the compiled `obend` binary or `libobend` FFI",
                    f.rel_path
                ),
                remediation: "Delete the Python mock class and invoke `obend` via `subprocess.run` or bind `libobend` via `ctypes`/`cffi`.".to_string(),
            });
        }

        // Flag E2E test modules that neither call `obend`/`libobend` themselves nor import a helper that does
        if !f.has_real_subprocess_or_ffi_call && !suite_has_any_real_bridge {
            findings.push(Finding {
                rule_id: "python/e2e-self-mock".to_string(),
                severity: Severity::Error,
                artifact_kind: ArtifactKind::P,
                max_regime: Regime::Attested,
                sink: Some(Sink::Theater),
                path: f.rel_path.clone(),
                line: 1,
                column: 1,
                symbol: None,
                message: format!(
                    "E2E module `{}` ({} test functions) contains zero subprocess or FFI calls to `obend` or `libobend` (pure Python self-mocking theater)",
                    f.rel_path, f.test_fn_count
                ),
                remediation: "Execute the real `obend` CLI or `libobend` C-ABI from E2E tests, or delete pure-Python reimplementations of Lean semantics.".to_string(),
            });
        }
    }

    (count, findings)
}
