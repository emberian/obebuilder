//! Line-aware test-placement scan. Literal tokens are opaque barriers, never source code.
use anyhow::{Context, Result};
use obb_core::{ArtifactKind, Finding, Regime, Severity};
use std::path::Path;

#[derive(Clone, Copy, PartialEq)]
enum Language {
    Rust,
    JavaScript,
    Python,
}

struct Token {
    text: String,
    line: usize,
    column: usize,
}

// Treat a template and its nested interpolation strings as one opaque literal.
fn js_template_end(chars: &[char], start: usize) -> usize {
    // Each entry is a template's interpolation brace depth; zero means literal text.
    // Source-controlled nesting must not consume the process call stack.
    let mut templates = vec![0usize];
    let mut i = start + 1;
    while i < chars.len() {
        let top = templates.len() - 1;
        if templates[top] == 0 {
            match chars[i] {
                '\\' => i = (i + 2).min(chars.len()),
                '`' => {
                    templates.pop();
                    i += 1;
                    if templates.is_empty() {
                        return i;
                    }
                }
                '$' if chars.get(i + 1) == Some(&'{') => {
                    templates[top] = 1;
                    i += 2;
                }
                _ => i += 1,
            }
            continue;
        }
        match chars[i] {
            '`' => templates.push(0),
            '\'' | '"' => {
                let quote = chars[i];
                i += 1;
                while i < chars.len() && chars[i] != quote {
                    i += if chars[i] == '\\' { 2 } else { 1 };
                }
            }
            '/' if chars.get(i + 1) == Some(&'/') => {
                while i < chars.len() && chars[i] != '\n' {
                    i += 1;
                }
                continue;
            }
            '/' if chars.get(i + 1) == Some(&'*') => {
                i += 2;
                while i + 1 < chars.len() && !chars[i..].starts_with(&['*', '/']) {
                    i += 1;
                }
                i = (i + 2).min(chars.len());
                continue;
            }
            '{' => templates[top] += 1,
            '}' => templates[top] -= 1,
            _ => {}
        }
        i = (i + 1).min(chars.len());
    }
    i
}

fn tokens(source: &str, language: Language) -> Vec<Token> {
    let c: Vec<char> = source.chars().collect();
    let mut out: Vec<Token> = Vec::new();
    let (mut i, mut line, mut column) = (0, 1, 1);
    while i < c.len() {
        let start = i;
        let (start_line, start_column) = (line, column);
        let mut literal = false;
        let mut comment = false;
        if (language == Language::Python && c[i] == '#')
            || (language != Language::Python && c[i..].starts_with(&['/', '/']))
        {
            comment = true;
            while i < c.len() && c[i] != '\n' {
                i += 1;
            }
        } else if language != Language::Python && c[i..].starts_with(&['/', '*']) {
            comment = true;
            i += 2;
            let mut depth = 1;
            while i < c.len() && depth > 0 {
                if language == Language::Rust && c[i..].starts_with(&['/', '*']) {
                    depth += 1;
                    i += 2;
                } else if c[i..].starts_with(&['*', '/']) {
                    depth -= 1;
                    i += 2;
                } else {
                    i += 1;
                }
            }
        } else if language == Language::Rust
            && (c[i] == 'r' || (matches!(c[i], 'b' | 'c') && c.get(i + 1) == Some(&'r')))
        {
            let mut j = i + if c[i] == 'r' { 1 } else { 2 };
            while c.get(j) == Some(&'#') {
                j += 1;
            }
            if c.get(j) == Some(&'"') {
                let hashes = j - i - if c[i] == 'r' { 1 } else { 2 };
                literal = true;
                i = j + 1;
                while i < c.len() {
                    if c[i] == '"' && (1..=hashes).all(|h| c.get(i + h) == Some(&'#')) {
                        i += hashes + 1;
                        break;
                    }
                    i += 1;
                }
            }
        }
        if i == start && language == Language::JavaScript && c[i] == '`' {
            literal = true;
            i = js_template_end(&c, i);
        }
        if i == start
            && (c[i] == '"'
                || (language != Language::Rust && c[i] == '\'')
                || (language == Language::JavaScript && c[i] == '`'))
        {
            literal = true;
            let quote = c[i];
            let width =
                if language == Language::Python && c[i..].starts_with(&[quote, quote, quote]) {
                    3
                } else {
                    1
                };
            i += width;
            while i < c.len() {
                if c[i] == '\\' {
                    i = (i + 2).min(c.len());
                } else if (0..width).all(|k| c.get(i + k) == Some(&quote)) {
                    i += width;
                    break;
                } else {
                    i += 1;
                }
            }
        }
        // Rust character literals, but not lifetime parameters such as `'a` or `'static`.
        if i == start && language == Language::Rust && c[i] == '\'' {
            let mut j = i + 1;
            if c.get(j) == Some(&'\\') {
                // `'\''`, `'\n'`, `'\x41'`, `'\u{10FFFF}'`: skip the escaped char, then scan the
                // short escape body to its closing quote.
                j += 2;
                let limit = (j + 10).min(c.len());
                while j < limit && c[j] != '\'' && c[j] != '\n' {
                    j += 1;
                }
            } else {
                j += 1;
            }
            if c.get(j) == Some(&'\'') {
                literal = true;
                i = j + 1;
            }
        }
        // JavaScript regex literals can contain test-shaped text too.
        if i == start
            && language == Language::JavaScript
            && c[i] == '/'
            && out.last().is_none_or(|t| {
                matches!(
                    t.text.as_str(),
                    "=" | "(" | "[" | "," | ":" | "return" | "=>" | "!" | ";" | "{"
                )
            })
        {
            literal = true;
            i += 1;
            let mut class = false;
            while i < c.len() {
                match c[i] {
                    '\\' => {
                        i = (i + 2).min(c.len());
                        continue;
                    }
                    '[' => class = true,
                    ']' => class = false,
                    '/' if !class => {
                        i += 1;
                        break;
                    }
                    '\n' => break,
                    _ => {}
                }
                i += 1;
            }
        }
        if i == start {
            i += 1;
            if c[start].is_alphabetic() || matches!(c[start], '_' | '$') {
                while i < c.len() && (c[i].is_alphanumeric() || matches!(c[i], '_' | '$')) {
                    i += 1;
                }
            }
        }
        if !comment && !c[start].is_whitespace() {
            out.push(Token {
                text: if literal {
                    "<literal>".into()
                } else {
                    c[start..i].iter().collect()
                },
                line: start_line,
                column: start_column,
            });
        }
        for ch in &c[start..i] {
            if *ch == '\n' {
                line += 1;
                column = 1;
            } else {
                column += 1;
            }
        }
    }
    out
}

/// `#[test]`, `#[<runtime>::test(..)]`, `#[cfg(test)]` and the inner `#![cfg(test)]` form.
/// `#[cfg(not(test))]` gates library code and is not a test declaration.
fn rust_test_attribute(ts: &[Token], i: usize) -> bool {
    let text = |k: usize| ts.get(k).map(|t| t.text.as_str()).unwrap_or("");
    if text(i) != "#" {
        return false;
    }
    let open = if text(i + 1) == "!" { i + 2 } else { i + 1 };
    if text(open) != "[" {
        return false;
    }
    let attr: Vec<&str> = ts[open + 1..]
        .iter()
        .take_while(|t| t.text != "]")
        .map(|t| t.text.as_str())
        .collect();
    let path_len = attr
        .iter()
        .position(|t| matches!(*t, "(" | "="))
        .unwrap_or(attr.len());
    let path = &attr[..path_len];
    if path.last() == Some(&"test") {
        return true;
    }
    path.len() == 1
        && path[0] == "cfg"
        && attr.iter().enumerate().any(|(k, t)| {
            *t == "test"
                && !(k >= 2
                    && attr[k - 1] == "("
                    && attr[k - 2] == "not"
                    && attr.get(k + 1) == Some(&")"))
        })
}

/// `describe('..', ..)`, `it("..", ..)`, `test(`..`, ..)` and their `.only` / `.skip` /
/// `.concurrent` / `.todo` forms. The name must be a literal: `test(value)` is an ordinary call
/// (or a method definition) in library code, not a test declaration.
fn javascript_test_call(ts: &[Token], i: usize) -> bool {
    let text = |k: usize| ts.get(k).map(|t| t.text.as_str()).unwrap_or("");
    if !matches!(text(i), "describe" | "it" | "test")
        || (i > 0 && matches!(ts[i - 1].text.as_str(), "." | "function"))
    {
        return false;
    }
    let open =
        if text(i + 1) == "." && matches!(text(i + 2), "only" | "skip" | "concurrent" | "todo") {
            i + 3
        } else {
            i + 1
        };
    text(open) == "(" && text(open + 1) == "<literal>"
}

fn test_path(path: &str) -> bool {
    let parts: Vec<_> = path.split('/').collect();
    let file = parts.last().copied().unwrap_or("");
    parts.iter().any(|p| {
        matches!(
            *p,
            "test" | "tests" | "__tests__" | "fixtures" | "benches" | "examples"
        )
    }) || file.starts_with("test_")
        || file.ends_with("_test.py")
        || [".test.", ".spec."]
            .iter()
            .any(|suffix| file.contains(suffix))
}

pub fn scan_test_in_library(root: &Path) -> Result<Vec<Finding>> {
    let mut findings = Vec::new();
    for entry in walkdir::WalkDir::new(root).into_iter().filter_entry(|e| {
        e.depth() == 0
            || !e.file_type().is_dir()
            || (!e.file_name().to_string_lossy().starts_with('.')
                && !matches!(
                    e.file_name().to_str(),
                    Some("target" | "node_modules" | "vendor" | "__pycache__")
                ))
    }) {
        let entry = entry?;
        if !entry.file_type().is_file() {
            continue;
        }
        let path = entry.path();
        let rel = path
            .strip_prefix(root)?
            .to_string_lossy()
            .replace('\\', "/");
        if test_path(&rel) {
            continue;
        }
        let language = match path.extension().and_then(|s| s.to_str()) {
            Some("rs") if rel.split('/').any(|p| p == "src") => Language::Rust,
            Some("js" | "jsx" | "ts" | "tsx" | "mjs" | "cjs" | "mts" | "cts") => {
                Language::JavaScript
            }
            Some("py") => Language::Python,
            _ => continue,
        };
        let source =
            std::fs::read_to_string(path).with_context(|| format!("read {}", path.display()))?;
        let ts = tokens(&source, language);
        for (i, token) in ts.iter().enumerate() {
            let at = |k: usize| ts.get(i + k).map(|t| t.text.as_str()).unwrap_or("");
            let matches = match language {
                Language::Rust => rust_test_attribute(&ts, i),
                Language::JavaScript => javascript_test_call(&ts, i),
                Language::Python => {
                    (at(0) == "def" && at(1).starts_with("test_"))
                        || [at(0), at(1), at(2)] == ["unittest", ".", "TestCase"]
                }
            };
            if matches {
                let lang = match language {
                    Language::Rust => "rust",
                    Language::JavaScript => "javascript",
                    Language::Python => "python",
                };
                findings.push(Finding {
                    rule_id: format!("{lang}/test-in-library"),
                    severity: Severity::Error,
                    artifact_kind: ArtifactKind::P,
                    max_regime: Regime::Attested,
                    sink: None,
                    path: rel.clone(),
                    line: token.line,
                    column: token.column,
                    symbol: Some(token.text.clone()),
                    message: "Executable test declaration in a library source file".into(),
                    remediation: "Move the test to a dedicated test file or tests directory."
                        .into(),
                });
            }
        }
    }
    Ok(findings)
}
