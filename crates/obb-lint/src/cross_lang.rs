//! Cross-language (`Rust ↔ Lean`) wire domain-tag & static framing-arity drift detector
//! (`cross-lang/domain-tag-drift`).
//!
//! Catches two classes of silent cryptographic/protocol boundary divergence in `< 30ms`:
//! 1. **Shared wire tags with mismatched static framing arity** (e.g., Rust hashing
//!    `"OBEND.CUSTODY.AUTHORITY/v1"` over `&[3 fields]` while Lean hashes the same tag over
//!    `[5 fields]`).
//! 2. **Orphaned versioned Rust wire tags** in `crates/obend-{crypto-exec,sandbox,sel4-verifier}/`
//!    that claim a protocol version (`/v1`, `_V1`, `.V1`, `-v1`, `:v1`) with zero matching domain
//!    tag in `lean/Obend/**/*.lean`.

use crate::lean_lexer::{LeanToken, LeanTokenKind, tokenize_lean};
use crate::rust_rules::{RsTok, RsTokKind, tokenize_rust};
use obb_core::{ArtifactKind, Finding, Regime, Severity, Sink};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};

#[derive(Debug, Clone)]
pub struct WireTagSite {
    pub tag: String,
    pub rel_path: String,
    pub line: usize,
    pub col: usize,
    pub static_arity: Option<usize>,
}

/// Returns `true` when `s` is a canonical `"OBEND."` or `"OBEND_"` cryptographic/protocol domain tag
/// (printable non-whitespace ASCII, length `7..=128`).
pub fn is_obend_wire_tag(s: &str) -> bool {
    if s.len() < 7 || s.len() > 128 {
        return false;
    }
    if !(s.starts_with("OBEND.") || s.starts_with("OBEND_")) {
        return false;
    }
    s.bytes().all(|b| (0x21..=0x7E).contains(&b))
}

/// Returns `true` when `s` is a valid dynamic prefix like `"OBEND.CUSTODY."` or `"OBEND_"` used in `++`.
fn is_obend_wire_prefix(s: &str) -> bool {
    (s.starts_with("OBEND.") || s.starts_with("OBEND_"))
        && s.len() >= 6
        && s.len() <= 128
        && s.bytes().all(|b| (0x21..=0x7E).contains(&b))
}

/// Returns `true` when a wire tag claims an explicit protocol version suffix/segment
/// (`/v1`, `/v01`, `_V1`, `.V1`, `-v1`, `:v1`, `@v1`, etc.).
pub fn claims_protocol_version(tag: &str) -> bool {
    let bytes = tag.as_bytes();
    let mut i = 0usize;
    while i + 2 < bytes.len() {
        let sep = bytes[i];
        let v = bytes[i + 1];
        if matches!(sep, b'/' | b'_' | b'.' | b'-' | b':' | b'@')
            && matches!(v, b'v' | b'V')
            && bytes[i + 2].is_ascii_digit()
        {
            let mut j = i + 2;
            while j < bytes.len() && bytes[j].is_ascii_digit() {
                j += 1;
            }
            if j == bytes.len() || matches!(bytes[j], b'/' | b'_' | b'.' | b'-' | b':' | b'@') {
                return true;
            }
        }
        i += 1;
    }
    false
}

/// Segment-level test/bench/mock tag check so legitimate tags like `"OBEND.TESTAMENT/v1"` or
/// `"OBEND_TESTNET/v1"` are NOT skipped.
fn is_test_or_bench_tag(tag: &str) -> bool {
    tag.split(['.', '_', '/', '-', ':']).any(|seg| {
        matches!(
            seg.to_ascii_uppercase().as_str(),
            "TEST" | "TESTS" | "BENCH" | "BENCHES" | "MOCK" | "DUMMY" | "EXAMPLE"
        )
    })
}

fn is_load_bearing_wire_crate(rel_path: &str) -> bool {
    rel_path.starts_with("crates/obend-crypto-exec/")
        || rel_path.starts_with("crates/obend-sandbox/")
        || rel_path.starts_with("crates/obend-sel4-verifier/")
}

fn rust_crate_key(rel_path: &str) -> String {
    let mut comps = rel_path.split('/');
    match (comps.next(), comps.next()) {
        (Some("crates"), Some(krate)) => format!("crates/{krate}"),
        (Some(first), _) => first.to_string(),
        _ => String::new(),
    }
}

fn is_excluded_rust_path(rel_path: &str) -> bool {
    rel_path.contains("/tests/")
        || rel_path.contains("/benches/")
        || rel_path.contains("/examples/")
        || rel_path.ends_with("_test.rs")
        || rel_path.ends_with("/tests.rs")
}

fn is_excluded_lean_path(rel_path: &str) -> bool {
    rel_path.contains("/Teeth/")
        || rel_path.starts_with("Obend/Teeth/")
        || rel_path.starts_with("lean/Obend/Teeth/")
        || rel_path.contains("/tests/")
        || rel_path.starts_with("tests/")
        || rel_path.starts_with("lean/tests/")
        || rel_path.ends_with("Test.lean")
        || rel_path.ends_with("Tests.lean")
}

/// Run the cross-language wire-tag & framing-arity scanner across `crates/` and `lean/Obend/`.
pub fn scan_cross_lang_domain_tags(repo_root: &Path, strict_wire: bool) -> Vec<Finding> {
    let crates_dir = repo_root.join("crates");
    let lean_obend_dir = repo_root.join("lean/Obend");
    if !crates_dir.is_dir() || !lean_obend_dir.is_dir() {
        return Vec::new();
    }

    let (lean_sites, lean_dynamic_prefixes) = collect_lean_wire_sites(repo_root, &lean_obend_dir);
    let rust_sites = collect_rust_wire_sites(repo_root, &crates_dir);

    let mut lean_by_tag: BTreeMap<String, Vec<WireTagSite>> = BTreeMap::new();
    for s in lean_sites {
        lean_by_tag.entry(s.tag.clone()).or_default().push(s);
    }

    let mut rust_by_tag: BTreeMap<String, Vec<WireTagSite>> = BTreeMap::new();
    for s in rust_sites {
        rust_by_tag.entry(s.tag.clone()).or_default().push(s);
    }

    let severity = if strict_wire {
        Severity::Error
    } else {
        Severity::Warning
    };
    let mut findings = Vec::new();

    for (tag, rs_list) in &rust_by_tag {
        if is_test_or_bench_tag(tag) {
            continue;
        }

        if let Some(ln_list) = lean_by_tag.get(tag) {
            // 1. Shared exact tag: compare statically visible framing arities per divergent site
            let rs_arities: BTreeSet<usize> =
                rs_list.iter().filter_map(|s| s.static_arity).collect();
            let ln_arities: BTreeSet<usize> =
                ln_list.iter().filter_map(|s| s.static_arity).collect();

            if !rs_arities.is_empty() && !ln_arities.is_empty() && rs_arities != ln_arities {
                let rs_site = rs_list
                    .iter()
                    .find(|s| s.static_arity.is_some_and(|a| !ln_arities.contains(&a)))
                    .or_else(|| rs_list.iter().find(|s| s.static_arity.is_some()))
                    .unwrap_or(&rs_list[0]);
                let ln_site = ln_list
                    .iter()
                    .find(|s| s.static_arity.is_some_and(|a| !rs_arities.contains(&a)))
                    .or_else(|| ln_list.iter().find(|s| s.static_arity.is_some()))
                    .unwrap_or(&ln_list[0]);
                let rs_fmt = format_arity_set(&rs_arities);
                let ln_fmt = format_arity_set(&ln_arities);

                findings.push(Finding {
                    rule_id: "cross-lang/domain-tag-drift".to_string(),
                    severity,
                    artifact_kind: ArtifactKind::P,
                    max_regime: Regime::Attested,
                    sink: Some(Sink::Mirror),
                    path: rs_site.rel_path.clone(),
                    line: rs_site.line,
                    column: rs_site.col,
                    symbol: Some(tag.clone()),
                    message: format!(
                        "Shared wire domain tag `\"{tag}\"` has mismatched static framing arity: Rust `{}:{}` frames {rs_fmt} field(s), whereas Lean `{}:{}` frames {ln_fmt} field(s)",
                        rs_site.rel_path, rs_site.line, ln_site.rel_path, ln_site.line
                    ),
                    remediation: format!(
                        "Align the length-framed preimage field count and ordering for `\"{tag}\"` across `{}` and `{}` (every committed field must match byte-for-byte across Rust and Lean).",
                        rs_site.rel_path, ln_site.rel_path
                    ),
                });
            }
        } else if claims_protocol_version(tag) {
            // Suppress orphan false positive if Lean constructs this namespace dynamically via `"OBEND.PREFIX." ++ ...`
            if lean_dynamic_prefixes
                .iter()
                .any(|pfx| tag.starts_with(pfx.as_str()))
            {
                continue;
            }
            // 2. Orphaned versioned Rust wire tag in load-bearing crypto/sandbox/sel4 crates
            if let Some(rs_site) = rs_list
                .iter()
                .find(|s| is_load_bearing_wire_crate(&s.rel_path))
            {
                findings.push(Finding {
                    rule_id: "cross-lang/domain-tag-drift".to_string(),
                    severity,
                    artifact_kind: ArtifactKind::P,
                    max_regime: Regime::Attested,
                    sink: Some(Sink::Mirror),
                    path: rs_site.rel_path.clone(),
                    line: rs_site.line,
                    column: rs_site.col,
                    symbol: Some(tag.clone()),
                    message: format!(
                        "Versioned Rust wire domain tag `\"{tag}\"` in `{}:{}` has zero matching domain tag anywhere in `lean/Obend/` (cross-language domain-tag drift)",
                        rs_site.rel_path, rs_site.line
                    ),
                    remediation: format!(
                        "Use the exact canonical domain-separation tag defined in `lean/Obend/` (and verify identical field framing), or formalize `\"{tag}\"` in the corresponding `lean/Obend/` specification."
                    ),
                });
            }
        }
    }

    findings
}

fn format_arity_set(set: &BTreeSet<usize>) -> String {
    let parts: Vec<String> = set.iter().map(usize::to_string).collect();
    if parts.len() == 1 {
        parts[0].clone()
    } else {
        format!("{{{}}}", parts.join(", "))
    }
}

fn collect_sorted_files(dir: &Path, ext: &str) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    for entry in walkdir::WalkDir::new(dir)
        .into_iter()
        .filter_entry(|e| {
            let name = e.file_name().to_str().unwrap_or("");
            if e.depth() > 0 && e.file_type().is_dir() && name.starts_with('.') {
                return false;
            }
            if e.depth() <= 2 && e.file_type().is_dir() && matches!(name, "target" | "astra") {
                return false;
            }
            true
        })
        .flatten()
    {
        if entry.file_type().is_file()
            && entry.path().extension().and_then(|e| e.to_str()) == Some(ext)
        {
            paths.push(entry.path().to_path_buf());
        }
    }
    paths.sort();
    paths
}

fn may_contain_obend_tag_or_alias_use_lean(src: &str, has_global_aliases: bool) -> bool {
    has_global_aliases || may_contain_obend_tag_def_only(src)
}

fn may_contain_obend_tag_def_only(src: &str) -> bool {
    src.contains("BEND")
        || src.contains("0x4f")
        || src.contains("0x4F")
        || src.contains("\\x4")
        || src.contains("\\x5")
        || src.contains("\\u{4")
        || src.contains("\\u004")
        || src.contains("b'O'")
        || src.contains("b'\\x4")
        || (src.contains("79") && src.contains("66") && src.contains("69"))
}

fn parse_u8_nat_lit(raw: &str) -> Option<u8> {
    let cleaned: String = raw
        .trim_end_matches("u8")
        .trim_end_matches("_u8")
        .chars()
        .filter(|&c| c != '_')
        .collect();
    if let Some(hex) = cleaned
        .strip_prefix("0x")
        .or_else(|| cleaned.strip_prefix("0X"))
    {
        u8::from_str_radix(hex, 16).ok()
    } else {
        cleaned.parse::<u8>().ok()
    }
}

/// Fold adjacent Lean string literal concatenations `"OBEND." ++ "FOO/v1"` into a single `StrLit`.
fn fold_lean_string_concats(raw_tokens: Vec<LeanToken>) -> Vec<LeanToken> {
    let mut out: Vec<LeanToken> = Vec::with_capacity(raw_tokens.len());
    let mut i = 0usize;
    while i < raw_tokens.len() {
        if let LeanTokenKind::StrLit(s1) = &raw_tokens[i].kind {
            let mut combined = s1.clone();
            let mut j = i + 1;
            while j + 1 < raw_tokens.len()
                && matches!(&raw_tokens[j].kind, LeanTokenKind::Symbol(op) if op == "++")
                && let LeanTokenKind::StrLit(s2) = &raw_tokens[j + 1].kind
            {
                combined.push_str(s2);
                j += 2;
            }
            let mut tok = raw_tokens[i].clone();
            tok.kind = LeanTokenKind::StrLit(combined);
            out.push(tok);
            i = j;
            continue;
        }
        out.push(raw_tokens[i].clone());
        i += 1;
    }
    out
}

/// Try decoding a contiguous `[0x4f, 0x42, ...]` or `#[0x4f, 0x42, ...]` ASCII byte-list literal
/// starting at `tokens[open_idx]`. Returns `(decoded_tag, close_idx_inclusive)` when it forms a
/// valid `OBEND.` / `OBEND_` wire tag.
fn decode_lean_ascii_byte_list(tokens: &[LeanToken], open_idx: usize) -> Option<(String, usize)> {
    let open_ok = matches!(
        &tokens.get(open_idx)?.kind,
        LeanTokenKind::Symbol(s) if s == "[" || s == "#["
    );
    if !open_ok {
        return None;
    }
    let mut bytes = Vec::new();
    let mut i = open_idx + 1;
    while i < tokens.len() {
        if matches!(&tokens[i].kind, LeanTokenKind::Symbol(s) if s == "]") {
            let s = String::from_utf8(bytes).ok()?;
            if is_obend_wire_tag(&s) {
                return Some((s, i));
            }
            return None;
        }
        let b = if let LeanTokenKind::NatLit(n) = &tokens[i].kind {
            i += 1;
            parse_u8_nat_lit(n)?
        } else if matches!(&tokens[i].kind, LeanTokenKind::Symbol(s) if s == "(") {
            let LeanTokenKind::NatLit(n) = &tokens.get(i + 1)?.kind else {
                return None;
            };
            let val = parse_u8_nat_lit(n)?;
            let mut depth = 1usize;
            i += 2;
            while i < tokens.len() && depth > 0 {
                match &tokens[i].kind {
                    LeanTokenKind::Symbol(s) if s == "(" => depth += 1,
                    LeanTokenKind::Symbol(s) if s == ")" => depth -= 1,
                    _ => {}
                }
                i += 1;
            }
            val
        } else {
            return None;
        };
        if !(0x21..=0x7E).contains(&b) {
            return None;
        }
        bytes.push(b);
        if i < tokens.len() {
            if matches!(&tokens[i].kind, LeanTokenKind::Symbol(s) if s == ",") {
                i += 1;
            } else if !matches!(&tokens[i].kind, LeanTokenKind::Symbol(s) if s == "]") {
                return None;
            }
        }
    }
    None
}

fn skip_lean_tag_postfix(tokens: &[LeanToken], mut idx: usize, was_parenthesized: bool) -> usize {
    while idx < tokens.len() {
        match &tokens[idx].kind {
            LeanTokenKind::Symbol(s)
                if matches!(
                    s.as_str(),
                    ".toUTF8" | ".data" | ".toList" | ".bytes" | ".toByteArray"
                ) =>
            {
                idx += 1;
            }
            _ => break,
        }
    }
    if was_parenthesized
        && idx < tokens.len()
        && matches!(&tokens[idx].kind, LeanTokenKind::Symbol(s) if s == ")")
    {
        idx += 1;
        while idx < tokens.len() {
            match &tokens[idx].kind {
                LeanTokenKind::Symbol(s)
                    if matches!(
                        s.as_str(),
                        ".toUTF8" | ".data" | ".toList" | ".bytes" | ".toByteArray"
                    ) =>
                {
                    idx += 1;
                }
                _ => break,
            }
        }
    }
    idx
}

/// Count static list/array elements `[e1, e2, ...]` or `#[e1, e2, ...]` at `tokens[list_idx]` in Lean.
/// Returns `None` if the list is dynamically extended (`[a, b] ++ rest` or `[a, b].append ...`).
fn count_lean_list_arity(tokens: &[LeanToken], list_idx: usize) -> Option<usize> {
    let is_open = matches!(
        &tokens.get(list_idx)?.kind,
        LeanTokenKind::Symbol(s) if s == "[" || s == "#["
    );
    if !is_open {
        return None;
    }
    if decode_lean_ascii_byte_list(tokens, list_idx).is_some() {
        return None;
    }

    let mut depth = 1usize;
    let mut i = list_idx + 1;
    let mut commas = 0usize;
    let mut tokens_in_current_elem = 0usize;
    let mut any_elem = false;

    while i < tokens.len() && depth > 0 {
        match &tokens[i].kind {
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "[" | "#[" | "(" | "{" | "⟨") => {
                if depth == 1 {
                    tokens_in_current_elem += 1;
                    any_elem = true;
                }
                depth += 1;
            }
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "]" | ")" | "}" | "⟩") => {
                depth -= 1;
                if depth == 0 {
                    // Reject dynamic list concatenation or length-altering transforms (`[a, b] ++ rest`, `[a, b].drop 1`, etc.)
                    if let Some(after) = tokens.get(i + 1) {
                        match &after.kind {
                            LeanTokenKind::Symbol(op)
                                if matches!(op.as_str(), "++" | "::" | "|>")
                                    || (op.starts_with('.')
                                        && !matches!(op.as_str(), ".map" | ".toArray")) =>
                            {
                                return None;
                            }
                            _ => {}
                        }
                    }
                    if !any_elem {
                        return Some(0);
                    }
                    let total = if tokens_in_current_elem == 0 {
                        commas
                    } else {
                        commas + 1
                    };
                    return Some(total);
                }
                if depth == 1 {
                    tokens_in_current_elem += 1;
                }
            }
            LeanTokenKind::Symbol(s) if s == "," && depth == 1 => {
                commas += 1;
                tokens_in_current_elem = 0;
            }
            _ => {
                if depth == 1 {
                    tokens_in_current_elem += 1;
                    any_elem = true;
                }
            }
        }
        i += 1;
    }
    None
}

type TagAliasMap = HashMap<String, Option<String>>;

fn scan_lean_tag_defs_in_tokens(tokens: &[LeanToken]) -> TagAliasMap {
    let mut tag_defs: TagAliasMap = HashMap::new();
    let mut record = |k: String, val: String| match tag_defs.get(&k) {
        None => {
            tag_defs.insert(k, Some(val));
        }
        Some(Some(prev)) if prev != &val => {
            tag_defs.insert(k, None);
        }
        _ => {}
    };
    let mut i = 0usize;
    while i < tokens.len() {
        if matches!(&tokens[i].kind, LeanTokenKind::Ident(kw) if kw == "def" || kw == "abbrev")
            && let Some(LeanToken {
                kind: LeanTokenKind::Ident(def_name),
                ..
            }) = tokens.get(i + 1)
        {
            let short = def_name.rsplit('.').next().unwrap_or(def_name.as_str());
            let mut j = i + 2;
            while j < tokens.len() && j < i + 24 {
                if matches!(&tokens[j].kind, LeanTokenKind::Symbol(s) if s == ":=") {
                    if let Some(LeanToken {
                        kind: LeanTokenKind::StrLit(lit),
                        ..
                    }) = tokens.get(j + 1)
                        && is_obend_wire_tag(lit)
                    {
                        record(short.to_string(), lit.clone());
                    } else if let Some((decoded, _)) = decode_lean_ascii_byte_list(tokens, j + 1) {
                        record(short.to_string(), decoded);
                    }
                    break;
                }
                j += 1;
            }
        }
        i += 1;
    }
    tag_defs
}

fn collect_lean_wire_sites(
    repo_root: &Path,
    lean_obend_dir: &Path,
) -> (Vec<WireTagSite>, BTreeSet<String>) {
    let lean_paths = collect_sorted_files(lean_obend_dir, "lean");
    let mut tokenized_tag_files: Vec<(String, Vec<LeanToken>, TagAliasMap)> = Vec::new();
    let mut other_lean_files: Vec<(String, PathBuf)> = Vec::new();
    // `Some(tag)` when unambiguous across `lean/Obend/`, `None` on conflicting definitions
    let mut global_lean_defs: TagAliasMap = HashMap::new();
    let mut dynamic_prefixes: BTreeSet<String> = BTreeSet::new();

    for path in lean_paths {
        let Ok(rel) = path.strip_prefix(repo_root) else {
            continue;
        };
        let rel_str = rel.to_string_lossy().replace('\\', "/");
        if is_excluded_lean_path(&rel_str) {
            continue;
        };
        let Ok(src) = std::fs::read_to_string(&path) else {
            continue;
        };
        if may_contain_obend_tag_def_only(&src) {
            let toks = fold_lean_string_concats(tokenize_lean(&src));
            let local_defs = scan_lean_tag_defs_in_tokens(&toks);
            for (k, v_opt) in &local_defs {
                match (global_lean_defs.get(k), v_opt) {
                    (_, None) => {
                        global_lean_defs.insert(k.clone(), None);
                    }
                    (None, Some(v)) => {
                        global_lean_defs.insert(k.clone(), Some(v.clone()));
                    }
                    (Some(Some(existing)), Some(v)) if existing != v => {
                        global_lean_defs.insert(k.clone(), None);
                    }
                    _ => {}
                }
            }
            // Record dynamic `"OBEND.PREFIX." ++ nonLiteral` prefixes
            for idx in 0..toks.len() {
                if let LeanTokenKind::StrLit(s) = &toks[idx].kind
                    && is_obend_wire_prefix(s)
                    && toks
                        .get(idx + 1)
                        .is_some_and(|t| matches!(&t.kind, LeanTokenKind::Symbol(op) if op == "++"))
                {
                    dynamic_prefixes.insert(s.clone());
                }
            }
            tokenized_tag_files.push((rel_str, toks, local_defs));
        } else {
            other_lean_files.push((rel_str, path));
        }
    }

    let mut out = Vec::new();
    for (rel_str, toks, local_defs) in &tokenized_tag_files {
        out.extend(extract_lean_wire_sites_from_tokens(
            rel_str,
            toks,
            local_defs,
            &global_lean_defs,
        ));
    }

    // Only scan non-tag files if at least one global alias name appears in their raw text
    if global_lean_defs.values().any(|v| v.is_some()) {
        let active_names: Vec<&str> = global_lean_defs
            .iter()
            .filter_map(|(k, v)| v.as_ref().map(|_| k.as_str()))
            .collect();
        let empty_local = HashMap::new();
        for (rel_str, path) in other_lean_files {
            let Ok(src) = std::fs::read_to_string(&path) else {
                continue;
            };
            if !active_names.iter().any(|name| src.contains(name)) {
                continue;
            }
            if !may_contain_obend_tag_or_alias_use_lean(&src, true) {
                continue;
            }
            let toks = fold_lean_string_concats(tokenize_lean(&src));
            out.extend(extract_lean_wire_sites_from_tokens(
                &rel_str,
                &toks,
                &empty_local,
                &global_lean_defs,
            ));
        }
    }

    (out, dynamic_prefixes)
}

pub fn extract_lean_wire_sites_from_src(rel_path: &str, src: &str) -> Vec<WireTagSite> {
    let toks = fold_lean_string_concats(tokenize_lean(src));
    let local_defs = scan_lean_tag_defs_in_tokens(&toks);
    let global_defs = local_defs.clone();
    extract_lean_wire_sites_from_tokens(rel_path, &toks, &local_defs, &global_defs)
}

fn is_lean_lowercase_field_projection(id: &str) -> bool {
    if let Some((root, _rest)) = id.split_once('.') {
        root.chars().next().is_some_and(|c| c.is_ascii_lowercase())
    } else {
        false
    }
}

fn is_lean_top_decl_kw(id: &str) -> bool {
    matches!(
        id,
        "def"
            | "abbrev"
            | "theorem"
            | "lemma"
            | "instance"
            | "structure"
            | "class"
            | "inductive"
            | "example"
            | "opaque"
            | "axiom"
    )
}

fn extract_lean_wire_sites_from_tokens(
    rel_path: &str,
    tokens: &[LeanToken],
    local_defs: &HashMap<String, Option<String>>,
    global_defs: &HashMap<String, Option<String>>,
) -> Vec<WireTagSite> {
    let mut sites = Vec::new();
    let mut shadowed_locals: BTreeSet<String> = BTreeSet::new();
    let mut in_decl_sig = false;
    let mut sig_paren_depth = 0usize;
    let mut idx = 0usize;
    while idx < tokens.len() {
        match &tokens[idx].kind {
            LeanTokenKind::Ident(kw) if tokens[idx].col == 1 && is_lean_top_decl_kw(kw) => {
                shadowed_locals.clear();
                in_decl_sig = true;
                sig_paren_depth = 0;
            }
            LeanTokenKind::Symbol(s) if in_decl_sig && matches!(s.as_str(), "(" | "{" | "[") => {
                sig_paren_depth += 1;
            }
            LeanTokenKind::Symbol(s) if in_decl_sig && matches!(s.as_str(), ")" | "}" | "]") => {
                sig_paren_depth = sig_paren_depth.saturating_sub(1);
            }
            LeanTokenKind::Symbol(s) if in_decl_sig && sig_paren_depth == 0 && s == ":=" => {
                in_decl_sig = false;
            }
            LeanTokenKind::Ident(kw) if in_decl_sig && sig_paren_depth == 0 && kw == "where" => {
                in_decl_sig = false;
            }
            LeanTokenKind::Ident(param) if in_decl_sig && sig_paren_depth > 0 => {
                // Record binder names before `:` inside `(param : Ty)` so shadowed params never resolve as tag aliases
                if tokens
                    .get(idx + 1)
                    .is_some_and(|t| matches!(&t.kind, LeanTokenKind::Symbol(s) if s == ":"))
                {
                    shadowed_locals.insert(param.clone());
                }
            }
            LeanTokenKind::Ident(kw) if kw == "fun" || kw == "λ" => {
                let mut k = idx + 1;
                while k < tokens.len() && k < idx + 10 {
                    match &tokens[k].kind {
                        LeanTokenKind::Symbol(s) if s == "=>" => break,
                        LeanTokenKind::Ident(v) if v != "_" => {
                            shadowed_locals.insert(v.clone());
                        }
                        _ => {}
                    }
                    k += 1;
                }
            }
            _ => {}
        }

        if let LeanTokenKind::StrLit(s) = &tokens[idx].kind
            && is_obend_wire_tag(s)
        {
            let was_paren = idx > 0
                && matches!(&tokens[idx - 1].kind, LeanTokenKind::Symbol(sym) if sym == "(");
            let next_after = skip_lean_tag_postfix(tokens, idx + 1, was_paren);
            let static_arity = count_lean_list_arity(tokens, next_after);
            sites.push(WireTagSite {
                tag: s.clone(),
                rel_path: rel_path.to_string(),
                line: tokens[idx].line,
                col: tokens[idx].col,
                static_arity,
            });
            idx += 1;
            continue;
        }

        if let Some((decoded, close_idx)) = decode_lean_ascii_byte_list(tokens, idx) {
            let next_after = skip_lean_tag_postfix(tokens, close_idx + 1, false);
            let static_arity = count_lean_list_arity(tokens, next_after);
            sites.push(WireTagSite {
                tag: decoded,
                rel_path: rel_path.to_string(),
                line: tokens[idx].line,
                col: tokens[idx].col,
                static_arity,
            });
            idx = close_idx + 1;
            continue;
        }

        if !in_decl_sig
            && let LeanTokenKind::Ident(id) = &tokens[idx].kind
            && !is_lean_lowercase_field_projection(id)
        {
            let short = id.rsplit('.').next().unwrap_or(id.as_str());
            let is_unqualified_shadowed = !id.contains('.') && shadowed_locals.contains(short);
            let is_def_lhs = idx > 0
                && matches!(&tokens[idx - 1].kind, LeanTokenKind::Ident(kw) if kw == "def" || kw == "abbrev");
            if !is_def_lhs && !is_unqualified_shadowed {
                let resolved = match local_defs.get(short) {
                    Some(opt) => opt.as_ref(),
                    None => global_defs.get(short).and_then(|o| o.as_ref()),
                };
                if let Some(aliased_tag) = resolved {
                    let next_after = skip_lean_tag_postfix(tokens, idx + 1, false);
                    if let Some(arity) = count_lean_list_arity(tokens, next_after) {
                        sites.push(WireTagSite {
                            tag: aliased_tag.clone(),
                            rel_path: rel_path.to_string(),
                            line: tokens[idx].line,
                            col: tokens[idx].col,
                            static_arity: Some(arity),
                        });
                    }
                }
            }
        }

        idx += 1;
    }

    sites
}

/// Remove `#[cfg(test)]` / `#[test]` items, `#![cfg(test)]` whole-file test modules, and
/// nested `mod tests { #![cfg(test)] ... }` blocks without swallowing sibling production items.
fn filter_non_test_rust_tokens(toks: &[RsTok]) -> Vec<RsTok> {
    let mut out = Vec::with_capacity(toks.len());
    let n = toks.len();
    let mut i = 0usize;
    let mut brace_depth = 0usize;

    while i < n {
        // Inner attribute `#![cfg(test)]`: skip whole file at top level, or skip enclosing `{ ... }` module
        if matches!(&toks[i].kind, RsTokKind::Symbol(s) if s == "#")
            && toks
                .get(i + 1)
                .is_some_and(|t| matches!(&t.kind, RsTokKind::Symbol(s) if s == "!"))
            && toks
                .get(i + 2)
                .is_some_and(|t| matches!(&t.kind, RsTokKind::Symbol(s) if s == "["))
            && let Some((is_cfg_test, attr_end)) = inspect_rust_attr_body(toks, i + 3)
            && is_cfg_test
        {
            if brace_depth == 0 {
                return Vec::new();
            }
            let mut inner_depth = 1usize;
            let mut k = attr_end;
            while k < n && inner_depth > 0 {
                match &toks[k].kind {
                    RsTokKind::Symbol(s) if s == "{" => inner_depth += 1,
                    RsTokKind::Symbol(s) if s == "}" => {
                        inner_depth -= 1;
                        if inner_depth == 0 {
                            out.push(toks[k].clone());
                            brace_depth = brace_depth.saturating_sub(1);
                            k += 1;
                            break;
                        }
                    }
                    _ => {}
                }
                k += 1;
            }
            i = k;
            continue;
        }

        if matches!(&toks[i].kind, RsTokKind::Symbol(s) if s == "#[")
            && let Some((is_cfg_test, attr_end)) = inspect_rust_attr_body(toks, i + 1)
            && is_cfg_test
        {
            i = skip_rust_attributed_item(toks, attr_end);
            continue;
        }
        match &toks[i].kind {
            RsTokKind::Symbol(s) if s == "{" => brace_depth += 1,
            RsTokKind::Symbol(s) if s == "}" => brace_depth = brace_depth.saturating_sub(1),
            _ => {}
        }
        out.push(toks[i].clone());
        i += 1;
    }
    out
}

/// Inspect the body of `#[ ... ]` or `#![ ... ]` starting right after the opening `[` (`body_start`),
/// returning `(is_test_only, next_idx_after_closing_bracket)`.
fn inspect_rust_attr_body(toks: &[RsTok], body_start: usize) -> Option<(bool, usize)> {
    let mut depth = 1usize;
    let mut i = body_start;
    let mut idents: Vec<&str> = Vec::new();
    let mut paren_stack: Vec<bool> = Vec::new(); // true when immediately preceded by `not`
    let mut prev_ident: Option<&str> = None;
    let mut saw_positive_test = false;

    while i < toks.len() && depth > 0 {
        match &toks[i].kind {
            RsTokKind::Symbol(s) if s == "[" || s == "#[" => depth += 1,
            RsTokKind::Symbol(s) if s == "]" => depth -= 1,
            RsTokKind::Symbol(s) if s == "(" => {
                paren_stack.push(prev_ident == Some("not"));
                prev_ident = None;
            }
            RsTokKind::Symbol(s) if s == ")" => {
                let _ = paren_stack.pop();
                prev_ident = None;
            }
            RsTokKind::Ident(id) => {
                let s = id.as_str();
                idents.push(s);
                if s == "test" && !paren_stack.iter().any(|&neg| neg) {
                    saw_positive_test = true;
                }
                prev_ident = Some(s);
            }
            RsTokKind::DocOrLineComment(_) => {}
            _ => {
                prev_ident = None;
            }
        }
        i += 1;
    }

    // `#[cfg(test)]` / `#[cfg(all(test, not(feature = "x")))]` (but NOT `#[cfg(any(test, ...))]`!)
    // OR `#[test]` / `#[tokio::test]`
    let is_cfg_test =
        idents.first() == Some(&"cfg") && saw_positive_test && !idents.contains(&"any");
    let is_fn_test = idents.first() != Some(&"cfg") && idents.last() == Some(&"test");
    Some((is_cfg_test || is_fn_test, i))
}

/// Skip stacked `#[...]` attributes and then skip the single item (`{ ... }` block, `;`-terminated item,
/// or `,` / `}` delimited field/variant/arm) attached to `#[cfg(test)]`.
fn skip_rust_attributed_item(toks: &[RsTok], mut i: usize) -> usize {
    while i < toks.len() {
        if matches!(&toks[i].kind, RsTokKind::Symbol(s) if s == "#[")
            && let Some((_, next_i)) = inspect_rust_attr_body(toks, i + 1)
        {
            i = next_i;
            continue;
        }
        break;
    }
    let mut paren_depth = 0usize;
    while i < toks.len() {
        match &toks[i].kind {
            RsTokKind::Symbol(s) if s == "(" || s == "[" => paren_depth += 1,
            RsTokKind::Symbol(s) if s == ")" || s == "]" => {
                paren_depth = paren_depth.saturating_sub(1);
            }
            RsTokKind::Symbol(s) if s == ";" && paren_depth == 0 => {
                return i + 1;
            }
            // Struct field / enum variant / match arm / fn param delimiter — stop before sibling!
            RsTokKind::Symbol(s) if s == "," && paren_depth == 0 => {
                return i + 1;
            }
            RsTokKind::Symbol(s) if s == "}" && paren_depth == 0 => {
                return i;
            }
            RsTokKind::Symbol(s) if s == "{" && paren_depth == 0 => {
                let mut brace_depth = 1usize;
                i += 1;
                while i < toks.len() && brace_depth > 0 {
                    match &toks[i].kind {
                        RsTokKind::Symbol(b) if b == "{" => brace_depth += 1,
                        RsTokKind::Symbol(b) if b == "}" => brace_depth -= 1,
                        _ => {}
                    }
                    i += 1;
                }
                return i;
            }
            _ => {}
        }
        i += 1;
    }
    toks.len()
}

/// Fold `concat!("OBEND.", "FOO", "/v1")` and `[b'O', b'B', ...]` / `[0x4f, 0x42, ...]` ASCII byte arrays
/// in Rust token streams into synthetic `RsTokKind::StrLit` tokens.
fn fold_rust_concat_and_byte_arrays(raw: Vec<RsTok>) -> Vec<RsTok> {
    let mut out = Vec::with_capacity(raw.len());
    let mut i = 0usize;
    while i < raw.len() {
        // 1. `concat!("a", "b", ...)`
        if matches!(&raw[i].kind, RsTokKind::Ident(id) if id == "concat")
            && raw
                .get(i + 1)
                .is_some_and(|t| matches!(&t.kind, RsTokKind::Symbol(s) if s == "!"))
            && raw
                .get(i + 2)
                .is_some_and(|t| matches!(&t.kind, RsTokKind::Symbol(s) if s == "("))
        {
            let mut j = i + 3;
            let mut combined = String::new();
            let mut ok = true;
            while j < raw.len() {
                if matches!(&raw[j].kind, RsTokKind::Symbol(s) if s == ")") {
                    break;
                }
                match &raw[j].kind {
                    RsTokKind::StrLit(piece) => combined.push_str(piece),
                    RsTokKind::Symbol(s) if s == "," => {}
                    RsTokKind::DocOrLineComment(_) => {}
                    _ => {
                        ok = false;
                        break;
                    }
                }
                j += 1;
            }
            if ok && j < raw.len() && matches!(&raw[j].kind, RsTokKind::Symbol(s) if s == ")") {
                out.push(RsTok {
                    kind: RsTokKind::StrLit(combined),
                    line: raw[i].line,
                    col: raw[i].col,
                });
                i = j + 1;
                continue;
            }
        }

        // 2. `[b'O', b'B', ...]` or `[0x4f, 0x42, ...]` forming an `OBEND.` / `OBEND_` wire tag
        if let Some((decoded, close_idx)) = decode_rust_ascii_byte_array(&raw, i) {
            out.push(RsTok {
                kind: RsTokKind::StrLit(decoded),
                line: raw[i].line,
                col: raw[i].col,
            });
            i = close_idx + 1;
            continue;
        }

        out.push(raw[i].clone());
        i += 1;
    }
    out
}

fn decode_rust_ascii_byte_array(toks: &[RsTok], open_idx: usize) -> Option<(String, usize)> {
    if !matches!(&toks.get(open_idx)?.kind, RsTokKind::Symbol(s) if s == "[") {
        return None;
    }
    let mut bytes = Vec::new();
    let mut i = open_idx + 1;
    while i < toks.len() {
        match &toks[i].kind {
            RsTokKind::DocOrLineComment(_) => {
                i += 1;
                continue;
            }
            RsTokKind::Symbol(s) if s == "]" => {
                let s = String::from_utf8(bytes).ok()?;
                if is_obend_wire_tag(&s) {
                    return Some((s, i));
                }
                return None;
            }
            RsTokKind::NumLit(n) => {
                let b = parse_u8_nat_lit(n)?;
                if !(0x21..=0x7E).contains(&b) {
                    return None;
                }
                bytes.push(b);
                i += 1;
                while i < toks.len() && matches!(&toks[i].kind, RsTokKind::DocOrLineComment(_)) {
                    i += 1;
                }
                if i < toks.len() {
                    if matches!(&toks[i].kind, RsTokKind::Symbol(s) if s == ",") {
                        i += 1;
                    } else if !matches!(&toks[i].kind, RsTokKind::Symbol(s) if s == "]") {
                        return None;
                    }
                }
            }
            _ => return None,
        }
    }
    None
}

fn skip_rust_tag_postfix(toks: &[RsTok], mut idx: usize) -> usize {
    // Handle `&TAG[..]` slice syntax
    if toks
        .get(idx)
        .is_some_and(|t| matches!(&t.kind, RsTokKind::Symbol(s) if s == "["))
        && toks
            .get(idx + 1)
            .is_some_and(|t| matches!(&t.kind, RsTokKind::Symbol(s) if s == "."))
        && toks
            .get(idx + 2)
            .is_some_and(|t| matches!(&t.kind, RsTokKind::Symbol(s) if s == "."))
        && toks
            .get(idx + 3)
            .is_some_and(|t| matches!(&t.kind, RsTokKind::Symbol(s) if s == "]"))
    {
        idx += 4;
    }

    while idx < toks.len() {
        if matches!(&toks[idx].kind, RsTokKind::Symbol(s) if s == ".")
            && let Some(RsTok {
                kind: RsTokKind::Ident(m),
                ..
            }) = toks.get(idx + 1)
            && matches!(
                m.as_str(),
                "as_bytes" | "as_slice" | "to_vec" | "to_owned" | "into_bytes" | "as_ref" | "into"
            )
            && toks
                .get(idx + 2)
                .is_some_and(|t| matches!(&t.kind, RsTokKind::Symbol(s) if s == "("))
            && toks
                .get(idx + 3)
                .is_some_and(|t| matches!(&t.kind, RsTokKind::Symbol(s) if s == ")"))
        {
            idx += 4;
            continue;
        }
        break;
    }
    idx
}

/// Given `after_tag_idx` pointing right after `"OBEND..."` (or its `const` alias), check if it is
/// followed by `, &[e1, ..., ek]`, `, [e1, ..., ek]`, `, vec![e1, ..., ek]`, or `, &vec![e1, ..., ek]`
/// and return `Some(k)`. Ignores repeat arrays `[val; N]` and iterator chains `[a, b].iter().chain(...)`.
fn parse_rust_following_framing_arity(toks: &[RsTok], after_tag_idx: usize) -> Option<usize> {
    let mut i = skip_rust_tag_postfix(toks, after_tag_idx);
    while i < toks.len() && matches!(&toks[i].kind, RsTokKind::DocOrLineComment(_)) {
        i += 1;
    }
    if !toks
        .get(i)
        .is_some_and(|t| matches!(&t.kind, RsTokKind::Symbol(s) if s == ","))
    {
        return None;
    }
    i += 1;
    while i < toks.len() && matches!(&toks[i].kind, RsTokKind::DocOrLineComment(_)) {
        i += 1;
    }

    // Optional `&` / `&mut`
    if toks
        .get(i)
        .is_some_and(|t| matches!(&t.kind, RsTokKind::Symbol(s) if s == "&"))
    {
        i += 1;
        if toks
            .get(i)
            .is_some_and(|t| matches!(&t.kind, RsTokKind::Ident(id) if id == "mut"))
        {
            i += 1;
        }
    }
    // Optional `vec!`
    if toks
        .get(i)
        .is_some_and(|t| matches!(&t.kind, RsTokKind::Ident(id) if id == "vec"))
        && toks
            .get(i + 1)
            .is_some_and(|t| matches!(&t.kind, RsTokKind::Symbol(s) if s == "!"))
    {
        i += 2;
    }

    let bracket_idx = i;
    if !toks
        .get(bracket_idx)
        .is_some_and(|t| matches!(&t.kind, RsTokKind::Symbol(s) if s == "["))
    {
        return None;
    }
    if decode_rust_ascii_byte_array(toks, bracket_idx).is_some() {
        return None;
    }

    let mut depth = 1usize;
    let mut angle_depth = 0usize;
    let mut j = bracket_idx + 1;
    let mut commas = 0usize;
    let mut tokens_in_current_elem = 0usize;
    let mut any_elem = false;

    while j < toks.len() && depth > 0 {
        match &toks[j].kind {
            // Turbofish generic arguments `encode::<A, B>(x)` at top level of slice
            RsTokKind::Symbol(s)
                if s == "<"
                    && (angle_depth > 0
                        || (j > bracket_idx + 1
                            && matches!(&toks[j - 1].kind, RsTokKind::Symbol(p) if p == "::"))) =>
            {
                angle_depth += 1;
                if depth == 1 {
                    tokens_in_current_elem += 1;
                    any_elem = true;
                }
            }
            RsTokKind::Symbol(s) if s == ">" && angle_depth > 0 => {
                angle_depth -= 1;
                if depth == 1 {
                    tokens_in_current_elem += 1;
                }
            }
            RsTokKind::Symbol(s) if s == ">>" && angle_depth > 0 => {
                angle_depth = angle_depth.saturating_sub(2);
                if depth == 1 {
                    tokens_in_current_elem += 1;
                }
            }
            RsTokKind::Symbol(s) if matches!(s.as_str(), "[" | "#[" | "(" | "{") => {
                if depth == 1 {
                    tokens_in_current_elem += 1;
                    any_elem = true;
                }
                depth += 1;
            }
            RsTokKind::Symbol(s) if matches!(s.as_str(), "]" | ")" | "}") => {
                depth -= 1;
                if depth == 0 {
                    // Reject `[a, b].iter().chain(...)` dynamic extension
                    if toks
                        .get(j + 1)
                        .is_some_and(|t| matches!(&t.kind, RsTokKind::Symbol(d) if d == "."))
                        && let Some(RsTok {
                            kind: RsTokKind::Ident(m),
                            ..
                        }) = toks.get(j + 2)
                        && !matches!(m.as_str(), "as_slice" | "as_ref")
                    {
                        return None;
                    }
                    if !any_elem {
                        return Some(0);
                    }
                    let total = if tokens_in_current_elem == 0 {
                        commas
                    } else {
                        commas + 1
                    };
                    return Some(total);
                }
                if depth == 1 {
                    tokens_in_current_elem += 1;
                }
            }
            // Reject repeat-array syntax `[0u8; 32]` at top level of the slice
            RsTokKind::Symbol(s) if s == ";" && depth == 1 && angle_depth == 0 => {
                return None;
            }
            RsTokKind::Symbol(s) if s == "," && depth == 1 && angle_depth == 0 => {
                commas += 1;
                tokens_in_current_elem = 0;
            }
            RsTokKind::DocOrLineComment(_) => {}
            _ => {
                if depth == 1 {
                    tokens_in_current_elem += 1;
                    any_elem = true;
                }
            }
        }
        j += 1;
    }

    None
}

fn is_rust_const_style_ident(name: &str) -> bool {
    name.bytes().any(|b| b.is_ascii_uppercase()) && !name.bytes().any(|b| b.is_ascii_lowercase())
}

fn scan_rust_tag_consts_in_tokens(toks: &[RsTok]) -> HashMap<String, Option<String>> {
    let mut tag_consts: HashMap<String, Option<String>> = HashMap::new();
    let mut i = 0usize;
    while i < toks.len() {
        if matches!(&toks[i].kind, RsTokKind::Ident(kw) if kw == "const" || kw == "static") {
            let mut name_idx = i + 1;
            if toks
                .get(name_idx)
                .is_some_and(|t| matches!(&t.kind, RsTokKind::Ident(m) if m == "mut"))
            {
                name_idx += 1;
            }
            if let Some(RsTok {
                kind: RsTokKind::Ident(cname),
                ..
            }) = toks.get(name_idx)
                && cname != "fn"
                && cname != "_"
                && is_rust_const_style_ident(cname)
            {
                let mut j = name_idx + 1;
                let mut depth = 0usize;
                while j < toks.len() && j < i + 36 {
                    match &toks[j].kind {
                        RsTokKind::Symbol(s) if matches!(s.as_str(), "[" | "(" | "<") => {
                            depth += 1;
                        }
                        RsTokKind::Symbol(s) if matches!(s.as_str(), "]" | ")" | ">") => {
                            depth = depth.saturating_sub(1);
                        }
                        RsTokKind::Symbol(s) if s == ";" && depth == 0 => break,
                        RsTokKind::Symbol(s) if s == "{" && depth == 0 => break,
                        RsTokKind::Symbol(s) if s == "=" && depth == 0 => {
                            let mut k = j + 1;
                            while toks.get(k).is_some_and(|t| {
                                matches!(&t.kind, RsTokKind::Symbol(sym) if sym == "&" || sym == "*")
                                    || matches!(&t.kind, RsTokKind::DocOrLineComment(_))
                            }) {
                                k += 1;
                            }
                            if let Some(RsTok {
                                kind: RsTokKind::StrLit(lit),
                                ..
                            }) = toks.get(k)
                                && is_obend_wire_tag(lit)
                            {
                                match tag_consts.get(cname) {
                                    None => {
                                        tag_consts.insert(cname.clone(), Some(lit.clone()));
                                    }
                                    Some(Some(prev)) if prev != lit => {
                                        tag_consts.insert(cname.clone(), None);
                                    }
                                    _ => {}
                                }
                            }
                            break;
                        }
                        _ => {}
                    }
                    j += 1;
                }
            }
        }
        i += 1;
    }
    tag_consts
}

fn collect_rust_wire_sites(repo_root: &Path, crates_dir: &Path) -> Vec<WireTagSite> {
    let rs_paths = collect_sorted_files(crates_dir, "rs");
    let mut tag_files: Vec<(String, String, Vec<RsTok>, TagAliasMap)> = Vec::new();
    let mut other_files: Vec<(String, String, PathBuf)> = Vec::new();
    // `crate_key -> (const_ident -> Some(tag) | None on conflict)`
    let mut crate_consts: HashMap<String, TagAliasMap> = HashMap::new();

    for path in rs_paths {
        let Ok(rel) = path.strip_prefix(repo_root) else {
            continue;
        };
        let rel_str = rel.to_string_lossy().replace('\\', "/");
        if is_excluded_rust_path(&rel_str) {
            continue;
        }
        let Ok(src) = std::fs::read_to_string(&path) else {
            continue;
        };
        let krate = rust_crate_key(&rel_str);
        if may_contain_obend_tag_def_only(&src) {
            let toks =
                fold_rust_concat_and_byte_arrays(filter_non_test_rust_tokens(&tokenize_rust(&src)));
            let local_consts = scan_rust_tag_consts_in_tokens(&toks);
            let kmap = crate_consts.entry(krate.clone()).or_default();
            for (cname, tag_opt) in &local_consts {
                match (kmap.get(cname), tag_opt) {
                    (_, None) => {
                        kmap.insert(cname.clone(), None);
                    }
                    (None, Some(tag)) => {
                        kmap.insert(cname.clone(), Some(tag.clone()));
                    }
                    (Some(Some(existing)), Some(tag)) if existing != tag => {
                        kmap.insert(cname.clone(), None);
                    }
                    _ => {}
                }
            }
            tag_files.push((rel_str, krate, toks, local_consts));
        } else {
            other_files.push((rel_str, krate, path));
        }
    }

    let mut out = Vec::new();
    let empty_kmap = HashMap::new();
    for (rel_str, krate, toks, local_consts) in &tag_files {
        let kmap = crate_consts.get(krate).unwrap_or(&empty_kmap);
        out.extend(extract_rust_wire_sites_from_tokens(
            rel_str,
            toks,
            local_consts,
            kmap,
        ));
    }

    // Scan sibling files in crates that exported `OBEND` constants so cross-file `hash(TAG, &[...])` is caught
    let empty_local = HashMap::new();
    for (rel_str, krate, path) in other_files {
        let Some(kmap) = crate_consts.get(&krate) else {
            continue;
        };
        let crate_names: Vec<&str> = kmap
            .iter()
            .filter_map(|(cname, val)| val.as_ref().map(|_| cname.as_str()))
            .collect();
        if crate_names.is_empty() {
            continue;
        }
        let Ok(src) = std::fs::read_to_string(&path) else {
            continue;
        };
        if !crate_names.iter().any(|cn| src.contains(cn)) {
            continue;
        }
        let toks =
            fold_rust_concat_and_byte_arrays(filter_non_test_rust_tokens(&tokenize_rust(&src)));
        out.extend(extract_rust_wire_sites_from_tokens(
            &rel_str,
            &toks,
            &empty_local,
            kmap,
        ));
    }

    out
}

pub fn extract_rust_wire_sites_from_src(rel_path: &str, src: &str) -> Vec<WireTagSite> {
    let toks = fold_rust_concat_and_byte_arrays(filter_non_test_rust_tokens(&tokenize_rust(src)));
    let local_consts = scan_rust_tag_consts_in_tokens(&toks);
    let kmap = local_consts.clone();
    extract_rust_wire_sites_from_tokens(rel_path, &toks, &local_consts, &kmap)
}

fn extract_rust_wire_sites_from_tokens(
    rel_path: &str,
    toks: &[RsTok],
    local_consts: &HashMap<String, Option<String>>,
    crate_kmap: &HashMap<String, Option<String>>,
) -> Vec<WireTagSite> {
    let mut sites = Vec::new();
    // Single O(N) delimiter stack tracking whether current token is immediately inside `[ ... ]`
    let mut delim_stack: Vec<char> = Vec::new();

    for (idx, tok) in toks.iter().enumerate() {
        match &tok.kind {
            RsTokKind::Symbol(s) => match s.as_str() {
                "[" | "#[" => delim_stack.push('['),
                "(" => delim_stack.push('('),
                "{" => delim_stack.push('{'),
                "]" | ")" | "}" => {
                    let _ = delim_stack.pop();
                }
                _ => {}
            },
            RsTokKind::StrLit(s) if is_obend_wire_tag(s) => {
                let in_square = delim_stack.last() == Some(&'[');
                let static_arity = if in_square {
                    None
                } else {
                    parse_rust_following_framing_arity(toks, idx + 1)
                };
                sites.push(WireTagSite {
                    tag: s.clone(),
                    rel_path: rel_path.to_string(),
                    line: tok.line,
                    col: tok.col,
                    static_arity,
                });
            }
            RsTokKind::Ident(id) if is_rust_const_style_ident(id) => {
                let is_const_decl = idx > 0
                    && matches!(
                        &toks[idx - 1].kind,
                        RsTokKind::Ident(kw) if kw == "const" || kw == "static" || kw == "mut"
                    );
                // Ignore field access `foo.TAG` while allowing path access `tags::TAG`
                let is_dot_field =
                    idx > 0 && matches!(&toks[idx - 1].kind, RsTokKind::Symbol(s) if s == ".");
                // Ignore `use crate::tags::TAG;` imports and `let TAG: ...` local bindings
                let is_let_or_param = idx > 0
                    && matches!(&toks[idx - 1].kind, RsTokKind::Ident(kw) if kw == "let")
                    || toks
                        .get(idx + 1)
                        .is_some_and(|t| matches!(&t.kind, RsTokKind::Symbol(s) if s == ":"));
                let is_followed_by_semi_or_path = toks.get(idx + 1).is_some_and(
                    |t| matches!(&t.kind, RsTokKind::Symbol(s) if s == ";" || s == "::"),
                );
                let in_square = delim_stack.last() == Some(&'[');
                if !in_square
                    && !is_const_decl
                    && !is_dot_field
                    && !is_let_or_param
                    && !is_followed_by_semi_or_path
                {
                    let resolved = match local_consts.get(id) {
                        Some(opt) => opt.as_ref(),
                        None => crate_kmap.get(id).and_then(|o| o.as_ref()),
                    };
                    if let Some(aliased_tag) = resolved
                        && let Some(arity) = parse_rust_following_framing_arity(toks, idx + 1)
                    {
                        sites.push(WireTagSite {
                            tag: aliased_tag.clone(),
                            rel_path: rel_path.to_string(),
                            line: tok.line,
                            col: tok.col,
                            static_arity: Some(arity),
                        });
                    }
                }
            }
            _ => {}
        }
    }

    sites
}
