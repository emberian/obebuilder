//! Structural parser and repository-wide declaration/constructor index for Lean 4 files.

use crate::lean_lexer::{LeanToken, LeanTokenKind, tokenize_lean};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::Path;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclKind {
    Theorem,
    Def,
    Abbrev,
    Opaque,
    Axiom,
    Instance,
    Example,
    Inductive,
    Structure,
    Class,
    TacticElab,
}

#[derive(Debug, Clone)]
pub struct BinderParam {
    pub name: String,
    pub is_underscore: bool,
    pub is_instance_bracket: bool,
    pub type_tokens: Vec<LeanToken>,
    pub line: usize,
    pub col: usize,
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub name: String,
    pub type_tokens: Vec<LeanToken>,
    pub line: usize,
    pub col: usize,
}

#[derive(Debug, Clone)]
pub struct WhereField {
    pub name: String,
    pub params: Vec<String>,
    pub rhs_tokens: Vec<LeanToken>,
    pub line: usize,
    pub col: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct LeanImport {
    pub module: String,
    pub is_public: bool,
    pub is_meta: bool,
    pub is_all: bool,
    pub line: usize,
    pub col: usize,
}

#[derive(Debug, Clone)]
pub struct ParsedLeanDecl {
    pub kind: DeclKind,
    pub name: String,
    pub fq_name: String,
    pub rel_path: String,
    pub line: usize,
    pub col: usize,
    pub fixture_kept: bool,
    pub attributes: Vec<String>,
    pub binders: Vec<BinderParam>,
    pub type_tokens: Vec<LeanToken>,
    pub body_tokens: Vec<LeanToken>,
    pub where_fields: Vec<WhereField>,
    pub constructors: Vec<String>,
    pub struct_fields: Vec<StructField>,
}

#[derive(Debug, Clone)]
pub struct ParsedLeanFile {
    pub rel_path: String,
    pub directory_bucket: String,
    pub line_count: usize,
    pub has_module_kw: bool,
    pub imports: Vec<LeanImport>,
    pub expose_public_sections: Vec<(usize, usize)>,
    pub section_variables: Vec<BinderParam>,
    pub declarations: Vec<ParsedLeanDecl>,
    pub tooth_targets: Vec<(String, usize)>,
    pub assert_compiled_targets: Vec<(String, usize)>,
    pub guard_tokens: Vec<(usize, Vec<LeanToken>)>,
    pub max_heartbeats: Vec<(u64, usize)>,
    pub raw_sorry_sites: Vec<(usize, usize, String)>,
}

/// Complete repository-wide Lean symbol, module, and inductive constructor index.
#[derive(Debug, Default, Clone)]
pub struct LeanIndex {
    /// Relative paths under `lean/` such as `Obend/Core/Term.lean`.
    pub lean_rel_paths: HashSet<String>,
    /// Bare filename -> list of `Obend/...` relative paths (e.g. `Term.lean` -> `["Obend/Core/Term.lean"]`).
    pub by_basename: HashMap<String, Vec<String>>,
    /// Top-level subsystems under `lean/Obend/` (e.g. `Core`, `Hardware`, `Judge`, `Lower`).
    pub subsystems: HashSet<String>,
    /// Existing `review/*.md` paths relative to repo root.
    pub review_paths: HashSet<String>,
    /// Every declared constant name (fully qualified, namespace-dropped, 1-suffix, and 2-suffix).
    pub all_symbol_forms: HashSet<String>,
    /// Exact fully-qualified and short declaration names.
    pub exact_decls: HashSet<String>,
    /// Inductive name (both short like `Term` and qualified like `Obend.Core.Term.Term`) -> constructors.
    pub inductives: HashMap<String, BTreeSet<String>>,
    /// Module path (`Obend/Core/Term.lean`) -> map of inductive short name -> constructors.
    pub module_inductives: HashMap<String, BTreeMap<String, BTreeSet<String>>>,
    /// Parsed files in deterministic path order.
    pub files: Vec<ParsedLeanFile>,
}

impl LeanIndex {
    pub fn total_declarations(&self) -> usize {
        self.files.iter().map(|f| f.declarations.len()).sum()
    }

    pub fn total_inductives(&self) -> usize {
        self.files
            .iter()
            .flat_map(|f| f.declarations.iter())
            .filter(|d| d.kind == DeclKind::Inductive)
            .count()
    }

    pub fn register_symbol(&mut self, fq_name: &str) {
        if fq_name.is_empty() {
            return;
        }
        self.exact_decls.insert(fq_name.to_string());
        self.all_symbol_forms.insert(fq_name.to_string());
        let parts: Vec<&str> = fq_name.split('.').filter(|s| !s.is_empty()).collect();
        for start in 0..parts.len() {
            let suffix = parts[start..].join(".");
            self.all_symbol_forms.insert(suffix);
        }
        if let Some(last) = parts.last() {
            self.exact_decls.insert((*last).to_string());
        }
    }

    pub fn has_symbol(&self, candidate: &str) -> bool {
        if self.all_symbol_forms.contains(candidate) {
            return true;
        }
        // Also check module path form `Obend.Core.Term` -> `Obend/Core/Term.lean`
        if candidate.starts_with("Obend.") {
            let rel_lean = format!("{}.lean", candidate.replace('.', "/"));
            if self.lean_rel_paths.contains(&rel_lean) {
                return true;
            }
            let parts: Vec<&str> = candidate.split('.').collect();
            if parts.len() == 2 && parts[0] == "Obend" && self.subsystems.contains(parts[1]) {
                return true;
            }
        }
        false
    }
}

fn is_modifier_ident(s: &str) -> bool {
    matches!(
        s,
        "public"
            | "private"
            | "protected"
            | "noncomputable"
            | "partial"
            | "unsafe"
            | "meta"
            | "scoped"
            | "local"
    )
}

fn is_top_command_starter(tok: &LeanToken) -> bool {
    if !tok.first_on_line || tok.col > 3 {
        return false;
    }
    if tok.col > 1 {
        return match &tok.kind {
            LeanTokenKind::CommandHash(_) => true,
            LeanTokenKind::Symbol(s) if s == "@[" => true,
            LeanTokenKind::Ident(s) => {
                is_modifier_ident(s)
                    || matches!(
                        s.as_str(),
                        "theorem"
                            | "lemma"
                            | "def"
                            | "abbrev"
                            | "opaque"
                            | "axiom"
                            | "instance"
                            | "example"
                            | "inductive"
                            | "structure"
                            | "class"
                            | "namespace"
                            | "section"
                            | "end"
                            | "variable"
                    )
            }
            _ => false,
        };
    }
    match &tok.kind {
        LeanTokenKind::CommandHash(_) => true,
        LeanTokenKind::Symbol(s) if s == "@[" => true,
        LeanTokenKind::Ident(s) => {
            is_modifier_ident(s)
                || matches!(
                    s.as_str(),
                    "theorem"
                        | "lemma"
                        | "def"
                        | "abbrev"
                        | "opaque"
                        | "axiom"
                        | "instance"
                        | "example"
                        | "inductive"
                        | "structure"
                        | "class"
                        | "namespace"
                        | "section"
                        | "end"
                        | "open"
                        | "variable"
                        | "universe"
                        | "set_option"
                        | "attribute"
                        | "elab"
                        | "macro"
                        | "syntax"
                        | "infix"
                        | "infixl"
                        | "infixr"
                        | "prefix"
                        | "postfix"
                        | "notation"
                        | "run_cmd"
                        | "import"
                        | "module"
                        | "mutual"
                        | "termination_by"
                        | "decreasing_by"
                )
        }
        _ => false,
    }
}

fn directory_bucket_of(rel_path: &str) -> String {
    let trimmed = rel_path.strip_prefix("lean/").unwrap_or(rel_path);
    let parts: Vec<&str> = trimmed.split('/').collect();
    if parts.first() == Some(&"Obend") && parts.len() >= 3 {
        format!("Obend/{}", parts[1])
    } else if parts.len() >= 2 {
        parts[0].to_string()
    } else {
        "root".to_string()
    }
}

/// Parse a single `.lean` source file into structured declarations, inductives, tactics, and commands.
pub fn parse_lean_file(rel_path: &str, src: &str) -> ParsedLeanFile {
    let line_count = src.lines().count();
    let tokens = tokenize_lean(src);
    let n = tokens.len();
    let mut ns_stack: Vec<(bool, Vec<String>)> = Vec::new(); // (is_namespace, components)
    let mut has_module_kw = false;
    let mut imports = Vec::new();
    let mut expose_public_sections = Vec::new();
    let mut section_variables = Vec::new();
    let mut declarations = Vec::new();
    let mut tooth_targets = Vec::new();
    let mut assert_compiled_targets = Vec::new();
    let mut guard_tokens = Vec::new();
    let mut max_heartbeats = Vec::new();
    let mut raw_sorry_sites = Vec::new();

    // Scan for raw `sorry` / `sorryAx` tokens outside strings/comments (comments and strings are already distinct token kinds!)
    for (idx, tok) in tokens.iter().enumerate() {
        if let LeanTokenKind::Ident(id) = &tok.kind {
            if id == "sorry" || id == "sorryAx" {
                // Exclude constant quote / name check sites like `n == ``sorryAx` (which lexes as DoubleBacktickConst)
                let prev_is_dot = idx > 0
                    && matches!(&tokens[idx - 1].kind, LeanTokenKind::Symbol(s) if s == ".");
                if !prev_is_dot {
                    raw_sorry_sites.push((tok.line, tok.col, id.clone()));
                }
            }
        }
    }

    let mut pending_fixture_kept = false;
    let mut i = 0usize;

    while i < n {
        match &tokens[i].kind {
            LeanTokenKind::FixtureKeptComment(_) => {
                pending_fixture_kept = true;
                i += 1;
                continue;
            }
            LeanTokenKind::DocComment(_) => {
                i += 1;
                continue;
            }
            _ => {}
        }

        // `set_option maxHeartbeats N`
        if matches!(&tokens[i].kind, LeanTokenKind::Ident(s) if s == "set_option") {
            if i + 2 < n {
                if let (LeanTokenKind::Ident(opt), LeanTokenKind::NatLit(num_s)) =
                    (&tokens[i + 1].kind, &tokens[i + 2].kind)
                {
                    if opt == "maxHeartbeats" {
                        if let Ok(v) = num_s.replace('_', "").parse::<u64>() {
                            max_heartbeats.push((v, tokens[i].line));
                        }
                    }
                }
            }
            // If `set_option ... in`, skip past `in` without clearing `pending_fixture_kept`
            let mut j = i + 1;
            while j < n && j < i + 8 {
                if matches!(&tokens[j].kind, LeanTokenKind::Ident(s) if s == "in") {
                    i = j + 1;
                    break;
                }
                if tokens[j].first_on_line && j > i {
                    i = j;
                    break;
                }
                j += 1;
            }
            if j >= n || j >= i + 8 {
                i += 1;
            }
            continue;
        }

        // `#tooth <target>` / `#assert_compiled <target>` / `#guard <expr>`
        if let LeanTokenKind::CommandHash(cmd) = &tokens[i].kind {
            if cmd == "#tooth" {
                if let Some(LeanToken {
                    kind: LeanTokenKind::Ident(target),
                    line,
                    ..
                }) = tokens.get(i + 1)
                {
                    tooth_targets.push((target.clone(), *line));
                }
                pending_fixture_kept = false;
                i += 1;
                continue;
            } else if cmd == "#assert_compiled" {
                if let Some(LeanToken {
                    kind: LeanTokenKind::Ident(target),
                    line,
                    ..
                }) = tokens.get(i + 1)
                {
                    assert_compiled_targets.push((target.clone(), *line));
                }
                pending_fixture_kept = false;
                i += 1;
                continue;
            } else if cmd == "#guard" || cmd == "#silicon_check" {
                let gline = tokens[i].line;
                let mut gend = i + 1;
                let mut depth = 0isize;
                while gend < n {
                    if depth == 0 && gend > i + 1 && is_top_command_starter(&tokens[gend]) {
                        break;
                    }
                    match &tokens[gend].kind {
                        LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{" | "#[") => {
                            depth += 1;
                        }
                        LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}") => {
                            if depth > 0 {
                                depth -= 1;
                            }
                        }
                        _ => {}
                    }
                    gend += 1;
                }
                guard_tokens.push((gline, tokens[i + 1..gend].to_vec()));
                pending_fixture_kept = false;
                i = gend;
                continue;
            }
        }

        // `namespace Foo.Bar` / `section [Foo]` / `end [Foo.Bar]`
        if tokens[i].col == 1 {
            if let LeanTokenKind::Ident(kw) = &tokens[i].kind {
                if kw == "namespace" {
                    let mut parts = Vec::new();
                    if let Some(LeanToken {
                        kind: LeanTokenKind::Ident(ns),
                        ..
                    }) = tokens.get(i + 1)
                    {
                        if tokens[i + 1].line == tokens[i].line {
                            parts = ns.split('.').map(str::to_string).collect();
                            i += 2;
                            ns_stack.push((true, parts));
                            continue;
                        }
                    }
                    ns_stack.push((true, parts));
                    i += 1;
                    continue;
                } else if kw == "section" {
                    // Careful: `public section` is handled in modifiers if not caught here; top-level `section` pushes scope
                    let mut parts = Vec::new();
                    if let Some(LeanToken {
                        kind: LeanTokenKind::Ident(sec),
                        ..
                    }) = tokens.get(i + 1)
                    {
                        if tokens[i + 1].line == tokens[i].line {
                            parts = sec.split('.').map(str::to_string).collect();
                            i += 2;
                            ns_stack.push((false, parts));
                            continue;
                        }
                    }
                    ns_stack.push((false, parts));
                    i += 1;
                    continue;
                } else if kw == "end" {
                    if let Some(LeanToken {
                        kind: LeanTokenKind::Ident(_closed),
                        ..
                    }) = tokens.get(i + 1)
                    {
                        if tokens[i + 1].line == tokens[i].line {
                            let _ = ns_stack.pop();
                            i += 2;
                            continue;
                        }
                    }
                    let _ = ns_stack.pop();
                    i += 1;
                    continue;
                }
            }
        }

        // Collect leading `@[...]` attributes and modifiers (`public`, `private`, `meta`, `noncomputable`, etc.)
        let decl_start = i;
        let mut cursor = i;
        let mut attrs: Vec<String> = Vec::new();
        let mut mods: Vec<String> = Vec::new();
        let mut attr_start_pos: Option<(usize, usize)> = None;
        while cursor < n {
            match &tokens[cursor].kind {
                LeanTokenKind::DocComment(_) => {
                    cursor += 1;
                }
                LeanTokenKind::FixtureKeptComment(_) => {
                    pending_fixture_kept = true;
                    cursor += 1;
                }
                LeanTokenKind::Symbol(s) if s == "@[" => {
                    if attr_start_pos.is_none() {
                        attr_start_pos = Some((tokens[cursor].line, tokens[cursor].col));
                    }
                    cursor += 1;
                    let mut depth = 1usize;
                    while cursor < n && depth > 0 {
                        match &tokens[cursor].kind {
                            LeanTokenKind::Symbol(o) if o == "[" || o == "@[" => depth += 1,
                            LeanTokenKind::Symbol(c) if c == "]" => depth -= 1,
                            LeanTokenKind::Ident(attr_id) if depth == 1 => {
                                attrs.push(attr_id.clone());
                            }
                            _ => {}
                        }
                        cursor += 1;
                    }
                }
                LeanTokenKind::Ident(m) if is_modifier_ident(m) => {
                    mods.push(m.clone());
                    cursor += 1;
                }
                _ => break,
            }
        }

        if cursor >= n {
            break;
        }

        let kw = match &tokens[cursor].kind {
            LeanTokenKind::Ident(s) => s.as_str(),
            _ => {
                i = cursor + 1;
                continue;
            }
        };

        // Handle `module` header keyword
        if kw == "module" && cursor == decl_start && tokens[cursor].col == 1 {
            has_module_kw = true;
            i = cursor + 1;
            continue;
        }

        // Handle `[public] [meta] import [all] <Module>...`
        if kw == "import" {
            let imp_line = tokens[decl_start].line;
            let imp_col = tokens[decl_start].col;
            let is_public = mods.iter().any(|m| m == "public");
            let is_meta = mods.iter().any(|m| m == "meta");
            let mut j = cursor + 1;
            let mut is_all = false;
            if j < n && tokens[j].line == tokens[cursor].line {
                if matches!(&tokens[j].kind, LeanTokenKind::Ident(s) if s == "all") {
                    is_all = true;
                    j += 1;
                }
            }
            while j < n {
                if j > cursor + 1 && tokens[j].first_on_line {
                    break;
                }
                if let LeanTokenKind::Ident(mod_name) = &tokens[j].kind {
                    imports.push(LeanImport {
                        module: mod_name.clone(),
                        is_public,
                        is_meta,
                        is_all,
                        line: imp_line,
                        col: imp_col,
                    });
                }
                j += 1;
            }
            pending_fixture_kept = false;
            i = j;
            continue;
        }

        // Handle `[attribute] [public] section [Name]`
        if kw == "section" && cursor > decl_start {
            let is_pub = mods.iter().any(|m| m == "public");
            let has_expose = attrs.iter().any(|a| a == "expose");
            if is_pub && has_expose && ns_stack.iter().all(|(is_ns, _)| *is_ns) {
                let (eline, ecol) =
                    attr_start_pos.unwrap_or((tokens[decl_start].line, tokens[decl_start].col));
                expose_public_sections.push((eline, ecol));
            }
            let mut parts = Vec::new();
            let mut next_i = cursor + 1;
            if let Some(LeanToken {
                kind: LeanTokenKind::Ident(sec),
                line: sline,
                ..
            }) = tokens.get(cursor + 1)
            {
                if *sline == tokens[cursor].line {
                    parts = sec.split('.').map(str::to_string).collect();
                    next_i = cursor + 2;
                }
            }
            ns_stack.push((false, parts));
            pending_fixture_kept = false;
            i = next_i;
            continue;
        }

        // Handle `variable (...) [...] {...}` commands for section-scoped `[HypothesisLedger ...]`
        if kw == "variable" {
            let mut v_end = cursor + 1;
            let mut bdepth = 0isize;
            while v_end < n {
                if bdepth == 0 && v_end > cursor + 1 && is_top_command_starter(&tokens[v_end]) {
                    break;
                }
                match &tokens[v_end].kind {
                    LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{") => {
                        if bdepth == 0 {
                            let open = s.as_str();
                            let close = match open {
                                "(" => ")",
                                "[" => "]",
                                _ => "}",
                            };
                            let gstart = v_end + 1;
                            let mut d = 1usize;
                            let mut k = v_end + 1;
                            while k < n && d > 0 {
                                match &tokens[k].kind {
                                    LeanTokenKind::Symbol(o) if o == open => d += 1,
                                    LeanTokenKind::Symbol(c) if c == close => d -= 1,
                                    _ => {}
                                }
                                k += 1;
                            }
                            let gend = k.saturating_sub(1);
                            if gstart <= gend && gend <= n {
                                extract_binder_group(
                                    &tokens[gstart..gend],
                                    open == "[",
                                    &mut section_variables,
                                );
                            }
                            v_end = k;
                            continue;
                        }
                        bdepth += 1;
                    }
                    LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}") => {
                        if bdepth > 0 {
                            bdepth -= 1;
                        }
                    }
                    _ => {}
                }
                v_end += 1;
            }
            pending_fixture_kept = false;
            i = v_end;
            continue;
        }

        let decl_kind = match kw {
            "theorem" | "lemma" => Some(DeclKind::Theorem),
            "def" => Some(DeclKind::Def),
            "abbrev" => Some(DeclKind::Abbrev),
            "opaque" => Some(DeclKind::Opaque),
            "axiom" => Some(DeclKind::Axiom),
            "instance" => Some(DeclKind::Instance),
            "example" => Some(DeclKind::Example),
            "inductive" => Some(DeclKind::Inductive),
            "structure" => Some(DeclKind::Structure),
            "class" => Some(DeclKind::Class),
            "elab" | "macro" => Some(DeclKind::TacticElab),
            _ => None,
        };

        let Some(kind) = decl_kind else {
            if cursor == decl_start {
                i += 1;
            } else {
                i = cursor + 1;
            }
            continue;
        };

        // Find end of this top-level command (next column-1 top-level command starter)
        let cmd_line = tokens[cursor].line;
        let cmd_col = tokens[cursor].col;
        let mut cmd_end = cursor + 1;
        let mut bracket_depth = 0isize;
        while cmd_end < n {
            if bracket_depth == 0 && cmd_end > cursor + 1 && is_top_command_starter(&tokens[cmd_end])
            {
                break;
            }
            match &tokens[cmd_end].kind {
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{" | "#[" | "@[") => {
                    bracket_depth += 1;
                }
                LeanTokenKind::SyntaxQuoteOpen | LeanTokenKind::AntiquoteOpen => {
                    bracket_depth += 1;
                }
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}") => {
                    if bracket_depth > 0 {
                        bracket_depth -= 1;
                    }
                }
                _ => {}
            }
            cmd_end += 1;
        }

        let cmd_slice = &tokens[cursor..cmd_end];
        if let Some(parsed) = parse_command_slice(
            kind,
            cmd_slice,
            &ns_stack,
            rel_path,
            cmd_line,
            cmd_col,
            pending_fixture_kept,
            attrs,
        ) {
            declarations.push(parsed);
        }
        pending_fixture_kept = false;
        i = cmd_end;
    }

    ParsedLeanFile {
        rel_path: rel_path.to_string(),
        directory_bucket: directory_bucket_of(rel_path),
        line_count,
        has_module_kw,
        imports,
        expose_public_sections,
        section_variables,
        declarations,
        tooth_targets,
        assert_compiled_targets,
        guard_tokens,
        max_heartbeats,
        raw_sorry_sites,
    }
}

fn qualify_name(ns_stack: &[(bool, Vec<String>)], name: &str) -> String {
    let mut prefix: Vec<&str> = Vec::new();
    for (is_ns, parts) in ns_stack {
        if *is_ns {
            for p in parts {
                prefix.push(p.as_str());
            }
        }
    }
    if prefix.is_empty() {
        name.to_string()
    } else if name.starts_with(&format!("{}.", prefix.join("."))) {
        name.to_string()
    } else {
        format!("{}.{}", prefix.join("."), name)
    }
}

fn parse_command_slice(
    kind: DeclKind,
    cmd: &[LeanToken],
    ns_stack: &[(bool, Vec<String>)],
    rel_path: &str,
    line: usize,
    col: usize,
    fixture_kept: bool,
    attributes: Vec<String>,
) -> Option<ParsedLeanDecl> {
    if cmd.is_empty() {
        return None;
    }

    // Special case: `elab ... : tactic => ...` / `macro ... : tactic => ...`
    if kind == DeclKind::TacticElab {
        let mut is_tactic = false;
        let mut tactic_name = String::from("<tactic>");
        for w in cmd.windows(2) {
            if matches!(&w[0].kind, LeanTokenKind::Symbol(s) if s == ":")
                && matches!(&w[1].kind, LeanTokenKind::Ident(s) if s == "tactic")
            {
                is_tactic = true;
            }
        }
        for tok in cmd.iter().skip(1).take(6) {
            if let LeanTokenKind::StrLit(s) = &tok.kind {
                let clean = s.trim().to_string();
                if !clean.is_empty() {
                    tactic_name = clean;
                    break;
                }
            } else if let LeanTokenKind::Ident(id) = &tok.kind {
                if id != "elab" && id != "macro" {
                    tactic_name = id.clone();
                    break;
                }
            }
        }
        if !is_tactic {
            return None;
        }
        // Body starts after top-level `=>`
        let mut depth = 0isize;
        let mut arrow_pos = None;
        for (idx, tok) in cmd.iter().enumerate() {
            match &tok.kind {
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{") => depth += 1,
                LeanTokenKind::SyntaxQuoteOpen | LeanTokenKind::AntiquoteOpen => depth += 1,
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}") => {
                    if depth > 0 {
                        depth -= 1;
                    }
                }
                LeanTokenKind::Symbol(s) if s == "=>" && depth == 0 => {
                    arrow_pos = Some(idx);
                    break;
                }
                _ => {}
            }
        }
        let body_tokens = arrow_pos
            .map(|p| cmd[p + 1..].to_vec())
            .unwrap_or_default();
        return Some(ParsedLeanDecl {
            kind,
            name: tactic_name.clone(),
            fq_name: qualify_name(ns_stack, &tactic_name),
            rel_path: rel_path.to_string(),
            line,
            col,
            fixture_kept,
            attributes,
            binders: Vec::new(),
            type_tokens: Vec::new(),
            body_tokens,
            where_fields: Vec::new(),
            constructors: Vec::new(),
            struct_fields: Vec::new(),
        });
    }

    // Extract declaration name (for `example` or anonymous `instance`, synthesize one if omitted)
    let mut pos = 1usize;
    // Skip optional `(priority := ...)` on `instance`
    if kind == DeclKind::Instance
        && pos + 1 < cmd.len()
        && matches!(&cmd[pos].kind, LeanTokenKind::Symbol(s) if s == "(")
        && matches!(&cmd[pos + 1].kind, LeanTokenKind::Ident(s) if s == "priority")
    {
        let mut d = 1usize;
        pos += 1;
        while pos < cmd.len() && d > 0 {
            match &cmd[pos].kind {
                LeanTokenKind::Symbol(s) if s == "(" => d += 1,
                LeanTokenKind::Symbol(s) if s == ")" => d -= 1,
                _ => {}
            }
            pos += 1;
        }
    }

    let name = if kind == DeclKind::Example {
        format!("example@{line}")
    } else if pos < cmd.len() {
        match &cmd[pos].kind {
            LeanTokenKind::Ident(id) => {
                pos += 1;
                id.clone()
            }
            _ if kind == DeclKind::Instance => format!("inst@{line}"),
            _ => return None,
        }
    } else {
        return None;
    };

    // Skip universe parameters `.{u, v}` if present
    if pos < cmd.len() && matches!(&cmd[pos].kind, LeanTokenKind::Symbol(s) if s == "." || s == "{") {
        if matches!(&cmd[pos].kind, LeanTokenKind::Symbol(s) if s == ".") {
            pos += 1;
        }
        if pos < cmd.len() && matches!(&cmd[pos].kind, LeanTokenKind::Symbol(s) if s == "{") {
            // Only universe params if right after name on same line and before binders/colon; check if inside contains `:`
            let mut look = pos + 1;
            let mut d = 1usize;
            let mut has_colon = false;
            while look < cmd.len() && d > 0 {
                match &cmd[look].kind {
                    LeanTokenKind::Symbol(s) if s == "{" => d += 1,
                    LeanTokenKind::Symbol(s) if s == "}" => d -= 1,
                    LeanTokenKind::Symbol(s) if s == ":" => has_colon = true,
                    _ => {}
                }
                look += 1;
            }
            if !has_colon {
                pos = look;
            }
        }
    }

    let fq_name = qualify_name(ns_stack, &name);

    // Inductive parsing: collect constructors after `where` or top-level `|`
    if kind == DeclKind::Inductive {
        let mut constructors = Vec::new();
        let mut depth = 0isize;
        let mut in_body = false;
        let mut header_colon_idx: Option<usize> = None;
        let mut body_start_idx: Option<usize> = None;
        let mut idx = pos;
        while idx < cmd.len() {
            match &cmd[idx].kind {
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{") => depth += 1,
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}") => {
                    if depth > 0 {
                        depth -= 1;
                    }
                }
                LeanTokenKind::Symbol(s) if s == ":" && !in_body && depth == 0 && header_colon_idx.is_none() => {
                    header_colon_idx = Some(idx);
                }
                LeanTokenKind::Ident(s) if s == "where" && depth == 0 => {
                    if body_start_idx.is_none() {
                        body_start_idx = Some(idx);
                    }
                    in_body = true;
                }
                LeanTokenKind::Ident(s) if s == "deriving" && depth == 0 => {
                    if body_start_idx.is_none() {
                        body_start_idx = Some(idx);
                    }
                    break;
                }
                LeanTokenKind::Symbol(s) if s == "|" && depth == 0 => {
                    if body_start_idx.is_none() {
                        body_start_idx = Some(idx);
                    }
                    in_body = true;
                    // Next identifier (skipping optional doc comments or modifiers) is the constructor name!
                    let mut k = idx + 1;
                    while k < cmd.len()
                        && matches!(&cmd[k].kind, LeanTokenKind::DocComment(_) | LeanTokenKind::Symbol(_))
                    {
                        if matches!(&cmd[k].kind, LeanTokenKind::Symbol(sym) if sym != ".") {
                            break;
                        }
                        k += 1;
                    }
                    if let Some(LeanToken {
                        kind: LeanTokenKind::Ident(ctor),
                        ..
                    }) = cmd.get(k)
                    {
                        let short_ctor = ctor.rsplit('.').next().unwrap_or(ctor).to_string();
                        constructors.push(short_ctor);
                    }
                }
                _ => {}
            }
            idx += 1;
        }
        let header_type_tokens = match header_colon_idx {
            Some(hc) => {
                let end_hdr = body_start_idx.unwrap_or(cmd.len());
                if hc + 1 <= end_hdr {
                    cmd[hc + 1..end_hdr].to_vec()
                } else {
                    Vec::new()
                }
            }
            None => Vec::new(),
        };
        return Some(ParsedLeanDecl {
            kind,
            name,
            fq_name,
            rel_path: rel_path.to_string(),
            line,
            col,
            fixture_kept,
            attributes,
            binders: Vec::new(),
            type_tokens: header_type_tokens,
            body_tokens: Vec::new(),
            where_fields: Vec::new(),
            constructors,
            struct_fields: Vec::new(),
        });
    }

    // Structure / Class field extraction
    if kind == DeclKind::Structure || kind == DeclKind::Class {
        let mut fields = Vec::new();
        let mut struct_fields = Vec::new();
        let mut struct_binders = Vec::new();
        let mut header_type_tokens = Vec::new();
        let mut depth = 0isize;
        let mut after_where = false;
        let mut header_colon_idx: Option<usize> = None;
        let mut extends_idx: Option<usize> = None;
        let mut where_idx: Option<usize> = None;
        // Extract header binders `(α : Type) [Foo α]` before `extends` / `:` / `where`
        let mut b_idx = pos;
        while b_idx < cmd.len() {
            match &cmd[b_idx].kind {
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "{" | "[") => {
                    let open = s.as_str();
                    let close = match open {
                        "(" => ")",
                        "{" => "}",
                        _ => "]",
                    };
                    let gstart = b_idx + 1;
                    let mut d = 1usize;
                    b_idx += 1;
                    while b_idx < cmd.len() && d > 0 {
                        match &cmd[b_idx].kind {
                            LeanTokenKind::Symbol(o) if o == open => d += 1,
                            LeanTokenKind::Symbol(c) if c == close => d -= 1,
                            _ => {}
                        }
                        b_idx += 1;
                    }
                    let gend = b_idx.saturating_sub(1);
                    if gstart <= gend && gend <= cmd.len() {
                        extract_binder_group(
                            &cmd[gstart..gend],
                            open == "[",
                            &mut struct_binders,
                        );
                    }
                }
                _ => break,
            }
        }
        for (idx, tok) in cmd.iter().enumerate().skip(pos) {
            match &tok.kind {
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{") => depth += 1,
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}") => {
                    if depth > 0 {
                        depth -= 1;
                    }
                }
                LeanTokenKind::Ident(s) if s == "extends" && !after_where && depth == 0 && extends_idx.is_none() => {
                    extends_idx = Some(idx);
                }
                LeanTokenKind::Symbol(s) if s == ":" && !after_where && depth == 0 && header_colon_idx.is_none() => {
                    header_colon_idx = Some(idx);
                }
                LeanTokenKind::Ident(s) if s == "where" && depth == 0 => {
                    after_where = true;
                    where_idx = Some(idx);
                }
                LeanTokenKind::Ident(s) if s == "deriving" && depth == 0 => {
                    break;
                }
                LeanTokenKind::Ident(field_id)
                    if after_where && depth == 0 && tok.first_on_line && tok.col > 1 =>
                {
                    if idx + 1 < cmd.len()
                        && matches!(
                            &cmd[idx + 1].kind,
                            LeanTokenKind::Symbol(sym) if sym == ":" || sym == "(" || sym == "{" || sym == "["
                        )
                    {
                        fields.push(field_id.clone());
                        // Extract field's type tokens between `:` (at depth 0 relative to field) and `:=` or next field / `deriving`
                        let mut k = idx + 1;
                        let mut fdepth = 0isize;
                        let mut fcolon = None;
                        while k < cmd.len() {
                            if fdepth == 0
                                && k > idx + 1
                                && ((cmd[k].first_on_line && cmd[k].col <= tok.col)
                                    || matches!(&cmd[k].kind, LeanTokenKind::Ident(s) if s == "deriving")
                                    || matches!(&cmd[k].kind, LeanTokenKind::Symbol(s) if s == ":="))
                            {
                                break;
                            }
                            match &cmd[k].kind {
                                LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{") => {
                                    fdepth += 1;
                                }
                                LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}") => {
                                    if fdepth > 0 {
                                        fdepth -= 1;
                                    }
                                }
                                LeanTokenKind::Symbol(s) if s == ":" && fdepth == 0 && fcolon.is_none() => {
                                    fcolon = Some(k);
                                }
                                _ => {}
                            }
                            k += 1;
                        }
                        let ftype = match fcolon {
                            Some(fc) if fc + 1 <= k => cmd[fc + 1..k].to_vec(),
                            _ => Vec::new(),
                        };
                        struct_fields.push(StructField {
                            name: field_id.clone(),
                            type_tokens: ftype,
                            line: tok.line,
                            col: tok.col,
                        });
                    }
                }
                _ => {}
            }
        }
        let end_hdr = where_idx.unwrap_or(cmd.len());
        if let Some(ext) = extends_idx {
            if ext <= end_hdr {
                header_type_tokens = cmd[ext..end_hdr].to_vec();
            }
        } else if let Some(hc) = header_colon_idx {
            if hc + 1 <= end_hdr {
                header_type_tokens = cmd[hc + 1..end_hdr].to_vec();
            }
        }
        return Some(ParsedLeanDecl {
            kind,
            name,
            fq_name,
            rel_path: rel_path.to_string(),
            line,
            col,
            fixture_kept,
            attributes,
            binders: struct_binders,
            type_tokens: header_type_tokens,
            body_tokens: Vec::new(),
            where_fields: Vec::new(),
            constructors: fields,
            struct_fields,
        });
    }

    // Parse binders, optional `: Type`, and `:= Body` / `where ...` / `| pat => ...`
    let mut binders = Vec::new();
    let mut depth = 0isize;
    let mut colon_idx: Option<usize> = None;
    let mut body_sep_idx: Option<(usize, &str)> = None;

    let mut idx = pos;
    while idx < cmd.len() {
        let tok = &cmd[idx];
        match &tok.kind {
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "{" | "[") && colon_idx.is_none() && depth == 0 => {
                let open = s.as_str();
                let close = match open {
                    "(" => ")",
                    "{" => "}",
                    "[" => "]",
                    _ => ")",
                };
                let group_start = idx + 1;
                let mut d = 1usize;
                idx += 1;
                while idx < cmd.len() && d > 0 {
                    match &cmd[idx].kind {
                        LeanTokenKind::Symbol(o) if o == open => d += 1,
                        LeanTokenKind::Symbol(c) if c == close => d -= 1,
                        _ => {}
                    }
                    idx += 1;
                }
                let group_end = idx.saturating_sub(1);
                if group_start <= group_end && group_end <= cmd.len() {
                    extract_binder_group(&cmd[group_start..group_end], open == "[", &mut binders);
                }
                continue;
            }
            LeanTokenKind::Ident(param_id)
                if colon_idx.is_none()
                    && depth == 0
                    && param_id != "where"
                    && !matches!(param_id.as_str(), "extends") =>
            {
                // Bare binder identifier like `def foo x y := ...`
                binders.push(BinderParam {
                    name: param_id.clone(),
                    is_underscore: param_id.starts_with('_'),
                    is_instance_bracket: false,
                    type_tokens: Vec::new(),
                    line: tok.line,
                    col: tok.col,
                });
                idx += 1;
                continue;
            }
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "{" | "[" | "#[" | "@[") => {
                depth += 1;
            }
            LeanTokenKind::SyntaxQuoteOpen | LeanTokenKind::AntiquoteOpen => {
                depth += 1;
            }
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "}" | "]") => {
                if depth > 0 {
                    depth -= 1;
                }
            }
            LeanTokenKind::Symbol(s) if s == ":" && depth == 0 && colon_idx.is_none() => {
                colon_idx = Some(idx);
            }
            LeanTokenKind::Symbol(s) if s == ":=" && depth == 0 => {
                body_sep_idx = Some((idx, ":="));
                break;
            }
            LeanTokenKind::Ident(s) if s == "where" && depth == 0 => {
                body_sep_idx = Some((idx, "where"));
                break;
            }
            LeanTokenKind::Symbol(s)
                if s == "|" && depth == 0 && tok.first_on_line && colon_idx.is_some() =>
            {
                body_sep_idx = Some((idx, "|"));
                break;
            }
            _ => {}
        }
        idx += 1;
    }

    let type_tokens = match (colon_idx, body_sep_idx) {
        (Some(c), Some((b, _))) if c + 1 <= b => cmd[c + 1..b].to_vec(),
        (Some(c), None) if c + 1 <= cmd.len() => cmd[c + 1..].to_vec(),
        _ => Vec::new(),
    };

    let (body_tokens, where_fields) = match body_sep_idx {
        Some((b, ":=")) => (cmd[b + 1..].to_vec(), Vec::new()),
        Some((b, "|")) => (cmd[b..].to_vec(), Vec::new()),
        Some((b, "where")) => {
            let wf = parse_where_fields(&cmd[b + 1..]);
            (cmd[b + 1..].to_vec(), wf)
        }
        _ => (Vec::new(), Vec::new()),
    };

    Some(ParsedLeanDecl {
        kind,
        name,
        fq_name,
        rel_path: rel_path.to_string(),
        line,
        col,
        fixture_kept,
        attributes,
        binders,
        type_tokens,
        body_tokens,
        where_fields,
        constructors: Vec::new(),
        struct_fields: Vec::new(),
    })
}

fn extract_binder_group(group: &[LeanToken], is_instance_bracket: bool, out: &mut Vec<BinderParam>) {
    // Find top-level `:` inside the binder group `(x y : Nat)`
    let mut depth = 0isize;
    let mut colon_pos = None;
    for (i, t) in group.iter().enumerate() {
        match &t.kind {
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{") => depth += 1,
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}") => {
                if depth > 0 {
                    depth -= 1;
                }
            }
            LeanTokenKind::Symbol(s) if s == ":" && depth == 0 => {
                colon_pos = Some(i);
                break;
            }
            _ => {}
        }
    }
    if is_instance_bracket && colon_pos.is_none() {
        // Anonymous `[DecidableEq α]` instance binder
        out.push(BinderParam {
            name: String::from("_inst"),
            is_underscore: true,
            is_instance_bracket: true,
            type_tokens: group.to_vec(),
            line: group.first().map(|t| t.line).unwrap_or(1),
            col: group.first().map(|t| t.col).unwrap_or(1),
        });
        return;
    }
    let (lhs, rhs_type) = match colon_pos {
        Some(c) => (&group[..c], group[c + 1..].to_vec()),
        None => (group, Vec::new()),
    };
    for t in lhs {
        if let LeanTokenKind::Ident(name) = &t.kind {
            out.push(BinderParam {
                name: name.clone(),
                is_underscore: name.starts_with('_'),
                is_instance_bracket,
                type_tokens: rhs_type.clone(),
                line: t.line,
                col: t.col,
            });
        }
    }
}

fn parse_where_fields(tokens: &[LeanToken]) -> Vec<WhereField> {
    let mut fields = Vec::new();
    if tokens.is_empty() {
        return fields;
    }

    // Identify field starts: tokens with `first_on_line == true` whose indentation column equals the first field's column
    // (or `<= base_col`) and where an Ident is followed on that header by `:=` or pattern `|`.
    let mut field_starts: Vec<usize> = Vec::new();
    let mut base_col: Option<usize> = None;
    let mut depth = 0isize;

    for (idx, tok) in tokens.iter().enumerate() {
        if matches!(&tok.kind, LeanTokenKind::Ident(s) if s == "deriving") && depth == 0 {
            break;
        }
        if depth == 0 && tok.first_on_line {
            if let LeanTokenKind::Ident(_fname) = &tok.kind {
                if let Some(bc) = base_col {
                    if tok.col == bc {
                        field_starts.push(idx);
                    }
                } else if tok.col > 1 {
                    base_col = Some(tok.col);
                    field_starts.push(idx);
                }
            }
        }
        match &tok.kind {
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{") => depth += 1,
            LeanTokenKind::SyntaxQuoteOpen | LeanTokenKind::AntiquoteOpen => depth += 1,
            LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}") => {
                if depth > 0 {
                    depth -= 1;
                }
            }
            _ => {}
        }
    }

    for (pos_i, &start) in field_starts.iter().enumerate() {
        let end = field_starts.get(pos_i + 1).copied().unwrap_or(tokens.len());
        let slice = &tokens[start..end];
        let Some(LeanToken {
            kind: LeanTokenKind::Ident(fname),
            line,
            col,
            ..
        }) = slice.first()
        else {
            continue;
        };

        let mut d = 0isize;
        let mut assign_idx = None;
        for (k, t) in slice.iter().enumerate().skip(1) {
            match &t.kind {
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{") => d += 1,
                LeanTokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}") => {
                    if d > 0 {
                        d -= 1;
                    }
                }
                LeanTokenKind::Symbol(s) if s == ":=" && d == 0 => {
                    assign_idx = Some(k);
                    break;
                }
                _ => {}
            }
        }

        if let Some(a_idx) = assign_idx {
            let mut params = Vec::new();
            for t in &slice[1..a_idx] {
                if let LeanTokenKind::Ident(p) = &t.kind {
                    params.push(p.clone());
                }
            }
            fields.push(WhereField {
                name: fname.clone(),
                params,
                rhs_tokens: slice[a_idx + 1..].to_vec(),
                line: *line,
                col: *col,
            });
        } else {
            fields.push(WhereField {
                name: fname.clone(),
                params: Vec::new(),
                rhs_tokens: slice[1..].to_vec(),
                line: *line,
                col: *col,
            });
        }
    }

    fields
}

/// Build a complete `LeanIndex` for a repository root.
pub fn build_lean_index(repo_root: &Path) -> LeanIndex {
    let mut index = LeanIndex::default();

    // Collect `review/*.md` if present
    let review_dir = repo_root.join("review");
    if review_dir.is_dir() {
        if let Ok(entries) = std::fs::read_dir(&review_dir) {
            for entry in entries.flatten() {
                let p = entry.path();
                if p.extension().and_then(|e| e.to_str()) == Some("md") {
                    if let Some(fname) = p.file_name().and_then(|n| n.to_str()) {
                        index.review_paths.insert(format!("review/{fname}"));
                    }
                }
            }
        }
    }

    // Optional `.lake/build/census/environment.txt` augmentation if built
    let env_txt = repo_root.join("lean/.lake/build/census/environment.txt");
    if let Ok(raw_env) = std::fs::read_to_string(&env_txt) {
        for line in raw_env.lines() {
            let trimmed = line.trim();
            if !trimmed.is_empty() {
                index.register_symbol(trimmed);
            }
        }
    }

    // Walk `.lean` files deterministically
    let mut lean_files: Vec<std::path::PathBuf> = Vec::new();
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
            && entry.path().extension().and_then(|e| e.to_str()) == Some("lean")
        {
            lean_files.push(entry.path().to_path_buf());
        }
    }
    lean_files.sort();

    // Subsystem discovery under `lean/Obend/`
    let obend_dir = repo_root.join("lean/Obend");
    if obend_dir.is_dir() {
        if let Ok(entries) = std::fs::read_dir(&obend_dir) {
            for entry in entries.flatten() {
                let p = entry.path();
                if p.is_dir() {
                    if let Some(sub) = p.file_name().and_then(|s| s.to_str()) {
                        index.subsystems.insert(sub.to_string());
                    }
                } else if p.extension().and_then(|e| e.to_str()) == Some("lean") {
                    if let Some(stem) = p.file_stem().and_then(|s| s.to_str()) {
                        index.subsystems.insert(stem.to_string());
                    }
                }
            }
        }
    }

    for abs_path in lean_files {
        let Ok(rel) = abs_path.strip_prefix(repo_root) else {
            continue;
        };
        let rel_str = rel.to_string_lossy().replace('\\', "/");
        let Ok(src) = std::fs::read_to_string(&abs_path) else {
            continue;
        };

        // Record `Obend/.../*.lean` relative path (normalized without `lean/` prefix, matching `DocsCensus.lean`)
        let norm_obend_rel = rel_str.strip_prefix("lean/").unwrap_or(&rel_str).to_string();
        if norm_obend_rel.starts_with("Obend/") {
            index.lean_rel_paths.insert(norm_obend_rel.clone());
            if let Some(base) = abs_path.file_name().and_then(|s| s.to_str()) {
                index
                    .by_basename
                    .entry(base.to_string())
                    .or_default()
                    .push(norm_obend_rel.clone());
            }
            // Register module name as constant too (`Obend.Core.Term`)
            let mod_const = norm_obend_rel
                .strip_suffix(".lean")
                .unwrap_or(&norm_obend_rel)
                .replace('/', ".");
            index.register_symbol(&mod_const);
        }

        let parsed = parse_lean_file(&rel_str, &src);

        for decl in &parsed.declarations {
            index.register_symbol(&decl.fq_name);
            index.register_symbol(&decl.name);

            match decl.kind {
                DeclKind::Inductive => {
                    let mut ctor_set = BTreeSet::new();
                    for ctor in &decl.constructors {
                        ctor_set.insert(ctor.clone());
                        index.register_symbol(&format!("{}.{}", decl.fq_name, ctor));
                        index.register_symbol(&format!("{}.{}", decl.name, ctor));
                    }
                    index
                        .inductives
                        .entry(decl.name.clone())
                        .or_default()
                        .extend(ctor_set.iter().cloned());
                    index
                        .inductives
                        .entry(decl.fq_name.clone())
                        .or_default()
                        .extend(ctor_set.iter().cloned());
                    index
                        .module_inductives
                        .entry(norm_obend_rel.clone())
                        .or_default()
                        .entry(decl.name.clone())
                        .or_default()
                        .extend(ctor_set);
                }
                DeclKind::Structure | DeclKind::Class => {
                    index.register_symbol(&format!("{}.mk", decl.fq_name));
                    index.register_symbol(&format!("{}.mk", decl.name));
                    for field in &decl.constructors {
                        index.register_symbol(&format!("{}.{}", decl.fq_name, field));
                        index.register_symbol(&format!("{}.{}", decl.name, field));
                    }
                }
                _ => {}
            }
        }

        index.files.push(parsed);
    }

    index
}
