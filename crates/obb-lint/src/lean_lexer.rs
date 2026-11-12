//! Proper lexical scanner for Lean 4 source files.
//! Handles nested `/- ... -/` block comments, `/-- ... -/` docstrings, `--` line comments
//! (including `-- fixture kept`), string literals, syntax quotations `` `(...) ``,
//! antiquotations `$(...)`, French quotes `«...»`, and exact 1-based `(line, col)` spans.

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeanTokenKind {
    Ident(String),
    StrLit(String),
    NatLit(String),
    DocComment(String),
    FixtureKeptComment(String),
    CommandHash(String), // e.g. `#tooth`, `#assert_compiled`, `#silicon_check`
    SyntaxQuoteOpen,     // `` `( ``
    AntiquoteOpen,       // `$(`
    AntiquoteIdent(String), // `$x`
    DoubleBacktickConst(String), // `` ``Foo.bar ``
    Symbol(String),      // `:=`, `=>`, `|`, `:`, `(`, `)`, `{`, `}`, `[`, `]`, `⟨`, `⟩`, `∀`, `→`, `∧`, `↔`, `=`, `==`, etc.
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeanToken {
    pub kind: LeanTokenKind,
    pub line: usize,
    pub col: usize,
    pub first_on_line: bool,
}

fn is_ident_start(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}

fn is_ident_continue(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\'' || c == '?' || c == '!' || matches!(c, '₀'..='₉' | 'ₐ'..='ₜ')
}

pub fn tokenize_lean(src: &str) -> Vec<LeanToken> {
    let chars: Vec<char> = src.chars().collect();
    let n = chars.len();
    let mut i = 0;
    let mut line = 1usize;
    let mut col = 1usize;
    let mut first_on_line = true;
    let mut tokens = Vec::new();

    while i < n {
        let c = chars[i];

        // Newline
        if c == '\n' {
            line += 1;
            col = 1;
            first_on_line = true;
            i += 1;
            continue;
        }

        // Horizontal whitespace
        if c.is_whitespace() {
            col += 1;
            i += 1;
            continue;
        }

        // Line comment `-- ...`
        if c == '-' && i + 1 < n && chars[i + 1] == '-' {
            let start_line = line;
            let start_col = col;
            i += 2;
            col += 2;
            let mut text = String::new();
            while i < n && chars[i] != '\n' {
                text.push(chars[i]);
                i += 1;
                col += 1;
            }
            let trimmed = text.trim();
            if trimmed.starts_with("fixture kept") {
                tokens.push(LeanToken {
                    kind: LeanTokenKind::FixtureKeptComment(trimmed.to_string()),
                    line: start_line,
                    col: start_col,
                    first_on_line,
                });
                first_on_line = false;
            }
            continue;
        }

        // Nested block comment `/- ... -/` or docstring `/-- ... -/`
        if c == '/' && i + 1 < n && chars[i + 1] == '-' {
            let start_line = line;
            let start_col = col;
            let is_doc = i + 2 < n && chars[i + 2] == '-' && (i + 3 >= n || chars[i + 3] != '-');
            let is_mod_doc = i + 2 < n && chars[i + 2] == '!';
            i += 2;
            col += 2;
            if is_doc || is_mod_doc {
                i += 1;
                col += 1;
            }
            let mut depth = 1usize;
            let mut body = String::new();
            while i < n && depth > 0 {
                if chars[i] == '/' && i + 1 < n && chars[i + 1] == '-' {
                    depth += 1;
                    body.push('/');
                    body.push('-');
                    i += 2;
                    col += 2;
                } else if chars[i] == '-' && i + 1 < n && chars[i + 1] == '/' {
                    depth -= 1;
                    if depth > 0 {
                        body.push('-');
                        body.push('/');
                    }
                    i += 2;
                    col += 2;
                } else if chars[i] == '\n' {
                    body.push('\n');
                    line += 1;
                    col = 1;
                    first_on_line = true;
                    i += 1;
                } else {
                    body.push(chars[i]);
                    i += 1;
                    col += 1;
                }
            }
            if is_doc {
                tokens.push(LeanToken {
                    kind: LeanTokenKind::DocComment(body),
                    line: start_line,
                    col: start_col,
                    first_on_line,
                });
            }
            continue;
        }

        let start_line = line;
        let start_col = col;
        let tok_first = first_on_line;
        first_on_line = false;

        // Interpolated string prefix `s!"..."` or `m!"..."` or normal string `"..."`
        if (matches!(c, 's' | 'm' | 'f') && i + 2 < n && chars[i + 1] == '!' && chars[i + 2] == '"')
            || c == '"'
        {
            let mut s = String::new();
            if c != '"' {
                i += 3;
                col += 3;
            } else {
                i += 1;
                col += 1;
            }
            while i < n && chars[i] != '"' {
                if chars[i] == '\\' && i + 1 < n {
                    i += 1;
                    col += 1;
                    s.push(chars[i]);
                    if chars[i] == '\n' {
                        line += 1;
                        col = 1;
                    } else {
                        col += 1;
                    }
                    i += 1;
                } else {
                    if chars[i] == '\n' {
                        line += 1;
                        col = 1;
                    } else {
                        col += 1;
                    }
                    s.push(chars[i]);
                    i += 1;
                }
            }
            if i < n && chars[i] == '"' {
                i += 1;
                col += 1;
            }
            tokens.push(LeanToken {
                kind: LeanTokenKind::StrLit(s),
                line: start_line,
                col: start_col,
                first_on_line: tok_first,
            });
            continue;
        }

        // Char literal `'a'` or `'\n'` (careful not to confuse with primed identifiers handled below)
        if c == '\'' && i + 2 < n {
            if chars[i + 1] == '\\' && i + 3 < n && chars[i + 3] == '\'' {
                i += 4;
                col += 4;
                tokens.push(LeanToken {
                    kind: LeanTokenKind::StrLit(chars[i - 2].to_string()),
                    line: start_line,
                    col: start_col,
                    first_on_line: tok_first,
                });
                continue;
            } else if chars[i + 2] == '\'' && chars[i + 1] != '\'' {
                let ch = chars[i + 1];
                i += 3;
                col += 3;
                tokens.push(LeanToken {
                    kind: LeanTokenKind::StrLit(ch.to_string()),
                    line: start_line,
                    col: start_col,
                    first_on_line: tok_first,
                });
                continue;
            }
        }

        // Backtick syntax quote `` `( `` or constant quote `` ``Foo `` or single quote `` `Foo ``
        if c == '`' {
            if i + 1 < n && chars[i + 1] == '(' {
                i += 2;
                col += 2;
                tokens.push(LeanToken {
                    kind: LeanTokenKind::SyntaxQuoteOpen,
                    line: start_line,
                    col: start_col,
                    first_on_line: tok_first,
                });
                continue;
            }
            if i + 1 < n && chars[i + 1] == '`' {
                i += 2;
                col += 2;
                let mut name = String::new();
                while i < n && (is_ident_continue(chars[i]) || chars[i] == '.') {
                    name.push(chars[i]);
                    i += 1;
                    col += 1;
                }
                tokens.push(LeanToken {
                    kind: LeanTokenKind::DoubleBacktickConst(name),
                    line: start_line,
                    col: start_col,
                    first_on_line: tok_first,
                });
                continue;
            }
            // Single backtick Name literal `` `Obend.Foo ``
            i += 1;
            col += 1;
            let mut name = String::new();
            while i < n && (is_ident_continue(chars[i]) || chars[i] == '.') {
                name.push(chars[i]);
                i += 1;
                col += 1;
            }
            tokens.push(LeanToken {
                kind: LeanTokenKind::Symbol(format!("`{name}")),
                line: start_line,
                col: start_col,
                first_on_line: tok_first,
            });
            continue;
        }

        // Antiquotation `$(...)` or `$ident`
        if c == '$' && i + 1 < n {
            if chars[i + 1] == '(' {
                i += 2;
                col += 2;
                tokens.push(LeanToken {
                    kind: LeanTokenKind::AntiquoteOpen,
                    line: start_line,
                    col: start_col,
                    first_on_line: tok_first,
                });
                continue;
            } else if is_ident_start(chars[i + 1]) {
                i += 1;
                col += 1;
                let mut id = String::new();
                while i < n && is_ident_continue(chars[i]) {
                    id.push(chars[i]);
                    i += 1;
                    col += 1;
                }
                tokens.push(LeanToken {
                    kind: LeanTokenKind::AntiquoteIdent(id),
                    line: start_line,
                    col: start_col,
                    first_on_line: tok_first,
                });
                continue;
            }
        }

        // Hash command `#tooth`, `#assert_compiled`, `#silicon_check`, `#guard`, or BitVec literal `1#64`
        if c == '#' && i + 1 < n && is_ident_start(chars[i + 1]) {
            let mut cmd = String::from("#");
            i += 1;
            col += 1;
            while i < n && is_ident_continue(chars[i]) {
                cmd.push(chars[i]);
                i += 1;
                col += 1;
            }
            tokens.push(LeanToken {
                kind: LeanTokenKind::CommandHash(cmd),
                line: start_line,
                col: start_col,
                first_on_line: tok_first,
            });
            continue;
        }

        // French quotes `«ident»`
        if c == '«' {
            i += 1;
            col += 1;
            let mut id = String::new();
            while i < n && chars[i] != '»' && chars[i] != '\n' {
                id.push(chars[i]);
                i += 1;
                col += 1;
            }
            if i < n && chars[i] == '»' {
                i += 1;
                col += 1;
            }
            tokens.push(LeanToken {
                kind: LeanTokenKind::Ident(id),
                line: start_line,
                col: start_col,
                first_on_line: tok_first,
            });
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
            tokens.push(LeanToken {
                kind: LeanTokenKind::NatLit(num),
                line: start_line,
                col: start_col,
                first_on_line: tok_first,
            });
            continue;
        }

        // Identifiers (including dotted names like `Obend.Judge.Format` when `.` is followed by ident start)
        if is_ident_start(c) {
            let mut id = String::new();
            loop {
                while i < n && is_ident_continue(chars[i]) {
                    id.push(chars[i]);
                    i += 1;
                    col += 1;
                }
                if i + 1 < n && chars[i] == '.' && is_ident_start(chars[i + 1]) {
                    id.push('.');
                    i += 1;
                    col += 1;
                } else {
                    break;
                }
            }
            tokens.push(LeanToken {
                kind: LeanTokenKind::Ident(id),
                line: start_line,
                col: start_col,
                first_on_line: tok_first,
            });
            continue;
        }

        // Anonymous constructor / dot-notation `.ok`, `.refused`, `.kernel`
        if c == '.' && i + 1 < n && is_ident_start(chars[i + 1]) {
            let mut sym = String::from(".");
            i += 1;
            col += 1;
            while i < n && is_ident_continue(chars[i]) {
                sym.push(chars[i]);
                i += 1;
                col += 1;
            }
            tokens.push(LeanToken {
                kind: LeanTokenKind::Symbol(sym),
                line: start_line,
                col: start_col,
                first_on_line: tok_first,
            });
            continue;
        }

        // Multi-character operators
        let two: Option<String> = if i + 1 < n {
            Some(format!("{}{}", c, chars[i + 1]))
        } else {
            none_str()
        };
        let three: Option<String> = if i + 2 < n {
            Some(format!("{}{}{}", c, chars[i + 1], chars[i + 2]))
        } else {
            None
        };

        if let Some(ref s3) = three {
            if matches!(s3.as_str(), "<->" | "=:=" | "=?=" | "<;>" | ">>>" | "<<<") {
                i += 3;
                col += 3;
                tokens.push(LeanToken {
                    kind: LeanTokenKind::Symbol(s3.clone()),
                    line: start_line,
                    col: start_col,
                    first_on_line: tok_first,
                });
                continue;
            }
        }
        if let Some(ref s2) = two {
            if matches!(
                s2.as_str(),
                ":=" | "=>" | "->" | "<-" | "==" | "!=" | "<=" | ">=" | "&&" | "||" | "++" | "::" | "|>" | "<|" | "#[" | "@["
            ) {
                i += 2;
                col += 2;
                tokens.push(LeanToken {
                    kind: LeanTokenKind::Symbol(s2.clone()),
                    line: start_line,
                    col: start_col,
                    first_on_line: tok_first,
                });
                continue;
            }
        }

        i += 1;
        col += 1;
        tokens.push(LeanToken {
            kind: LeanTokenKind::Symbol(c.to_string()),
            line: start_line,
            col: start_col,
            first_on_line: tok_first,
        });
    }

    tokens
}

#[inline]
fn none_str() -> Option<String> {
    None
}
