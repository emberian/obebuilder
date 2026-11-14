//! Structural scanner for `.obend` source files (`DESIGN.md` §2.6: ".obend claims restating their method").

use obb_core::{ArtifactKind, Finding, Regime, Severity, Sink};
use std::collections::HashMap;
use std::path::Path;

#[derive(Debug, Clone)]
struct SpecDef {
    body_norm: String,
    line: usize,
}

#[derive(Debug, Clone)]
struct SpecClaim {
    name: String,
    expr_raw: String,
    line: usize,
    col: usize,
}

pub fn lint_obend_file(rel_path: &str, src: &str) -> Vec<Finding> {
    let mut findings = Vec::new();
    let lines: Vec<&str> = src.lines().collect();

    let mut current_spec: Option<String> = None;
    let mut spec_defs: HashMap<String, SpecDef> = HashMap::new();
    let mut spec_claims: Vec<(String, SpecClaim)> = Vec::new();

    let mut i = 0usize;
    while i < lines.len() {
        let raw_line = lines[i];
        let code_line = strip_obend_comment(raw_line);
        let trimmed = code_line.trim();
        let indent = raw_line.chars().take_while(|c| c.is_whitespace()).count();

        if trimmed.is_empty() {
            i += 1;
            continue;
        }

        if indent == 0 {
            if current_spec.is_some() {
                flush_spec_claims(rel_path, &spec_defs, &spec_claims, &mut findings);
                spec_defs.clear();
                spec_claims.clear();
                current_spec = None;
            }

            if let Some(rest) = trimmed.strip_prefix("spec ") {
                let spec_name = rest
                    .split_whitespace()
                    .next()
                    .unwrap_or("<spec>")
                    .trim_end_matches(':')
                    .to_string();
                current_spec = Some(spec_name);
            } else if let Some(rest) = trimmed.strip_prefix("law ")
                && let Some((law_name, expr)) = rest.split_once(':')
            {
                let norm = normalize_obend_expr(expr);
                if norm == "true" || is_reflexive_eq(&norm) {
                    findings.push(Finding {
                            rule_id: "obend/tautological-law".to_string(),
                            severity: Severity::Error,
                            artifact_kind: ArtifactKind::S,
                            max_regime: Regime::Attested,
                            sink: Some(Sink::Theater),
                            path: rel_path.to_string(),
                            line: i + 1,
                            column: 1,
                            symbol: Some(law_name.trim().to_string()),
                            message: format!(
                                "`.obend` law `{}` is a trivial tautology (`{}`)",
                                law_name.trim(),
                                expr.trim()
                            ),
                            remediation: "State a non-trivial state transition or invariant constraint over `old`/`new` fields.".to_string(),
                        });
                }
            }
            i += 1;
            continue;
        }

        // Inside a `spec` block
        if let Some(ref sname) = current_spec {
            if let Some(rest) = trimmed.strip_prefix("def ") {
                if let Some((sig, after_colon)) = rest.split_once(':') {
                    let def_name = sig.split('(').next().unwrap_or(sig).trim().to_string();
                    // Note: signature has `:` for param types too! Split at `:=` or trailing `:` after `-> Ret`
                    let inline_body = if let Some((_, rhs_assign)) = rest.split_once(":=") {
                        rhs_assign.trim()
                    } else if let Some((_, ret_rhs)) = rest.rsplit_once("->") {
                        ret_rhs.split_once(':').map(|(_, b)| b.trim()).unwrap_or("")
                    } else {
                        after_colon.trim()
                    };

                    let mut body_acc = String::new();
                    if !inline_body.is_empty() {
                        body_acc.push_str(inline_body);
                    } else {
                        let mut k = i + 1;
                        while k < lines.len() {
                            let next_code = strip_obend_comment(lines[k]);
                            let next_trim = next_code.trim();
                            let next_indent =
                                lines[k].chars().take_while(|c| c.is_whitespace()).count();
                            if !next_trim.is_empty() && next_indent <= indent {
                                break;
                            }
                            if !next_trim.is_empty() {
                                if !body_acc.is_empty() {
                                    body_acc.push(' ');
                                }
                                body_acc.push_str(next_trim);
                            }
                            k += 1;
                        }
                    }
                    let _ = spec_defs.insert(
                        def_name,
                        SpecDef {
                            body_norm: normalize_obend_expr(&body_acc),
                            line: i + 1,
                        },
                    );
                }
            } else if let Some(rest) = trimmed.strip_prefix("claim ") {
                // Parse `claim name(args): expr`
                if let Some((head, claim_expr)) = split_after_signature_colon(rest) {
                    let claim_name = head.split('(').next().unwrap_or(head).trim().to_string();
                    spec_claims.push((
                        sname.clone(),
                        SpecClaim {
                            name: claim_name,
                            expr_raw: claim_expr.trim().to_string(),
                            line: i + 1,
                            col: indent + 1,
                        },
                    ));
                }
            }
        }

        i += 1;
    }

    if current_spec.is_some() {
        flush_spec_claims(rel_path, &spec_defs, &spec_claims, &mut findings);
    }

    findings
}

fn flush_spec_claims(
    rel_path: &str,
    spec_defs: &HashMap<String, SpecDef>,
    spec_claims: &[(String, SpecClaim)],
    findings: &mut Vec<Finding>,
) {
    for (spec_name, claim) in spec_claims {
        if let Some((lhs, rhs)) = claim.expr_raw.split_once("==") {
            let lhs_trim = lhs.trim();
            let rhs_norm = normalize_obend_expr(rhs);
            let lhs_norm = normalize_obend_expr(lhs);

            if lhs_norm == rhs_norm {
                findings.push(Finding {
                    rule_id: "obend/claim-restates-method".to_string(),
                    severity: Severity::Error,
                    artifact_kind: ArtifactKind::S,
                    max_regime: Regime::Attested,
                    sink: Some(Sink::Theater),
                    path: rel_path.to_string(),
                    line: claim.line,
                    column: claim.col,
                    symbol: Some(format!("{spec_name}.{}", claim.name)),
                    message: format!(
                        "Claim `{}.{}` is a syntactic reflexivity tautology (`{}`)",
                        spec_name, claim.name, claim.expr_raw
                    ),
                    remediation: "Replace reflexive `x == x` claim with an algebraic or conservation property independent of syntax.".to_string(),
                });
                continue;
            }

            // Check `self.<method>(...) == <body of def <method>>` or `<method>(...) == <body of def <method>>`
            let call_target = lhs_trim.strip_prefix("self.").unwrap_or(lhs_trim);
            let method_name = call_target.split('(').next().unwrap_or(call_target).trim();
            if !method_name.is_empty()
                && let Some(def_info) = spec_defs.get(method_name)
                && !def_info.body_norm.is_empty()
                && def_info.body_norm == rhs_norm
            {
                findings.push(Finding {
                            rule_id: "obend/claim-restates-method".to_string(),
                            severity: Severity::Warning,
                            artifact_kind: ArtifactKind::S,
                            max_regime: Regime::Attested,
                            sink: Some(Sink::Theater),
                            path: rel_path.to_string(),
                            line: claim.line,
                            column: claim.col,
                            symbol: Some(format!("{spec_name}.{}", claim.name)),
                            message: format!(
                                "Claim `{}.{}` literally restates the implementation body of `def {method_name}` (line {})",
                                spec_name, claim.name, def_info.line
                            ),
                            remediation: format!(
                                "State a relational property (e.g. monotonicity, conservation, round-trip, or equivalence to an independent spec) rather than repeating `{method_name}`'s formula."
                            ),
                        });
            }
        }
    }
}

fn strip_obend_comment(line: &str) -> &str {
    let bytes = line.as_bytes();
    let mut in_str = false;
    for (idx, &b) in bytes.iter().enumerate() {
        if b == b'"' {
            in_str = !in_str;
        } else if b == b'#' && !in_str {
            return &line[..idx];
        }
    }
    line
}

fn split_after_signature_colon(s: &str) -> Option<(&str, &str)> {
    let mut paren_depth = 0usize;
    for (idx, ch) in s.char_indices() {
        match ch {
            '(' => paren_depth += 1,
            ')' => paren_depth = paren_depth.saturating_sub(1),
            ':' if paren_depth == 0 => {
                return Some((&s[..idx], &s[idx + 1..]));
            }
            _ => {}
        }
    }
    None
}

fn normalize_obend_expr(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

fn is_reflexive_eq(norm: &str) -> bool {
    if let Some((a, b)) = norm.split_once("==") {
        !a.is_empty() && a == b
    } else {
        false
    }
}

pub fn scan_all_obend_files(repo_root: &Path) -> (usize, Vec<Finding>) {
    let mut count = 0usize;
    let mut findings = Vec::new();
    let mut paths = Vec::new();

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
            && entry.path().extension().and_then(|e| e.to_str()) == Some("obend")
        {
            paths.push(entry.path().to_path_buf());
        }
    }
    paths.sort();

    for p in paths {
        let Ok(rel) = p.strip_prefix(repo_root) else {
            continue;
        };
        let rel_str = rel.to_string_lossy().replace('\\', "/");
        if let Ok(src) = std::fs::read_to_string(&p) {
            count += 1;
            findings.extend(lint_obend_file(&rel_str, &src));
        }
    }

    (count, findings)
}
