//! `obb harness` — Canonical Multi-Agent Harness Customizations (Antigravity, Claude Code,
//! Codex) & Progressive-Disclosure Skill Verifier.
//!
//! Materializes and audits:
//! - Root rules: `AGENTS.md` (`< 12,000` B), `GEMINI.md` (`< 4,000` B, `@[AGENTS.md](./AGENTS.md)`),
//!   and `CLAUDE.md` (`< 4,000` B, `@AGENTS.md`), all strictly under the `24,000`-byte rule ceiling
//!   even after `@[...]` include expansion.
//! - Progressive-disclosure workspace skills in both `.agents/skills/<name>/SKILL.md` and
//!   `.claude/skills/<name>/SKILL.md` with validated YAML frontmatter (`name`, third-person
//!   `description`) and deterministic SHA-256 content-integrity headers:
//!   1. `obend-anti-cosplay`
//!   2. `obend-spec-exec-refinement`
//!   3. `obend-proof-engineering`
//!   4. `obend-trailblaze-promotion`

use anyhow::Result;
use chrono::Utc;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs;
use std::path::Path;

pub const HARNESS_SCHEMA_VERSION: &str = "v4";
pub const RULE_FILE_HARD_CAP_BYTES: usize = 24_000;
pub const AGENTS_MD_BUDGET_BYTES: usize = 12_000;
pub const POINTER_RULE_BUDGET_BYTES: usize = 4_000;

const MARKER_PREFIX: &str = "<!-- obb-harness: ";
const MARKER_SUFFIX: &str = " -->";

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum HarnessArtifactKind {
    RootRule,
    Skill,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HarnessArtifactEntry {
    pub artifact_id: String,
    pub kind: HarnessArtifactKind,
    pub rel_path: String,
    pub harnesses: Vec<String>,
    pub skill_name: Option<String>,
    pub description: Option<String>,
    pub byte_len: usize,
    pub byte_budget: usize,
    pub sha256: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HarnessListReport {
    pub schema_version: String,
    pub rule_hard_cap_bytes: usize,
    pub total_artifacts: usize,
    pub root_rules: usize,
    pub skills: usize,
    pub artifacts: Vec<HarnessArtifactEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HarnessInstallFileAction {
    pub rel_path: String,
    pub artifact_id: String,
    pub action: String,
    pub bytes_written: usize,
    pub sha256: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HarnessRefusal {
    pub rel_path: String,
    pub kind: String,
    pub message: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HarnessInstallReport {
    pub repo_root: String,
    pub schema_version: String,
    pub installed_at: String,
    pub force: bool,
    pub passed: bool,
    pub files_written: usize,
    pub files_unchanged: usize,
    pub actions: Vec<HarnessInstallFileAction>,
    pub refusals: Vec<HarnessRefusal>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HarnessCheckIssue {
    pub rel_path: String,
    pub kind: String,
    pub message: String,
    pub remediation: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HarnessCheckedFile {
    pub rel_path: String,
    pub artifact_id: String,
    pub exists: bool,
    pub byte_len: usize,
    pub expanded_byte_len: usize,
    pub byte_budget: usize,
    pub marker_valid: bool,
    pub checksum_matches_template: bool,
    pub frontmatter_valid: Option<bool>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HarnessCheckReport {
    pub repo_root: String,
    pub schema_version: String,
    pub checked_at: String,
    pub passed: bool,
    pub checked_files: Vec<HarnessCheckedFile>,
    pub issues: Vec<HarnessCheckIssue>,
}

struct RenderedArtifact {
    artifact_id: String,
    kind: HarnessArtifactKind,
    rel_path: String,
    harnesses: Vec<&'static str>,
    skill_name: Option<&'static str>,
    description: Option<&'static str>,
    byte_budget: usize,
    body_sha256: String,
    full_content: String,
}

fn sha256_hex(input: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(input.as_bytes());
    hex::encode(hasher.finalize())
}

fn format_marker_line(artifact_id: &str, sha256: &str) -> String {
    format!(
        "{MARKER_PREFIX}{HARNESS_SCHEMA_VERSION} | id: {artifact_id} | sha256: {sha256}{MARKER_SUFFIX}"
    )
}

fn render_root_rule(
    rel_path: &str,
    artifact_id: &str,
    harnesses: Vec<&'static str>,
    byte_budget: usize,
    body: &str,
) -> RenderedArtifact {
    let clean_body = body.trim_matches('\n');
    let canonical_payload = format!("{clean_body}\n");
    let digest = sha256_hex(&canonical_payload);
    let marker = format_marker_line(artifact_id, &digest);
    let full_content = format!("{marker}\n{canonical_payload}");
    RenderedArtifact {
        artifact_id: artifact_id.to_string(),
        kind: HarnessArtifactKind::RootRule,
        rel_path: rel_path.to_string(),
        harnesses,
        skill_name: None,
        description: None,
        byte_budget,
        body_sha256: digest,
        full_content,
    }
}

fn render_skill_pair(
    skill_name: &'static str,
    description: &'static str,
    markdown_body: &str,
) -> Vec<RenderedArtifact> {
    let frontmatter = format!(
        "---\nname: {skill_name}\ndescription: >-\n  {}\n---",
        description.trim().replace('\n', "\n  ")
    );
    let clean_body = markdown_body.trim_matches('\n');
    let canonical_payload = format!("{frontmatter}\n{clean_body}\n");
    let digest = sha256_hex(&canonical_payload);
    let artifact_id = format!("skill:{skill_name}");
    let marker = format_marker_line(&artifact_id, &digest);
    // Keep YAML frontmatter strictly at byte 0 (`---\n...`) per `agy-customizations/docs/skills.md`!
    let full_content = format!("{frontmatter}\n{marker}\n{clean_body}\n");

    vec![
        RenderedArtifact {
            artifact_id: artifact_id.clone(),
            kind: HarnessArtifactKind::Skill,
            rel_path: format!(".agents/skills/{skill_name}/SKILL.md"),
            harnesses: vec!["antigravity", "codex"],
            skill_name: Some(skill_name),
            description: Some(description),
            byte_budget: RULE_FILE_HARD_CAP_BYTES,
            body_sha256: digest.clone(),
            full_content: full_content.clone(),
        },
        RenderedArtifact {
            artifact_id,
            kind: HarnessArtifactKind::Skill,
            rel_path: format!(".claude/skills/{skill_name}/SKILL.md"),
            harnesses: vec!["claude-code"],
            skill_name: Some(skill_name),
            description: Some(description),
            byte_budget: RULE_FILE_HARD_CAP_BYTES,
            body_sha256: digest,
            full_content,
        },
    ]
}

fn canonical_artifacts() -> Vec<RenderedArtifact> {
    let mut out = Vec::with_capacity(11);

    out.push(render_root_rule(
        "AGENTS.md",
        "rule:AGENTS.md",
        vec!["codex", "antigravity", "claude-code"],
        AGENTS_MD_BUDGET_BYTES,
        AGENTS_MD_BODY,
    ));
    out.push(render_root_rule(
        "GEMINI.md",
        "rule:GEMINI.md",
        vec!["antigravity"],
        POINTER_RULE_BUDGET_BYTES,
        GEMINI_MD_BODY,
    ));
    out.push(render_root_rule(
        "CLAUDE.md",
        "rule:CLAUDE.md",
        vec!["claude-code"],
        POINTER_RULE_BUDGET_BYTES,
        CLAUDE_MD_BODY,
    ));

    out.extend(render_skill_pair(
        "obend-anti-cosplay",
        SKILL_ANTI_COSPLAY_DESC,
        SKILL_ANTI_COSPLAY_BODY,
    ));
    out.extend(render_skill_pair(
        "obend-spec-exec-refinement",
        SKILL_SPEC_EXEC_DESC,
        SKILL_SPEC_EXEC_BODY,
    ));
    out.extend(render_skill_pair(
        "obend-proof-engineering",
        SKILL_PROOF_ENG_DESC,
        SKILL_PROOF_ENG_BODY,
    ));
    out.extend(render_skill_pair(
        "obend-trailblaze-promotion",
        SKILL_TRAILBLAZE_DESC,
        SKILL_TRAILBLAZE_BODY,
    ));

    out
}

/// List all canonical `obb harness` customization artifacts (`AGENTS.md`, `GEMINI.md`, `CLAUDE.md`,
/// and the 4 progressive-disclosure skills across `.agents/skills/` and `.claude/skills/`).
pub fn harness_list() -> HarnessListReport {
    let rendered = canonical_artifacts();
    let root_rules = rendered
        .iter()
        .filter(|a| a.kind == HarnessArtifactKind::RootRule)
        .count();
    let skills = rendered
        .iter()
        .filter(|a| a.kind == HarnessArtifactKind::Skill)
        .count();
    let artifacts = rendered
        .into_iter()
        .map(|a| HarnessArtifactEntry {
            artifact_id: a.artifact_id,
            kind: a.kind,
            rel_path: a.rel_path,
            harnesses: a.harnesses.into_iter().map(str::to_string).collect(),
            skill_name: a.skill_name.map(str::to_string),
            description: a.description.map(str::to_string),
            byte_len: a.full_content.len(),
            byte_budget: a.byte_budget,
            sha256: a.body_sha256,
        })
        .collect();

    HarnessListReport {
        schema_version: HARNESS_SCHEMA_VERSION.to_string(),
        rule_hard_cap_bytes: RULE_FILE_HARD_CAP_BYTES,
        total_artifacts: root_rules + skills,
        root_rules,
        skills,
        artifacts,
    }
}

fn has_obb_harness_marker(raw: &str) -> bool {
    raw.lines()
        .any(|l| l.trim().starts_with(MARKER_PREFIX) && l.trim().ends_with(MARKER_SUFFIX))
}

/// Materialize canonical `obb harness` rules and progressive-disclosure skills into `repo_root`.
/// Refuses to clobber pre-existing unmanaged files unless `force == true`.
pub fn harness_install(repo_root: &Path, force: bool) -> Result<HarnessInstallReport> {
    let canon = repo_root
        .canonicalize()
        .unwrap_or_else(|_| repo_root.to_path_buf());
    let rendered = canonical_artifacts();

    let mut refusals = Vec::new();
    if !force {
        for art in &rendered {
            let full_path = canon.join(&art.rel_path);
            if full_path.exists() {
                let existing = fs::read_to_string(&full_path).unwrap_or_default();
                if !has_obb_harness_marker(&existing) {
                    refusals.push(HarnessRefusal {
                        rel_path: art.rel_path.clone(),
                        kind: "unmanaged_existing_file".to_string(),
                        message: format!(
                            "`{}` exists without an `obb-harness` marker header; re-run with `--force` to overwrite",
                            art.rel_path
                        ),
                    });
                }
            }
        }
    }

    if !refusals.is_empty() {
        return Ok(HarnessInstallReport {
            repo_root: canon.to_string_lossy().to_string(),
            schema_version: HARNESS_SCHEMA_VERSION.to_string(),
            installed_at: Utc::now().to_rfc3339(),
            force,
            passed: false,
            files_written: 0,
            files_unchanged: 0,
            actions: Vec::new(),
            refusals,
        });
    }

    let mut files_written = 0usize;
    let mut files_unchanged = 0usize;
    let mut actions = Vec::with_capacity(rendered.len());

    for art in rendered {
        let full_path = canon.join(&art.rel_path);
        if let Some(parent) = full_path.parent() {
            fs::create_dir_all(parent)?;
        }
        let existing = fs::read_to_string(&full_path).ok();
        let action_label = if existing.as_deref() == Some(art.full_content.as_str()) {
            files_unchanged += 1;
            "unchanged"
        } else {
            let existed = existing.is_some();
            fs::write(&full_path, &art.full_content)?;
            files_written += 1;
            if existed { "updated" } else { "created" }
        };
        actions.push(HarnessInstallFileAction {
            rel_path: art.rel_path,
            artifact_id: art.artifact_id,
            action: action_label.to_string(),
            bytes_written: art.full_content.len(),
            sha256: art.body_sha256,
        });
    }

    Ok(HarnessInstallReport {
        repo_root: canon.to_string_lossy().to_string(),
        schema_version: HARNESS_SCHEMA_VERSION.to_string(),
        installed_at: Utc::now().to_rfc3339(),
        force,
        passed: true,
        files_written,
        files_unchanged,
        actions,
        refusals: Vec::new(),
    })
}

#[derive(Debug)]
struct ParsedMarker {
    version: String,
    artifact_id: String,
    sha256: String,
    payload_without_marker: String,
}

fn extract_marker_and_payload(raw: &str) -> Option<ParsedMarker> {
    let normalized = raw.replace("\r\n", "\n");
    let mut marker_info: Option<(String, String, String)> = None;
    let mut kept_lines: Vec<&str> = Vec::new();

    for line in normalized.lines() {
        let trimmed = line.trim();
        if marker_info.is_none()
            && let Some(inner) = trimmed
                .strip_prefix(MARKER_PREFIX)
                .and_then(|s| s.strip_suffix(MARKER_SUFFIX))
        {
            let parts: Vec<&str> = inner.split('|').map(str::trim).collect();
            if parts.len() == 3 {
                let ver = parts[0].to_string();
                let id = parts[1].strip_prefix("id:")?.trim().to_string();
                let sha = parts[2].strip_prefix("sha256:")?.trim().to_string();
                marker_info = Some((ver, id, sha));
                continue;
            }
        }
        kept_lines.push(line);
    }

    let (version, artifact_id, sha256) = marker_info?;
    let mut payload = kept_lines.join("\n");
    payload.push('\n');
    Some(ParsedMarker {
        version,
        artifact_id,
        sha256,
        payload_without_marker: payload,
    })
}

#[derive(Debug)]
struct ParsedSkillFrontmatter {
    name: String,
    description: String,
}

fn parse_skill_frontmatter(raw: &str) -> std::result::Result<ParsedSkillFrontmatter, String> {
    let normalized = raw.replace("\r\n", "\n");
    let Some(after_open) = normalized.strip_prefix("---\n") else {
        return Err("`SKILL.md` must begin at byte 0 with `---` YAML frontmatter".to_string());
    };
    let Some((yaml_block, _rest)) = after_open.split_once("\n---\n") else {
        return Err("`SKILL.md` YAML frontmatter is missing closing `---` delimiter".to_string());
    };

    let mut name: Option<String> = None;
    let mut desc_lines: Vec<String> = Vec::new();
    let mut in_desc_block = false;

    for line in yaml_block.lines() {
        if in_desc_block {
            if line.starts_with("  ") || line.trim().is_empty() {
                desc_lines.push(line.trim().to_string());
                continue;
            }
            in_desc_block = false;
        }
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("name:") {
            let val = rest.trim().trim_matches('"').trim_matches('\'').to_string();
            name = Some(val);
        } else if let Some(rest) = trimmed.strip_prefix("description:") {
            let val = rest.trim();
            if matches!(val, ">-" | ">" | "|-" | "|") || val.is_empty() {
                in_desc_block = true;
            } else {
                desc_lines.push(val.trim_matches('"').trim_matches('\'').to_string());
            }
        }
    }

    let skill_name = name
        .filter(|s| !s.is_empty())
        .ok_or_else(|| "YAML frontmatter missing required `name` field".to_string())?;
    if !skill_name
        .chars()
        .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
    {
        return Err(format!(
            "skill `name` (`{skill_name}`) must be lowercase and hyphenated"
        ));
    }

    let description = desc_lines
        .into_iter()
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>()
        .join(" ");
    if description.len() < 24 {
        return Err(
            "YAML frontmatter `description` must clearly explain what the skill does and when to activate it"
                .to_string(),
        );
    }
    let desc_low = description.to_ascii_lowercase();
    if desc_low.starts_with("i ")
        || desc_low.starts_with("i'm ")
        || desc_low.starts_with("we ")
        || desc_low.starts_with("you ")
    {
        return Err(
            "YAML frontmatter `description` must be written in third-person per `agy-customizations/docs/skills.md`"
                .to_string(),
        );
    }

    Ok(ParsedSkillFrontmatter {
        name: skill_name,
        description,
    })
}

/// Validate all 3 root rule files (`< 24,000` bytes each, including `@[AGENTS.md]` expansion)
/// and all 8 `.agents/skills/*/SKILL.md` + `.claude/skills/*/SKILL.md` files (YAML frontmatter,
/// marker headers, checksum integrity, and parity).
pub fn harness_check(repo_root: &Path) -> Result<HarnessCheckReport> {
    let canon = repo_root
        .canonicalize()
        .unwrap_or_else(|_| repo_root.to_path_buf());
    let rendered = canonical_artifacts();
    let mut checked_files = Vec::with_capacity(rendered.len());
    let mut issues = Vec::new();

    let agents_raw = fs::read_to_string(canon.join("AGENTS.md")).ok();
    let agents_len = agents_raw.as_ref().map(|s| s.len()).unwrap_or(0);

    for art in &rendered {
        let full_path = canon.join(&art.rel_path);
        let Ok(raw) = fs::read_to_string(&full_path) else {
            issues.push(HarnessCheckIssue {
                rel_path: art.rel_path.clone(),
                kind: "missing_file".to_string(),
                message: format!("Managed harness file `{}` is missing", art.rel_path),
                remediation: format!(
                    "Run `obb harness install --repo {}` to materialize `{}`.",
                    canon.display(),
                    art.rel_path
                ),
            });
            checked_files.push(HarnessCheckedFile {
                rel_path: art.rel_path.clone(),
                artifact_id: art.artifact_id.clone(),
                exists: false,
                byte_len: 0,
                expanded_byte_len: 0,
                byte_budget: art.byte_budget,
                marker_valid: false,
                checksum_matches_template: false,
                frontmatter_valid: art.skill_name.map(|_| false),
            });
            continue;
        };

        let byte_len = raw.len();
        let expanded_byte_len =
            if art.rel_path == "GEMINI.md" && raw.contains("@[AGENTS.md](./AGENTS.md)") {
                byte_len + agents_len
            } else {
                byte_len
            };

        // 1. Byte-ceiling checks (`< 24,000` hard rule cap + specific budget cap)
        if art.kind == HarnessArtifactKind::RootRule
            && expanded_byte_len >= RULE_FILE_HARD_CAP_BYTES
        {
            issues.push(HarnessCheckIssue {
                rel_path: art.rel_path.clone(),
                kind: "rule_hard_cap_exceeded".to_string(),
                message: format!(
                    "Rule file `{}` expands to {} bytes (>= {} byte Antigravity per-file cap)",
                    art.rel_path, expanded_byte_len, RULE_FILE_HARD_CAP_BYTES
                ),
                remediation: "Keep root rule files concise and push procedural runbooks into `.agents/skills/*/SKILL.md`.".to_string(),
            });
        }
        if byte_len >= art.byte_budget {
            issues.push(HarnessCheckIssue {
                rel_path: art.rel_path.clone(),
                kind: "byte_budget_exceeded".to_string(),
                message: format!(
                    "`{}` is {} bytes (>= {} byte budget)",
                    art.rel_path, byte_len, art.byte_budget
                ),
                remediation: format!(
                    "Re-run `obb harness install --repo {} --force` or trim `{}` under {} bytes.",
                    canon.display(),
                    art.rel_path,
                    art.byte_budget
                ),
            });
        }

        // 2. Root-rule structural checks vs Skill YAML frontmatter checks
        let mut frontmatter_valid = None;
        match art.kind {
            HarnessArtifactKind::RootRule => {
                if raw.trim_start().starts_with("---") {
                    issues.push(HarnessCheckIssue {
                        rel_path: art.rel_path.clone(),
                        kind: "forbidden_rule_frontmatter".to_string(),
                        message: format!(
                            "Standalone root rule `{}` must not start with YAML frontmatter (`---`)",
                            art.rel_path
                        ),
                        remediation: "Remove YAML frontmatter from standalone `AGENTS.md`/`GEMINI.md`/`CLAUDE.md` rule files.".to_string(),
                    });
                }
                if art.rel_path == "GEMINI.md" && !raw.contains("@[AGENTS.md](./AGENTS.md)") {
                    issues.push(HarnessCheckIssue {
                        rel_path: art.rel_path.clone(),
                        kind: "missing_agents_include".to_string(),
                        message: "`GEMINI.md` does not reference `@[AGENTS.md](./AGENTS.md)`"
                            .to_string(),
                        remediation: "Reference `@[AGENTS.md](./AGENTS.md)` in `GEMINI.md` rather than duplicating `AGENTS.md`.".to_string(),
                    });
                }
                if art.rel_path == "CLAUDE.md" && !raw.contains("@AGENTS.md") {
                    issues.push(HarnessCheckIssue {
                        rel_path: art.rel_path.clone(),
                        kind: "missing_agents_include".to_string(),
                        message: "`CLAUDE.md` does not reference `@AGENTS.md`".to_string(),
                        remediation: "Reference `@AGENTS.md` in `CLAUDE.md` rather than duplicating `AGENTS.md`.".to_string(),
                    });
                }
            }
            HarnessArtifactKind::Skill => {
                let expected_skill = art.skill_name.unwrap_or("");
                match parse_skill_frontmatter(&raw) {
                    Ok(fm) => {
                        if fm.name != expected_skill {
                            frontmatter_valid = Some(false);
                            issues.push(HarnessCheckIssue {
                                rel_path: art.rel_path.clone(),
                                kind: "skill_name_mismatch".to_string(),
                                message: format!(
                                    "`{}` frontmatter `name: {}` does not match directory `{expected_skill}`",
                                    art.rel_path, fm.name
                                ),
                                remediation: format!(
                                    "Set `name: {expected_skill}` in `{}`.",
                                    art.rel_path
                                ),
                            });
                        } else {
                            let _ = fm.description;
                            frontmatter_valid = Some(true);
                        }
                    }
                    Err(err_msg) => {
                        frontmatter_valid = Some(false);
                        issues.push(HarnessCheckIssue {
                            rel_path: art.rel_path.clone(),
                            kind: "invalid_skill_frontmatter".to_string(),
                            message: format!("`{}`: {err_msg}", art.rel_path),
                            remediation: format!(
                                "Restore valid `name` + third-person `description` YAML frontmatter via `obb harness install --repo {} --force`.",
                                canon.display()
                            ),
                        });
                    }
                }
            }
        }

        // 3. Marker header + SHA-256 body checksum + template drift verification
        let mut marker_valid = false;
        let mut checksum_matches_template = false;
        match extract_marker_and_payload(&raw) {
            None => {
                issues.push(HarnessCheckIssue {
                    rel_path: art.rel_path.clone(),
                    kind: "missing_marker_header".to_string(),
                    message: format!(
                        "`{}` is missing the `<!-- obb-harness: ... -->` integrity header",
                        art.rel_path
                    ),
                    remediation: format!(
                        "Run `obb harness install --repo {} --force`.",
                        canon.display()
                    ),
                });
            }
            Some(pm) => {
                let actual_sha = sha256_hex(&pm.payload_without_marker);
                if pm.version != HARNESS_SCHEMA_VERSION {
                    issues.push(HarnessCheckIssue {
                        rel_path: art.rel_path.clone(),
                        kind: "schema_version_drift".to_string(),
                        message: format!(
                            "`{}` has harness schema `{}` (expected `{HARNESS_SCHEMA_VERSION}`)",
                            art.rel_path, pm.version
                        ),
                        remediation: format!(
                            "Run `obb harness install --repo {}` to upgrade to `{HARNESS_SCHEMA_VERSION}`.",
                            canon.display()
                        ),
                    });
                } else if pm.artifact_id != art.artifact_id {
                    issues.push(HarnessCheckIssue {
                        rel_path: art.rel_path.clone(),
                        kind: "marker_id_mismatch".to_string(),
                        message: format!(
                            "`{}` marker id is `{}` (expected `{}`)",
                            art.rel_path, pm.artifact_id, art.artifact_id
                        ),
                        remediation: format!(
                            "Run `obb harness install --repo {} --force`.",
                            canon.display()
                        ),
                    });
                } else if pm.sha256 != actual_sha {
                    issues.push(HarnessCheckIssue {
                        rel_path: art.rel_path.clone(),
                        kind: "checksum_mismatch".to_string(),
                        message: format!(
                            "`{}` was modified outside `obb harness` (header sha256 `{}...` != actual `{}...`)",
                            art.rel_path,
                            &pm.sha256[..pm.sha256.len().min(12)],
                            &actual_sha[..12]
                        ),
                        remediation: format!(
                            "Update canonical templates in `obebuilder` or re-sync via `obb harness install --repo {} --force`.",
                            canon.display()
                        ),
                    });
                } else {
                    marker_valid = true;
                    if actual_sha == art.body_sha256 {
                        checksum_matches_template = true;
                    } else {
                        issues.push(HarnessCheckIssue {
                            rel_path: art.rel_path.clone(),
                            kind: "template_drift".to_string(),
                            message: format!(
                                "`{}` checksum (`{}...`) has drifted from current `obb harness` `{HARNESS_SCHEMA_VERSION}` template (`{}...`)",
                                art.rel_path,
                                &actual_sha[..12],
                                &art.body_sha256[..12]
                            ),
                            remediation: format!(
                                "Run `obb harness install --repo {}` to refresh drifted harness files.",
                                canon.display()
                            ),
                        });
                    }
                }
            }
        }

        checked_files.push(HarnessCheckedFile {
            rel_path: art.rel_path.clone(),
            artifact_id: art.artifact_id.clone(),
            exists: true,
            byte_len,
            expanded_byte_len,
            byte_budget: art.byte_budget,
            marker_valid,
            checksum_matches_template,
            frontmatter_valid,
        });
    }

    Ok(HarnessCheckReport {
        repo_root: canon.to_string_lossy().to_string(),
        schema_version: HARNESS_SCHEMA_VERSION.to_string(),
        checked_at: Utc::now().to_rfc3339(),
        passed: issues.is_empty(),
        checked_files,
        issues,
    })
}

// ============================================================================
// Canonical Root Rule Templates (`AGENTS.md`, `GEMINI.md`, `CLAUDE.md`)
// ============================================================================

const AGENTS_MD_BODY: &str = r#"# Obend Canonical Agent Engineering Rules (`AGENTS.md`)

Shared always-on engineering constitution for Codex, Antigravity, and Claude Code. Keep all edits aligned with every invariant below without exception.

## 1. Hard Remote-Only Build & Verification Rule (Zero macOS Builds)

- **NEVER execute `lake`, `lean`, `cargo`, `rustc`, or `Holmake` on macOS.** Local workstation CPUs and memory must never run Lean elaboration, Rust builds, or proof search.
- Execute **all** Lean 4.35, Rust, GPU, and RTL/HDL builds and tests remotely on `bb2` or `hbox` under hard memory and wall-clock caps (`SWARM_MEM_MAX=12G`, `timeout --kill-after=10s 600s`):
  ```bash
  obb broker probe --hosts bb2,hbox
  obb broker plan-build Obend.Trailblaze.CathedralApex --repo . --host bb2 --max-rss-gb 12 --timeout-secs 600 --exec
  ```
- When running direct SSH verification against a remote worktree on `bb2`, always wrap invocations in `SWARM_MEM_MAX=12G timeout --kill-after=10s 600s`.

## 2. Scar-Free In-Place Architecture (`AMBITION.md:62`)

- ***"Nothing lands beside; everything replaces."***
- Never introduce `*V2.lean`, `*New.lean`, `Mock*.lean`, `Golden*.lean`, `*Poles.lean`, or parallel wrapper structs to avoid repairing a broken carrier, compiler pass, or theorem.
- Upgrade flawed definitions **in place**, update every downstream caller across the import cone, and delete superseded scaffolding in the same commit.
- Maintain **zero retired-subsystem fossils** and **zero `.obb/` or `ledger/` state pollution** inside `Obend` git worktrees.

## 3. Kernel Soundness & Lean 4.35 Module Encapsulation (`LAW-M1`, `LAW-M2`)

- **Zero Trust Bypasses:**
  - `0 sorry` / `0 sorryAx` anywhere in the repository.
  - `0` custom `axiom` declarations.
  - `0 native_decide`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, or `Lean.trustCompiler` in `lean/Obend/` library modules (`lean/native-decide-in-proof`).
  - `0 Classical.choice` in `Type`-valued computational extractors (branch constructively via `DecidableEq` / `PSum`).
- **`LAW-M1` Module Encapsulation:**
  - Every `.lean` file in `Obend/` begins with `module` and uses `public section` for exported signatures.
  - **Never** place `@[expose] public section` at top level in files `> 80` lines (`lean/file-wide-expose`).
  - **Never** exceed `12` per-declaration `@[expose]` attributes in a `> 80`-line `module` file (`lean/excessive-decl-expose`). Seal recursive/operational bodies inside `.olean.private` and export equational or soundness theorems (`*_eq`, `*_sound`) instead.
- **`LAW-M2` Meta-Import Hygiene:**
  - Restrict `public meta import Lean` strictly to `lean/Obend/Tactic/` and `lean/Obend/Elab/` (`lean/public-meta-import-leak`).

## 4. Anti-Cosplay & `Spec ↔ Exec` Data-Refinement Mandates

- **Stage-A `*Obligations` Honesty (`lean/obligation-tautological-field`):**
  - Never write tautological Stage-A obligation signatures (`P → Q → P ∧ Q`, `a = b → f a = f b`, `(φ.meet ψ).implies φ = true`, unused quantified binders, non-existential `*Extract` fields, or trivial `> 0` bounds under `Gkr`/`ZeroKnowledge`/`Attested`/`Refines`/`IsaEquiv` names).
  - Before locking any commitment-binding obligation (`digest H t₁ = digest H t₂ → t₁ = t₂ ∨ Collision H`), verify that **every** field of `t` is length-framed (`frameBytes`) in the preimage; omitting even one field makes Stage-B literally `False`.
- **Stage-B Instance Honesty (`lean/obligation-projection-cosplay`):**
  - Never discharge `*Obligations` or `*Ledger` instances via 1–3 line `rfl`, `congrArg`, `Bool.and_eq_true`, `And.left`/`And.right`, `fun _ => trivial`, or trivial carriers (`Unit`, `Bool`, `Nat`).
- **Inhabited `Judge` Completeness & Refusal (`lean/judge-empty-fragment`):**
  - Never set `Fragment := fun _ => False` or `refutes := fun _ => false` inside `Obend.Judge` instances or builders (`SilverWorkflow.toJudge`), and never restate `check` inside `Meaning` (`lean/tautological-judge-meaning`).
- **Environment Anti-Narrowing & Multi-Turn Completeness (`lean/single-sequence-harness`):**
  - Never claim apex protocol safety from a single-turn theorem (`apex_*_turn_safe` / `apex_*_turn_sound`) without a multi-turn trace/reachability invariant (`List *Turn`, `Reach`, `SafeWP`, `ValidTrace`, `MultiTurnHoare`) covering state accumulation (`RevokedSet` growth, `Mandate` budget depletion, persistent `UMem`), and pair open-world environment filters with completeness theorems (`skip_implies_contract_violation` / multi-handle reachability).
- **Full-Width Cryptographic Carriers & `Spec ↔ Exec` Efficiency:**
  - Ban `Nat` digests and `≤ 64`-bit scalar digest stand-ins (`lean/narrow-digest-weld`); use 256-bit carriers (`BitVec 256`, 32-byte `ByteArray`, or 4×`UInt64`).
  - Pair clean inductive/`List` `Spec` definitions with $O(N)$ / $O(N \log N)$ `ByteArray`, `Array UInt64`, `Array`, and `BitVec` `Exec` implementations connected by proved refinement theorems (`Simulates`, `@[csimp]`, `*_exec_eq_*`).

## 5. Mandatory Pre-Landing Verification Gates

Run all mechanical gates before landing or promoting any slice:

```bash
obb lint --repo <repo> --strict --strict-expose --strict-harnesses
obb cone --repo <repo>
obb pipeline check --repo <repo> --strict
obb apex check --repo <repo>
obb harness check --repo <repo>
```

Every load-bearing checker and soundness theorem must be paired with `#tooth` mutation-sensitivity witnesses and inhabitedness witnesses (`lean/uninhabited-premise-risk`).

## 6. Progressive-Disclosure Skills (Load On Demand)

Activate the dedicated runbooks under `.agents/skills/<name>/SKILL.md` (and `.claude/skills/<name>/SKILL.md`) when working in their domain:

1. **`obend-anti-cosplay`**: Field guide to the **10 Mistakes Models Like to Make** in `Obend` + `#tooth` / `#audit_claim_contract` verification runbook.
2. **`obend-spec-exec-refinement`**: Verified `Spec ↔ Exec` playbook (`ByteArray`, unboxed `Array UInt64`, `BitVec`, sorted binary-search & linear merge-scan arrays, `Simulates`, `@[csimp]`).
3. **`obend-proof-engineering`**: Lean 4.35 `LAW-M1` encapsulation, `0 Classical` `PSum` extractors, `termination_by structural` WHNF discipline, `GPaco`/`MultiTurnHoare`, remote `bb2`/`hbox` builds.
4. **`obend-trailblaze-promotion`**: Stage-A (`*Obligations`) $\to$ Stage-B (`0` open obligations) promotion runbook, pre-lock `Collision H` injectivity proofs, and `quarry/obend-apex.toml` wiring.
"#;

const GEMINI_MD_BODY: &str = r#"# Antigravity Workspace Configuration (`GEMINI.md`)

@[AGENTS.md](./AGENTS.md)

## Antigravity Progressive-Disclosure Skills (`.agents/skills/`)

Do not inline bulky runbooks into conversation turns; activate the matching workspace skill on demand:

| Skill | Activate When |
| :--- | :--- |
| `obend-anti-cosplay` | Designing or auditing `*Obligations` classes, `Judge` instances, Merkle/hash commitments, hardware structs, string-aware lexers, or AST compilers. |
| `obend-spec-exec-refinement` | Pairing `List`/inductive `Spec` models with `ByteArray`, `Array UInt64`, `BitVec`, sorted binary-search / merge-scan arrays, `Simulates`, or `@[csimp]`. |
| `obend-proof-engineering` | Fixing `LAW-M1` `@[expose]` bloat, eliminating `Classical.choice`, avoiding `WellFounded.fix` WHNF blowups, writing `#tooth` witnesses, or batching remote `bb2`/`hbox` builds. |
| `obend-trailblaze-promotion` | Promoting a Stage-A `Trailblaze` organ to Stage-B (`0` open obligations) and registering apex theorems in `quarry/obend-apex.toml`. |

## Multi-Agent Worktree & Swarm Discipline

- Partition parallel write lanes up front with `obb cone --repo . plan --propose <lane>=<files...>` so concurrent workers never contend on `public_fan_in > 25` hub headers.
- Isolate concurrent edits in `scratch/worktrees/<lane>` synced to `/home/build/obend/wt-<lane>` on `bb2`; never run `lake`, `lean`, `cargo`, `rustc`, or `Holmake` on macOS.
"#;

const CLAUDE_MD_BODY: &str = r#"# Claude Code Deputy Configuration (`CLAUDE.md`)

@AGENTS.md

## Claude Code Skills Index (`.claude/skills/`)

Read the relevant `SKILL.md` before editing Lean specs, runtime data structures, or Stage-A/Stage-B obligations:

- `.claude/skills/obend-anti-cosplay/SKILL.md` — **10 Mistakes Models Like to Make** & `obb lint --strict --strict-expose` audit gates.
- `.claude/skills/obend-spec-exec-refinement/SKILL.md` — `Spec ↔ Exec` refinement (`ByteArray`, `Array UInt64`, `BitVec`, sorted binary-search / $O(N)$ merge-scans, `Simulates`, `@[csimp]`).
- `.claude/skills/obend-proof-engineering/SKILL.md` — Lean 4.35 `module` encapsulation (`≤ 12` `@[expose]`), `0 Classical` `PSum` extractors, structural WHNF recursion, `#tooth`, `GPaco`, remote `bb2`/`hbox` broker builds.
- `.claude/skills/obend-trailblaze-promotion/SKILL.md` — Stage-A $\to$ Stage-B promotion workflow, pre-lock `Collision H` preimage injectivity, and `quarry/obend-apex.toml` registration.

## Deputy Execution Rules

1. **Zero Local Builds:** Never run `lake`, `lean`, `cargo`, `rustc`, or `Holmake` on macOS; execute all builds on `bb2` or `hbox` with `SWARM_MEM_MAX=12G` and `timeout --kill-after=10s 600s`.
2. **Never Weaken Specs to Close Goals:** Do not weaken theorem conclusions, shrink `Judge.Fragment` to `False`, set `refutes := false`, or spray `@[expose]` across `module` definitions to appease tactics.
3. **Pre-Report Gate:** Run `obb lint --repo <worktree> --strict --strict-expose` and remote `lake build` before reporting any slice ready.
"#;

// ============================================================================
// Skill 1: `obend-anti-cosplay`
// ============================================================================

const SKILL_ANTI_COSPLAY_DESC: &str = "Identifies and eliminates the 10 formal-verification cosplay failure modes in Obend Lean 4 modules. Use this skill when authoring or auditing Stage-A *Obligations classes, Judge instances, cryptographic commitments, hardware structs, stateful lexers, runtime data structures, or compiler passes.";

const SKILL_ANTI_COSPLAY_BODY: &str = r#"# Obend Anti-Cosplay Field Guide: 10 Mistakes Models Like to Make

Every failure mode below arises when optimizing for surface compilation instead of genuine mathematical or operational content. Treat all 10 as hard blockers in `Obend`.

## The 10 Mistakes Models Like to Make

### 1. Tautological Stage-A `*Obligations` Fields (`lean/obligation-tautological-field`)
- **Failure Mode:** Writing placeholder propositions inside `class *Obligations : Prop` that sound ambitious in identifiers/docstrings while stating propositional tautologies or micro-bounds:
  - Equality congruence: `sameOpeningZeroKnowledge : ∀ (commitA commitB : BitVec 256), commitA = commitB → commitA.toNat = commitB.toNat`.
  - Conjunction repackaging: `teeHardwareRootAttested : ∀ step, step.flopsUsed ≤ step.flopsCap → step.batchCallTreeRoot ≠ 0 → step.flopsUsed ≤ step.flopsCap ∧ step.batchCallTreeRoot ≠ 0` (`P → Q → P ∧ Q`).
  - Lattice meet elimination: `siliconSimpKernelProofSound : ∀ (φ ψ : CofibLUT16), (φ.meet ψ).implies φ = true`.
  - Scalar `> 0` consequence under a `Gkr`/`ZeroKnowledge`/`Attested`/`IsaEquiv` name: `kernelArithmeticGkrSound : ∀ b, checkNoWrap b = true → b.modulusP > 0`.
  - Non-existential `*Extract` fields that universally quantify the witness (`∀ tree, verify tree = true → ...`) instead of extracting `∃ tree, ...`.
- **Fix:** Prove trivial algebraic facts directly as ordinary lemmas (never open obligations), and state the exact semantic, ISA, or cryptographic soundness/extraction statement in `*Obligations`.

### 2. Dropped-Field Commitments Making Stage-B Injectivity `False`
- **Failure Mode:** Omitting a structural field from a hash preimage (`HttpsSessionNode.serverDomain` dropped in `callTreeDigestBytes`) while locking Stage-A `callTreeDigest H t₁ = callTreeDigest H t₂ → t₁ = t₂ ∨ Collision H`. Two nodes differing only in `serverDomain` have **identical** preimages (`pre₁ = pre₂`), so `Collision H` (`pre₁ ≠ pre₂ ∧ H pre₁ = H pre₂`) is `False` AND `t₁ = t₂` is `False` — rendering Stage B mathematically uninhabitable.
- **Fix:** Length-frame **every** constructor tag and payload field (`frameBytes domain.toUTF8.toList` with canonical `< 2^32` / `< 2^64` width guards) and constructively prove `callTreeDigestBytes_binding` (`if hPre : pre₁ = pre₂` on `List UInt8`, `0 Classical`) *before* sealing Stage A.

### 3. Domain-Collapse Encodings (`∂𝕀 = 𝕀`)
- **Failure Mode:** Modeling cubical cofibration face lattices as 4-variable Boolean truth tables (`CofibLUT16` over `BitVec 16`, `{0,1}^4`), where `(varEq0 v).join (varEq1 v) = top` collapses the boundary `(i = 0) ∨ (i = 1)` onto the entire interval (`∂𝕀 = 𝕀`).
- **Fix:** Encode cubical face ideals over the 3-element partial cube `{0, 1, *}^3` (`FaceIdeal3` as `BitVec 27`, mapping `(p₀, p₁, p₂) : Fin 3 × Fin 3 × Fin 3` to `p₀ + 3*p₁ + 9*p₂` with interior `(2,2,2)` at bit `26`), and prove `(varEq0 v).join (varEq1 v) ≠ top` + `#tooth`.

### 4. Host-Ghost Fields Smuggled into Hardware Structs
- **Failure Mode:** Embedding unbounded Lean host heap types inside synthesizable hardware structures (e.g., `CamSlotEntry.expr : KExpr` alongside a 64-bit `CamWord64`, 1-character symbol hashes colliding `"a"` and `"b"`, or quadratic pairing encodings overflowing 64 bits at 181 nodes).
- **Fix:** Keep hardware carrier structs (`CamSlotEntry`, `TileConfig`, `DprSlot`) strictly fixed-width (`BitVec`, `UInt64`, bounded `Fin`) and relate them to host `KExpr` syntax via an external simulation/indexing table.

### 5. `False ∨ False` Cryptographic Reduction Vacuity & Narrow Welds
- **Failure Mode:** Discharging dual-assumption cryptographic reductions (`HashBinding ∨ LatticeHardness`) where uninhabited parameters collapse both branches, or comparing only limb `0` (`digest[0] == expected[0]`, `≤ 64`-bit scalar stand-in, `lean/narrow-digest-weld`).
- **Fix:** Bind full 256-bit commitments (`BitVec 256`, 32-byte `ByteArray`, or all 4×`UInt64` limbs) and accompany every reduction hypothesis with a constructive inhabitedness witness (`lean/uninhabited-premise-risk`).

### 6. Unbound Fiat-Shamir Public Instances
- **Failure Mode:** Computing Fiat-Shamir challenges from prover round commitments alone without absorbing the domain separator and complete length-framed public statement/instance into the transcript sponge.
- **Fix:** Absorb protocol domain tag + length-framed public statement + prior round commitments into the transcript state before squeezing every verifier challenge.

### 7. `Fragment := False` / `refutes := false` Judge Evasion (`lean/judge-empty-fragment`)
- **Failure Mode:** Implementing `Obend.Judge` (`SilverWorkflow.toJudge`) with `Fragment := fun _ => False` and `refutes := fun _ => false` so `complete` and `refuted` discharge by `cases` without proving completeness or refusal soundness on any input.
- **Fix:** Equip workflows with an inhabited `DecidableFragment : W → Prop` and `silverComplete : ∀ w, DecidableFragment w → Spec w → runValid w = true`, setting `Fragment := DecidableFragment` and `refutes := fun _ => true`.

### 8. Stateless Lexer / String-Escape Boundary Smuggling
- **Failure Mode:** Scanning raw `{`, `}`, `[`, `]` bytes in `lexJsonVpaSymbols` without string/escape state, falsely rejecting valid `{"note":"unmatched } inside string"}` and accepting malformed `{"bad":"\"}"}` where `\"` smuggles an unclosed string past structural framing.
- **Fix:** Track explicit `(inString : Bool, escaped : Bool)` state in both `Spec` (`List UInt8`) and `Exec` (`ByteArray`) lexers, and lock behavior with positive + negative `#tooth` witnesses.

### 9. $O(N^2)$ Linked-List Runtime Representations Without `Spec ↔ Exec`
- **Failure Mode:** Running quadratic `List.filter` multiset equality (`List MemOp`) or boxed `List Int` inner products on hot runtime audit paths.
- **Fix:** Keep `List` definitions as the `Spec` layer and pair them with $O(N)$ / $O(N \log N)$ `Array` / `ByteArray` `Exec` checkers (`checkSortedBagEqExec`, `intDotExec`, sorted binary-search tables) + proved `Spec ↔ Exec` equivalence.

### 10. Summary-Stub Compilers & Frame-Escape Blind Spots
- **Failure Mode:** Writing a "lowering" function (`lowerBookSummaryToDeltaNet`) that counts declaration headers and emits a static 2-node stub while ignoring `Obend.Leaf.Expr` AST bodies, or computing `LeafDef.reads` without a `NoEscapingSelf` guard rejecting bare `LeafExpr.var "self"`.
- **Fix:** Structurally compile every AST constructor (`nat`, `var`, `app`, `letE`, projections), wire bound variables linearly (`era` for 0 uses, `replicator` trees for $>1$ uses), and enforce syntactic non-escape guards in frame theorems.

## Precondition Narrowing / Bug-Steering & Single-Turn Harnesses (`lean/single-sequence-harness`)

- **Single-Turn Reset Blindness:** Proving `theorem apex_*_turn_safe` or `theorem apex_*_turn_sound` over a single `*Turn` carrier leaves multi-turn state-accumulation hazards completely unverified — growing `RevokedSet` tables, depleting `Mandate` budgets, and persistent `UMem` aliasing only manifest across arbitrary turn sequences. Always pair step lemmas with a multi-turn trace/reachability invariant (`List *Turn`, `Reach`, `SafeWP`, `ValidTrace`, or `MultiTurnHoare`) in the same module; `obb lint --strict-harnesses` and `obb apex check` reject isolated single-turn apex theorems.
- **Precondition Narrowing & Bug-Steering:** Never "close" an open-world environment harness by tightening transition filters to silently skip states where bugs trigger, or by restricting resource handles to singleton instances. Every open-world environment filter/harness must pair safety with an explicit **environment completeness theorem** (`skip_implies_contract_violation` and multi-handle reachability), proving that any skipped/rejected step genuinely violates the external caller contract and that distinct concurrent handles remain reachable.

## Verification Runbook

1. Run static anti-cosplay, harness-completeness & encapsulation lints locally (read-only Rust binary, zero Lean invocation):
   `obb lint --repo <repo> --strict --strict-expose --strict-harnesses`
2. Verify Stage-A / Stage-B obligation pipeline discipline and multi-turn apex wiring:
   `obb pipeline check --repo <repo> --strict && obb apex check --repo <repo>`
3. Verify `#tooth` mutation sensitivity and `#audit_claim_contract` / `#print axioms` remotely on `bb2`:
   `obb broker plan-build <Module> --repo <repo> --host bb2 --max-rss-gb 12 --timeout-secs 600 --exec`
"#;

// ============================================================================
// Skill 2: `obend-spec-exec-refinement`
// ============================================================================

const SKILL_SPEC_EXEC_DESC: &str = "Guides verified Spec-to-Exec data and algorithmic refinement in Obend Lean 4 modules. Use this skill when pairing inductive or List specifications with unboxed ByteArray, Array UInt64, BitVec, sorted binary-search or merge-scan arrays, Simulates relations, or @[csimp] theorems.";

const SKILL_SPEC_EXEC_BODY: &str = r#"# Obend `Spec ↔ Exec` Verified Efficiency Playbook

In `Obend`, proofs reason over clean inductive structures while runtime verifiers execute unboxed $O(N)$ / $O(N \log N)$ loops. Never sacrifice proof clarity for array index arithmetic, and never ship quadratic `List` traversals or `Nat` digests on hot runtime paths.

## 1. Canonical Two-Tier Carrier Pairing

| Domain Object | `Spec` Carrier (Proof-Friendly) | `Exec` Carrier (Unboxed Runtime) | Bridge Theorem |
| :--- | :--- | :--- | :--- |
| Wire / JSON / HTTP payloads | `List UInt8` | `ByteArray` | `(lexExec bs).toList = lexSpec bs.toList` |
| 256-bit Merkle / AEAD digests | `List UInt8` (len 32) / `BitVec 256` | `BitVec 256` / `ByteArray` / `Array UInt64` (size 4) | `toBytes_inj` + `Collision H` |
| Cubical 3-cube face ideals | `Fin 3 → Fin 3 → Fin 3 → Bool` | `BitVec 27` (`FaceIdeal3`) + dual-tile `BitVec 16 × BitVec 16` | `decode_encode` + `eval_eq` |
| Offline/online memory logs | `List MemOp` (`countMemOp`) | Sorted `Array MemOp` (`checkSortedBagEqExec`) | `verifyMemoryExec_sound` |
| Static key / capability tables | `List (Key × Val)` (`List.lookup`) | Sorted `Array (Key × Val)` (binary search) | `binSearch_eq_lookup` (under `Pairwise (· < ·)`) |
| Exact integer / fixed-point dot products | `List Int` (`intDot`, `sliceSum`) | `Array Int` / unboxed `Array UInt64` (`intDotExec`) | `intDotExec_eq_intDot` |

## 2. Sorted Binary Search & Linear Merge-Scan Over $O(N^2)$ `List.filter`

- **Multiset / Permutation Bag Checks:** Never run `List.filter` per element ($O(N^2)$). Define `countMemOp (target : MemOp) (log : List MemOp) : Nat` as the `Spec` multiplicity function, sort `(addr, timestamp)` into `Array MemOp` in $O(N \log N)$, and verify equality in a single $O(N)$ merge-scan (`checkSortedBagEqExec`) paired with `checkSortedBagEqExec a b = true → ∀ op, countMemOp op a.toList = countMemOp op b.toList`.
- **Dictionary / Allowlist Lookups:** Store static routing, capability, or symbol tables in strictly sorted `Array`s checked once for strict monotonicity (`isStrictlySorted arr = true`), then execute $O(\log N)$ binary search proven equivalent to `Spec` `List.lookup`.

## 3. Canonical Length-Prefixed Byte Framing

Never concatenate variable-length fields directly (`req ++ resp`) inside commitments. Always frame variable-width slices with explicit big-endian length prefixes and canonical width bounds:

```lean
def frameBytes (xs : List UInt8) : List UInt8 :=
  be 4 xs.length ++ xs
```

Pair `frameBytes` with `frameBytes_append_inj` (`xs₁.length < 2^32 → xs₂.length < 2^32 → frameBytes xs₁ ++ rest₁ = frameBytes xs₂ ++ rest₂ → xs₁ = xs₂ ∧ rest₁ = rest₂`) so composite Merkle preimages decompose deterministically.

## 4. `Simulates` & `@[csimp]` Wiring

- **Same-Type Fast Replacement (`@[csimp]`):** When `specFn : α → β` and `execFn : α → β` share identical signatures, prove `@[csimp] theorem specFn_eq_execFn : @specFn = @execFn` so compiled executables invoke `execFn` automatically while kernel proofs unfold `specFn`.
- **Refined-Carrier Simulation (`Simulates`):** When `Exec` changes representation (`ByteArray` vs `List UInt8`, `Array UInt64` vs `List Nat`), define an explicit abstraction map `α_abs : ExecState → SpecState` (or `Simulates : SpecMachine → ExecMachine → Prop`) and prove step/acceptance commutation:
  `α_abs (stepExec s) = stepSpec (α_abs s)` and `acceptExec s = acceptSpec (α_abs s)`.

## 5. Validation Checklist

1. Confirm zero narrow-digest or `Nat` digest regressions: `obb lint --repo <repo> --rule lean/narrow-digest-weld --strict`.
2. Confirm `Exec` helpers stay encapsulated behind `public section` (`≤ 12` `@[expose]` per file): `obb lint --repo <repo> --strict --strict-expose`.
3. Build and test equivalence theorems remotely on `bb2` (`SWARM_MEM_MAX=12G`, `timeout 600s`).
"#;

// ============================================================================
// Skill 3: `obend-proof-engineering`
// ============================================================================

const SKILL_PROOF_ENG_DESC: &str = "Provides Lean 4.35 proof-engineering patterns for Obend: LAW-M1 module encapsulation, 0-Classical PSum extractors, structural WHNF recursion, #tooth mutation guards, GPaco/MultiTurnHoare coinduction, and remote bb2/hbox broker builds. Use this skill when writing or debugging Lean 4 proofs and module headers.";

const SKILL_PROOF_ENG_BODY: &str = r#"# Obend Lean 4.35 Proof Engineering Runbook

## 1. `LAW-M1` Module Encapsulation & `@[expose]` Discipline

Every `Obend/` module uses Lean 4.35's `module` system to isolate `.olean.private` implementation bodies from public `.olean` headers:

```lean
module
public import Obend.Judge.Class
import Obend.Core.InternalLemmas  -- private import: zero downstream cone leakage!

public section
namespace Obend.Subsystem
set_option autoImplicit false
```

- **Hard Caps:** Never use `@[expose] public section` in files `> 80` lines (`lean/file-wide-expose`), and keep per-declaration `@[expose]` attributes `≤ 12` per file (`lean/excessive-decl-expose`).
- **How to Drop `@[expose]` Without Breaking Callers:**
  - Keep carrier `inductive` / `structure` / `class` declarations in `public section` (their constructors/projections remain accessible without `@[expose]` on function defs).
  - Seal operational functions (`audit*`, `verify*`, `compile*`) without `@[expose]`, and export crisp `theorem` contracts (`verifyFoo_iff`, `auditFoo_sound`).
  - For smoke vectors, prefer `by decide` in `tests/` or keep at most 1–2 tiny fixture constants exposed if kernel `rfl` tests in another module require definitional unfolding.

## 2. `0 Classical` Constructive Proofs & `PSum` Extractors

Never pull `Classical.choice` or `Classical.em` into `Type`-valued extractors or kernel security theorems:
- When a `Prop` disjunction `t₁ = t₂ ∨ Collision H` is proved from `H pre₁ = H pre₂`, branch constructively using `DecidableEq` on `List UInt8` / `ByteArray`:
  ```lean
  if hPre : pre₁ = pre₂ then
    exact Or.inl (preimage_injective hCan₁ hCan₂ hPre)
  else
    exact Or.inr ⟨pre₁, pre₂, hPre, hHashEq⟩
  ```
  This constructs `Collision H` with **zero `Classical` axioms**.
- For computational witness/refusal extractors in `Type`, return `PSum Witness (RefusalClause × Trace)` or `Except Refusal Witness` paired with bidirectional soundness/refusal theorems.

## 3. Structural Recursion vs `WellFounded.fix` Kernel WHNF Traps

- On nested mutual inductives (`inductive HttpsSessionNode | mk ... (children : List HttpsSessionNode)`), **always** annotate mutual traversals with `termination_by structural n` / `termination_by structural ns`.
- Omitting `structural` causes Lean to compile via `WellFounded.fix` over `sizeOf` (which traverses `String` byte lists), causing kernel `decide` and WHNF reduction to stall or blow out `maxHeartbeats`.
- Never reach for `native_decide` in `lean/Obend/` to paper over a slow WHNF reduction; fix the `structural` recursion or prove the goal symbolically (`simp`, `omega`, induction).

## 4. `#tooth` Mutation Sensitivity & `GPaco` / `MultiTurnHoare`

- **`#tooth` Discipline:** Pair every checker (`verify*`, `audit*`, `check*`) with concrete accepted **and** planted-fault refused witnesses (`#tooth` / `example : audit pol plantedBad = .error (.specificClause ...)`), proving the refusal names the exact violated clause rather than vacuous `false`.
- **Reactive & Multi-Turn Protocols (`GPaco` / `MultiTurnHoare`):** Model unbounded multi-turn protocol safety (viability envelopes, governance state transitions, channel non-interference) via parameterized coinduction (`GPaco`) or `MultiTurnHoare` invariants rather than finite 1-step unrollings.

## 5. Remote-Only Build Execution (`bb2` / `hbox`)

**NEVER run `lake`, `lean`, `cargo`, `rustc`, or `Holmake` on macOS.**

```bash
# 1. Check remote load, free RAM (ZFS-ARC aware), and runaway processes:
obb broker probe --hosts bb2,hbox

# 2. Plan & execute a SHA-pinned, .olean-seeded, 12 GiB / 600s bounded build:
obb broker plan-build Obend.Trailblaze.Polis Obend.Trailblaze.CathedralApex \
  --repo /Users/ember/dev/obend --host bb2 --max-rss-gb 12 --timeout-secs 600 --exec

# 3. Direct remote worktree verification on bb2 (after rsyncing worktree):
ssh bb2 'cd /home/build/obend/wt-lane/lean && SWARM_MEM_MAX=12G timeout --kill-after=10s 600s lake build Obend.Trailblaze.Polis'
```
"#;

// ============================================================================
// Skill 4: `obend-trailblaze-promotion`
// ============================================================================

const SKILL_TRAILBLAZE_DESC: &str = "Executes the Stage-A (*Obligations) to Stage-B (0 open obligations) Trailblaze organ promotion workflow, pre-lock Collision H injectivity proofs, scar-free in-place replacement, and quarry/obend-apex.toml registration. Use this skill when designing, overhauling, or sealing Trailblaze organs.";

const SKILL_TRAILBLAZE_BODY: &str = r#"# Obend Trailblaze Promotion Runbook (`Stage A` $\to$ `Stage B`)

Every `Obend.Trailblaze` organ begins at **Stage A** (`STAGE_A_LOCKED`: `0 sorry`, `0 axiom`, explicit `[<Organ>Obligations]` typeclass parameters) and retires by promotion to **Stage B** (`STAGE_B_SEALED`: `0` open unproved obligations).

## Step 1: Pre-Lock Satisfiability & Preimage Injectivity Audit

Before locking any Stage-A `class <Organ>Obligations : Prop`:
1. **Prove Commitment Preimage Injectivity First:** If any theorem claims `digest H x = digest H y → x = y ∨ Collision H`, write out the canonical domain guard (`CanonicalNode x`: bounded field widths `< 2^64` / `< 2^32`) and **prove** `digest_binding` constructively (`0 Classical`) right away. Never defer preimage framing to Stage B, or a dropped field (`HttpsSessionNode.serverDomain`) will make Stage B `False`.
2. **Witness Every Premise:** Include at least one constructive `example`, `#guard`, or `*_complete` theorem proving `audit*` / `verify*` admits valid multi-hop inputs (`lean/uninhabited-premise-risk`).
3. **Complete `SilverWorkflow` $\to$ `Judge` Bridge:** Populate `DecidableFragment` and `silverComplete` on `SilverWorkflow` instances so `SilverWorkflow.toJudge` carries a real `Fragment` and `refutes := fun _ => true` (`0` `lean/judge-empty-fragment` warnings).

## Step 2: Lock Stage-A Interface Cleanly

Verify the Stage-A lock passes every anti-cosplay and cone gate:

```bash
obb lint --repo <repo> --strict --strict-expose
obb pipeline check --repo <repo> --strict
obb cone --repo <repo>
```

- Confirm `0` `lean/obligation-tautological-field` errors, `0` `lean/excessive-decl-expose` errors, and `PipelineStage == STAGE_A_LOCKED`.
- Keep `<Organ>ObligationManifest` entries synchronized 1-to-1 with remaining open fields in `class <Organ>Obligations`.

## Step 3: Scar-Free In-Place Discharge (*"Nothing lands beside; everything replaces"*)

When promoting an obligation field from Stage A to Stage B:
1. **Prove the Unconditional Theorem In Place:** Prove the real theorem directly in the organ module (or a private `Proofs/` submodule) with `0 sorry`, `0` custom `axiom`s, and `0 native_decide`.
2. **Delete Discharged Obligation Fields:** Remove the proved field from `class <Organ>Obligations` and `<Organ>ObligationManifest`, wiring the proved theorem directly into `apex_<organ>_*` (prefer direct unconditional theorems over keeping wrapper typeclasses!).
3. **Or Seal via Non-Cosplay Production Instance:** When a multi-module boundary requires keeping the class (`STAGE_B_SEALED`), provide `instance : <Organ>Obligations ProdCarrier` backed by substantive multi-line domain theorems (`0` `lean/obligation-projection-cosplay` errors; never instantiate on `Unit`/`Bool`/`Nat`).

## Step 4: `quarry/obend-apex.toml` Registration & Final Seal

1. Register or update the organ's apex theorem in `<obebuilder>/quarry/obend-apex.toml` (`subsystem`, `module`, `theorem`, `organ`).
2. Run the full verification battery (static local `obb` + remote `bb2` kernel build):
   ```bash
   obb lint --repo <repo> --strict --strict-expose
   obb pipeline check --repo <repo> --strict
   obb apex check --repo <repo> --manifest <obebuilder>/quarry/obend-apex.toml
   obb harness check --repo <repo>
   ssh bb2 'cd /home/build/obend/dev/lean && SWARM_MEM_MAX=12G timeout --kill-after=10s 600s lake build Obend.Trailblaze.CathedralApex'
   ```
"#;
