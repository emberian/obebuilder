use obb_lint::harness::*;
use std::fs;

#[test]
fn canonical_templates_respect_all_byte_budgets_and_frontmatter_laws() {
    let list = harness_list();
    assert_eq!(list.total_artifacts, 11);
    assert_eq!(list.root_rules, 3);
    assert_eq!(list.skills, 8);

    for art in &list.artifacts {
        assert!(
            art.byte_len < art.byte_budget,
            "`{}` ({} B) exceeded budget ({} B)",
            art.rel_path,
            art.byte_len,
            art.byte_budget
        );
        assert!(art.byte_len < RULE_FILE_HARD_CAP_BYTES);
    }

    let dir = tempfile::tempdir().unwrap();
    let install_rep = harness_install(dir.path(), false).unwrap();
    assert!(install_rep.passed);
    assert_eq!(install_rep.files_written, 11);
    assert_eq!(install_rep.files_unchanged, 0);

    // Second install is idempotent (`11 unchanged`)
    let install_again = harness_install(dir.path(), false).unwrap();
    assert!(install_again.passed);
    assert_eq!(install_again.files_written, 0);
    assert_eq!(install_again.files_unchanged, 11);

    // Check passes with 0 issues
    let check_ok = harness_check(dir.path()).unwrap();
    assert!(check_ok.passed, "issues: {:#?}", check_ok.issues);
    assert_eq!(check_ok.checked_files.len(), 11);

    // Drift detection: mutate one byte in `.claude/skills/obend-anti-cosplay/SKILL.md`
    let target_skill = dir
        .path()
        .join(".claude/skills/obend-anti-cosplay/SKILL.md");
    let mut mutated = fs::read_to_string(&target_skill).unwrap();
    mutated.push_str("\n<!-- manual drift -->\n");
    fs::write(&target_skill, mutated).unwrap();

    let check_drift = harness_check(dir.path()).unwrap();
    assert!(!check_drift.passed);
    assert!(
        check_drift
            .issues
            .iter()
            .any(|i| i.kind == "checksum_mismatch"
                && i.rel_path == ".claude/skills/obend-anti-cosplay/SKILL.md")
    );

    // Unmanaged file protection without `--force`, overridden with `--force`
    let unmanaged_dir = tempfile::tempdir().unwrap();
    fs::write(
        unmanaged_dir.path().join("AGENTS.md"),
        "# Hand-written custom AGENTS\n",
    )
    .unwrap();
    let refused = harness_install(unmanaged_dir.path(), false).unwrap();
    assert!(!refused.passed);
    assert_eq!(refused.refusals.len(), 1);

    let forced = harness_install(unmanaged_dir.path(), true).unwrap();
    assert!(forced.passed);
    assert!(harness_check(unmanaged_dir.path()).unwrap().passed);
}
