use obb_lint::{KNOWN_STATIC_LINT_RULE_IDS, is_known_static_lint_rule_id};

#[test]
fn known_static_lint_rule_ids_are_strictly_sorted_and_searchable() {
    for pair in KNOWN_STATIC_LINT_RULE_IDS.windows(2) {
        assert!(
            pair[0] < pair[1],
            "KNOWN_STATIC_LINT_RULE_IDS must be strictly sorted: {:?} >= {:?}",
            pair[0],
            pair[1]
        );
    }
    for &id in KNOWN_STATIC_LINT_RULE_IDS {
        assert!(is_known_static_lint_rule_id(id));
    }
    assert!(!is_known_static_lint_rule_id(
        "lean/spec-insensitive-change"
    ));
    assert!(!is_known_static_lint_rule_id("made_up_nonexistent_floor"));
}
