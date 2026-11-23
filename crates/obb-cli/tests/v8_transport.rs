use obb_judge::{Gate, JudgeReceipt, issue_judge_receipt, transport::Transport};
use serde_json::json;
use std::{fs, process::Command};

#[test]
fn verifies_binary_content_modes_paths_mac_and_v1_wire() {
    use std::os::unix::fs::PermissionsExt;
    let dir = tempfile::tempdir().unwrap();
    let repo = dir.path();
    let git = |args: &[&str]| {
        let out = Command::new("git")
            .args([
                "-c",
                "user.name=Test",
                "-c",
                "user.email=test@example.org",
                "-c",
                "commit.gpgsign=false",
                "-C",
            ])
            .arg(repo)
            .args(args)
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8(out.stdout).unwrap().trim().to_owned()
    };
    git(&["init", "-b", "main"]);
    fs::write(repo.join("a"), [0, 255, 0]).unwrap();
    fs::write(repo.join("b"), "data").unwrap();
    fs::write(repo.join("outside"), "private to whole tree").unwrap();
    git(&["add", "a", "b", "outside"]);
    git(&["commit", "-m", "inputs"]);
    let g:Gate=serde_json::from_value(json!({"name":"unit","formats":["cone-unit@1"],
        "floors":[{"floor":"files","inputs":["b","a"],"command":"test -f a && test -f b && test ! -e outside"}],
        "methods":[{"format":"cone-unit@1","floor":"files","method":"eval:external:shell"}],"basis":["external:shell"]})).unwrap();
    let r = issue_judge_receipt(&g, repo, "HEAD").unwrap();
    let key = fs::read(repo.join(".obb/receipt.key")).unwrap();
    let tree = git(&["rev-parse", "HEAD^{tree}"]);
    assert_eq!(
        r.verify_transport(&key, repo, &tree).unwrap(),
        Transport::Transported
    );
    let mut forged = r.clone();
    forged.transport.as_mut().unwrap().cone_blobs.remove("a");
    forged.receipt_hash = forged.compute_hash().unwrap();
    assert!(forged.verify_transport(&key, repo, &tree).is_err());
    fs::set_permissions(repo.join("a"), fs::Permissions::from_mode(0o755)).unwrap();
    git(&["update-index", "--chmod=+x", "a"]);
    git(&["rm", "b"]);
    let changed = git(&["write-tree"]);
    assert_eq!(
        r.verify_transport(&key, repo, &changed).unwrap(),
        Transport::Invalidated {
            changed_paths: vec!["a".into(), "b".into()]
        }
    );
    let mut v1 = r;
    v1.transport = None;
    v1.receipt_version = 1;
    v1.authenticate(&key).unwrap();
    let wire = serde_json::to_string(&v1).unwrap();
    assert!(!wire.contains("cone_blobs"));
    let restored: JudgeReceipt = serde_json::from_str(&wire).unwrap();
    restored.verify_authenticated(&key).unwrap();
    assert!(restored.verify_transport(&key, repo, &tree).is_err());
}
