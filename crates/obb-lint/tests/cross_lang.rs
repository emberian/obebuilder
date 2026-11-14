use obb_core::Severity;
use std::collections::BTreeSet;

use obb_lint::cross_lang::*;
use std::fs;

#[test]
fn detects_shared_tag_framing_arity_mismatch_and_orphaned_rust_wire_tags() {
    let dir = tempfile::tempdir().unwrap();
    let rs_sandbox = dir.path().join("crates/obend-sandbox/src");
    let rs_crypto = dir.path().join("crates/obend-crypto-exec/src");
    let lean_polis = dir.path().join("lean/Obend/Polis");
    let lean_crypto = dir.path().join("lean/Obend/Crypto");
    fs::create_dir_all(&rs_sandbox).unwrap();
    fs::create_dir_all(&rs_crypto).unwrap();
    fs::create_dir_all(&lean_polis).unwrap();
    fs::create_dir_all(&lean_crypto).unwrap();

    fs::write(
        rs_sandbox.join("custody.rs"),
        r#"
const ORPHAN_ROOT_TAG: &str = "OBEND_AMEND_ROOT_V1";

pub fn authority_root(a: Vec<u8>, b: Vec<u8>, c: Vec<u8>) -> [u8; 32] {
    hash(
        "OBEND.CUSTODY.AUTHORITY/v1",
        &[
            a,
            b,
            c,
        ],
    )
}

pub fn mind_root(id: Vec<u8>, parent: Vec<u8>) -> [u8; 32] {
    hash("OBEND.CUSTODY.MIND/v1", &[id, parent])
}

pub fn proposal_commit(payload: &[u8]) -> [u8; 32] {
    cshake(b"OBEND.AMEND.PROPOSAL_COMMIT/v1", payload)
}

#[cfg(test)]
mod tests {
    #[test]
    fn ignored_test_only_tag() {
        let _ = b"OBEND.ONLY.IN.CFG.TEST/v1";
    }
}
"#,
    )
    .unwrap();

    fs::write(
        rs_crypto.join("transcript.rs"),
        r#"
pub const FS_SEED_CUSTOMIZATION: &[u8] = b"OBEND.CRYPTO.FS.SEED/v1";
"#,
    )
    .unwrap();

    fs::write(
        lean_polis.join("GrainPowerbox.lean"),
        r#"module
public section
namespace Obend.Polis

def authorityRoot (a b c d e : List UInt8) : ByteArray :=
  hash "OBEND.CUSTODY.AUTHORITY/v1" [a, b, c, d, e]

def childMind (id parent : List UInt8) : ByteArray :=
  hash "OBEND.CUSTODY.MIND/v1" [id, parent]

end Obend.Polis
"#,
    )
    .unwrap();

    fs::write(
            lean_crypto.join("Transcript.lean"),
            r#"module
public section
namespace Obend.Crypto

/-- `"OBEND.CRYPTO.FS.SEED/v1"` in ASCII. Note docstring mentioning `"OBEND.AMEND.PROPOSAL_COMMIT/v1"` must NOT satisfy orphan check! -/
def fsSeedCustomization : List UInt8 :=
  [0x4f, 0x42, 0x45, 0x4e, 0x44, 0x2e, 0x43, 0x52, 0x59, 0x50, 0x54, 0x4f, 0x2e,
   0x46, 0x53, 0x2e, 0x53, 0x45, 0x45, 0x44, 0x2f, 0x76, 0x31]

end Obend.Crypto
"#,
        )
        .unwrap();

    let warn_findings = scan_cross_lang_domain_tags(dir.path(), false);
    assert_eq!(
        warn_findings.len(),
        3,
        "expected 1 arity mismatch + 2 orphaned tags, got: {warn_findings:#?}"
    );
    assert!(
        warn_findings
            .iter()
            .all(|f| f.severity == Severity::Warning)
    );

    let auth = warn_findings
        .iter()
        .find(|f| f.symbol.as_deref() == Some("OBEND.CUSTODY.AUTHORITY/v1"))
        .expect("AUTHORITY/v1 arity mismatch must fire");
    assert!(auth.message.contains("frames 3 field(s)"));
    assert!(auth.message.contains("frames 5 field(s)"));

    assert!(
        warn_findings
            .iter()
            .any(|f| f.symbol.as_deref() == Some("OBEND_AMEND_ROOT_V1")),
        "orphaned _V1 tag must fire"
    );
    assert!(
        warn_findings
            .iter()
            .any(|f| f.symbol.as_deref() == Some("OBEND.AMEND.PROPOSAL_COMMIT/v1")),
        "orphaned b\".../v1\" byte-string tag must fire even if quoted in Lean docstring"
    );
    assert!(
        warn_findings
            .iter()
            .all(|f| f.symbol.as_deref() != Some("OBEND.CUSTODY.MIND/v1"))
    );
    assert!(
        warn_findings
            .iter()
            .all(|f| f.symbol.as_deref() != Some("OBEND.CRYPTO.FS.SEED/v1"))
    );
    assert!(
        warn_findings
            .iter()
            .all(|f| f.symbol.as_deref() != Some("OBEND.ONLY.IN.CFG.TEST/v1"))
    );

    let err_findings = scan_cross_lang_domain_tags(dir.path(), true);
    assert_eq!(err_findings.len(), 3);
    assert!(err_findings.iter().all(|f| f.severity == Severity::Error));
}

#[test]
fn resolves_cross_file_sized_array_consts_concat_escapes_and_cfg_edge_cases() {
    let dir = tempfile::tempdir().unwrap();
    let rs_crypto = dir.path().join("crates/obend-crypto-exec/src");
    let lean_crypto = dir.path().join("lean/Obend/Crypto");
    fs::create_dir_all(&rs_crypto).unwrap();
    fs::create_dir_all(&lean_crypto).unwrap();

    // Cross-file `const PKG_TAG: &[u8; 24] = b"..."` (`;` inside `[u8; 24]`!), `const fn` distraction,
    // struct-field `#[cfg(test)]` NOT swallowing the next fn, `concat!`, `\u{4f}`, `[b'O', ...]`,
    // `OBEND.TESTAMENT/v1` NOT skipped as `TEST`
    fs::write(
        rs_crypto.join("tags.rs"),
        r#"
pub const PKG_TAG: &[u8; 24] = b"OBEND.CUSTODY.PACKAGE/v1";
pub const BUF_TAG: &str = "OBEND.CRYPTO.BUF/v1";
pub const fn helper_len() -> usize { 24 }
"#,
    )
    .unwrap();

    fs::write(
        rs_crypto.join("lib.rs"),
        r#"
mod tags;

pub struct State {
    #[cfg(test)]
    pub debug_counter: u64,
    pub epoch: u64,
}

pub fn pkg_digest(a: Vec<u8>, b: Vec<u8>, c: Vec<u8>) -> [u8; 32] {
    let _zero = ("OBEND.CRYPTO.BUF/v1", [0u8; 32]);
    let _chained = hash("OBEND.CRYPTO.BUF/v1", &[a.clone()].iter().chain(&[]).collect::<Vec<_>>());
    hash(tags::PKG_TAG, &vec![a, b, c])
}

#[cfg(any(test, feature = "prod"))]
pub fn testament_commit(x: &[u8]) -> [u8; 32] {
    cshake(concat!("OBEND.", "TESTAMENT/v1"), x)
}

pub fn escaped_orphan(x: &[u8]) -> [u8; 32] {
    cshake("\u{4f}\x42END.ESCAPED/v1", x)
}

pub fn dynamic_ok(x: &[u8]) -> [u8; 32] {
    cshake("OBEND.DYN.SUBKIND/v1", x)
}

#[cfg(all(test, not(feature = "fips")))]
mod extra_tests {
    pub const IGNORED: &str = "OBEND.ALL.TEST.IGNORED/v1";
}
"#,
    )
    .unwrap();

    fs::write(
        lean_crypto.join("Tags.lean"),
        r#"module
public section
namespace Obend.Crypto

def pkgTag : String := "OBEND.CUSTODY." ++ "PACKAGE/v1"
def bufTag : String := "OBEND.CRYPTO.BUF/v1"
def dynTag (k : String) : String := "OBEND.DYN." ++ k

end Obend.Crypto
"#,
    )
    .unwrap();

    fs::write(
        lean_crypto.join("Pkg.lean"),
        r#"module
public import Obend.Crypto.Tags
public section
namespace Obend.Crypto

def pkgDigest (a b : List UInt8) : ByteArray :=
  hash pkgTag [a, b]

def bufDigest (a b : List UInt8) (rest : List (List UInt8)) : ByteArray :=
  let _dyn := hash bufTag ([a] ++ rest)
  hash bufTag [a, b]

end Obend.Crypto
"#,
    )
    .unwrap();

    let findings = scan_cross_lang_domain_tags(dir.path(), false);
    let syms: BTreeSet<&str> = findings
        .iter()
        .filter_map(|f| f.symbol.as_deref())
        .collect();
    let expected: BTreeSet<&str> = [
        "OBEND.CUSTODY.PACKAGE/v1",
        "OBEND.TESTAMENT/v1",
        "OBEND.ESCAPED/v1",
    ]
    .into_iter()
    .collect();
    assert_eq!(
        syms, expected,
        "must catch cross-file PKG_TAG arity drift + concat! TESTAMENT/v1 + escaped orphan while ignoring [0u8; 32], ++ rest, dynamic prefix, and #[cfg(all(test, not(...)))]: {findings:#?}"
    );
}
