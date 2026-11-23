//! Receipt authentication. Keys are opaque bytes; the environment value is used literally.

use anyhow::{Context, Result, bail};
use sha2::{Digest, Sha256};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use subtle::ConstantTimeEq;

fn key_path(root: &Path) -> PathBuf {
    root.join(".obb/receipt.key")
}

/// Environment keys take precedence, then the selected state vault, then the candidate repo.
/// Unreadable or empty keys fail closed; callers that verify candidate receipts require `Some(key)`.
pub fn load_receipt_key(state_dir: Option<&Path>, repo: &Path) -> Result<Option<Vec<u8>>> {
    match std::env::var("OBB_RECEIPT_KEY") {
        Ok(value) => return nonempty(value.into_bytes()).map(Some),
        Err(std::env::VarError::NotPresent) => {}
        Err(error) => return Err(error.into()),
    }
    for root in state_dir.into_iter().chain(std::iter::once(repo)) {
        let path = key_path(root);
        match std::fs::read(&path) {
            Ok(key) => return nonempty(key).map(Some),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(error).with_context(|| format!("reading {}", path.display())),
        }
    }
    Ok(None)
}

fn nonempty(key: Vec<u8>) -> Result<Vec<u8>> {
    if key.is_empty() {
        bail!("receipt authentication key must not be empty");
    }
    Ok(key)
}

/// Create a random 256-bit key with mode 0600, atomically and without replacing another writer.
pub fn ensure_receipt_key(state_dir: Option<&Path>, repo: &Path) -> Result<Vec<u8>> {
    if let Some(key) = load_receipt_key(state_dir, repo)? {
        return Ok(key);
    }
    let path = key_path(state_dir.unwrap_or(repo));
    let parent = path.parent().context("receipt key has no parent")?;
    std::fs::create_dir_all(parent)?;
    let mut key = vec![0; 32];
    std::fs::File::open("/dev/urandom")?.read_exact(&mut key)?;
    let mut temporary = tempfile::NamedTempFile::new_in(parent)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        temporary
            .as_file()
            .set_permissions(std::fs::Permissions::from_mode(0o600))?;
    }
    temporary.write_all(&key)?;
    temporary.as_file().sync_all()?;
    match temporary.persist_noclobber(&path) {
        Ok(_) => Ok(key),
        Err(error) if error.error.kind() == std::io::ErrorKind::AlreadyExists => {
            nonempty(std::fs::read(path)?)
        }
        Err(error) => Err(error.error.into()),
    }
}

/// RFC 2104 HMAC using SHA-256's 64-byte block size (including long-key normalization).
pub fn hmac_sha256(key: &[u8], message: &[u8]) -> [u8; 32] {
    let mut block = [0u8; 64];
    if key.len() > block.len() {
        block[..32].copy_from_slice(&Sha256::digest(key));
    } else {
        block[..key.len()].copy_from_slice(key);
    }
    let mut inner_pad = [0x36; 64];
    let mut outer_pad = [0x5c; 64];
    for (index, byte) in block.iter().enumerate() {
        inner_pad[index] ^= byte;
        outer_pad[index] ^= byte;
    }
    let mut inner = Sha256::new();
    inner.update(inner_pad);
    inner.update(message);
    let mut outer = Sha256::new();
    outer.update(outer_pad);
    outer.update(inner.finalize());
    outer.finalize().into()
}

/// MAC domain of a `JudgeReceipt` (`receipt_mac` over `receipt_hash`).
pub(crate) const RECEIPT_CONTEXT: &str = "obb-judge-receipt-v1";
/// MAC domain of a cached cone verdict (`.obb/cache/cones/<digest>.json`).
pub(crate) const CONE_CONTEXT: &str = "obb-cone-verdict-v1";

/// One key signs receipts and cache entries. The NUL-terminated context keeps a tag made for
/// one kind of message from ever verifying as the other, whatever the two encodings become.
fn in_context(context: &str, message: &[u8]) -> Vec<u8> {
    let mut tagged = Vec::with_capacity(context.len() + 1 + message.len());
    tagged.extend_from_slice(context.as_bytes());
    tagged.push(0);
    tagged.extend_from_slice(message);
    tagged
}

pub(crate) fn mac_hex(key: &[u8], context: &str, message: &[u8]) -> String {
    use std::fmt::Write;
    let mut output = String::with_capacity(64);
    for byte in hmac_sha256(key, &in_context(context, message)) {
        write!(output, "{byte:02x}").expect("writing to String");
    }
    output
}

pub(crate) fn verify_mac(key: &[u8], context: &str, message: &[u8], mac: &str) -> bool {
    // Length and decoding branches depend only on the supplied, public tag. Compare the
    // expected raw MAC in constant time, without formatting secret-dependent hex digits.
    if mac.len() != 64 {
        return false;
    }
    let digit = |byte| match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    };
    let mut supplied = [0; 32];
    for (output, pair) in supplied.iter_mut().zip(mac.as_bytes().as_chunks::<2>().0) {
        let (Some(high), Some(low)) = (digit(pair[0]), digit(pair[1])) else {
            return false;
        };
        *output = high << 4 | low;
    }
    bool::from(hmac_sha256(key, &in_context(context, message)).ct_eq(&supplied))
}
