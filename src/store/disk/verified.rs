//! The verification-record layer.
//!
//! A definition whose content hash has passed a check (parity, a doctest, a
//! snapshot case) records that pass here, keyed by the same hash, so an unchanged
//! hash is a recorded pass rather than a re-run. The layer offers append and read
//! access over a fixed, header-versioned format.
//!
//! One append-only file per hash at `verified/<first 2 hex>/<rest>`, one record
//! per line, tab-separated, header-versioned:
//!
//! ```text
//! prism-store-verified<TAB>v2
//! <check-kind><TAB><scheme><TAB><identity><TAB><status>
//! ```
//!
//! `check-kind` names the check (`parity`, `doctest`, `test`, ...); `scheme`
//! is the hash scheme the record was made under, so a scheme bump invalidates
//! old records; `identity` is the full artifact fingerprint for the toolchain,
//! target/backend, and flags that produced the verdict; `status` is `pass` or
//! `fail`. A record is meaningful only for the `scheme` and `identity` it
//! carries.

use std::fmt::Write as _;
use std::fs;
use std::io;
use std::path::Path;

use super::{atomic_write, shard_path, HashHex, FIELD_SEP, VERIFIED_DIR};

const VERIFIED_HEADER_V1: &str = "prism-store-verified\tv1";
const VERIFIED_HEADER_V2: &str = "prism-store-verified\tv2";

/// A single verification outcome recorded against a content hash.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedRecord {
    /// Which check ran (`parity`, `doctest`, `test`, ...).
    pub kind: String,
    /// The hash scheme in force when the check passed; a record is valid only
    /// under this scheme.
    pub scheme: String,
    /// The behavior-affecting artifact identity in force when the check passed.
    pub identity: String,
    /// Whether the check passed.
    pub passed: bool,
}

const STATUS_PASS: &str = "pass";
const STATUS_FAIL: &str = "fail";

pub(super) fn put(root: &Path, hash: &HashHex<'_>, record: &VerifiedRecord) -> io::Result<()> {
    let mut records = get(root, hash)?;
    records.push(record.clone());
    let mut body = String::from(VERIFIED_HEADER_V2);
    body.push('\n');
    for r in &records {
        let status = if r.passed { STATUS_PASS } else { STATUS_FAIL };
        let _ = writeln!(
            body,
            "{}{FIELD_SEP}{}{FIELD_SEP}{}{FIELD_SEP}{status}",
            r.kind, r.scheme, r.identity
        );
    }
    atomic_write(&shard_path(&root.join(VERIFIED_DIR), hash), body.as_bytes())
}

pub(super) fn get(root: &Path, hash: &HashHex<'_>) -> io::Result<Vec<VerifiedRecord>> {
    let path = shard_path(&root.join(VERIFIED_DIR), hash);
    let text = match fs::read_to_string(&path) {
        Ok(t) => t,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(e) => return Err(e),
    };
    let mut lines = text.lines();
    let header = lines.next();
    if header != Some(VERIFIED_HEADER_V1) && header != Some(VERIFIED_HEADER_V2) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("malformed verification record at {}", path.display()),
        ));
    }
    let mut out = Vec::new();
    for line in lines {
        let fields: Vec<&str> = line.split(FIELD_SEP).collect();
        match (header, fields.as_slice()) {
            (Some(VERIFIED_HEADER_V1), [kind, scheme, status]) => out.push(VerifiedRecord {
                kind: (*kind).to_string(),
                scheme: (*scheme).to_string(),
                identity: String::new(),
                passed: *status == STATUS_PASS,
            }),
            (Some(VERIFIED_HEADER_V2), [kind, scheme, identity, status]) => {
                out.push(VerifiedRecord {
                    kind: (*kind).to_string(),
                    scheme: (*scheme).to_string(),
                    identity: (*identity).to_string(),
                    passed: *status == STATUS_PASS,
                });
            }
            _ => {}
        }
    }
    Ok(out)
}
