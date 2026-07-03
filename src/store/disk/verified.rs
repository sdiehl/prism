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
//! prism-store-verified<TAB>v1
//! <check-kind><TAB><scheme><TAB><status>
//! ```
//!
//! `check-kind` names the check (`parity`, `doctest`, `test`, ...); `scheme` is
//! the hash scheme the record was made under, so a scheme bump invalidates old
//! records; `status` is `pass` or `fail`. A record is meaningful only for the
//! `scheme` it carries.

use std::fmt::Write as _;
use std::fs;
use std::io;
use std::path::Path;

use super::{atomic_write, shard_path, validate_hash, HashHex, FIELD_SEP, VERIFIED_DIR};

const VERIFIED_HEADER: &str = "prism-store-verified\tv1";

/// A single verification outcome recorded against a content hash.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedRecord {
    /// Which check ran (`parity`, `doctest`, `test`, ...).
    pub kind: String,
    /// The hash scheme in force when the check passed; a record is valid only
    /// under this scheme.
    pub scheme: String,
    /// Whether the check passed.
    pub passed: bool,
}

const STATUS_PASS: &str = "pass";
const STATUS_FAIL: &str = "fail";

pub(super) fn put(root: &Path, hash: &HashHex, record: &VerifiedRecord) -> io::Result<()> {
    validate_hash(hash)?;
    let mut records = get(root, hash)?;
    records.push(record.clone());
    let mut body = String::from(VERIFIED_HEADER);
    body.push('\n');
    for r in &records {
        let status = if r.passed { STATUS_PASS } else { STATUS_FAIL };
        let _ = writeln!(body, "{}{FIELD_SEP}{}{FIELD_SEP}{status}", r.kind, r.scheme);
    }
    atomic_write(&shard_path(&root.join(VERIFIED_DIR), hash), body.as_bytes())
}

pub(super) fn get(root: &Path, hash: &HashHex) -> io::Result<Vec<VerifiedRecord>> {
    validate_hash(hash)?;
    let path = shard_path(&root.join(VERIFIED_DIR), hash);
    let text = match fs::read_to_string(&path) {
        Ok(t) => t,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(e) => return Err(e),
    };
    let mut lines = text.lines();
    if lines.next() != Some(VERIFIED_HEADER) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("malformed verification record at {}", path.display()),
        ));
    }
    let mut out = Vec::new();
    for line in lines {
        let mut fields = line.splitn(3, FIELD_SEP);
        if let (Some(kind), Some(scheme), Some(status)) =
            (fields.next(), fields.next(), fields.next())
        {
            out.push(VerifiedRecord {
                kind: kind.to_string(),
                scheme: scheme.to_string(),
                passed: status == STATUS_PASS,
            });
        }
    }
    Ok(out)
}
