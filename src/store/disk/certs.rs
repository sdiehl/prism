//! The certificate layer: immutable, append-only, content-addressed attestations.
//!
//! One file per attested subject at `certs/<first 2 hex>/<rest>`, holding that
//! subject's serialized `cert`-kind envelope. Sharded and immutable exactly like
//! the anonymous object layer: writing a subject that already carries an identical
//! certificate writes nothing, and different bytes for an existing subject are
//! corruption, never a silent overwrite. Unlike an object, a subject need not have
//! a certificate at all, so [`get`] returns `None` rather than erroring on a miss.

use std::fs;
use std::io;
use std::path::Path;

use super::{atomic_write, shard_path, HashHex, Written, CERTS_DIR};

pub(super) fn put(root: &Path, subject: &HashHex<'_>, bytes: &[u8]) -> io::Result<Written> {
    let path = shard_path(&root.join(CERTS_DIR), subject);
    if path.exists() {
        let existing = fs::read(&path)?;
        if existing == bytes {
            return Ok(Written::Hit);
        }
        return Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            format!(
                "certificate at {} already exists with different bytes for subject {subject} \
                 (certificates are immutable)",
                path.display()
            ),
        ));
    }
    atomic_write(&path, bytes)?;
    Ok(Written::New)
}

pub(super) fn get(root: &Path, subject: &HashHex<'_>) -> io::Result<Option<Vec<u8>>> {
    match fs::read(shard_path(&root.join(CERTS_DIR), subject)) {
        Ok(bytes) => Ok(Some(bytes)),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(e),
    }
}

pub(super) fn has(root: &Path, subject: &HashHex<'_>) -> bool {
    shard_path(&root.join(CERTS_DIR), subject).exists()
}
