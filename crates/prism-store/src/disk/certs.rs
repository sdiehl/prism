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

use super::{shard_path, HashHex, Written, CERTS_DIR};

// Publish by the link-if-absent commit, exactly like the object layer: the commit
// point itself refuses to replace an existing file, so a writer that loses the
// race falls through to the byte comparison instead of renaming over the winner.
// A check followed by a replacing rename would leave that window open.
pub(super) fn put(
    root: &Path,
    pending: Option<&super::PendingWrites>,
    subject: &HashHex<'_>,
    bytes: &[u8],
) -> io::Result<Written> {
    let path = shard_path(&root.join(CERTS_DIR), subject);
    if let Some(existing) = pending
        .map(|pending| super::pending_read(pending, &path))
        .transpose()?
        .flatten()
    {
        return if existing == bytes {
            Ok(Written::Hit)
        } else {
            Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                format!(
                    "staged certificate at {} already holds different bytes for subject {subject}",
                    path.display()
                ),
            ))
        };
    }
    if !path.exists() && super::atomic_write_if_absent_in(pending, &path, bytes)? {
        return Ok(Written::New);
    }
    let existing = fs::read(&path)?;
    if existing == bytes {
        return Ok(Written::Hit);
    }
    Err(io::Error::new(
        io::ErrorKind::AlreadyExists,
        format!(
            "certificate at {} already exists with different bytes for subject {subject} \
             (certificates are immutable)",
            path.display()
        ),
    ))
}

pub(super) fn get(
    root: &Path,
    pending: Option<&super::PendingWrites>,
    subject: &HashHex<'_>,
) -> io::Result<Option<Vec<u8>>> {
    super::read_visible(pending, &shard_path(&root.join(CERTS_DIR), subject))
}

pub(super) fn has(
    root: &Path,
    pending: Option<&super::PendingWrites>,
    subject: &HashHex<'_>,
) -> bool {
    let path = shard_path(&root.join(CERTS_DIR), subject);
    path.exists() || pending.is_some_and(|pending| super::pending_contains(pending, &path))
}
