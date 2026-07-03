//! The anonymous object layer: immutable, append-only, content-addressed blobs.
//!
//! One file per content hash at `objects/<first 2 hex>/<rest>`. Writing a hash
//! that already exists verifies the new bytes match the stored bytes and writes
//! nothing; a mismatch means two different definitions collided on one hash (a
//! codegen or hashing bug), which is corruption and a hard error, never a silent
//! overwrite.

use std::fs;
use std::io;
use std::path::Path;

use super::{atomic_write, shard_path, validate_hash, HashHex, Written, OBJECTS_DIR};

pub(super) fn put(root: &Path, hash: &HashHex, bytes: &[u8]) -> io::Result<Written> {
    validate_hash(hash)?;
    let path = shard_path(&root.join(OBJECTS_DIR), hash);
    if path.exists() {
        let existing = fs::read(&path)?;
        if existing == bytes {
            return Ok(Written::Hit);
        }
        return Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            format!(
                "content-hash collision at {}: an object with different bytes already exists \
                 for hash {hash} (anonymous objects are immutable)",
                path.display()
            ),
        ));
    }
    atomic_write(&path, bytes)?;
    Ok(Written::New)
}

pub(super) fn get(root: &Path, hash: &HashHex) -> io::Result<Vec<u8>> {
    validate_hash(hash)?;
    fs::read(shard_path(&root.join(OBJECTS_DIR), hash))
}

pub(super) fn has(root: &Path, hash: &HashHex) -> bool {
    validate_hash(hash).is_ok() && shard_path(&root.join(OBJECTS_DIR), hash).exists()
}
