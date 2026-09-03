//! The anonymous object layer: immutable, content-addressed blobs.
//!
//! One file per content hash at `objects/<first 2 hex>/<rest>`. Writing a hash
//! that already exists verifies the new bytes match the stored bytes and writes
//! nothing; a mismatch means two different definitions collided on one hash (a
//! codegen or hashing bug), which is corruption and a hard error, never a silent
//! overwrite.
//!
//! Immutable does not mean unbounded: each shard is capped, and a publish that
//! lands in a full shard retires that shard's oldest entries. A retired object
//! whose binding survives reads as an ordinary cache miss and is re-derived
//! (the query read path treats an absent object as a miss, never corruption),
//! so eviction needs no liveness analysis. A hit refreshes the file's age,
//! keeping hot objects ahead of cold generations.

use std::fs;
use std::io;
use std::path::Path;
use std::sync::atomic::AtomicBool;

use super::{
    evict_shard_overflow, refresh_entry_age, runaway_estimate, shard_path, HashHex, Written,
    OBJECTS_DIR, OBJECT_SHARD_BUDGET, SAMPLE_SHARD, SHARD_COUNT,
};

// Tripwire threshold for a broken eviction path: a layer holding this many
// objects is worth naming (once per process, see `runaway_estimate`) long
// before it grows into a disk-eating catalog.
const OBJECT_LAYER_WARN_ENTRIES: u64 = 1 << 20;

static LAYER_SIZE_WARNED: AtomicBool = AtomicBool::new(false);

// The runaway-layer tripwire (see `runaway_estimate` for the sampling scheme).
fn warn_if_runaway_layer(hash: &HashHex<'_>, entry: &Path) {
    if !hash.as_str().starts_with(SAMPLE_SHARD) {
        return;
    }
    let Some(shard_dir) = entry.parent() else {
        return;
    };
    let threshold = OBJECT_LAYER_WARN_ENTRIES / SHARD_COUNT;
    if let Some(estimate) = runaway_estimate(shard_dir, threshold, &LAYER_SIZE_WARNED) {
        eprintln!(
            "warning: store object layer holds roughly {estimate} objects; \
             `prism store gc` sweeps unreferenced ones"
        );
    }
}

pub(super) fn put(
    root: &Path,
    pending: Option<&super::PendingWrites>,
    hash: &HashHex<'_>,
    bytes: &[u8],
) -> io::Result<Written> {
    let path = shard_path(&root.join(OBJECTS_DIR), hash);
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
                    "staged object at {} already holds different bytes for hash {hash}",
                    path.display()
                ),
            ))
        };
    }
    if !path.exists() && super::atomic_write_if_absent_in(pending, &path, bytes)? {
        if let Some(shard_dir) = path.parent() {
            evict_shard_overflow(shard_dir, &path, OBJECT_SHARD_BUDGET);
        }
        warn_if_runaway_layer(hash, &path);
        return Ok(Written::New);
    }
    let existing = fs::read(&path)?;
    if existing == bytes {
        refresh_entry_age(&path);
        return Ok(Written::Hit);
    }
    Err(io::Error::new(
        io::ErrorKind::AlreadyExists,
        format!(
            "content-hash collision at {}: an object with different bytes already exists \
             for hash {hash} (anonymous objects are immutable)",
            path.display()
        ),
    ))
}

// During a deferred-durability window a freshly put object is a staged temp,
// not yet a published file, so both read paths fall back to the pending queue:
// the same compile must be able to bind a query against an object it just
// wrote before the commit barrier publishes it.
pub(super) fn get(
    root: &Path,
    pending: Option<&super::PendingWrites>,
    hash: &HashHex<'_>,
) -> io::Result<Vec<u8>> {
    let path = shard_path(&root.join(OBJECTS_DIR), hash);
    super::read_visible(pending, &path)?
        .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, format!("object {hash} is absent")))
}

pub(super) fn has(root: &Path, pending: Option<&super::PendingWrites>, hash: &HashHex<'_>) -> bool {
    let path = shard_path(&root.join(OBJECTS_DIR), hash);
    path.exists() || pending.is_some_and(|pending| super::pending_contains(pending, &path))
}
