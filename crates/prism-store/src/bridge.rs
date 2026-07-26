//! The Incr durable-snapshot bridge onto the real content-addressed store.
//!
//! `run_incr_durable` persists its reduced memo table as one opaque blob keyed by
//! a caller tag. The file substrate writes that blob to a path; this bridge writes
//! it to the git-style store instead, so a durable run rides the same object layer
//! the compiler uses for definitions. A blob is stored as an immutable object
//! addressed by its content hash, and a mutable ref binds the caller tag to that
//! hash, exactly the objects-plus-refs split git uses.
//!
//! Content addressing is what makes a warm hit safe: the tag resolves to a hash,
//! the retrieved bytes are re-hashed, and a mismatch (a corrupted or externally
//! swapped object) reads as absent, so the caller cold-starts rather than serving
//! wrong bytes. An identical re-store is a byte-for-byte object hit that writes
//! nothing, so an unchanged snapshot costs no new objects. Everything here is
//! cache state: a missing ref, a missing object, or a hash mismatch all mean
//! "cold start", never an error the program observes.

use std::io;
use std::path::Path;

use super::disk::Store;

// Address a blob by the lowercase-hex blake3 of its bytes, the same rendering the
// `blake3` builtin and every derived `Hash` produce, so the store key a program
// would compute and the key written here agree.
fn content_hash(bytes: &[u8]) -> String {
    blake3::hash(bytes).to_hex().to_string()
}

/// Store `content` as a named blob.
///
/// Writes the immutable object at its content hash, then points the ref `key`
/// at it. Idempotent when `content` is unchanged (the object write is a hit
/// and the ref is repointed to the same hash).
///
/// # Errors
/// Fails on any filesystem error opening or writing the store.
pub fn put(root: &Path, key: &str, content: &str) -> io::Result<()> {
    let store = Store::open_or_create(root)?;
    let hash = content_hash(content.as_bytes());
    store.put(&hash, content.as_bytes())?;
    store.set_ref(key, &hash)
}

/// Read the named blob bound to `key`, or `None` when it is absent, dangling, or
/// its object no longer hashes to the ref (corruption or an external swap). A
/// `None` return is a cold start, not an error.
///
/// # Errors
/// Fails only on a filesystem error other than a missing object.
pub fn get(root: &Path, key: &str) -> io::Result<Option<String>> {
    let store = Store::open_or_create(root)?;
    let Some(hash) = store.get_ref(key)? else {
        return Ok(None);
    };
    let bytes = match store.get(&hash) {
        Ok(b) => b,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e),
    };
    // Re-address the retrieved bytes: a mismatch means the object was corrupted or
    // swapped, so the blob is unusable and the caller cold-starts.
    if content_hash(&bytes) != hash {
        return Ok(None);
    }
    Ok(String::from_utf8(bytes).ok())
}

/// Whether `key` names a blob whose object is present. False on a missing ref, a
/// dangling ref, or any filesystem error.
#[must_use]
pub fn has(root: &Path, key: &str) -> bool {
    let Ok(store) = Store::open_or_create(root) else {
        return false;
    };
    matches!(store.get_ref(key), Ok(Some(hash)) if store.has(&hash))
}
