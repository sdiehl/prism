//! The metadata layer: mutable, human-facing facts keyed by the same content
//! hash as the anonymous object, living beside it (never inside it).
//!
//! One blob per hash at `meta/<first 2 hex>/<rest>`, rewritten in place when a
//! name or doc changes. Editing metadata never touches the anonymous object, so
//! a rename does not mint a new content hash.
//!
//! Format (line-oriented, tab-separated, versioned by its header):
//!
//! ```text
//! prism-store-meta<TAB>v1
//! name<TAB><canonical name>
//! type<TAB><rendered type>
//! doc<TAB><doc comment, blank if none>
//! ```
//!
//! `doc` (and source positions, once the format grows them) are reserved keys:
//! an unknown key is ignored on read so the format can grow without a version
//! bump for additive fields.

use std::fs;
use std::io;
use std::path::Path;

use super::{atomic_write, shard_path, HashHex, FIELD_SEP, META_DIR};

const META_HEADER: &str = "prism-store-meta\tv1";
const KEY_NAME: &str = "name";
const KEY_TYPE: &str = "type";
const KEY_DOC: &str = "doc";

/// The metadata-layer facts for one definition. Extended (not replaced) as later
/// future formats add source positions and richer documentation.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DefMeta {
    /// The canonical human name the hash is bound to.
    pub name: String,
    /// The rendered principal type (and effects), as the docs show it.
    pub ty: String,
    /// The definition's doc comment, empty when none.
    pub doc: String,
}

pub(super) fn put(root: &Path, hash: &HashHex<'_>, m: &DefMeta) -> io::Result<()> {
    let body = format!(
        "{META_HEADER}\n{KEY_NAME}{FIELD_SEP}{}\n{KEY_TYPE}{FIELD_SEP}{}\n{KEY_DOC}{FIELD_SEP}{}\n",
        m.name, m.ty, m.doc
    );
    atomic_write(&shard_path(&root.join(META_DIR), hash), body.as_bytes())
}

pub(super) fn get(root: &Path, hash: &HashHex<'_>) -> io::Result<Option<DefMeta>> {
    let path = shard_path(&root.join(META_DIR), hash);
    let text = match fs::read_to_string(&path) {
        Ok(t) => t,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e),
    };
    let mut lines = text.lines();
    if lines.next() != Some(META_HEADER) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("malformed metadata at {}", path.display()),
        ));
    }
    let mut m = DefMeta::default();
    for line in lines {
        match line.split_once(FIELD_SEP) {
            Some((KEY_NAME, v)) => m.name = v.to_string(),
            Some((KEY_TYPE, v)) => m.ty = v.to_string(),
            Some((KEY_DOC, v)) => m.doc = v.to_string(),
            _ => {}
        }
    }
    Ok(Some(m))
}
