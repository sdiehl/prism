//! Content-address identity primitives shared by every layer.
//!
//! The digest newtype whose hex text is the single spelling used at each
//! serialization boundary, the hash-scheme tag, and the abbreviation width.

use serde::{Deserialize, Serialize};

/// A content hash: a hex digest produced by the hasher.
///
/// A newtype over the hex string so a content hash cannot be confused with an
/// arbitrary string as it travels through the identity, store, and lineage code.
/// It renders and serializes exactly as its inner hex (via
/// `Display`/`Deref`/`as_str`), so the wire bytes, on-disk objects, and folded
/// roots are byte-identical to the bare string they replaced.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Digest(String);

impl Digest {
    /// The digest's hex text. The single spelling used at every serialization
    /// boundary (disk objects, wire codec, hash inputs), so byte identity holds.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Consume the digest, yielding its owned hex string.
    #[must_use]
    pub fn into_string(self) -> String {
        self.0
    }
}

impl std::ops::Deref for Digest {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for Digest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl AsRef<str> for Digest {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl From<String> for Digest {
    fn from(s: String) -> Self {
        Self(s)
    }
}

impl From<&str> for Digest {
    fn from(s: &str) -> Self {
        Self(s.to_string())
    }
}

impl From<Digest> for String {
    fn from(d: Digest) -> Self {
        d.0
    }
}

/// Scheme tag: every hash commits to it, so a change to this encoding cannot
/// silently reuse an old hash computed under a different scheme.
pub const SCHEME: &str = "prism-core-hash-v1";

/// Width, in hex characters, of the abbreviated hash prefix shown in the
/// human-facing `core-hash`/`shape`/`stdlib-hash` dumps. Full hashes are longer;
/// display truncates to this many leading nibbles.
pub const HASH_PREFIX_HEX: usize = 16;
