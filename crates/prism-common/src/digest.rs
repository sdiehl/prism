//! Content-address identity primitives shared by every layer.
//!
//! The digest newtype whose hex text is the single spelling used at each
//! serialization boundary, the hash-scheme tag, and the abbreviation width.

use serde::{Deserialize, Serialize};

/// A content hash: the lowercase hex of a 32-byte digest.
///
/// A newtype over the hex string so a content hash cannot be confused with an
/// arbitrary string as it travels through the identity, store, and lineage code.
/// Construction validates the spelling, so a malformed hash is refused once at
/// the boundary that read it (including deserialization) and never travels.
/// It renders and serializes exactly as its inner hex (via
/// `Display`/`Deref`/`as_str`), so the wire bytes, on-disk objects, and folded
/// roots are byte-identical to the bare string they replaced.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(try_from = "String", into = "String")]
pub struct Digest(String);

/// Hex width of a full digest: 32 bytes.
pub const DIGEST_HEX: usize = 64;

/// A string that is not a full lowercase hex digest.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("malformed content hash `{text}`: expected {DIGEST_HEX} lowercase hex digits")]
pub struct DigestError {
    /// The refused text.
    pub text: String,
}

impl Digest {
    /// Validate `text` as a full lowercase hex digest.
    ///
    /// # Errors
    /// [`DigestError`] when `text` is not exactly [`DIGEST_HEX`] lowercase hex digits.
    pub fn parse(text: impl Into<String>) -> Result<Self, DigestError> {
        let text = text.into();
        if text.len() == DIGEST_HEX
            && text
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            Ok(Self(text))
        } else {
            Err(DigestError { text })
        }
    }

    /// The digest of a 32-byte hash value.
    #[must_use]
    pub fn of_bytes(bytes: &[u8; 32]) -> Self {
        use std::fmt::Write;
        let mut hex = String::with_capacity(DIGEST_HEX);
        for b in bytes {
            let _ = write!(hex, "{b:02x}");
        }
        Self(hex)
    }

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

impl std::str::FromStr for Digest {
    type Err = DigestError;
    fn from_str(s: &str) -> Result<Self, DigestError> {
        Self::parse(s)
    }
}

impl TryFrom<String> for Digest {
    type Error = DigestError;
    fn try_from(s: String) -> Result<Self, DigestError> {
        Self::parse(s)
    }
}

impl From<Digest> for String {
    fn from(d: Digest) -> Self {
        d.0
    }
}

/// A digest qualified by the scheme that produced it, spelled `scheme:hex`.
///
/// Distinct from [`Digest`], which is always under the core hash scheme: a
/// lineage sidecar or event trace is addressed under another scheme, and the two
/// must not compare equal by accident of sharing hex.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(try_from = "String", into = "String")]
pub struct SchemedDigest {
    scheme: String,
    digest: Digest,
}

/// A string that is not `scheme:hex` with a lowercase scheme name and a full digest.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("malformed scheme-qualified hash `{text}`: expected `scheme:hex`")]
pub struct SchemedDigestError {
    /// The refused text.
    pub text: String,
}

impl SchemedDigest {
    /// Qualify `digest` with `scheme`.
    ///
    /// # Errors
    /// [`SchemedDigestError`] when `scheme` is empty or not lowercase alphanumeric
    /// with hyphens.
    pub fn new(scheme: &str, digest: Digest) -> Result<Self, SchemedDigestError> {
        if scheme.is_empty()
            || !scheme
                .bytes()
                .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
        {
            return Err(SchemedDigestError {
                text: format!("{scheme}:{digest}"),
            });
        }
        Ok(Self {
            scheme: scheme.to_string(),
            digest,
        })
    }

    /// Validate `text` as `scheme:hex`.
    ///
    /// # Errors
    /// [`SchemedDigestError`] when `text` has no `:`, a malformed scheme, or a
    /// malformed digest.
    pub fn parse(text: &str) -> Result<Self, SchemedDigestError> {
        let refuse = || SchemedDigestError {
            text: text.to_string(),
        };
        let (scheme, hex) = text.split_once(':').ok_or_else(refuse)?;
        let digest = Digest::parse(hex).map_err(|_| refuse())?;
        Self::new(scheme, digest).map_err(|_| refuse())
    }

    /// The scheme name.
    #[must_use]
    pub fn scheme(&self) -> &str {
        &self.scheme
    }

    /// The unqualified digest.
    #[must_use]
    pub const fn digest(&self) -> &Digest {
        &self.digest
    }
}

impl std::fmt::Display for SchemedDigest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.scheme, self.digest)
    }
}

impl std::str::FromStr for SchemedDigest {
    type Err = SchemedDigestError;
    fn from_str(s: &str) -> Result<Self, SchemedDigestError> {
        Self::parse(s)
    }
}

impl TryFrom<String> for SchemedDigest {
    type Error = SchemedDigestError;
    fn try_from(s: String) -> Result<Self, SchemedDigestError> {
        Self::parse(&s)
    }
}

impl From<SchemedDigest> for String {
    fn from(d: SchemedDigest) -> Self {
        d.to_string()
    }
}

/// Scheme tag: every hash commits to it, so a change to this encoding cannot
/// silently reuse an old hash computed under a different scheme.
pub const SCHEME: &str = "prism-core-hash-v2";

/// Width, in hex characters, of the abbreviated hash prefix shown in the
/// human-facing `core-hash`/`shape`/`stdlib-hash` dumps. Full hashes are longer;
/// display truncates to this many leading nibbles.
pub const HASH_PREFIX_HEX: usize = 16;
