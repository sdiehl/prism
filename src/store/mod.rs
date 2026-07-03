//! The content-addressed store: definitions serialized to compact wire bytes,
//! keyed by their per-definition content hash.
//!
//! This module owns the *bytes*, the reversible codec between elaborated
//! anonymous Core and the `def`-kind wire frame that lives in the store. The
//! on-disk object layout (the sharded directory, the index) is a separate
//! concern layered on top of [`codec::encode_def`]/[`codec::decode_def`].
//!
//! A stored definition is hash-consed per node: a subexpression that occurs more
//! than once, anywhere in the serialized group, is one node-table entry
//! referenced by index from each occurrence. The exposed identity stays the
//! per-definition content hash ([`crate::core::hash_group`]); node sharing is the
//! storage representation beneath it, and two nodes share exactly when the hash
//! considers them equal (alpha-normalized, dependency-substituted).

/// The `cert`-kind wire envelope; see [`cert`].
///
/// A digest that attests a property of another digest. The minimal certificate is
/// a parity-passed record keyed by hash.
pub mod cert;
pub mod codec;
/// Store-level instance coherence.
///
/// The canonical `(class, head) -> instance-hash` bindings and the cross-program
/// conflict error; see [`coherence`].
pub mod coherence;
/// The on-disk two-layer store that holds the codec's bytes; see [`disk::Store`].
pub mod disk;
/// Verification caching over the store: a hash that passed a check is a recorded
/// pass, not a re-run; see [`verify`].
pub mod verify;

/// The parse failures a hostile or stale `def` frame can produce. Decode is
/// total: every malformed input lands on one of these rather than a panic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CodecError {
    /// The scheme tag was absent or not [`crate::core::HASH_SCHEME`].
    Scheme,
    /// The kind varint was not the `def` kind.
    Kind,
    /// A varint ran past its byte cap, or the buffer ended mid-value.
    Truncated,
    /// A length prefix (string, list, or table) exceeded its named bound.
    TooLarge,
    /// A tag, op discriminant, or node reference had no valid interpretation.
    Malformed,
    /// A node or dependency index pointed outside its table.
    BadReference,
    /// The reconstructed graph exceeded the node-expansion budget.
    DepthLimit,
    /// Bytes remained after the frame was fully decoded.
    TrailingBytes,
    /// A string field held bytes that were not valid UTF-8.
    Utf8,
}

impl std::fmt::Display for CodecError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let msg = match self {
            Self::Scheme => "unrecognized or missing wire scheme tag",
            Self::Kind => "frame is not the expected wire kind",
            Self::Truncated => "input ended inside a value or a varint ran too long",
            Self::TooLarge => "a length prefix exceeded its bound",
            Self::Malformed => "a tag or discriminant had no valid interpretation",
            Self::BadReference => "a node or dependency index was out of range",
            Self::DepthLimit => "the reconstructed graph exceeded the expansion budget",
            Self::TrailingBytes => "trailing bytes after the decoded frame",
            Self::Utf8 => "a string field was not valid UTF-8",
        };
        f.write_str(msg)
    }
}

impl std::error::Error for CodecError {}
