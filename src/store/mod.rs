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
/// Committing an elaborated program's definitions into the store.
pub mod commit;
pub use commit::commit_program;
/// The shadow-parser comparison receipt: the deterministic half attested as a
/// certificate, the machine readings recorded as a decision; see [`receipt`].
pub mod receipt;
/// The Incr durable-snapshot bridge: a named blob rides the store's object layer
/// (keyed by content hash) with a ref for the caller tag; see [`bridge`].
pub use prism_store::bridge;
/// The on-disk two-layer store that holds the codec's bytes; see [`disk::Store`].
pub use prism_store::disk;
/// Verification caching over the store: a hash that passed a check is a recorded
/// pass, not a re-run; see [`verify`].
pub mod verify;

pub use prism_common::binary::CodecError;
