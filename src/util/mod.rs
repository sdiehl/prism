//! Dependency-light generic primitives shared across the compiler: the byte
//! substrate for the wire codecs, deterministic strongly-connected-component and
//! least-fixpoint solvers, and the compiler's own fresh-id supply. Kept
//! import-light so it stays a natural leaf at the eventual crate split.

// The byte substrate shared by the two content-addressed wire codecs
// (`store::codec` and `eval::kont`): varints, bounded blobs/strings, table
// numbering, and the hostile-input discipline. The schemas stay in the codecs.
pub(crate) mod binary;
pub(crate) mod fixpoint;
pub(crate) mod fresh;
pub(crate) mod scc;
