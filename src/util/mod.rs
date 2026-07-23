//! Dependency-light generic primitives shared across the compiler: the byte
//! substrate for the wire codecs, deterministic strongly-connected-component and
//! least-fixpoint solvers, and the compiler's own fresh-id supply. The module stays
//! import-light and independent of compiler-specific representations.

// The byte substrate shared by the two content-addressed wire codecs
// (`store::codec` and `eval::kont`): varints, bounded blobs/strings, table
// numbering, and the hostile-input discipline. The schemas stay in the codecs.
pub(crate) mod binary;
pub(crate) mod fixpoint;
pub(crate) mod fresh;
pub(crate) mod scc;
