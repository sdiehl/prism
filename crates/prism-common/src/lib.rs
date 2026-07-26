//! Dependency-light primitives shared across the Prism workspace.
//!
//! The interned symbol type, the byte substrate for the wire codecs,
//! deterministic strongly-connected-component and least-fixpoint solvers, and
//! the compiler's own fresh-id supply. This crate knows nothing of Prism
//! syntax or semantics.

pub mod binary;
pub mod digest;
pub mod fixpoint;
pub mod fresh;
pub mod scc;
pub mod sym;

/// Inclusive byte bounds of the printable ASCII range (`0x20..=0x7E`).
///
/// Bytes outside `LO..=HI` are non-printable and get escaped by the string
/// emitters; defined here so every crate that classifies string bytes agrees on
/// the range.
pub const ASCII_PRINTABLE_LO: u8 = 0x20;
pub const ASCII_PRINTABLE_HI: u8 = 0x7E;
