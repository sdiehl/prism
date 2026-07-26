//! The `stable` protocol's compiler-side home.
//!
//! The committed family lock manifests beside a source file, and the
//! digest-reseating formatter entry behind `prism wire --accept`. Both sit
//! above the syntax crate because rung digests and lock verdicts are semantic
//! (shape hashing), while the plain formatter and parser stay purely
//! syntactic.

pub mod lock;
pub mod wire_fmt;
