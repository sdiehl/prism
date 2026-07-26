//! The content-addressed object store.
//!
//! The on-disk two-layer store, its canonical keys, query records,
//! verification markers, and the wasm bridge stub. A store object is bytes
//! named by its digest; the compiler-side codecs that decompose a program
//! into objects live above this crate.

pub mod bridge;
pub mod disk;
