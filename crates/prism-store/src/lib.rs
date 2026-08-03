//! The content-addressed object store.
//!
//! The on-disk two-layer store, its canonical keys, query records,
//! verification markers, and the wasm bridge stub. A store object is bytes
//! named by its digest; the compiler-side codecs that decompose a program
//! into objects live above this crate.

// `redundant_pub_crate` (nursery) and the rustc `unreachable_pub` lint pull in
// opposite directions for a `pub(crate)` item in a private module, the honest
// visibility for the test-only fault-injection seam shared between the disk
// store's sibling modules. Keep the precise `pub(crate)` and silence the
// nursery half of the conflict.
#![allow(clippy::redundant_pub_crate)]

pub mod bridge;
pub mod disk;
