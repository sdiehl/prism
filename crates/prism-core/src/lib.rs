//! The Prism middle end.
//!
//! The type vocabulary, the call-by-push-value Core IR with its typed passes,
//! content hashing, and the compiler flag set. Sits below the driver,
//! evaluator, and backends; knows syntax (the AST it elaborates from) but
//! nothing of parsing, files, or code generation.

#![allow(clippy::many_single_char_names)]
// `redundant_pub_crate` (nursery) and the rustc `unreachable_pub` lint pull in
// opposite directions for a `pub(crate)` item in a `pub(crate)` module, the
// honest visibility for an item shared between sibling crate-internal modules
// (the Core passes and their support modules). Keep the precise `pub(crate)`
// and silence the nursery half of the conflict.
#![allow(clippy::redundant_pub_crate)]

pub mod core;
pub mod flags;
pub mod types;
