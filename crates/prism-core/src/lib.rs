//! The Prism middle end.
//!
//! The type vocabulary, the call-by-push-value Core IR with its typed passes,
//! content hashing, and the compiler flag set. Sits below the driver,
//! evaluator, and backends; knows syntax (the AST it elaborates from) but
//! nothing of parsing, files, or code generation.

pub mod core;
pub mod flags;
pub mod types;
