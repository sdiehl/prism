//! The native backends.
//!
//! LLVM and MLIR emission over lowered Core, the C runtime's materialization
//! and linking, the native continuation table, and the C-toolchain seam.
//! Everything here sits behind the driver's backend boundary; the front end
//! and interpreter never depend on this crate.

mod codegen;

pub use codegen::*;
