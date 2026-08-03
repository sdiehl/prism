//! The native backends.
//!
//! LLVM and MLIR emission over lowered Core, the C runtime's materialization
//! and linking, the native continuation table, and the C-toolchain seam.
//! Everything here sits behind the driver's backend boundary; the front end
//! and interpreter never depend on this crate.

// Instruction emission names registers, slots, and byte counts with the short
// letters the ABI notes use; spelling them out obscures the layout arithmetic.
#![allow(clippy::many_single_char_names)]
// `redundant_pub_crate` (nursery) and the rustc `unreachable_pub` lint pull in
// opposite directions for a `pub(crate)` item in a private module, the honest
// visibility for the codegen internals shared between `emit`, `dispatch`,
// `abi`, `mangle`, and `native_kont` but not exported from the crate. Keep the
// precise `pub(crate)` and silence the nursery half.
#![allow(clippy::redundant_pub_crate)]

mod codegen;

pub use codegen::*;
