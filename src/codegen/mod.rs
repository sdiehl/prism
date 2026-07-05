mod emit;
mod llvm;
#[cfg(feature = "mlir")]
mod mlir;
pub mod rt;

pub use llvm::{emit as emit_llvm, emit_bitcode as emit_llvm_bc};

#[cfg(feature = "mlir")]
pub use mlir::emit as emit_mlir;
