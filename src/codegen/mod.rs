mod abi;
mod dispatch;
mod emit;
pub mod isa;
mod llvm;
mod mangle;
#[cfg(feature = "mlir")]
mod mlir;
mod native_kont;
pub mod rt;

pub use emit::emit_with_isa;
pub(crate) use emit::ClosureSummary;
pub use isa::{Buf, Cmp, FloatBinOp, FloatIntrinsic, IntOp, Isa};
pub use llvm::{
    emit as emit_llvm, emit_bitcode as emit_llvm_bc,
    emit_bitcode_with_native_kont_table as emit_llvm_bc_with_native_kont_table,
    emit_native_kont_plan_bitcode as emit_llvm_native_kont_plan_bc,
    emit_selected_bitcode as emit_llvm_scc_bc,
    emit_with_native_kont_table as emit_llvm_with_native_kont_table, ClosurePlanShard,
    SccBitcodeError,
};
pub(crate) use llvm::{
    emit_closure_plan_shard_bitcode as emit_llvm_closure_plan_shard_bc,
    plan_closures_from_summaries as plan_llvm_closures_from_summaries,
    scc_closure_summary as llvm_scc_closure_summary, scc_function_map as llvm_scc_function_map,
    whole_function_map as llvm_function_map,
};
pub(crate) use mangle::{apply_symbol, lam_symbol};
pub use mangle::{native_symbol, trmc_symbol, MAIN_SYMBOL};
pub(crate) use native_kont::{
    state_map as native_kont_state_map, table as native_kont_table,
    IdentityRow as NativeKontIdentityRow,
};

#[cfg(feature = "mlir")]
pub use mlir::emit as emit_mlir;
