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
pub use emit::ClosureSummary;
pub use isa::{Buf, Cmp, FloatBinOp, FloatIntrinsic, IntOp, Isa};
pub use llvm::{
    compile_bitcode_to_object as compile_llvm_bitcode_to_object, emit as emit_llvm,
    emit_bitcode as emit_llvm_bc,
    emit_bitcode_with_native_kont_table as emit_llvm_bc_with_native_kont_table,
    emit_native_kont_plan_bitcode as emit_llvm_native_kont_plan_bc,
    emit_selected_bitcode as emit_llvm_scc_bc,
    emit_with_native_kont_table as emit_llvm_with_native_kont_table, ClosurePlanShard,
    SccBitcodeError,
};
pub use llvm::{
    emit_closure_plan_shard_bitcode as emit_llvm_closure_plan_shard_bc,
    plan_closures_from_summaries as plan_llvm_closures_from_summaries,
    scc_closure_summary as llvm_scc_closure_summary, scc_function_map as llvm_scc_function_map,
    whole_function_map as llvm_function_map,
};
pub use mangle::{apply_symbol, lam_symbol};
pub use mangle::{native_symbol, trmc_symbol, MAIN_SYMBOL};
pub use native_kont::{
    state_map as native_kont_state_map, table as native_kont_table,
    IdentityRow as NativeKontIdentityRow,
};

#[cfg(feature = "mlir")]
pub use mlir::emit as emit_mlir;

/// Keep a module a backend tool rejected in the temp directory for inspection,
/// and say where for the error message.
///
/// Each failure gets its own file, named by process and a per-process count,
/// so concurrent failures (parallel shards, or several compiler processes) do
/// not overwrite one another's evidence.
#[must_use]
pub fn keep_failed(ext: &str, bytes: &[u8]) -> String {
    static COUNT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let n = COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let kept = std::env::temp_dir().join(format!("prism_failed-{}-{n}.{ext}", std::process::id()));
    match std::fs::write(&kept, bytes) {
        Ok(()) => format!("kept at {}", kept.display()),
        Err(error) => format!("not kept ({}: {error})", kept.display()),
    }
}
