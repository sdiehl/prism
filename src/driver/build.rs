//! The native and MLIR build surface: elaborate a source through to a linked
//! executable (or emitted IR), plus the rc-balance smoke that needs no backend.
//! Split out of the driver so `mod.rs` holds the front-end pipeline and this
//! module holds the codegen back door. Every external path (`prism::build`,
//! `prism::build_on_report`, `prism::emit_ir`, `prism::build_mlir`,
//! `prism::rc_balanced`) resolves through the re-export in `mod.rs`, so the split
//! is invisible to callers.

use std::path::Path;

use crate::core::{balanced, insert_rc, reuse};
use crate::error::Error;
use crate::resolve::default_roots;

use super::{lowered_core, Config};

#[cfg(feature = "native")]
use std::collections::BTreeMap;

#[cfg(feature = "native")]
use crate::codegen::rt::RuntimeProfile;
#[cfg(feature = "native")]
use crate::codegen::{emit_llvm_bc_with_native_kont_table, emit_llvm_with_native_kont_table};
#[cfg(feature = "native")]
use crate::core::effect_lower::residual_effects;
#[cfg(feature = "native")]
use crate::core::LoweredCore;
#[cfg(feature = "native")]
use crate::names::ENTRY_POINT;
#[cfg(feature = "native")]
use crate::resolve::Root;
#[cfg(feature = "native")]
use crate::store::disk::CommitStats;
#[cfg(feature = "native")]
use crate::types::{Checked, CtorInfo};

#[cfg(feature = "mlir")]
use std::fs;
#[cfg(feature = "mlir")]
use std::process::Command;

#[cfg(feature = "mlir")]
use crate::codegen::emit_mlir;

#[cfg(feature = "native")]
use super::identity::{
    native_kont_table_for, native_kont_table_for_with_rows, NativeKontIdentityRows,
};
#[cfg(feature = "native")]
use super::native::cc_link;
#[cfg(feature = "mlir")]
use super::native::ir_failure;
#[cfg(feature = "native")]
use super::{commit_to_store, timing};

#[cfg(feature = "native")]
pub(super) fn compiled(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<(Checked, LoweredCore, BTreeMap<String, CtorInfo>), Error> {
    let (checked, lowered, ctors, sigs) = lowered_core(src, roots, cfg)?;
    residual_effects(&lowered).map_err(Error::InternalInvariant)?;
    Ok((
        checked,
        LoweredCore(reuse(&insert_rc(&lowered, &sigs))),
        ctors,
    ))
}

/// # Errors
/// Fails on front-end errors, codegen failure, or when linking with cc fails.
#[cfg(feature = "native")]
pub fn build(src: &str, out: &Path) -> Result<(), Error> {
    build_at(src, Path::new("."), out)
}

/// Like [`build`], resolving any module imports relative to `base`.
///
/// # Errors
/// Fails on front-end errors, codegen failure, or when linking with cc fails.
#[cfg(feature = "native")]
pub fn build_at(src: &str, base: &Path, out: &Path) -> Result<(), Error> {
    build_on(src, &default_roots(base), out, &Config::from_env())
}

#[cfg(feature = "native")]
fn require_main(checked: &Checked) -> Result<(), Error> {
    if checked.decls.iter().any(|d| d.name == ENTRY_POINT) {
        Ok(())
    } else {
        Err(Error::CodegenBackend("no main function to build".into()))
    }
}

/// Facts reported by a successful native build.
#[cfg(feature = "native")]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct NativeBuildReport {
    /// Store commit statistics when `PRISM_STORE` is enabled.
    pub store: Option<CommitStats>,
}

/// Like [`build_at`], but against an explicit module search path (a project's
/// source root, its path dependencies, and the stdlib).
///
/// # Errors
/// Fails on front-end errors, codegen failure, or when linking with cc fails.
#[cfg(feature = "native")]
pub fn build_on(src: &str, roots: &[Root], out: &Path, cfg: &Config) -> Result<(), Error> {
    build_on_report(src, roots, out, cfg).map(|_| ())
}

/// Like [`build_on`], returning the cache facts the build observed.
///
/// # Errors
/// Fails on front-end errors, codegen failure, store failure, or when linking
/// with cc fails.
#[cfg(feature = "native")]
pub fn build_on_report(
    src: &str,
    roots: &[Root],
    out: &Path,
    cfg: &Config,
) -> Result<NativeBuildReport, Error> {
    let (checked, core, ctors) = compiled(src, roots, cfg)?;
    require_main(&checked)?;
    let native_kont_table = native_kont_table_for(src, roots, cfg)?;
    let bc = out.with_extension("bc");
    timing::timed_res(
        cfg.timing.as_ref(),
        timing::Phase::EmitLlvm,
        "",
        || {
            emit_llvm_bc_with_native_kont_table(
                &core,
                &ctors,
                &native_kont_table,
                cfg.flags.native_kont_frames,
                &bc,
            )
            .map_err(Error::CodegenBackend)
        },
        |()| timing::llvm_artifact(&bc),
    )?;
    timing::timed_res(
        cfg.timing.as_ref(),
        timing::Phase::CcLink,
        "",
        || cc_link(&bc, out, cfg, RuntimeProfile::NativeBackend),
        |()| timing::RowExtras::default(),
    )?;
    // A successful build populates the store when the knob is on. Re-elaboration
    // is cheap relative to codegen and only happens under the opt-in flag; the
    // store is a cache, so a failure here would not invalidate the build (but is
    // surfaced rather than swallowed).
    let store = if cfg.flags.store {
        Some(commit_to_store(src, roots, cfg)?)
    } else {
        None
    };
    Ok(NativeBuildReport { store })
}

/// # Errors
/// Fails on front-end errors or codegen failure.
#[cfg(feature = "native")]
pub fn emit_ir(src: &str) -> Result<String, Error> {
    let roots = default_roots(Path::new("."));
    let cfg = Config::from_env();
    let (_, core, ctors) = compiled(src, &roots, &cfg)?;
    let native_kont_table =
        native_kont_table_for_with_rows(src, &roots, &cfg, NativeKontIdentityRows::Portable)?;
    emit_llvm_with_native_kont_table(
        &core,
        &ctors,
        &native_kont_table,
        cfg.flags.native_kont_frames,
    )
    .map_err(Error::CodegenBackend)
}

/// # Errors
/// Fails on front-end errors or an unbalanced rc insertion.
pub fn rc_balanced(src: &str) -> Result<(), Error> {
    let (_, lowered, _, sigs) =
        lowered_core(src, &default_roots(Path::new(".")), &Config::from_env())?;
    balanced(&reuse(&insert_rc(&lowered, &sigs)), &sigs).map_err(Error::CodegenBackend)
}

/// # Errors
/// Fails on front-end errors, codegen failure, or when the MLIR toolchain fails.
#[cfg(feature = "mlir")]
pub fn build_mlir(src: &str, out: &Path) -> Result<(), Error> {
    build_mlir_at(src, Path::new("."), out)
}

/// Like [`build_mlir`], resolving any module imports relative to `base`.
///
/// # Errors
/// Fails on front-end errors, codegen failure, or when the MLIR toolchain fails.
#[cfg(feature = "mlir")]
pub fn build_mlir_at(src: &str, base: &Path, out: &Path) -> Result<(), Error> {
    build_mlir_on(src, &default_roots(base), out, &Config::from_env())
}

/// Like [`build_mlir_at`], but against an explicit module search path.
///
/// # Errors
/// Fails on front-end errors, codegen failure, or when the MLIR toolchain fails.
#[cfg(feature = "mlir")]
pub fn build_mlir_on(src: &str, roots: &[Root], out: &Path, cfg: &Config) -> Result<(), Error> {
    let (checked, core, ctors) = compiled(src, roots, cfg)?;
    require_main(&checked)?;
    let mlir_text = emit_mlir(&core, &ctors).map_err(Error::CodegenBackend)?;
    let mlir_file = out.with_extension("mlir");
    fs::write(&mlir_file, &mlir_text)?;

    let ll_file = out.with_extension("ll");
    let translate_out = Command::new("mlir-translate")
        .arg("--mlir-to-llvmir")
        .arg(&mlir_file)
        .output()
        .map_err(|e| {
            Error::CodegenBackend(format!(
                "mlir-translate: {e} (is mlir-translate installed?)"
            ))
        })?;
    if !translate_out.status.success() {
        return Err(ir_failure(
            "mlir-translate",
            &mlir_file,
            &translate_out.stderr,
        ));
    }
    fs::write(&ll_file, &translate_out.stdout)?;

    let res = cc_link(&ll_file, out, cfg, RuntimeProfile::HostOracle);
    let _ = fs::remove_file(&mlir_file);
    res
}
