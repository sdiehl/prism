//! The native and MLIR build surface: elaborate a source through to a linked
//! executable (or emitted IR), plus the rc-balance smoke that needs no backend.
//! Split out of the driver so `mod.rs` holds the front-end pipeline and this
//! module holds the codegen back door. Every external path (`prism::build`,
//! `prism::build_on_report`, `prism::emit_ir`, `prism::build_mlir`,
//! `prism::rc_balanced`) resolves through the re-export in `mod.rs`, so the split
//! is invisible to callers.

use std::path::Path;

use crate::error::Error;
#[cfg(feature = "native")]
use crate::lineage::FactOutcome;
use crate::resolve::default_roots;

#[cfg(feature = "native")]
use super::lowered_core_with_identity;
use super::{reuse_lowered_core, Config};

#[cfg(feature = "native")]
use std::collections::BTreeMap;

#[cfg(feature = "native")]
use crate::codegen::rt::RuntimeProfile;
#[cfg(feature = "native")]
use crate::codegen::{
    emit_llvm_bc_with_native_kont_table, emit_llvm_with_native_kont_table, llvm_function_map,
    llvm_scc_function_map,
};
#[cfg(feature = "native")]
use crate::core::residual_effects;
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
use super::backend::materialize_scc_bitcode;

#[cfg(feature = "native")]
const EXPLAIN_QUERY_DIR: &str = "prism-explain-queries";
#[cfg(feature = "native")]
use super::cache::{NativeArtifactCache, NativeCacheStatus};
#[cfg(feature = "native")]
use super::identity::{
    native_kont_table_for_with_rows, native_kont_table_of, NativeKontIdentityRows,
};
#[cfg(feature = "mlir")]
use super::native::ir_failure;
#[cfg(feature = "native")]
use super::native::{cc_link, cc_link_many};
#[cfg(feature = "native")]
use super::{commit_to_store, timing};

#[cfg(feature = "native")]
fn commit_session_decisions(roots: &[Root], cfg: &Config) -> Result<(), Error> {
    if let Some(session) = &cfg.session {
        session.commit_decisions(roots, cfg)?;
    }
    Ok(())
}

#[cfg(feature = "native")]
pub(super) fn compiled(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<
    (
        Checked,
        LoweredCore,
        BTreeMap<String, CtorInfo>,
        crate::core::Hashes,
    ),
    Error,
> {
    let (checked, lowered, ctors, hashes) = lowered_core_with_identity(src, roots, cfg)?;
    residual_effects(&lowered).map_err(Error::InternalInvariant)?;
    Ok((checked, lowered, ctors, hashes))
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
fn remove_stale_bitcode(out: &Path) -> Result<(), Error> {
    match std::fs::remove_file(out.with_extension("bc")) {
        Ok(()) => Ok(()),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(Error::Io(e)),
    }
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
    /// Final-binary compiler-query result for this build.
    pub cache: NativeCacheStatus,
    /// LLVM bitcode query result, or `Disabled` when a final-binary hit skipped it.
    pub bitcode_cache: NativeCacheStatus,
}

#[cfg(feature = "native")]
impl NativeBuildReport {
    /// Stable explanation of the exact durable-query boundary that invalidated.
    #[must_use]
    pub const fn cache_explanation(&self) -> &'static str {
        match (self.cache, self.bitcode_cache) {
            (NativeCacheStatus::Disabled, _) => "compiler cache disabled",
            (NativeCacheStatus::Hit, _) => "linked artifact key matched",
            (NativeCacheStatus::Write, NativeCacheStatus::Hit) => {
                "linked artifact key changed; LLVM bitcode key matched"
            }
            (NativeCacheStatus::Write, NativeCacheStatus::Write) => {
                "linked artifact and LLVM bitcode keys changed"
            }
            (NativeCacheStatus::Write, NativeCacheStatus::Disabled) => {
                "linked artifact key changed; LLVM bitcode cache disabled"
            }
            (NativeCacheStatus::Miss, _) => "linked artifact key did not match",
            (NativeCacheStatus::Write, NativeCacheStatus::Miss) => {
                "linked artifact and LLVM bitcode keys did not match"
            }
        }
    }
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
    let artifact_cache = NativeArtifactCache::for_build(src, roots, out, cfg)?;
    if let Some(cache) = &artifact_cache {
        if let Some(output_hash) = cache.materialize(out)? {
            remove_stale_bitcode(out)?;
            if let Some(session) = &cfg.session {
                session.record_hit();
            }
            cache.record_decision(cfg, FactOutcome::Hit, Some(output_hash.clone()), "");
            timing::cache_hit(
                cfg.timing.as_ref(),
                timing::Phase::CcLink,
                src,
                timing::ArtifactKind::Native,
                output_hash,
            );
            commit_session_decisions(roots, cfg)?;
            return Ok(NativeBuildReport {
                store: None,
                cache: NativeCacheStatus::Hit,
                bitcode_cache: NativeCacheStatus::Disabled,
            });
        }
        if let Some(session) = &cfg.session {
            session.record_miss();
        }
    }
    let (checked, core, ctors, hashes) = compiled(src, roots, cfg)?;
    require_main(&checked)?;
    let native_kont_table =
        native_kont_table_of(&hashes, roots, cfg, NativeKontIdentityRows::Full)?;
    let semantic_cache =
        NativeArtifactCache::for_semantic_build(&core, &ctors, &native_kont_table, out, cfg)?;
    if let Some(cache) = &semantic_cache {
        if let Some(output_hash) = cache.materialize(out)? {
            remove_stale_bitcode(out)?;
            if let Some(session) = &cfg.session {
                session.record_hit();
            }
            cache.record_decision(cfg, FactOutcome::Hit, Some(output_hash.clone()), "");
            if let Some(raw) = &artifact_cache {
                raw.bind_output(&output_hash)?;
                raw.record_decision(
                    cfg,
                    FactOutcome::Write,
                    Some(output_hash.clone()),
                    "raw source identity resolved to an existing semantic artifact",
                );
                if let Some(session) = &cfg.session {
                    session.record_write();
                }
            }
            timing::cache_hit(
                cfg.timing.as_ref(),
                timing::Phase::CcLink,
                src,
                timing::ArtifactKind::Native,
                output_hash,
            );
            commit_session_decisions(roots, cfg)?;
            return Ok(NativeBuildReport {
                store: None,
                cache: NativeCacheStatus::Hit,
                bitcode_cache: NativeCacheStatus::Disabled,
            });
        }
        if let Some(session) = &cfg.session {
            session.record_miss();
        }
    }
    let bc = out.with_extension("bc");
    let bitcode_cache = NativeArtifactCache::for_bitcode(&core, &ctors, &native_kont_table, cfg)?;
    let bitcode_hit = if let Some(cache) = &bitcode_cache {
        cache.materialize_file(&bc, false)?.map_or_else(
            || {
                if let Some(session) = &cfg.session {
                    session.record_miss();
                }
                false
            },
            |output_hash| {
                if let Some(session) = &cfg.session {
                    session.record_hit();
                }
                cache.record_decision(cfg, FactOutcome::Hit, Some(output_hash.clone()), "");
                timing::cache_hit(
                    cfg.timing.as_ref(),
                    timing::Phase::EmitLlvm,
                    src,
                    timing::ArtifactKind::Llvm,
                    output_hash,
                );
                true
            },
        )
    } else {
        false
    };
    let scc_directory = out.with_extension("prism_scc.d");
    let scc_bitcode = if bitcode_hit {
        None
    } else {
        materialize_scc_bitcode(&core, &ctors, &native_kont_table, &scc_directory, cfg)?
    };
    if !bitcode_hit && scc_bitcode.is_none() {
        let emit_status = if artifact_cache.is_some() {
            timing::CacheStatus::Miss
        } else {
            timing::CacheStatus::Cold
        };
        timing::timed_res_status(
            cfg.timing.as_ref(),
            timing::Phase::EmitLlvm,
            "",
            emit_status,
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
        if let Some(cache) = &bitcode_cache {
            let output = cache.store_result(&bc)?;
            cache.record_decision(
                cfg,
                FactOutcome::Write,
                Some(output),
                "whole-program bitcode inputs changed",
            );
            if let Some(session) = &cfg.session {
                session.record_write();
            }
        }
    }
    let bitcode_status = if bitcode_hit || scc_bitcode.as_ref().is_some_and(|scc| scc.all_hit) {
        NativeCacheStatus::Hit
    } else if bitcode_cache.is_some() {
        NativeCacheStatus::Write
    } else {
        NativeCacheStatus::Disabled
    };
    if scc_bitcode.is_some() {
        remove_stale_bitcode(out)?;
    }
    let link_status = if artifact_cache.is_some() {
        timing::CacheStatus::Write
    } else {
        timing::CacheStatus::Cold
    };
    let link_result = timing::timed_res_status(
        cfg.timing.as_ref(),
        timing::Phase::CcLink,
        "",
        link_status,
        || {
            scc_bitcode.as_ref().map_or_else(
                || cc_link(&bc, out, cfg, RuntimeProfile::NativeBackend),
                |scc| cc_link_many(&scc.paths, out, cfg, RuntimeProfile::NativeBackend),
            )
        },
        |()| timing::native_artifact(out),
    );
    let _ = std::fs::remove_dir_all(&scc_directory);
    link_result?;
    // A successful build populates the store when the knob is on. Re-elaboration
    // is cheap relative to codegen and only happens under the opt-in flag; the
    // store is a cache, so a failure here would not invalidate the build (but is
    // surfaced rather than swallowed).
    let store = if cfg.flags.store {
        Some(commit_to_store(src, roots, cfg)?)
    } else {
        None
    };
    let cache = if let Some(cache) = artifact_cache {
        let output_hash = cache.store_result(out)?;
        cache.record_decision(
            cfg,
            FactOutcome::Write,
            Some(output_hash.clone()),
            "source, compiler, runtime, or link inputs changed",
        );
        if let Some(session) = &cfg.session {
            session.record_write();
        }
        if let Some(semantic) = semantic_cache {
            semantic.bind_output(&output_hash)?;
            semantic.record_decision(
                cfg,
                FactOutcome::Write,
                Some(output_hash),
                "semantic program or link inputs changed",
            );
            if let Some(session) = &cfg.session {
                session.record_write();
            }
        }
        NativeCacheStatus::Write
    } else {
        NativeCacheStatus::Disabled
    };
    commit_session_decisions(roots, cfg)?;
    Ok(NativeBuildReport {
        store,
        cache,
        bitcode_cache: bitcode_status,
    })
}

/// Verify that SCC recomposition emits exactly the same normalized LLVM
/// function definitions as whole-program code generation.
///
/// # Errors
/// Fails compilation, code generation, or when any function body differs.
#[cfg(feature = "native")]
pub fn verify_backend_recomposition_on(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<(), Error> {
    let (_, core, ctors, _) = compiled(src, roots, cfg)?;
    let whole = llvm_function_map(&core, &ctors).map_err(Error::CodegenBackend)?;
    let mut recomposed = llvm_scc_function_map(&core, &ctors).map_err(Error::CodegenBackend)?;
    recomposed.retain(|name, _| whole.contains_key(name));
    if whole == recomposed {
        return Ok(());
    }
    let differing = whole
        .keys()
        .chain(recomposed.keys())
        .find(|name| whole.get(*name) != recomposed.get(*name))
        .cloned()
        .unwrap_or_else(|| "<unknown>".to_string());
    let detail = match (whole.get(&differing), recomposed.get(&differing)) {
        (Some(left), Some(right)) => left
            .lines()
            .zip(right.lines())
            .find(|(left, right)| left != right)
            .map_or_else(
                || "definition lengths differ".to_string(),
                |(left, right)| format!("whole `{left}`; recomposed `{right}`"),
            ),
        (Some(_), None) => "missing from recomposed output".to_string(),
        (None, Some(_)) => "added by recomposed output".to_string(),
        (None, None) => "unknown difference".to_string(),
    };
    Err(Error::CodegenVerification(format!(
        "whole-program and SCC-recomposed LLVM differ at `{differing}`: {detail}"
    )))
}

/// Evaluate downstream lowering and backend queries without linking an output.
/// Used by lineage explanation so final-linked-artifact hits cannot hide the
/// decisions beneath them.
///
/// # Errors
/// Fails on front-end, lowering, backend, or store errors.
#[cfg(feature = "native")]
pub(crate) fn explain_downstream_queries(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<(), Error> {
    let (_, core, ctors, hashes) = compiled(src, roots, cfg)?;
    let native_kont_table =
        native_kont_table_of(&hashes, roots, cfg, NativeKontIdentityRows::Full)?;
    let directory =
        std::env::temp_dir().join(format!("{EXPLAIN_QUERY_DIR}-{}", std::process::id()));
    let result = materialize_scc_bitcode(&core, &ctors, &native_kont_table, &directory, cfg);
    let _ = std::fs::remove_dir_all(directory);
    result?;
    commit_session_decisions(roots, cfg)
}

/// # Errors
/// Fails on front-end errors or codegen failure.
#[cfg(feature = "native")]
pub fn emit_ir(src: &str) -> Result<String, Error> {
    let roots = default_roots(Path::new("."));
    let cfg = Config::from_env();
    let (_, core, ctors, _) = compiled(src, &roots, &cfg)?;
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
    reuse_lowered_core(src, &default_roots(Path::new(".")), &Config::from_env()).map(|_| ())
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
    let (checked, core, ctors, _) = compiled(src, roots, cfg)?;
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
