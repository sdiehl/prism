use std::collections::BTreeSet;

use crate::core::opt::{dump_core, next_dump_run};
use crate::core::typed::specialize::ho_specialize as ho_specialize_typed;
use crate::core::typed::specialize::specialize as specialize_typed;
use crate::core::typed::{
    cse as cse_typed, erase_newtypes as erase_newtypes_typed, exact_size as exact_size_typed,
    fuse as fuse_typed, inline as inline_typed, simplify as simplify_typed,
};
use crate::core::{
    audit_typed_core, lint_core, typed_verification_error, verify_typed_core, Core, CorePass,
    PassStage, PassStats, TypedCore, TypedCorePhase, UncheckedTypedCore, VerifyEnv,
};
use crate::error::Error;
use crate::sym::Sym;

use super::config::OptimizerDiagnostics;
use super::Config;

// Run one stage of the optimization pipeline over typed Core: verify the input,
// run each pass in order, and verify after every pass. The whole stage runs
// in-process with no durable cache: the pass work itself is tens of
// milliseconds on the full stdlib closure, so any per-definition cache has to
// beat that bar before it earns its lookups and writes back.
pub(super) fn run_typed_opt_queries<P: TypedCorePhase>(
    typed: TypedCore<P>,
    env: &VerifyEnv,
    newtype_ctors: &BTreeSet<Sym>,
    stage: PassStage,
    cfg: &Config,
) -> Result<TypedCore<P>, Error> {
    let passes = cfg
        .optimization_plan()
        .passes(stage, cfg.optimizer_options());
    let diagnostics = cfg.optimizer_diagnostics();
    audit_typed_core(&typed, env).map_err(typed_verification_error)?;
    run_typed_stage_plain(typed, env, newtype_ctors, stage, &passes, &diagnostics)
}

// Whole-program passes in order, with the diagnostic switches served from the
// erased view exactly as the erased pipeline served them (same dump labels and
// ordinals, same lint panic, same tick report).
fn run_typed_stage_plain<P: TypedCorePhase>(
    typed: TypedCore<P>,
    env: &VerifyEnv,
    newtype_ctors: &BTreeSet<Sym>,
    stage: PassStage,
    passes: &[CorePass],
    diagnostics: &OptimizerDiagnostics,
) -> Result<TypedCore<P>, Error> {
    let lint = |core: &Core, after: &str| {
        if diagnostics.core_lint {
            if let Err(errs) = lint_core(core, stage) {
                panic!(
                    "PRISM_CORE_LINT: ill-formed Core after {after}:\n{}",
                    errs.join("\n")
                );
            }
        }
    };
    let dump_sink = diagnostics.dump_core.clone();
    let dump_run = next_dump_run();
    let mut ord = 0;
    let mut stats = PassStats::default();
    if dump_sink.is_some() || diagnostics.core_lint {
        let erased = typed.clone().erase();
        if let Some(sink) = &dump_sink {
            dump_core(sink, dump_run, ord, "input", &erased);
            ord += 1;
        }
        lint(&erased, "<input>");
    }
    let mut current = typed;
    for &pass in passes {
        reject_off_stage(pass, stage)?;
        let (next, ticks) =
            run_typed_pass(pass, current, newtype_ctors, env, diagnostics.opt_stats)?;
        let next = verify_typed_core(next, env).map_err(typed_verification_error)?;
        stats.record(pass.name(), ticks);
        if dump_sink.is_some() || diagnostics.core_lint {
            let erased = next.clone().erase();
            lint(&erased, pass.name());
            if let Some(sink) = &dump_sink {
                dump_core(sink, dump_run, ord, pass.name(), &erased);
                ord += 1;
            }
        }
        current = next;
    }
    if diagnostics.opt_stats {
        eprint!("{}", stats.report());
    }
    Ok(current)
}

// A pass outside its stage is a driver routing bug, never a user error.
fn reject_off_stage(pass: CorePass, stage: PassStage) -> Result<(), Error> {
    if pass.stage() == stage {
        Ok(())
    } else {
        Err(Error::InternalInvariant(format!(
            "typed optimizer stage runner rejected {}",
            pass.name()
        )))
    }
}

fn run_typed_pass<P: TypedCorePhase>(
    pass: CorePass,
    core: TypedCore<P>,
    newtype_ctors: &BTreeSet<Sym>,
    env: &VerifyEnv,
    report_declines: bool,
) -> Result<(UncheckedTypedCore<P>, u64), Error> {
    Ok(match pass {
        CorePass::Fuse => {
            let (next, stats) = fuse_typed(core);
            (next, stats.ticks())
        }
        CorePass::Specialize => {
            let (next, stats) = specialize_typed(core).map_err(Error::from)?;
            (next, stats.ticks())
        }
        CorePass::HoSpecialize => {
            let (next, stats) = ho_specialize_typed(core, report_declines).map_err(Error::from)?;
            (next, stats.ticks())
        }
        CorePass::ExactSize => {
            let (next, stats) = exact_size_typed(core);
            (next, stats.ticks())
        }
        CorePass::Inline => {
            let (next, stats) = inline_typed(core);
            (next, stats.ticks())
        }
        CorePass::EraseNewtypes => {
            let (next, stats) = erase_newtypes_typed(core.into_unchecked(), newtype_ctors, env);
            (next, stats.ticks())
        }
        CorePass::Simplify => {
            let (next, stats) = simplify_typed(core.into_unchecked()).map_err(Error::from)?;
            (next, stats.ticks())
        }
        CorePass::Cse => {
            let (next, stats) = cse_typed(core.into_unchecked());
            (next, stats.ticks())
        }
    })
}

// The single predicate for "may this build read or write the durable store".
// The module interface cache and the native backend caches consult it, so the
// wasm carve-out and the flag logic live in exactly one place.
//
// The store is a filesystem cache; wasm32 (the browser playground) has no
// persistent filesystem and each compile is ephemeral, so opening it would fail
// `create_dir_all` with an unsupported-platform error. The cache is
// observationally invisible, so skipping it there changes nothing.
pub(super) const fn cache_enabled(cfg: &Config) -> bool {
    cfg.flags().compiler_cache && !cfg.flags().store && cfg!(not(target_arch = "wasm32"))
}
