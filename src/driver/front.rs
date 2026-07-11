//! The one staged front-end runner.
//!
//! Every driver entry point (`check`, `frontend`, `elaborated`, the dumps, the
//! interpreters) runs a prefix of lex/parse/resolve/desugar/typecheck/elaborate,
//! historically each with its own subtly different stops and warning policies. A
//! single [`run_front`] holds that pipeline; the differences that exist on purpose
//! between entry points become the named fields of [`FrontOpts`], so a divergence
//! is either expressible there or it cannot happen. Consumers read the stage they
//! need off the returned [`Front`] and apply their own presentation.

use crate::core::opt::PassStage;
use crate::core::{elaborate, newtype_ctors, run_opt, run_opt_spec, ElaboratedCore};
use crate::error::Error;
use crate::parse::{parse, ParseResult};
use crate::resolve::{resolve_modules_in, Root};
use crate::syntax::ast::{Core as CorePhase, Program};
use crate::syntax::desugar::{desugar, retarget_cooperative};
use crate::types::{check as typecheck, Checked};

use super::timing::{self, ArtifactKind, CountKey, Phase, RowExtras};
use super::verify::{fip_check, reconcile_effects, replayable_check};
use super::{core_root_digest, emit_warnings, lint_surface, Config};

// How far [`run_front`] drives the pipeline. A consumer that needs only types
// stops at `Checked` and never pays for elaboration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FrontStop {
    // Stop after typechecking; the resulting `Front` carries no Core.
    Checked,
    // Continue through elaboration into pre-optimizer Core.
    Elaborated,
}

// The intentional, named divergences between frontend consumers. Every field is
// a difference that exists on purpose between two existing entry points; anything
// not expressible here cannot differ between them, because each entry point runs
// the single `run_front` with one of these presets.
// Each flag is an independent, on-purpose policy difference between entry points,
// not a state machine; the family is deliberately flat so the presets read as a
// table.
#[derive(Clone, Copy, Debug)]
#[allow(clippy::struct_excessive_bools)]
pub(super) struct FrontOpts {
    // The stage to stop at.
    stop: FrontStop,
    // Compute surface lints and print checker/lint warnings to stderr. Off for the
    // quiet identity surface, which observes Core rather than diagnostics.
    diagnostics: bool,
    // Retarget the policy-neutral cooperative scheduler entry per `cfg.scheduler`.
    // Off for the identity surface: a program's hash must not move with the
    // `--scheduler` choice.
    scheduler_retarget: bool,
    // Run the fip / replayable / effect-reconciliation validators. They judge the
    // program as written, so they run only on the full compile path, not on the
    // pre-opt identity surface or the type-only stop.
    validate: bool,
    // Run the pre-lowering Core-to-Core optimizer. Off for the identity surface:
    // identity is a property of the pre-optimizer term, independent of the level.
    pre_opt: bool,
}

impl FrontOpts {
    // Type-check only, with diagnostics: the `check` family.
    pub(super) const CHECK: Self = Self {
        stop: FrontStop::Checked,
        diagnostics: true,
        scheduler_retarget: false,
        validate: false,
        pre_opt: false,
    };
    // The full compile path: scheduler retarget, validators, and the pre-lowering
    // optimizer, feeding lowering and codegen.
    pub(super) const FULL: Self = Self {
        stop: FrontStop::Elaborated,
        diagnostics: true,
        scheduler_retarget: true,
        validate: true,
        pre_opt: true,
    };
    // The public validity verdict (`prism check`): elaborate and run every
    // semantic validator (fip / replayable / effect reconciliation), but stop
    // before scheduler retarget, optimization, lowering, and codegen. This is
    // what makes `check` agree with `build`: a program `check` accepts is one the
    // compiler considers valid, the fip / noalloc / replayable annotations
    // included. The type-only `CHECK` preset stays for internal callers (dump,
    // report, snapshots) that observe the checked program rather than judging it.
    pub(super) const CHECK_VALIDATED: Self = Self {
        stop: FrontStop::Elaborated,
        diagnostics: true,
        scheduler_retarget: false,
        validate: true,
        pre_opt: false,
    };
    // The content-addressed identity surface, additionally validated: the store
    // and package paths commit only programs that pass every semantic validator,
    // so a persisted definition never carries an fbip / noalloc / replayable
    // claim the build path would reject. Validation is side-effect-free on the
    // pre-optimizer Core, so the committed identity is byte-identical to `IDENTITY`.
    pub(super) const IDENTITY_VALIDATED: Self = Self {
        stop: FrontStop::Elaborated,
        diagnostics: false,
        scheduler_retarget: false,
        validate: true,
        pre_opt: false,
    };
    // The content-addressed identity surface: pre-optimizer Core with no scheduler
    // retarget, no validators, and no diagnostics, so a hash depends on the source
    // alone.
    pub(super) const IDENTITY: Self = Self {
        stop: FrontStop::Elaborated,
        diagnostics: false,
        scheduler_retarget: false,
        validate: false,
        pre_opt: false,
    };
}

// The staged frontend results, held as one value so every entry point reads the
// stage it needs from a common runner rather than re-deriving a prefix of the
// pipeline with its own subtly different stops and policies.
pub(super) struct Front {
    program: Program<CorePhase>,
    checked: Checked,
    // The pre-optimizer elaborated Core, present iff the runner was asked to stop
    // at `FrontStop::Elaborated`.
    core: Option<ElaboratedCore>,
}

impl Front {
    // The checked program, for a `FrontStop::Checked` consumer.
    pub(super) fn into_checked(self) -> Checked {
        self.checked
    }

    // The elaborated stages as the legacy positional tuple. Only called by
    // consumers that requested `FrontStop::Elaborated`, so a missing Core is a
    // driver bug, not a user error.
    pub(super) fn into_elaborated(self) -> (Program<CorePhase>, Checked, ElaboratedCore) {
        let core = self
            .core
            .expect("Front::into_elaborated on a type-only front");
        (self.program, self.checked, core)
    }
}

// The one canonical frontend runner. Every entry point derives its stages from
// here, selecting the intentional divergences through `opts`; nothing else may
// differ between them.
pub(super) fn run_front(
    src: &str,
    roots: &[Root],
    cfg: &Config,
    opts: FrontOpts,
) -> Result<Front, Error> {
    let timer = cfg.timing.as_ref();
    let ParseResult { program, .. } = timing::timed_res(
        timer,
        Phase::Parse,
        src,
        || parse(src),
        |_| RowExtras::default(),
    )?;
    let program = timing::timed_res(
        timer,
        Phase::Resolve,
        src,
        || resolve_modules_in(program, roots),
        |_| RowExtras::default(),
    )?;
    let lints = if opts.diagnostics {
        lint_surface(src, &program)
    } else {
        Vec::new()
    };
    let mut program = timing::timed_res(
        timer,
        Phase::Desugar,
        src,
        || desugar(program),
        |_| RowExtras::default(),
    )?;
    if opts.scheduler_retarget {
        if let Some(target) = cfg.scheduler.retarget() {
            retarget_cooperative(&mut program, target);
        }
    }
    let mut checked = timing::timed_res(
        timer,
        Phase::Typecheck,
        src,
        || typecheck(&program),
        |c: &Checked| RowExtras::default().count(CountKey::Defs, c.decls.len()),
    )?;
    if opts.diagnostics {
        checked.warnings.extend(lints);
        emit_warnings(src, &checked);
    }
    if opts.stop == FrontStop::Checked {
        return Ok(Front {
            program,
            checked,
            core: None,
        });
    }
    let core = timing::timed_res(
        timer,
        Phase::Elaborate,
        src,
        || elaborate(&program, &checked),
        |c| RowExtras::default().out(ArtifactKind::Core, core_root_digest(&program, &checked, c)),
    )?;
    if opts.validate {
        fip_check(&program, &checked, &core)?;
        replayable_check(&program, &checked)?;
        reconcile_effects(&checked, &core)?;
    }
    // Mid-level Core-to-Core optimization tier. Runs above the interpreter/native
    // fork so both backends consume the same optimized Core (the parity oracle
    // holds by construction). Placed after the fip/effect validators so they
    // still judge the program as written. Newtype erasure is mandatory (a
    // representation both backends depend on); specialization is opt-out via
    // `PRISM_NO_SPECIALIZE`. The level comes from the CLI `-O` flag (default O1),
    // unless an explicit `--passes` spec overrides it with its pre-stage list.
    let core = if opts.pre_opt {
        timing::timed(
            timer,
            Phase::OptPre,
            src,
            || {
                let nt = newtype_ctors(&program);
                let (core, _stats) = cfg.passes.as_ref().map_or_else(
                    || {
                        run_opt(
                            &core,
                            &nt,
                            cfg.opt,
                            PassStage::PreLowering,
                            &cfg.disabled,
                            &cfg.flags,
                        )
                    },
                    |spec| {
                        run_opt_spec(
                            &core,
                            &nt,
                            &spec.pre,
                            PassStage::PreLowering,
                            &cfg.disabled,
                            &cfg.flags,
                        )
                    },
                );
                core
            },
            |_| RowExtras::default(),
        )
    } else {
        core
    };
    Ok(Front {
        program,
        checked,
        core: Some(ElaboratedCore(core)),
    })
}
