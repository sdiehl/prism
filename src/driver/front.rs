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
use crate::core::{elaborate, newtype_ctors, ElaboratedCore};
use crate::error::Error;
use crate::parse::{parse, ParseResult};
use crate::resolve::{resolve_loaded_modules, resolve_modules_in, Module, Root};
use crate::syntax::ast::{Core as CorePhase, Program};
use crate::syntax::desugar::{desugar, retarget_cooperative};
use crate::types::{check as typecheck, Checked};

use crate::tc::WarningOrigin;

use super::downstream::run_opt_queries;
use super::input::{
    field, load_front_inputs, semantic_inputs_digest, semantic_loaded_inputs_digest,
    source_inputs_digest,
};
use super::timing::{self, ArtifactKind, CountKey, Phase, RowExtras};
use super::verify::{fip_check, reconcile_effects, replayable_check};
use super::{core_root_digest, emit_warnings, lint_surface, Config};

const RAW_FRONT_QUERY_SCHEMA: &[u8] = b"prism-session-front-v1";
const SEMANTIC_FRONT_QUERY_SCHEMA: &[u8] = b"prism-session-semantic-front-v1";

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
#[derive(Clone, Debug)]
pub(super) struct Front {
    program: Program<CorePhase>,
    checked: Checked,
    // The Core selected for this consumer (pre-optimizer for identity/check,
    // optimized for the full compile path).
    core: Option<ElaboratedCore>,
    // The pre-optimizer identity Core, retained on the full path so hashing and
    // native metadata never re-run the frontend merely to recover it.
    #[cfg(feature = "native")]
    identity_core: Option<ElaboratedCore>,
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

    #[cfg(feature = "native")]
    pub(super) fn into_compilation(
        self,
    ) -> (Program<CorePhase>, Checked, ElaboratedCore, ElaboratedCore) {
        let core = self
            .core
            .expect("Front::into_compilation on a type-only front");
        let identity = self
            .identity_core
            .expect("Front::into_compilation without identity Core");
        (self.program, self.checked, identity, core)
    }
}

struct PreparedFront {
    program: Program<CorePhase>,
    lints: Vec<crate::tc::Warning>,
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
    let Some(session) = &cfg.session else {
        return run_front_uncached(src, roots, cfg, opts);
    };
    let loaded = if cfg.timing.is_none() {
        Some(load_front_inputs(src, roots, cfg.flags.query_threads)?)
    } else {
        None
    };
    let raw_key = if let Some(inputs) = &loaded {
        front_key_for(RAW_FRONT_QUERY_SCHEMA, &inputs.raw_digest, cfg, opts)
    } else {
        front_key(src, roots, cfg, opts)?
    };
    if let Some(front) = session.lookup(&raw_key) {
        session.record_hit();
        if opts.diagnostics {
            emit_warnings(src, &front.checked);
        }
        return Ok(front);
    }
    let (semantic_key, prepared) = if let Some(inputs) = loaded {
        let semantic =
            semantic_loaded_inputs_digest(src, &inputs.modules, roots, cfg.flags.query_threads)?;
        let key = front_key_for(SEMANTIC_FRONT_QUERY_SCHEMA, &semantic, cfg, opts);
        let prepared = prepare_loaded_front(src, cfg, opts, inputs.root, inputs.modules)?;
        (key, prepared)
    } else {
        (
            semantic_front_key(src, roots, cfg, opts)?,
            prepare_front(src, roots, cfg, opts)?,
        )
    };
    if let Some(mut front) = session.lookup(&semantic_key) {
        session.record_hit();
        front.program = prepared.program;
        refresh_warnings(&front.program, &mut front.checked, prepared.lints);
        if opts.diagnostics {
            emit_warnings(src, &front.checked);
        }
        session.insert_aliases([raw_key], &front);
        return Ok(front);
    }
    session.record_miss();
    let front = finish_front(src, cfg, opts, prepared)?;
    session.insert_aliases([raw_key, semantic_key], &front);
    Ok(front)
}

fn front_key(src: &str, roots: &[Root], cfg: &Config, opts: FrontOpts) -> Result<String, Error> {
    let input = source_inputs_digest(src, roots, cfg.flags.query_threads)?;
    Ok(front_key_for(RAW_FRONT_QUERY_SCHEMA, &input, cfg, opts))
}

fn semantic_front_key(
    src: &str,
    roots: &[Root],
    cfg: &Config,
    opts: FrontOpts,
) -> Result<String, Error> {
    let input = semantic_inputs_digest(src, roots, cfg.flags.query_threads)?;
    Ok(front_key_for(
        SEMANTIC_FRONT_QUERY_SCHEMA,
        &input,
        cfg,
        opts,
    ))
}

fn front_key_for(schema: &[u8], input: &str, cfg: &Config, opts: FrontOpts) -> String {
    let mut h = blake3::Hasher::new();
    field(&mut h, schema);
    field(&mut h, input.as_bytes());
    field(
        &mut h,
        cfg.artifact_identity_for("frontend")
            .fingerprint()
            .as_bytes(),
    );
    field(
        &mut h,
        &[
            opts.stop as u8,
            u8::from(opts.diagnostics),
            u8::from(opts.scheduler_retarget),
            u8::from(opts.validate),
            u8::from(opts.pre_opt),
        ],
    );
    h.finalize().to_hex().to_string()
}

fn run_front_uncached(
    src: &str,
    roots: &[Root],
    cfg: &Config,
    opts: FrontOpts,
) -> Result<Front, Error> {
    let prepared = prepare_front(src, roots, cfg, opts)?;
    finish_front(src, cfg, opts, prepared)
}

fn prepare_front(
    src: &str,
    roots: &[Root],
    cfg: &Config,
    opts: FrontOpts,
) -> Result<PreparedFront, Error> {
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
    prepare_resolved_front(src, cfg, opts, program)
}

fn prepare_loaded_front(
    src: &str,
    cfg: &Config,
    opts: FrontOpts,
    root: Program,
    modules: Vec<Module>,
) -> Result<PreparedFront, Error> {
    debug_assert!(cfg.timing.is_none());
    let program = resolve_loaded_modules(root, modules)?;
    prepare_resolved_front(src, cfg, opts, program)
}

fn prepare_resolved_front(
    src: &str,
    cfg: &Config,
    opts: FrontOpts,
    program: Program,
) -> Result<PreparedFront, Error> {
    let timer = cfg.timing.as_ref();
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
    Ok(PreparedFront { program, lints })
}

fn finish_front(
    src: &str,
    cfg: &Config,
    opts: FrontOpts,
    prepared: PreparedFront,
) -> Result<Front, Error> {
    let timer = cfg.timing.as_ref();
    let PreparedFront { program, lints } = prepared;
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
            #[cfg(feature = "native")]
            identity_core: None,
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
    #[cfg(feature = "native")]
    let identity_core = core.clone();
    let core = if opts.pre_opt {
        timing::timed_res(
            timer,
            Phase::OptPre,
            src,
            || {
                let nt = newtype_ctors(&program);
                run_opt_queries(&core, &nt, PassStage::PreLowering, cfg)
            },
            |_| RowExtras::default(),
        )?
    } else {
        core
    };
    Ok(Front {
        program,
        checked,
        core: Some(ElaboratedCore(core)),
        #[cfg(feature = "native")]
        identity_core: Some(ElaboratedCore(identity_core)),
    })
}

fn refresh_warnings(
    program: &Program<CorePhase>,
    checked: &mut Checked,
    surface_lints: Vec<crate::tc::Warning>,
) {
    checked
        .warnings
        .retain(|warning| !matches!(warning.origin, WarningOrigin::Surface));
    for warning in &mut checked.warnings {
        match warning.origin {
            WarningOrigin::Decl(name) => {
                if let Some(decl) = program.fns.iter().find(|decl| decl.name == name.as_str()) {
                    warning.span = decl.span;
                }
            }
            WarningOrigin::RootInstance(name) => {
                if let Some(instance) = program
                    .instances
                    .iter()
                    .find(|instance| instance.module.is_empty() && instance.name == name.as_str())
                {
                    warning.span = instance.span;
                }
            }
            WarningOrigin::Imported | WarningOrigin::Surface => {}
        }
    }
    checked.warnings.extend(surface_lints);
}
