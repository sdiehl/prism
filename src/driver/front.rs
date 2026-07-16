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
use crate::core::typed::{execute_pre as execute_typed_pre, PreExecutorFailure};
use crate::core::{
    effective_passes, elaborate_typed, newtype_ctors, typed_verification_error, Core,
    ElaboratedCore, TypedCore, TypedElaborated, VerifyEnv,
};
use crate::error::{Error, TypedCoreErasureFailure};
use crate::flags::WarnDupes;
use crate::parse::{parse, ParseResult};
use crate::resolve::{resolve_loaded_modules, resolve_modules_in, Module, Root};
use crate::syntax::ast::{Core as CorePhase, Program};
use crate::syntax::desugar::{desugar, retarget_cooperative};
use crate::types::{check as typecheck, check_allow_holes, Checked};

use crate::tc::WarningOrigin;

use super::downstream::run_opt_queries;
use super::input::{
    field, load_front_inputs, semantic_inputs_digest, semantic_loaded_inputs_digest,
    source_inputs_digest,
};
use super::timing::{self, ArtifactKind, CountKey, Phase, RowExtras};
use super::verify::{fip_check, reconcile_effects, replayable_check};
use super::{
    core_root_digest, dupes, emit_warning, emit_warnings, lint_surface, stdlib_hash, Config,
};

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
    // Retain typed holes through elaboration. Only the interpreter's explicit
    // deferred-hole entry point selects this; every compiler/codegen preset
    // keeps the ordinary up-front refusal.
    allow_holes: bool,
    // Collect exact per-node type/effect strings for the read-only typespans
    // dump. Off everywhere else so presentation metadata cannot affect builds.
    typed_tooltips: bool,
}

impl FrontOpts {
    // Type-check only, with diagnostics: the `check` family.
    pub(super) const CHECK: Self = Self {
        stop: FrontStop::Checked,
        diagnostics: true,
        scheduler_retarget: false,
        validate: false,
        pre_opt: false,
        allow_holes: false,
        typed_tooltips: false,
    };
    // The full compile path: scheduler retarget, validators, and the pre-lowering
    // optimizer, feeding lowering and codegen.
    pub(super) const FULL: Self = Self {
        stop: FrontStop::Elaborated,
        diagnostics: true,
        scheduler_retarget: true,
        validate: true,
        pre_opt: true,
        allow_holes: false,
        typed_tooltips: false,
    };
    // The full interpreter path with typed holes elaborated to deterministic
    // faults. Kept distinct from `FULL` so native and wasm cannot inherit it.
    pub(super) const FULL_DEFERRED_HOLES: Self = Self {
        stop: FrontStop::Elaborated,
        diagnostics: true,
        scheduler_retarget: true,
        validate: true,
        pre_opt: true,
        allow_holes: true,
        typed_tooltips: false,
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
        allow_holes: false,
        typed_tooltips: false,
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
        allow_holes: false,
        typed_tooltips: false,
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
        allow_holes: false,
        typed_tooltips: false,
    };
    // Typecheck-only analysis for `dump typespans` and static documentation
    // tooltips. It shares every ordinary check policy except the extra facts.
    pub(super) const TYPED_TOOLTIPS: Self = Self {
        stop: FrontStop::Checked,
        diagnostics: false,
        scheduler_retarget: false,
        validate: false,
        pre_opt: false,
        allow_holes: false,
        typed_tooltips: true,
    };
}

// The staged frontend results, held as one value so every entry point reads the
// stage it needs from a common runner rather than re-deriving a prefix of the
// pipeline with its own subtly different stops and policies.
#[derive(Clone, Debug)]
pub(super) struct Front {
    program: Program<CorePhase>,
    checked: Checked,
    // The verified typed artifact after the complete configured pre-lowering
    // pass sequence. Raw Core remains a compatibility and presentation shadow.
    typed_pre: Option<TypedFront>,
    // The Core selected for this consumer (pre-optimizer for identity/check,
    // optimized for the full compile path).
    core: Option<ElaboratedCore>,
    // The pre-optimizer identity Core, retained on the full path so hashing and
    // native metadata never re-run the frontend merely to recover it.
    #[cfg(feature = "native")]
    identity_core: Option<ElaboratedCore>,
}

#[derive(Clone, Debug)]
struct TypedFront {
    core: TypedCore<TypedElaborated>,
    verify_env: VerifyEnv,
}

impl Front {
    // The checked program, for a `FrontStop::Checked` consumer.
    pub(super) fn into_checked(self) -> Checked {
        self.checked
    }

    pub(super) fn into_program_checked(self) -> (Program<CorePhase>, Checked) {
        (self.program, self.checked)
    }

    // The verified artifact after the complete pre-lowering optimizer. The raw
    // tree travels with it only for existing compatibility consumers.
    pub(super) fn into_typed_pre(
        self,
    ) -> (
        Program<CorePhase>,
        Checked,
        ElaboratedCore,
        TypedCore<TypedElaborated>,
        VerifyEnv,
    ) {
        let core = self
            .core
            .expect("Front::into_typed_pre on a type-only front");
        let typed = self
            .typed_pre
            .expect("Front::into_typed_pre on a type-only front");
        (
            self.program,
            self.checked,
            core,
            typed.core,
            typed.verify_env,
        )
    }

    // The elaborated stages as the legacy positional tuple. Only called by
    // consumers that requested `FrontStop::Elaborated`, so a missing Core is a
    // driver bug, not a user error.
    pub(super) fn into_elaborated(self) -> (Program<CorePhase>, Checked, ElaboratedCore) {
        let (program, checked, core, _typed, _verify_env) = self.into_typed_pre();
        (program, checked, core)
    }

    #[cfg(feature = "native")]
    pub(super) fn into_compilation(
        self,
    ) -> (
        Program<CorePhase>,
        Checked,
        ElaboratedCore,
        ElaboratedCore,
        TypedCore<TypedElaborated>,
        VerifyEnv,
    ) {
        let identity = self
            .identity_core
            .expect("Front::into_compilation without identity Core");
        let core = self
            .core
            .expect("Front::into_compilation on a type-only front");
        let typed = self
            .typed_pre
            .expect("Front::into_compilation on a type-only front");
        (
            self.program,
            self.checked,
            identity,
            core,
            typed.core,
            typed.verify_env,
        )
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
        if opts.diagnostics && !cfg.flags.quiet {
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
        if opts.diagnostics && !cfg.flags.quiet {
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
            u8::from(opts.allow_holes),
            u8::from(opts.typed_tooltips),
            // Duplicate detection is diagnostics-only and never touches a content
            // hash, so it is absent from the artifact fingerprint; it must still
            // split the cache, or a warn/strict run could be served a front
            // computed (and stored warning-free) under a different mode. Both
            // knobs (own clones, stdlib reimplementations) split it.
            cfg.flags.warn_dupes as u8,
            cfg.flags.warn_stdlib_dupes as u8,
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
        || {
            if opts.typed_tooltips {
                crate::tc::check_tooltips(&program)
            } else if opts.allow_holes {
                check_allow_holes(&program)
            } else {
                typecheck(&program)
            }
        },
        |c: &Checked| RowExtras::default().count(CountKey::Defs, c.decls.len()),
    )?;
    if opts.diagnostics {
        checked.warnings.extend(lints);
        if !cfg.flags.quiet {
            emit_warnings(src, &checked);
        }
    }
    if opts.stop == FrontStop::Checked {
        return Ok(Front {
            program,
            checked,
            typed_pre: None,
            core: None,
            #[cfg(feature = "native")]
            identity_core: None,
        });
    }
    let elaboration = timing::timed_res(
        timer,
        Phase::Elaborate,
        src,
        || elaborate_typed(&program, &checked),
        |elaboration| {
            RowExtras::default().out(
                ArtifactKind::Core,
                core_root_digest(&program, &checked, elaboration.compatibility()),
            )
        },
    )?;
    let (core, typed, verify_env) = elaboration.into_parts();
    if opts.validate {
        fip_check(&program, &checked, &core)?;
        replayable_check(&program, &checked)?;
        reconcile_effects(&checked, &core)?;
    }
    // Duplicate detection runs on the pre-optimizer identity Core (matching the
    // stdlib fingerprint's regime), only on the user-facing validated paths, and
    // never on the hashing/identity surfaces. It reports after the batch warning
    // emit above, so its findings are emitted here, not through that pass. The
    // stdlib-reimplementation half is on by default; the own-clone half is opt-in.
    if opts.diagnostics
        && opts.validate
        && (cfg.flags.warn_dupes.enabled() || cfg.flags.warn_stdlib_dupes.enabled())
    {
        apply_dupes(src, cfg, &program, &mut checked, &core)?;
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
    let (core, typed) = if opts.pre_opt {
        timing::timed_res(
            timer,
            Phase::OptPre,
            src,
            || -> Result<(Core, TypedCore<TypedElaborated>), Error> {
                let nt = newtype_ctors(&program);
                let passes = effective_passes(
                    cfg.opt,
                    cfg.passes.as_ref(),
                    PassStage::PreLowering,
                    &cfg.disabled,
                    &cfg.flags,
                );
                let (typed, _stats) =
                    execute_typed_pre(typed, &verify_env, &nt, &passes).map_err(typed_pre_error)?;
                let compatibility = run_opt_queries(&core, &nt, PassStage::PreLowering, cfg)?;
                if typed.clone().erase() != compatibility {
                    return Err(TypedCoreErasureFailure.into());
                }
                Ok((compatibility, typed))
            },
            |_| RowExtras::default(),
        )?
    } else {
        (core, typed)
    };
    Ok(Front {
        program,
        checked,
        typed_pre: Some(TypedFront {
            core: typed,
            verify_env,
        }),
        core: Some(ElaboratedCore(core)),
        #[cfg(feature = "native")]
        identity_core: Some(ElaboratedCore(identity_core)),
    })
}

fn typed_pre_error(failure: PreExecutorFailure) -> Error {
    match failure {
        PreExecutorFailure::UnsupportedPass { occurrence, pass } => {
            Error::InternalInvariant(format!(
                "typed pre-lowering executor rejected {} at occurrence {occurrence}",
                pass.name()
            ))
        }
        PreExecutorFailure::Verification { violations, .. } => typed_verification_error(violations),
        PreExecutorFailure::Specialize { failure, .. } => failure.into(),
    }
}

// Run duplicate detection and surface each finding per the knob that governs it:
// own-clone groups by `warn_dupes`, stdlib reimplementations by
// `warn_stdlib_dupes`. A finding under a `Strict` knob aborts the compile with its
// declaration-family E-code (the earliest such wins, findings being source-sorted);
// a finding under `Warn` is recorded on `checked` (so a non-quiet semantic cache
// hit re-emits it) and emitted immediately unless quiet. The stdlib fingerprint is
// memoized, so this pays a fold only on the first call in a process.
fn apply_dupes(
    src: &str,
    cfg: &Config,
    program: &Program<CorePhase>,
    checked: &mut Checked,
    core: &Core,
) -> Result<(), Error> {
    let stdlib = stdlib_hash()?;
    let want = dupes::Want {
        clone: cfg.flags.warn_dupes.enabled(),
        stdlib: cfg.flags.warn_stdlib_dupes.enabled(),
    };
    let found = dupes::findings(src, program, checked, core, &stdlib.defs, want);
    for finding in found {
        let mode = if finding.is_stdlib() {
            cfg.flags.warn_stdlib_dupes
        } else {
            cfg.flags.warn_dupes
        };
        if mode == WarnDupes::Strict {
            return Err(finding.into_error());
        }
        let warning = finding.warning();
        if !cfg.flags.quiet {
            emit_warning(src, &warning);
        }
        checked.warnings.push(warning);
    }
    Ok(())
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

#[cfg(test)]
mod typed_pass_route_tests {
    use super::*;
    use crate::core::OptLevel;
    use crate::lineage::{FactOutcome, QueryKind};
    use crate::CompilerSession;

    #[test]
    fn front_retains_the_verified_full_typed_pre_result_across_session_clones() {
        let session = CompilerSession::new();
        let cfg = Config {
            opt: OptLevel::O2,
            session: Some(session.clone()),
            ..Config::default()
        };
        let source = concat!(
            "newtype Wrap = Wrap(Int)\n",
            "fn unwrap(w : Wrap) : Int = match w of { Wrap(n) => n }\n",
            "fn main() : Int = unwrap(Wrap(42))\n",
        );

        let cold = run_front(source, &[], &cfg, FrontOpts::FULL)
            .expect("cold front with retained typed pre result")
            .into_typed_pre();
        let warm = run_front(source, &[], &cfg, FrontOpts::FULL)
            .expect("warm front with retained typed pre result")
            .into_typed_pre();
        let (_, _, cold_compatibility, cold_typed, cold_env) = cold;
        let (_, _, warm_compatibility, warm_typed, warm_env) = warm;

        assert_eq!(session.stats().hits, 1);
        crate::core::verify_typed_core(&cold_typed, &cold_env)
            .expect("cold retained pre result verifies");
        crate::core::verify_typed_core(&warm_typed, &warm_env)
            .expect("cached retained pre result verifies");
        assert_eq!(cold_typed, warm_typed, "the cache clones typed witnesses");
        assert_eq!(cold_typed.erase(), cold_compatibility.0);
        assert_eq!(warm_typed.erase(), warm_compatibility.0);
    }

    #[test]
    fn typed_pre_route_preserves_erase_query_observations_without_inventing_specialize_queries() {
        let store =
            std::env::temp_dir().join(format!("prism-typed-newtype-query-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&store);

        let session = CompilerSession::new();
        let mut cfg = Config {
            opt: OptLevel::O1,
            session: Some(session.clone()),
            ..Config::default()
        };
        cfg.flags.compiler_cache = true;
        cfg.flags.store_path = Some(store.clone());
        let source = concat!(
            "newtype Wrap = Wrap(Int)\n",
            "fn unwrap(w : Wrap) : Int = match w of { Wrap(n) => n }\n",
            "fn untouched(x : Int) : Int = x\n",
            "fn main() : Int = untouched(unwrap(Wrap(42)))\n",
        );

        run_front(source, &[], &cfg, FrontOpts::FULL).expect("cold typed frontend");
        let cold = session.decisions();
        assert!(cold.iter().any(|decision| {
            decision.kind == QueryKind::Optimizer
                && decision.identity.contains(":EraseNewtypes:")
                && decision.outcome == FactOutcome::Write
        }));
        assert!(
            cold.iter()
                .all(|decision| !decision.identity.contains(":Specialize:")),
            "whole-program Specialize never had an optimizer-query boundary"
        );

        session.clear();
        run_front(source, &[], &cfg, FrontOpts::FULL).expect("warm typed frontend");
        let warm = session.decisions();
        assert!(warm.iter().any(|decision| {
            decision.kind == QueryKind::Optimizer
                && decision.identity.contains(":EraseNewtypes:")
                && decision.outcome == FactOutcome::Hit
        }));
        assert!(
            warm.iter()
                .all(|decision| !decision.identity.contains(":Specialize:")),
            "whole-program Specialize must not invent a cache/session query"
        );

        let _ = std::fs::remove_dir_all(store);
    }
}
