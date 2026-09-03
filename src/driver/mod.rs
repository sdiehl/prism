use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::convert::Infallible;
use std::path::Path;
use std::sync::OnceLock;

use crate::core::fbip::{borrow_sigs, infer_borrow_sigs, Fips, Sigs};
use crate::core::opt::PassStage;
use crate::core::typed::effect_lower::{FinishedLowering, TypedLoweringTransitionError};
use crate::core::typed::{
    explain_effect_tiers, insert_rc as insert_typed_rc, lower_effects as lower_typed_effects,
    prepare_effects, reuse as reuse_typed, Decline, EffectPlan, Prepared, TypedLowering,
};
use crate::core::{
    balanced, fip_annots, hash_program, hash_root, insert_rc, pp_core_pretty, reachable_fns, reuse,
    typed_verification_error, verify_typed_core, Comp, Core, DepGraph, Digest, EffectStrategy,
    ElaboratedCore, Hashes, LoweredCore, OpGrades, TypedCore, TypedEffectLowered, TypedElaborated,
    TypedReuseLowered, Value, VerifyEnv,
};
use crate::error::{render_warning, Error, SourceMap, TypeError};
use crate::names::ENTRY_POINT;
use crate::parse::{parse, ParseResult};
use crate::resolve::{default_roots, imported_paths, lint_bindings, resolve, Root};
use crate::store::coherence::{self, CoherenceError};
use crate::store::commit_program;
use crate::store::disk::{self as store, CommitStats, DefMeta};
use crate::sym::Sym;
use crate::syntax::ast::{Core as CorePhase, Fip, Program, Span};
use crate::syntax::desugar::desugar;
use crate::syntax::reflect::parse_unit;
use crate::tc::{check_seeded, Warning};
use crate::types::{show_effects, show_type_with_effects, Checked, CtorInfo, TypecheckSeed};

mod artifact;
#[cfg(feature = "native")]
mod backend;
mod build;
mod cache;
mod config;
mod decision;
mod diff;
mod downstream;
mod dump;
mod dump_syntax;
mod dupes;
mod execution;
mod front;
mod identity;
mod input;
mod interface;
mod module_graph;
mod modules;
#[cfg(feature = "native")]
mod native;
mod prune;
mod query;
mod report;
mod scheduler;
mod semantic_patch;
mod session;
pub mod stable_lock;
#[cfg(test)]
mod tests;
mod timing;
mod verify;
pub use artifact::{ArtifactField, ArtifactIdentity, ArtifactRow};
#[cfg(feature = "native")]
pub(crate) use build::explain_downstream_queries;
pub use build::rc_balanced;
#[cfg(feature = "native")]
pub use build::{
    build, build_at, build_on, build_on_report, emit_ir, verify_backend_recomposition_on,
    NativeBuildReport,
};
#[cfg(feature = "mlir")]
pub use build::{build_mlir, build_mlir_at, build_mlir_on};
#[cfg(feature = "native")]
pub(crate) use cache::CheckVerdictCache;
#[cfg(feature = "native")]
pub use cache::NativeCacheStatus;
pub use config::{BackendOpt, BuildMode, Config, Scheduler};
pub use decision::ModuleQueryDecision;
pub use diff::{
    diff_on, source_diff_on, DiffChangedDef, DiffNamedDef, SourceDiff, SOURCE_DIFF_FORMAT,
};
#[cfg(feature = "native")]
pub(crate) use diff::{diff_on_roots, render_source_diff, source_diff_on_roots};
pub use dump::{dump, dump_at, dump_on};
pub use execution::{
    debug_on, durable_run_on, interpret, interpret_at, interpret_deferred_holes, interpret_io_at,
    interpret_io_on, interpret_io_on_with_args, interpret_io_on_with_args_deferred_holes,
    interpret_on, observe_lowered_run_on, observe_run_on, observe_run_on_deferred_holes, record_on,
    record_on_with_args, record_run_on, replay_on, replay_run_on, resume_observed_on, resume_on,
    step_ruler_on, suspend_at_cut_on, suspend_line_cuts, suspend_on, CutReport, CutTarget,
    DurableRun, RecordedRun, StepRuler, StepRulerRow, SuspendAtCut, SuspendCut, SuspendResult,
    STEP_RULER_FORMAT,
};
use front::{run_front, run_front_verdict, Front, FrontRequest};
pub(crate) use identity::NAMESPACE_FORMAT;
pub(crate) use identity::{
    addressable_surface, addressable_surface_in, stdlib_driver_src, AddressableSurface,
};
pub use identity::{
    module_interface, namespace_identity, namespace_layers, namespace_root, public_surface,
    stdlib_hash, ModuleInterface, ModuleInterfaceEntry, NamespaceIdentity, NamespaceLayers,
    PublicDef, StdlibHash, MODULE_INTERFACE_FORMAT,
};
#[cfg(feature = "native")]
pub(crate) use identity::{stdlib_value_schemes, BuildIdentity, BuildRoot};
pub use identity::{EnvelopeHeader, WireKind, NAMESPACE_ARTIFACT_KIND};
pub use interface::RehydratedModuleInterface;
pub use module_graph::{
    module_graph, ModuleGraph, ModuleGraphNode, ModuleInvalidation, ModuleInvalidationCause,
    MODULE_GRAPH_FORMAT,
};
pub use modules::{check_modules_on, CheckedModule, ModuleCheckReport};
pub use query::{query_on, type_tokens};
pub use report::{report, report_at, report_on, shape_digests_of};
pub use semantic_patch::{
    apply_semantic_patch, fetch_semantic_patch, impact_semantic_patch,
    verify_semantic_patch_behavior, BehaviorCase, BehaviorCaseResult, BehaviorCorpus,
    BehaviorDivergence, BehaviorReceipt, DeltaReport, EvidenceTier, FetchReport, ImpactReport,
    InterfaceDelta, PatchRefusal, PatchRefusalBody, PatchRefusalSubject, StagedPatch,
    PATCH_BEHAVIOR_CORPUS_FORMAT, PATCH_BEHAVIOR_FORMAT, PATCH_DELTA_FORMAT, PATCH_FETCH_FORMAT,
    PATCH_IMPACT_FORMAT, PATCH_REFUSAL_FORMAT, PATCH_STAGE_FORMAT,
};
pub use session::{CompilerSession, QueryDecision, SessionStats};
pub use timing::{PhaseTally, TimingSink};
#[cfg(feature = "native")]
pub use verify::attest_on;

pub use prism_syntax::error::source::{PRELUDE, PRELUDE_END_MARK};

impl From<scheduler::QueryWorkerFailure> for Error {
    fn from(failure: scheduler::QueryWorkerFailure) -> Self {
        Self::InternalInvariant(failure.to_string())
    }
}

/// The source file extension. Modules `import Foo` resolve to `Foo.pr`.
pub const SOURCE_EXT: &str = "pr";
pub(super) const ROOT_MODULE_NAME: &str = "<root>";

#[must_use]
pub fn with_prelude(src: &str) -> String {
    format!("{PRELUDE}\n{src}")
}

/// The dotted paths of every module a source pulls in, in load order.
///
/// The CLI prints these as a build's file manifest. Pure (parse plus module
/// load), no compilation; a best-effort progress aid, so callers ignore its
/// error and let the real build surface any resolution failure.
///
/// # Errors
/// Fails when the source does not parse or an import resolves in no root.
pub fn source_modules(src: &str, roots: &[Root]) -> Result<Vec<String>, Error> {
    let ParseResult { program, .. } = parse(src)?;
    imported_paths(&program, roots)
}

/// Prepend a caller-supplied prelude instead of the built-in one.
///
/// A project that sets `[package] prelude` opts into its own always-on
/// definitions; the built-in prelude is not added on top, so the project's
/// prelude is the whole base. The [`PRELUDE_END_MARK`] line stamped between the
/// two is how diagnostics locate the user's own file.
#[must_use]
pub fn with_custom_prelude(prelude: &str, src: &str) -> String {
    format!("{prelude}\n{PRELUDE_END_MARK}\n{src}")
}

/// Make a documentation snippet runnable without a `main` boilerplate.
///
/// A snippet that already defines `main` is returned unchanged. Otherwise the
/// snippet body becomes an implicit `main`, so a bare expression
/// (`unwrap_or(0, Some(5))`) or a `let`-block runs like a REPL line and yields a
/// value. Leading imports stay at the top level, letting generated docs and
/// playground links carry their module context. A snippet that is neither
/// (top-level declarations with no `main`, which cannot sit inside a function
/// body) is returned unchanged, so the caller sees it has no entry point.
/// Idempotent: wrapping a wrapped snippet is a no-op.
#[must_use]
pub fn example_program(src: &str) -> String {
    let defines_main =
        |s: &str| parse(s).is_ok_and(|pr| pr.program.fns.iter().any(|d| d.name == ENTRY_POINT));
    if defines_main(src) {
        return src.to_string();
    }

    // Imports cannot be indented into a function body. Hoist a leading import
    // preamble and wrap only the remaining snippet.
    let lines = src.lines().collect::<Vec<_>>();
    let mut last_import = None;
    for (index, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if trimmed.starts_with("import ") {
            last_import = Some(index);
        } else if !trimmed.is_empty() {
            break;
        }
    }
    let (imports, rest) = last_import.map_or_else(
        || (String::new(), src.to_string()),
        |last| {
            let mut imports = lines[..=last].join("\n");
            imports.push('\n');
            let mut rest = lines[last + 1..].join("\n");
            if src.ends_with('\n') {
                rest.push('\n');
            }
            (imports, rest)
        },
    );
    let body: String = rest
        .lines()
        .map(|l| format!("  {l}"))
        .collect::<Vec<_>>()
        .join("\n");
    let wrapped = format!("{imports}fn {ENTRY_POINT}() =\n{body}");
    if parse(&wrapped).is_ok() {
        wrapped
    } else {
        src.to_string()
    }
}

/// # Examples
/// ```
/// let src = prism::with_prelude("fn double(x : Int) : Int = x * 2");
/// let checked = prism::check(&src).unwrap();
/// let double = checked.defs.decls.iter().find(|d| d.name == "double").unwrap();
/// assert_eq!(double.ty.show(), "(Int) -> Int");
/// ```
///
/// # Errors
/// Fails on lex, parse, or type errors.
pub fn check(src: &str) -> Result<Checked, Error> {
    check_at(src, Path::new("."))
}

/// Like [`check`], resolving any module imports relative to `base`.
///
/// # Errors
/// Fails on lex, parse, module, or type errors.
pub fn check_at(src: &str, base: &Path) -> Result<Checked, Error> {
    check_on(src, &default_roots(base))
}

/// Like [`check_at`], but against an explicit module search path (a project's
/// source root, its path dependencies, and the stdlib).
///
/// # Errors
/// Fails on lex, parse, module, or type errors.
pub fn check_on(src: &str, roots: &[Root]) -> Result<Checked, Error> {
    check_on_in(src, roots, &Config::default())
}

/// Typecheck one already-resolved module against checked dependency facts.
///
/// This is the semantic cutoff primitive used by independent module queries:
/// dependency implementation bodies are absent, and only the supplied seed can
/// satisfy their names.
///
/// # Errors
/// Fails on parse, resolution, desugaring, or type errors.
pub fn check_with_seed(src: &str, seed: &TypecheckSeed) -> Result<Checked, Error> {
    let program = parse_unit(src)?;
    let program = resolve(program)?;
    let program = desugar(program)?;
    Ok(check_seeded(&program, seed)?)
}

/// Like [`check_on`], threading an explicit [`Config`] so the CLI can carry a
/// timing sink into a `check`.
///
/// The `CHECK` preset consults no other `cfg` field (no scheduler retarget,
/// elaboration, validators, or optimizer), so the config changes nothing about
/// the result; it only lets `--time-compile` observe the type-check phases.
///
/// # Errors
/// Fails on lex, parse, module, or type errors.
pub fn check_on_in(src: &str, roots: &[Root], cfg: &Config) -> Result<Checked, Error> {
    Ok(run_front(src, roots, cfg, FrontRequest::Check)?.into_checked())
}

/// Like [`check_on_in`], but retaining typed holes as reports.
///
/// A typed hole is returned in [`crate::types::Reports::holes`] instead of
/// being raised, so a tool can ask what a hole's type and in-scope candidates are. Every other type
/// error still fails exactly as it does under [`check_on_in`]: the query answers
/// only about a program whose sole remaining question is the hole.
///
/// # Errors
/// Fails on lex, parse, module, or type errors other than the holes themselves.
pub fn check_allow_holes_on_in(src: &str, roots: &[Root], cfg: &Config) -> Result<Checked, Error> {
    Ok(run_front(src, roots, cfg, FrontRequest::CheckHoles)?.into_checked())
}

/// The documentation harness's verdict on a doc example.
///
/// Hole-tolerant like [`check_allow_holes_on_in`], but elaborated and
/// semantically validated the way `prism check` validates a program, so a doc
/// example cannot carry a `fip`, `noalloc`, or `replayable` claim the
/// compiler would reject. Quiet: no lints, no warning emission.
///
/// # Errors
/// Fails on lex, parse, module, type, or semantic-validation errors other than
/// the holes themselves.
pub fn check_docs_on(src: &str, roots: &[Root]) -> Result<Checked, Error> {
    let cfg = Config::default();
    Ok(run_front(src, roots, &cfg, FrontRequest::CheckHolesValidated)?.into_checked())
}

// The checked Core-surface tree plus presentation facts used only by
// `dump typespans` and the documentation preprocessor.
fn tooltip_checked_on(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<(Program<CorePhase>, Checked), Error> {
    Ok(run_front(src, roots, cfg, FrontRequest::TypedTooltips)?.into_program_checked())
}

// The resolved Core-surface tree plus the checker's verdict on it, used only by
// `dump tc-rejection`: the one seam that exports an artifact for a program the
// checker refused.
fn front_verdict_on(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<(Program<CorePhase>, Option<Error>), Error> {
    run_front_verdict(src, roots, cfg)
}

/// The public validity verdict behind `prism check`.
///
/// Type-checks, elaborates, and runs every semantic validator (fip / replayable /
/// effect reconciliation), so a program `check` accepts is one `build` also
/// accepts. Unlike [`check_on_in`] (the type-only surface used by `dump`,
/// `report`, and the snapshot oracle), this agrees with the full compile path on
/// validity.
///
/// # Errors
/// Fails on lex, parse, module, type, or semantic-validator errors.
pub fn check_validated_on_in(src: &str, roots: &[Root], cfg: &Config) -> Result<Checked, Error> {
    Ok(run_front(src, roots, cfg, FrontRequest::CheckValidated)?.into_checked())
}

// Unused-binding and shadowed-name lints over the resolved surface program,
// scoped to the user's own source (the prepended prelude is excluded by offset).
fn lint_surface(src: &str, prog: &Program) -> Vec<Warning> {
    let user_start = SourceMap::new(src).prelude_len();
    lint_bindings(prog, user_start)
}

// Surface non-fatal checker diagnostics (orphan/overlapping instances, unused or
// shadowed bindings) on stderr, with a source caret when the warning points into
// this source. Errors abort earlier, so this only runs once a program type checks.
fn emit_warnings(src: &str, checked: &Checked) {
    for w in &checked.reports.warnings {
        emit_warning(src, w);
    }
}

// Render one non-fatal diagnostic on stderr, with a source caret when the span
// points into this source. Shared by the batch emitter and the duplicate-detection
// pass, which surfaces its findings after elaboration (past the batch emit above).
fn emit_warning(src: &str, w: &Warning) {
    eprint!("{}", render_warning(src, "<source>", &w.span, &w.msg, true));
}

// The full compile path (scheduler retarget, validators, pre-lowering optimizer),
// as the legacy tuple its many consumers destructure. `pub(crate)` so the test
// lane's discovery can key targets by the same checked-program surface; additive.
pub(crate) fn frontend(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<(Program<CorePhase>, Checked, ElaboratedCore), Error> {
    run_front(src, roots, cfg, FrontRequest::Full).map(Front::into_elaborated)
}

/// Elaborate `src` and commit its definitions into the content-addressed store.
///
/// The single store-population entry point. It hashes each definition over
/// pre-optimizer elaborated Core, the one canonical identity regime, exactly as
/// the `core-hash`/`namespace` dumps and [`store_def_inputs`] do. A committed
/// object is therefore content-addressed independently of the optimizer level:
/// identity is a property of the elaborated term, and the optimizer
/// configuration (with every other toolchain choice) belongs to the verification
/// fingerprint, not to identity. The store root comes from the `PRISM_STORE_PATH`
/// knob (else a default cache location). Storing is a cache, so this never
/// affects the compiled result; it only records it.
///
/// # Errors
/// Fails on any front-end error or a store filesystem error.
pub fn commit_to_store(src: &str, roots: &[Root], cfg: &Config) -> Result<CommitStats, Error> {
    // Validate before committing: the store must never persist a definition
    // carrying an fbip / noalloc / replayable claim the build path would reject.
    // Validation is side-effect-free on the pre-optimizer Core, so the committed
    // identity is byte-identical to the unvalidated identity surface.
    let (program, checked, core) = elaborated_validated(src, roots)?;
    store_commit(&program, &checked, &core, cfg)
}

// Hash the program and write it into the store at the configured root. Kept
// beside `frontend` so the hashing inputs (borrow signatures, fip annotations,
// principal type) are computed once, the same way every other per-definition
// hashing site computes them.
fn store_commit(
    program: &Program<CorePhase>,
    checked: &Checked,
    core: &ElaboratedCore,
    cfg: &Config,
) -> Result<CommitStats, Error> {
    let hash_metas = hash_meta(checked, &borrow_sigs(program), &fip_annots(program));
    let hashes = hash_program(core, &hash_metas);
    let graph = DepGraph::of(core);
    let metas: BTreeMap<Sym, DefMeta> = checked
        .defs
        .decls
        .iter()
        .map(|d| {
            (
                Sym::new(&d.name),
                DefMeta {
                    name: d.name.clone(),
                    ty: show_type_with_effects(&d.ty, &d.effects),
                    doc: String::new(),
                },
            )
        })
        .collect();
    let root = store::resolve_store_path(cfg.flags().store_path.as_deref());
    let store = store::Store::open_or_create(&root)?;
    // Record this program's canonical `(class, head) -> instance-hash` bindings,
    // refusing any that a previously committed program bound to a different
    // instance. This lifts intra-program coherence (already enforced in the type
    // checker) across every program sharing the store. Checked before the objects
    // are written so a rejected commit leaves the store untouched.
    coherence::commit_canonical(&store, &program.instances, &program.canonicals, &hashes).map_err(
        |e| match e {
            CoherenceError::Io(io) => Error::Io(io),
            CoherenceError::Conflict { span, msg } => {
                Error::Type(TypeError::TypeFailure { span, msg })
            }
        },
    )?;
    let stats = commit_program(&store, core, &hashes, &hash_metas, &graph, &metas)?;
    // The first user-visible payoff of the store: check cost tracks the Merkle
    // closure of a change. `objects_hit` are the definitions whose hash was
    // unchanged (already compiled and stored); `objects_written` are the ones
    // that moved and were recompiled into the store. Behind the quiet knob, like
    // the other compiler-internal stat lines.
    if !cfg.flags().quiet {
        eprintln!(
            "store: {} unchanged, {} recompiled",
            stats.objects_hit, stats.objects_written
        );
    }
    Ok(stats)
}

/// The store codec's compile front door.
///
/// Elaborates `src` to pre-optimization anonymous Core, the per-definition
/// content hashes, and the elaboration metadata strings the hashes commit to,
/// gathered exactly as every other hashing site gathers them. Everything
/// `store::codec::encode_def` needs to serialize a definition, and everything a
/// re-hash needs to reproduce its hash.
///
/// # Errors
/// Fails on any front-end error.
pub fn store_def_inputs(src: &str) -> Result<(Core, Hashes, BTreeMap<Sym, String>), Error> {
    let roots = default_roots(Path::new("."));
    let (program, checked, core) = elaborated(src, &roots)?;
    let metas = hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program));
    let hashes = hash_program(&core, &metas);
    Ok((core.into_core(), hashes, metas))
}

// Elaborate a source to Core *before* the Core-to-Core optimizer runs: the one
// canonical identity surface. Every content hash is taken here, so the store
// commit, the `core-hash`/`dupes`/`namespace` dumps, the stdlib root, and the
// `store_def_inputs` re-hash front door all agree by construction. Pre-opt Core
// is used so identity cannot depend on an env-toggled pass (`Specialize`) or
// move when the optimizer is tuned, and so it holds every top-level definition
// exactly once (the optimizer has no whole-program DCE). Quiet: no warning
// emission, no surface lints.
fn elaborated(
    src: &str,
    roots: &[Root],
) -> Result<(Program<CorePhase>, Checked, ElaboratedCore), Error> {
    // The `IDENTITY` preset consults no `cfg` field (no retarget, no optimizer),
    // so a default config keeps this a pure function of source and roots.
    run_front(src, roots, &Config::default(), FrontRequest::Identity).map(Front::into_elaborated)
}

// The identity surface, additionally validated: same byte-identical pre-optimizer
// Core as `elaborated`, but only after every semantic validator passes. The store
// commit path uses this so a persisted definition never carries a claim the build
// path would reject.
fn elaborated_validated(
    src: &str,
    roots: &[Root],
) -> Result<(Program<CorePhase>, Checked, ElaboratedCore), Error> {
    run_front(
        src,
        roots,
        &Config::default(),
        FrontRequest::IdentityValidated,
    )
    .map(Front::into_elaborated)
}

// Shared front-end and rc-balance ICE check for the interpreter entries. The
// interpreter runs the un-lowered core, but the balance check over the
// effect-lowered core still runs so a bad lowering is caught here too.
fn prepared_core(src: &str, roots: &[Root], cfg: &Config) -> Result<ElaboratedCore, Error> {
    prepared_core_with_opts(src, roots, cfg, FrontRequest::Full)
}

// Prepare the verified unlowered interpreter program for a compiler-owned
// oracle. Unlike `prepared_core`, this intentionally does not run effect
// lowering and RC/reuse merely to discard their output: bootstrap executes the
// elaborated tree, and the ordinary interpreter entry points retain that ICE
// check unchanged. Crate-private so a language program cannot opt out of a
// production validation lane. Its only caller is the CLI bootstrap path, so it
// is gated with the `cli` module.
#[cfg(feature = "native")]
pub(crate) fn prepared_oracle_core(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<ElaboratedCore, Error> {
    let (_program, _checked, core, _typed, _verify_env) =
        run_front(src, roots, cfg, FrontRequest::Full)?.into_typed_pre();
    Ok(core)
}

// Interpreter-only typed-hole lane. Native/wasm/build never call this and keep
// the ordinary `E1021` refusal before elaboration.
fn prepared_core_deferred_holes(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<ElaboratedCore, Error> {
    prepared_core_with_opts(src, roots, cfg, FrontRequest::FullDeferredHoles)
}

// The borrow masks the reference-count lanes consume. With borrow inference
// enabled, the declared masks are extended over the provably pure functions;
// every RC consumer in one compilation reads this single map, so caller and
// callee always agree on each call's convention. Definition identity
// (`hash_meta`) always reads the declared `borrow_sigs` instead: the inferred
// masks are a pure function of the checked source, a cost decision like a
// lowering tier, never part of what a definition is.
fn rc_borrow_sigs(
    program: &Program<CorePhase>,
    checked: &Checked,
    core: &Core,
    cfg: &Config,
) -> Sigs {
    let declared = borrow_sigs(program);
    if !cfg.flags().borrow_infer {
        return declared;
    }
    let pure_fns = checked
        .defs
        .decls
        .iter()
        .filter(|decl| decl.pure)
        .map(|decl| Sym::new(&decl.name))
        .collect();
    infer_borrow_sigs(core, &pure_fns, &declared)
}

fn prepared_core_with_opts(
    src: &str,
    roots: &[Root],
    cfg: &Config,
    request: FrontRequest,
) -> Result<ElaboratedCore, Error> {
    let (program, checked, core, typed, verify_env) =
        run_front(src, roots, cfg, request)?.into_typed_pre();
    let sigs = rc_borrow_sigs(&program, &checked, &core, cfg);
    let lowered = lower_opt(
        typed,
        &verify_env,
        &checked.defs.ctors,
        &checked.op_grades(),
        cfg,
    )?;
    emit_lower_warning(src, lowered.warning(), cfg.flags().verbose);
    finish_lowered(lowered, &sigs, cfg)?;
    Ok(core)
}

// Effect-lower the verified typed Core, then run the late (post-lowering)
// optimization passes. The witness-carrying tree is authoritative and the sole
// transformation path; no legacy effect-lowering query or cache artifact is
// produced.
fn stage_validation_error(stage: &str, violations: &[String]) -> Error {
    Error::InternalInvariant(format!(
        "{stage} Core failed structural validation:\n{}",
        violations.join("\n")
    ))
}

fn lowering_transition_error(error: TypedLoweringTransitionError<Error>) -> Error {
    match error {
        TypedLoweringTransitionError::Pass(error) => error,
        TypedLoweringTransitionError::Invariant(error) => error.into(),
    }
}

fn lowering_erasure_error(error: TypedLoweringTransitionError<Infallible>) -> Error {
    match error {
        TypedLoweringTransitionError::Pass(never) => match never {},
        TypedLoweringTransitionError::Invariant(error) => error.into(),
    }
}

fn validated_elaborated_core(core: Core) -> Result<ElaboratedCore, Error> {
    ElaboratedCore::validate(core)
        .map_err(|violations| stage_validation_error("elaborated", &violations))
}

#[cfg(feature = "native")]
fn validated_lowered_core(core: Core) -> Result<LoweredCore, Error> {
    LoweredCore::validate(core).map_err(|violations| stage_validation_error("lowered", &violations))
}

fn lower_opt(
    typed: TypedCore<TypedElaborated>,
    verify_env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
    grades: &OpGrades,
    cfg: &Config,
) -> Result<TypedLowering, Error> {
    let mut typed_flags = cfg.flags().clone();
    typed_flags.quiet = true;
    let lowering = timing::timed_res(
        cfg.timing(),
        timing::Phase::LowerEffects,
        "",
        || lower_typed_effects(typed, verify_env, ctors, &typed_flags, grades).map_err(Error::from),
        |_| timing::RowExtras::default(),
    )?;
    timing::timed_res(
        cfg.timing(),
        timing::Phase::OptLate,
        "",
        || {
            lowering
                .try_map_core(|typed, env| {
                    downstream::run_typed_opt_queries(
                        typed,
                        env,
                        &BTreeSet::new(),
                        PassStage::Late,
                        cfg,
                    )
                })
                .map_err(lowering_transition_error)
        },
        |_| timing::RowExtras::default(),
    )
}

fn finish_lowered(
    lowered: TypedLowering,
    sigs: &Sigs,
    cfg: &Config,
) -> Result<FinishedLowering, Error> {
    timing::timed_res(
        cfg.timing(),
        timing::Phase::Rc,
        "",
        || {
            let finished = lowered
                .try_finish_core(|core, env| finish_lowered_typed(core, env, sigs))
                .map_err(lowering_transition_error)?;
            balanced(finished.core(), sigs)
                .map_err(|error| Error::CodegenBackend(format!("ICE: rc imbalance: {error}")))?;
            Ok(finished)
        },
        |_| timing::RowExtras::default(),
    )
}

fn finish_lowered_typed(
    core: TypedCore<TypedEffectLowered>,
    env: &VerifyEnv,
    sigs: &Sigs,
) -> Result<TypedCore<TypedReuseLowered>, Error> {
    let typed_owned =
        verify_typed_core(insert_typed_rc(core, sigs), env).map_err(typed_verification_error)?;
    let typed_reused =
        verify_typed_core(reuse_typed(typed_owned), env).map_err(typed_verification_error)?;
    Ok(typed_reused)
}

fn lowered_core(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<(Checked, LoweredCore, BTreeMap<String, CtorInfo>, Sigs), Error> {
    let (checked, sigs, lowered) = lowered_front(src, roots, cfg)?;
    let finished = lowered.try_erase_core().map_err(lowering_erasure_error)?;
    let (core, ctors) = finished.into_core_and_constructors();
    Ok((checked, core, ctors, sigs))
}

fn reuse_lowered_core(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<(Checked, LoweredCore, BTreeMap<String, CtorInfo>, Sigs), Error> {
    let (checked, sigs, lowered) = lowered_front(src, roots, cfg)?;
    let finished = finish_lowered(lowered, &sigs, cfg)?;
    let (core, ctors) = finished.into_core_and_constructors();
    Ok((checked, core, ctors, sigs))
}

fn lowered_front(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<(Checked, Sigs, TypedLowering), Error> {
    let (program, checked, core, typed, verify_env) =
        run_front(src, roots, cfg, FrontRequest::Full)?.into_typed_pre();
    let sigs = rc_borrow_sigs(&program, &checked, &core, cfg);
    let lowered = lower_opt(
        typed,
        &verify_env,
        &checked.defs.ctors,
        &checked.op_grades(),
        cfg,
    )?;
    emit_lower_warning(src, lowered.warning(), cfg.flags().verbose);
    Ok((checked, sigs, lowered))
}

#[cfg(feature = "native")]
fn lowered_core_with_identity(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<(Checked, LoweredCore, BTreeMap<String, CtorInfo>, Hashes), Error> {
    let (checked, lowered, sigs, hashes) = lowered_spine_with_identity(src, roots, cfg)?;
    let finished = finish_lowered(lowered, &sigs, cfg)?;
    let (core, ctors) = finished.into_core_and_constructors();
    Ok((checked, core, ctors, hashes))
}

// The front end, optimization, and effect lowering, stopping BEFORE
// reference-count insertion. The returned spine still carries its typed
// tree; `finish_lowered` completes it. The native build path uses the split
// to consult the semantic artifact cache against the pre-insertion term, so
// a hit never pays for the ownership passes it is about to discard.
#[cfg(feature = "native")]
fn lowered_spine_with_identity(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<(Checked, TypedLowering, Sigs, Hashes), Error> {
    let (program, checked, identity_core, core, typed, verify_env) =
        run_front(src, roots, cfg, FrontRequest::Full)?.into_compilation();
    let declared = borrow_sigs(&program);
    let sigs = rc_borrow_sigs(&program, &checked, &core, cfg);
    let hashes = if cfg.scheduler().retarget().is_some() {
        // Scheduler policy is execution configuration, never source identity.
        // The full path has already retargeted its surface program, so recover
        // the policy-neutral identity only for this non-default configuration.
        let (identity_program, identity_checked, canonical_core) = elaborated(src, roots)?;
        hash_program(
            &canonical_core,
            &hash_meta(
                &identity_checked,
                &borrow_sigs(&identity_program),
                &fip_annots(&identity_program),
            ),
        )
    } else {
        let metas = hash_meta(&checked, &declared, &fip_annots(&program));
        hash_program(&identity_core, &metas)
    };
    let lowered = lower_opt(
        typed,
        &verify_env,
        &checked.defs.ctors,
        &checked.op_grades(),
        cfg,
    )?;
    emit_lower_warning(src, lowered.warning(), cfg.flags().verbose);
    Ok((checked, lowered, sigs, hashes))
}

// Surface the effect-lowering fallback warning through the standard renderer,
// the same one `emit_warnings` uses for checker diagnostics. The diagnostic
// comes from the Core phase, which carries no source spans, so it renders as a
// plain `warning: ...` line (an empty span makes `render_warning` skip the caret).
// `verbose` (from DynFlags, off by default) gates it: the fusion fallback is a
// performance hint, not a correctness signal, so an ordinary build or docs run
// stays quiet and `--verbose` (or `PRISM_VERBOSE`) opts in.
fn emit_lower_warning(src: &str, warning: Option<&str>, verbose: bool) {
    if !verbose {
        return;
    }
    if let Some(msg) = warning {
        eprint!(
            "{}",
            render_warning(src, "<source>", &Span::empty(0), msg, true)
        );
    }
}

/// The effect-lowering strategy this snippet's program takes.
///
/// A performance classification of how its effects compile (`pure`, `evidence`,
/// `state-fusion`, `local-partial`, `whole-program-free-monad`,
/// `selective-free-monad`). A perf snapshot records this per corpus program so a
/// silent regression onto the slow free-monad path surfaces as a reviewable diff.
/// `full` carries the prelude.
///
/// # Errors
/// Fails on front-end or typed effect-lowering verification errors.
pub fn effect_strategy_full(full: &str, base: &Path) -> Result<EffectStrategy, Error> {
    effect_strategy_on(full, base, &Config::from_env())
}

/// Like [`effect_strategy_full`] under an explicit [`Config`].
///
/// The tier-parity oracle uses this to classify the same program under a
/// forced `flags.effect_tier` and under `auto`, deciding which programs a
/// forced build actually exercises.
///
/// # Errors
/// Fails on front-end or typed effect-lowering verification errors.
pub fn effect_strategy_on(full: &str, base: &Path, cfg: &Config) -> Result<EffectStrategy, Error> {
    typed_effect_facts(full, &default_roots(base), cfg).map(|(strategy, _)| strategy)
}

/// The effect-lowering fallback warnings this snippet's program raises.
///
/// Empty when it stays on a fused path. Each names the functions that lost
/// fusion and why, so a test can lock the diagnostic a slow-path program
/// produces. `full` carries the prelude.
///
/// # Errors
/// Fails on front-end or typed effect-lowering verification errors.
pub fn effect_warnings_full(full: &str, base: &Path) -> Result<Vec<String>, Error> {
    let cfg = Config::from_env();
    let (_, warning) = typed_effect_facts(full, &default_roots(base), &cfg)?;
    Ok(warning.into_iter().collect())
}

fn typed_effect_facts(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<(EffectStrategy, Option<String>), Error> {
    let mut cfg = cfg.clone();
    cfg.update_flags(|flags| flags.quiet = true);
    let (_, checked, _, typed, verify_env) =
        run_front(src, roots, &cfg, FrontRequest::Full)?.into_typed_pre();
    let lowering = lower_typed_effects(
        typed,
        &verify_env,
        &checked.defs.ctors,
        cfg.flags(),
        &checked.op_grades(),
    )?;
    Ok((lowering.strategy(), lowering.warning().map(str::to_owned)))
}

/// The prepared tree, the plan solved for it, and what the cascade decided from
/// them: everything the tier artifacts render, computed once from one front end.
struct TierFacts {
    prepared: Prepared,
    plan: EffectPlan,
    strategy: EffectStrategy,
    // The refusal is an outcome of the cascade, not a fact about the tree, so it
    // is read off the lowering that made the decision rather than re-derived
    // beside it.
    declined: Option<Decline>,
}

/// Solve the tier facts for one program.
///
/// The plan is a fact about the prepared tree, so it is computed from the same
/// preparation the strategy decision runs on.
fn tier_facts(src: &str, roots: &[Root], cfg: &Config) -> Result<TierFacts, Error> {
    let mut cfg = cfg.clone();
    cfg.update_flags(|flags| flags.quiet = true);
    let (_, checked, _, typed, verify_env) =
        run_front(src, roots, &cfg, FrontRequest::Full)?.into_typed_pre();
    let grades = checked.op_grades();
    let echo = typed.clone();
    let lowering = lower_typed_effects(
        typed,
        &verify_env,
        &checked.defs.ctors,
        cfg.flags(),
        &grades,
    )?;
    let prepared = prepare_effects(echo, &verify_env, &checked.defs.ctors, cfg.flags(), &grades)?;
    let plan = EffectPlan::analyze(prepared.functions());
    Ok(TierFacts {
        prepared,
        plan,
        strategy: lowering.strategy(),
        declined: lowering.confined_decline().copied(),
    })
}

/// The effect plan the cascade reads for this program, rendered beside the tier
/// it decided.
///
/// # Errors
/// Fails on front-end or typed effect-lowering verification errors.
pub(crate) fn typed_effect_plan(src: &str, roots: &[Root], cfg: &Config) -> Result<String, Error> {
    let facts = tier_facts(src, roots, cfg)?;
    Ok(facts.plan.render(facts.strategy, facts.declined))
}

/// The same facts as prose: one sentence per region naming the rung it lowered
/// to and the fact that put it there.
///
/// # Errors
/// Fails on front-end or typed effect-lowering verification errors.
pub(crate) fn typed_tier_explain(src: &str, roots: &[Root], cfg: &Config) -> Result<String, Error> {
    let facts = tier_facts(src, roots, cfg)?;
    Ok(explain_effect_tiers(
        facts.prepared.functions(),
        &facts.plan,
        facts.strategy,
        facts.declined,
    ))
}

/// The CBPV core IR of the snippet's own functions (prelude elided),
/// pretty-printed.
///
/// Effects are lowered to explicit `handle`/`do`, reference-counting
/// `dup`/`drop` inserted, and FBIP `reuse_token`/`reuse` in-place updates
/// applied: the lowest-level representation available without the LLVM
/// back-end. `src` is the bare snippet; the prelude is prepended internally.
///
/// # Errors
/// Fails on front-end errors.
pub fn core_ir(src: &str) -> Result<String, Error> {
    core_ir_full(&with_prelude(src), Path::new("."))
}

/// The optimized Core IR for `src` (prelude prepended internally).
///
/// As produced by the Core-to-Core tier, before reference counting and effect
/// lowering. The in-memory analogue of [`core_ir`], for callers that need the
/// term itself (linting, structural checks) rather than its pretty form.
///
/// # Errors
/// Fails on front-end errors.
pub fn core_of(src: &str) -> Result<Core, Error> {
    let (_, _, core) = frontend(
        &with_prelude(src),
        &default_roots(Path::new(".")),
        &Config::from_env(),
    )?;
    Ok(core.into_core())
}

/// Like [`core_ir`], but `full` already carries the prelude (as the REPL's
/// composed buffer does). Imports resolve relative to `base`.
///
/// Reference counting and FBIP reuse are applied, but effects are left as
/// readable `do`/`handle` nodes rather than lowered into the runtime's monadic
/// representation, mirroring `dump fbip`.
///
/// # Errors
/// Fails on front-end errors.
pub fn core_ir_full(full: &str, base: &Path) -> Result<String, Error> {
    let prelude = prelude_fn_names()?;
    let cfg = Config::from_env();
    let (program, checked, core) = frontend(full, &default_roots(base), &cfg)?;
    let sigs = rc_borrow_sigs(&program, &checked, &core, &cfg);
    let optimized = reuse(&insert_rc(&core, &sigs));
    Ok(pp_core_pretty(&strip_prelude(optimized, &prelude)))
}

/// Off-platform builtins (file IO, env, process) the snippet would invoke.
///
/// Found by scanning the elaborated core rather than token adjacency: a builtin
/// reached through a let-binding or passed as a value (`let f = read_file`) is
/// eta-expanded to a `StrBuiltin` node and so is still caught. `full` already
/// carries the prelude. Returns the offending names in first-seen order, empty
/// when the snippet stays on platform.
///
/// # Errors
/// Fails on front-end errors (lex, parse, module, type, fip).
pub fn off_platform_builtins(full: &str, roots: &[Root]) -> Result<Vec<&'static str>, Error> {
    // The input capability wrappers route host file/env IO through effects, so
    // the underlying prim builtin lives only in the always-reachable world
    // handler. Detect that usage from the surface wrapper a program reaches.
    const INPUT_WRAPPERS: &[&str] = &["read_file", "file_exists", "getenv", "args_count", "arg"];

    fn scan_val(v: &Value, out: &mut Vec<&'static str>) {
        match v {
            Value::Thunk(c) => scan_comp(c, out),
            Value::Ctor(_, _, fs) | Value::Tuple(fs) | Value::UnboxedTuple(fs) => {
                for f in fs {
                    scan_val(f, out);
                }
            }
            Value::UnboxedRecord(fs) => {
                for (_, f) in fs {
                    scan_val(f, out);
                }
            }
            _ => {}
        }
    }

    fn scan_comp(c: &Comp, out: &mut Vec<&'static str>) {
        if let Comp::StrBuiltin(b, _) = c {
            if b.off_platform() && !out.contains(&b.name()) {
                out.push(b.name());
            }
        }
        match c {
            Comp::Return(v)
            | Comp::Force(v)
            | Comp::Error(v)
            | Comp::FloatBuiltin(_, v)
            | Comp::Neg(_, v)
            | Comp::UnboxedProject(v, _)
            | Comp::Dup(v)
            | Comp::Drop(v)
            | Comp::Reuse(_, v)
            | Comp::RefNew(v)
            | Comp::RefGet(v) => scan_val(v, out),
            Comp::RefSet(c, v) | Comp::InitAt(c, v) => {
                scan_val(c, out);
                scan_val(v, out);
            }
            Comp::WithReuse { freed, body, .. } => {
                scan_val(freed, out);
                scan_comp(body, out);
            }
            Comp::Prim(_, a, b) => {
                scan_val(a, out);
                scan_val(b, out);
            }
            Comp::Bind(m, _, n) => {
                scan_comp(m, out);
                scan_comp(n, out);
            }
            Comp::App(f, args) => {
                scan_comp(f, out);
                for a in args {
                    scan_val(a, out);
                }
            }
            Comp::If(v, t, e) => {
                scan_val(v, out);
                scan_comp(t, out);
                scan_comp(e, out);
            }
            Comp::Call(_, args)
            | Comp::Do(_, args)
            | Comp::StrBuiltin(_, args)
            | Comp::Io(_, args) => {
                for a in args {
                    scan_val(a, out);
                }
            }
            Comp::Lam(_, b) | Comp::Mask(_, b) => scan_comp(b, out),
            Comp::Case(v, arms) => {
                scan_val(v, out);
                for (_, body) in arms {
                    scan_comp(body, out);
                }
            }
            Comp::Handle {
                body,
                return_body,
                ops,
                ..
            } => {
                scan_comp(body, out);
                if let Some(rb) = return_body {
                    scan_comp(rb, out);
                }
                for op in ops {
                    scan_comp(&op.body, out);
                }
            }
        }
    }

    let (_, _, core) = frontend(full, roots, &Config::from_env())?;
    let reachable = reachable_fns(&core);
    let mut out = Vec::new();
    for f in core.fns.iter().filter(|f| reachable.contains(&f.name)) {
        scan_comp(&f.body, &mut out);
    }
    for w in INPUT_WRAPPERS {
        if reachable.contains(&Sym::new(w)) && !out.contains(w) {
            out.push(w);
        }
    }
    Ok(out)
}

// Core function names contributed by the prelude alone, used to elide it from a
// snippet's IR dump. The prelude is a compile-time constant and its function
// names do not depend on any environment knob, so the set is memoized once per
// process rather than re-elaborating the prelude on every dump.
fn prelude_fn_names() -> Result<HashSet<Sym>, Error> {
    static CACHE: OnceLock<HashSet<Sym>> = OnceLock::new();
    if let Some(cached) = CACHE.get() {
        return Ok(cached.clone());
    }
    let (_, _, core) = frontend(PRELUDE, &default_roots(Path::new(".")), &Config::from_env())?;
    let names: HashSet<Sym> = core.into_core().fns.into_iter().map(|f| f.name).collect();
    let _ = CACHE.set(names.clone());
    Ok(names)
}

// Drop the prelude's functions from a core dump, leaving only the snippet's own
// declarations. The 300-plus prelude functions otherwise bury the user's code;
// the playground filters them the same way, so CLI `dump` matches it.
fn strip_prelude(core: Core, prelude: &HashSet<Sym>) -> Core {
    Core {
        fns: core
            .fns
            .into_iter()
            .filter(|f| !prelude.contains(&f.name))
            .collect(),
    }
}
// Out-of-Core elaboration inputs the content hash must commit to, keyed by
// canonical symbol: the generalized type, the principal effect row, the
// fip/fbip annotation, and the borrow mask. The last two affect
// codegen (the mask drives `insert_rc`, fip pins the loop lowering), so a change
// to either must change the hash even when the Core body is byte-identical.
pub(crate) fn hash_meta(checked: &Checked, sigs: &Sigs, fips: &Fips) -> BTreeMap<Sym, String> {
    checked
        .defs
        .decls
        .iter()
        .map(|d| {
            let sym = Sym::new(&d.name);
            let fip = fips
                .get(&sym)
                .copied()
                .and_then(Fip::render)
                .unwrap_or_default();
            let mask: String = sigs.get(&sym).map_or_else(String::new, |bs| {
                bs.iter().map(|b| if *b { 'b' } else { '.' }).collect()
            });
            (
                sym,
                // The content-hash meta must be a stable, complete rendering: it
                // always spells the effect row (even when empty) so a change to the
                // display flag `SHOW_EMPTY_EFFECT_ROW` can never move a hash.
                format!(
                    "{} ! {} fip:{fip} borrow:{mask}",
                    d.ty.show(),
                    show_effects(&d.effects)
                ),
            )
        })
        .collect()
}

// The whole-program identity of pre-optimizer elaborated Core: the same
// canonical regime the store commit and the `core-hash`/`namespace` dumps use
// (per-definition Merkle hashes folded into one root). Used only by the
// `--time-compile` `elaborate` row as its output artifact key, so it is computed
// only when the timing sink is installed.
pub(crate) fn core_root_digest(
    program: &Program<CorePhase>,
    checked: &Checked,
    core: &Core,
) -> String {
    let meta = hash_meta(checked, &borrow_sigs(program), &fip_annots(program));
    let entries: BTreeMap<String, Digest> = hash_program(core, &meta)
        .into_iter()
        .map(|(sym, hash)| (sym.as_str().to_string(), hash))
        .collect();
    hash_root(&entries).into_string()
}
