use std::collections::BTreeMap;
use std::path::Path;
use std::sync::OnceLock;

use crate::core::fbip::{borrow_sigs, Fips, Sigs};
use crate::core::opt::PassStage;
use crate::core::{
    balanced, fip_annots, hash_program, hash_root, insert_rc, lower_effects, pp_core_pretty, reuse,
    run_opt, run_opt_spec, Comp, Core, DepGraph, Digest, EffectStrategy, ElaboratedCore,
    LoweredCore, OpGrades, Value, HASH_SCHEME,
};
use crate::error::{Error, TypeError};
use crate::parse::{parse, ParseResult};
use crate::resolve::{default_roots, Root};
use crate::store::coherence::{self, CoherenceError};
use crate::store::disk::{self as store, CommitStats, DefMeta};
use crate::sym::Sym;
use crate::syntax::ast::{Core as CorePhase, Fip, Program, Span};
use crate::types::{show_effects, show_type_with_effects, Checked, CtorInfo};

mod artifact;
mod build;
mod config;
mod diff;
mod dump;
mod execution;
mod front;
mod identity;
#[cfg(feature = "native")]
mod native;
mod query;
mod report;
mod timing;
mod verify;
pub use artifact::{ArtifactField, ArtifactIdentity, ArtifactRow};
pub use build::rc_balanced;
#[cfg(feature = "native")]
pub use build::{build, build_at, build_on, build_on_report, emit_ir, NativeBuildReport};
#[cfg(feature = "mlir")]
pub use build::{build_mlir, build_mlir_at, build_mlir_on};
pub use config::{BackendOpt, Config, Scheduler};
pub use diff::{
    diff_on, source_diff_on, DiffChangedDef, DiffNamedDef, SourceDiff, SOURCE_DIFF_FORMAT,
};
pub(crate) use diff::{diff_on_roots, render_source_diff, source_diff_on_roots};
pub use dump::{dump, dump_at, dump_on};
pub use execution::{
    debug_on, interpret, interpret_at, interpret_io_at, interpret_io_on, interpret_io_on_with_args,
    record_on, record_on_with_args, record_run_on, replay_on, replay_run_on, resume_on,
    step_ruler_on, suspend_line_cuts, suspend_on, RecordedRun, StepRuler, StepRulerRow, SuspendCut,
    SuspendResult, STEP_RULER_FORMAT,
};
use front::{run_front, Front, FrontOpts};
pub(crate) use identity::stdlib_driver_src;
pub use identity::{
    namespace_identity, namespace_root, public_surface, stdlib_hash, NamespaceIdentity, PublicDef,
    StdlibHash,
};
#[cfg(feature = "native")]
pub(crate) use identity::{BuildIdentity, BuildRoot};
pub use query::query_on;
pub use report::{report, report_at, report_on, shape_digests_of};
pub use timing::TimingSink;
#[cfg(feature = "native")]
pub use verify::attest_on;

pub const PRELUDE: &str = include_str!("../../lib/prelude.pr");

/// The source file extension. Modules `import Foo` resolve to `Foo.pr`.
pub const SOURCE_EXT: &str = "pr";

/// Artifact kind for a whole-program namespace root.
pub const NAMESPACE_ARTIFACT_KIND: &str = "namespace";

/// Layout version of the `dump namespace` export envelope. The export records it
/// so a reader can tell which layout it is decoding and dispatch on it; a
/// layout-breaking change to the envelope bumps this. It is independent of the
/// hash scheme tag, which versions the hashing itself, not the export around it.
const NAMESPACE_FORMAT: u32 = 1;

/// The wire envelope's kind tag: the five things every serialized envelope can
/// name.
///
/// One header shape, `[scheme tag][kind][contract digest][body?]`, read five ways
/// rather than five formats. This enum is the single home of the family; the `dump namespace`
/// export and (later) the binary codec name their kind from here rather than
/// re-typing the strings. When the `lib/std/Wire.pr` codec needs the same
/// strings, they cross the phase boundary as a pinned hook (the `names.rs`
/// pattern: one canonical home with tested inverses), never a re-typed literal.
///
/// The textual name is what the human-facing header spells; the varint tag is
/// reserved for the compact binary body and is pinned here so the two encodings
/// agree on the family and its ordering before that body exists.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WireKind {
    /// A value at a frozen layout: contract digest names the type's `Stable.Vn`.
    Value,
    /// A definition: contract digest is the scheme identity, body is anonymous Core.
    Def,
    /// An effect signature: contract digest is the signature's shape digest.
    Protocol,
    /// A reified continuation: a `value` over `def` digests.
    Kont,
    /// A certificate: an attestation braided with the replay log.
    Cert,
}

impl WireKind {
    /// The textual header name, the stable string every text reader dispatches on.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::Value => "value",
            Self::Def => "def",
            Self::Protocol => "protocol",
            Self::Kont => "kont",
            Self::Cert => "cert",
        }
    }

    /// The varint discriminant reserved for the compact binary codec. Not emitted
    /// in the text envelope; pinned alongside `tag` so both encodings share one
    /// family ordering when the binary body lands in `lib/std/Wire.pr`.
    #[must_use]
    pub const fn varint(self) -> u8 {
        match self {
            Self::Value => 0,
            Self::Def => 1,
            Self::Protocol => 2,
            Self::Kont => 3,
            Self::Cert => 4,
        }
    }

    /// Recover a kind from its textual tag, rejecting anything outside the family.
    #[must_use]
    pub fn parse(tag: &str) -> Option<Self> {
        [
            Self::Value,
            Self::Def,
            Self::Protocol,
            Self::Kont,
            Self::Cert,
        ]
        .into_iter()
        .find(|k| k.tag() == tag)
    }
}

/// The envelope header recovered from a `dump namespace` export: enough to
/// dispatch a reader before it touches the body.
///
/// [`parse`](Self::parse) rejects a
/// scheme it does not recognize and a kind outside the family, so a stale or
/// foreign frame is caught on the header, not three fields into the body:
/// the contract is checked before the body, always.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnvelopeHeader {
    /// Which of the five envelope kinds this frame carries.
    pub kind: WireKind,
    /// The contract digest the reader checks before touching the body.
    pub contract: String,
    /// The export layout version (`NAMESPACE_FORMAT`).
    pub format: u32,
}

impl EnvelopeHeader {
    /// Parse the `envelope` object of a serialized export. Returns `None` on a
    /// foreign scheme, an unknown kind, or a missing/ill-typed field.
    #[must_use]
    pub fn parse(doc: &serde_json::Value) -> Option<Self> {
        let env = doc.get("envelope")?;
        if env.get("scheme")?.as_str()? != HASH_SCHEME {
            return None;
        }
        Some(Self {
            kind: WireKind::parse(env.get("kind")?.as_str()?)?,
            contract: env.get("contract")?.as_str()?.to_string(),
            format: u32::try_from(env.get("format")?.as_u64()?).ok()?,
        })
    }
}

#[cfg(feature = "native")]
const NATIVE_KONT_FRAME_FLAGS: [&str; 4] = [
    "-DPRISM_NATIVE_KONT_FRAMES",
    "-fno-omit-frame-pointer",
    "-funwind-tables",
    "-fno-optimize-sibling-calls",
];

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
    crate::resolve::imported_paths(&program, roots)
}

/// The boundary line [`with_custom_prelude`] stamps between a project's own
/// prelude and the user source.
///
/// The built-in prelude is located by its known text, but a custom prelude's
/// length is unknowable from content alone, so composition records the boundary
/// in the one artifact that crosses the pipeline (the composed source) and
/// [`SourceMap`](crate::error::SourceMap) reads it back. A comment to the
/// lexer; the `@`s keep it a line no formatter or ordinary source spells.
pub const PRELUDE_END_MARK: &str = "-- prism@prelude@end";

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
/// whole snippet becomes the body of an implicit `main`, so a bare expression
/// (`unwrap_or(0, Some(5))`) or a `let`-block runs like a REPL line and yields a
/// value. A snippet that is neither (top-level declarations with no `main`, which
/// cannot sit inside a function body) is returned unchanged, so the caller sees
/// it has no entry point. Idempotent: wrapping a wrapped snippet is a no-op.
#[must_use]
pub fn example_program(src: &str) -> String {
    let defines_main = |s: &str| {
        parse(s).is_ok_and(|pr| {
            pr.program
                .fns
                .iter()
                .any(|d| d.name == crate::names::ENTRY_POINT)
        })
    };
    if defines_main(src) {
        return src.to_string();
    }
    let body: String = src
        .lines()
        .map(|l| format!("  {l}"))
        .collect::<Vec<_>>()
        .join("\n");
    let wrapped = format!("fn {}() =\n{body}", crate::names::ENTRY_POINT);
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
/// let double = checked.decls.iter().find(|d| d.name == "double").unwrap();
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
    Ok(run_front(src, roots, cfg, FrontOpts::CHECK)?.into_checked())
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
    Ok(run_front(src, roots, cfg, FrontOpts::CHECK_VALIDATED)?.into_checked())
}

// Unused-binding and shadowed-name lints over the resolved surface program,
// scoped to the user's own source (the prepended prelude is excluded by offset).
fn lint_surface(src: &str, prog: &Program) -> Vec<crate::tc::Warning> {
    let user_start = crate::error::SourceMap::new(src).prelude_len();
    crate::resolve::lint_bindings(prog, user_start)
}

// Surface non-fatal checker diagnostics (orphan/overlapping instances, unused or
// shadowed bindings) on stderr, with a source caret when the warning points into
// this source. Errors abort earlier, so this only runs once a program type checks.
fn emit_warnings(src: &str, checked: &Checked) {
    for w in &checked.warnings {
        eprint!(
            "{}",
            crate::error::render_warning(src, "<source>", &w.span, &w.msg, true)
        );
    }
}

// The full compile path (scheduler retarget, validators, pre-lowering optimizer),
// as the legacy tuple its many consumers destructure.
fn frontend(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<(Program<CorePhase>, Checked, ElaboratedCore), Error> {
    run_front(src, roots, cfg, FrontOpts::FULL).map(Front::into_elaborated)
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
    let root = store::resolve_store_path(cfg.flags.store_path.as_deref());
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
    let stats = store::commit_program(&store, core, &hashes, &hash_metas, &graph, &metas)?;
    // The first user-visible payoff of the store: check cost tracks the Merkle
    // closure of a change. `objects_hit` are the definitions whose hash was
    // unchanged (already compiled and stored); `objects_written` are the ones
    // that moved and were recompiled into the store. Behind the quiet knob, like
    // the other compiler-internal stat lines.
    if !cfg.flags.quiet {
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
pub fn store_def_inputs(
    src: &str,
) -> Result<(Core, crate::core::Hashes, BTreeMap<Sym, String>), Error> {
    let roots = default_roots(Path::new("."));
    let (program, checked, core) = elaborated(src, &roots)?;
    let metas = hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program));
    let hashes = hash_program(&core, &metas);
    Ok((core.0, hashes, metas))
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
    run_front(src, roots, &Config::default(), FrontOpts::IDENTITY).map(Front::into_elaborated)
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
        FrontOpts::IDENTITY_VALIDATED,
    )
    .map(Front::into_elaborated)
}

// Shared front-end and rc-balance ICE check for the interpreter entries. The
// interpreter runs the un-lowered core, but the balance check over the
// effect-lowered core still runs so a bad lowering is caught here too.
fn prepared_core(src: &str, roots: &[Root], cfg: &Config) -> Result<ElaboratedCore, Error> {
    let (program, checked, core) = frontend(src, roots, cfg)?;
    let sigs = borrow_sigs(&program);
    let (lowered, _, warning) = lower_opt(&core, &checked.ctors, &checked.op_grades(), cfg)?;
    emit_lower_warning(src, warning.as_deref(), cfg.flags.quiet);
    balanced(&reuse(&insert_rc(&lowered, &sigs)), &sigs)
        .map_err(|e| Error::CodegenBackend(format!("ICE: rc imbalance: {e}")))?;
    Ok(core)
}

// The effect-lowered core, its constructor table, and any fallback warning.
type Lowered = (LoweredCore, BTreeMap<String, CtorInfo>, Option<String>);

// Effect-lower `core`, then run the late (post-lowering) optimization passes on
// the result. The late stage is where the simplifier lives: lowering has already
// fixed the var/State fusion strategy, so simplifying here cannot defeat it. Every
// path that produces or shows the lowered native core goes through this, so the
// compiled binary and the `lowered`/`llvm`/`mlir` dumps stay in step.
fn lower_opt(
    core: &ElaboratedCore,
    ctors: &BTreeMap<String, CtorInfo>,
    grades: &OpGrades,
    cfg: &Config,
) -> Result<Lowered, Error> {
    let (lowered, ctors, warning) = timing::timed_res(
        cfg.timing.as_ref(),
        timing::Phase::LowerEffects,
        "",
        || lower_effects(core, ctors, &cfg.flags, grades),
        |_| timing::RowExtras::default(),
    )?;
    let empty = std::collections::BTreeSet::new();
    let (lowered, _stats) = timing::timed(
        cfg.timing.as_ref(),
        timing::Phase::OptLate,
        "",
        || {
            cfg.passes.as_ref().map_or_else(
                || {
                    run_opt(
                        &lowered,
                        &empty,
                        cfg.opt,
                        PassStage::Late,
                        &cfg.disabled,
                        &cfg.flags,
                    )
                },
                |spec| {
                    run_opt_spec(
                        &lowered,
                        &empty,
                        &spec.late,
                        PassStage::Late,
                        &cfg.disabled,
                        &cfg.flags,
                    )
                },
            )
        },
        |_| timing::RowExtras::default(),
    );
    Ok((LoweredCore(lowered), ctors, warning))
}

fn lowered_core(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<(Checked, LoweredCore, BTreeMap<String, CtorInfo>, Sigs), Error> {
    let (program, checked, core) = frontend(src, roots, cfg)?;
    let sigs = borrow_sigs(&program);
    let (lowered, ctors, warning) = lower_opt(&core, &checked.ctors, &checked.op_grades(), cfg)?;
    emit_lower_warning(src, warning.as_deref(), cfg.flags.quiet);
    Ok((checked, lowered, ctors, sigs))
}

// Surface the effect-lowering fallback warning through the standard renderer,
// the same one `emit_warnings` uses for checker diagnostics. The diagnostic
// comes from the Core phase, which carries no source spans, so it renders as a
// plain `warning: ...` line (an empty span makes `render_warning` skip the caret).
// `quiet` (from DynFlags) silences it, matching the documented PRISM_QUIET
// contract that covers both the fallback and matcher-drift warnings.
fn emit_lower_warning(src: &str, warning: Option<&str>, quiet: bool) {
    if quiet {
        return;
    }
    if let Some(msg) = warning {
        eprint!(
            "{}",
            crate::error::render_warning(src, "<source>", &Span::empty(0), msg, true)
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
/// Fails on front-end errors.
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
/// Fails on front-end errors.
pub fn effect_strategy_on(full: &str, base: &Path, cfg: &Config) -> Result<EffectStrategy, Error> {
    let (_, checked, core) = frontend(full, &default_roots(base), cfg)?;
    Ok(crate::core::effect_strategy(
        &core,
        &checked.ctors,
        &cfg.flags,
        &checked.op_grades(),
    )?)
}

/// The effect-lowering fallback warnings this snippet's program raises.
///
/// Empty when it stays on a fused path. Each names the functions that lost
/// fusion and why, so a test can lock the diagnostic a slow-path program
/// produces. `full` carries the prelude.
///
/// # Errors
/// Fails on front-end errors.
pub fn effect_warnings_full(full: &str, base: &Path) -> Result<Vec<String>, Error> {
    let cfg = Config::from_env();
    let (_, checked, core) = frontend(full, &default_roots(base), &cfg)?;
    let (_, _, warning) = lower_effects(&core, &checked.ctors, &cfg.flags, &checked.op_grades())?;
    Ok(warning.into_iter().collect())
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
    Ok(core.0)
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
    let (program, _, core) = frontend(full, &default_roots(base), &Config::from_env())?;
    let sigs = borrow_sigs(&program);
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
pub fn off_platform_builtins(full: &str, base: &Path) -> Result<Vec<&'static str>, Error> {
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
            Comp::RefSet(c, v) => {
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

    let (_, _, core) = frontend(full, &default_roots(base), &Config::from_env())?;
    let reachable = crate::core::reachable_fns(&core);
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
fn prelude_fn_names() -> Result<std::collections::HashSet<Sym>, Error> {
    static CACHE: OnceLock<std::collections::HashSet<Sym>> = OnceLock::new();
    if let Some(cached) = CACHE.get() {
        return Ok(cached.clone());
    }
    let (_, _, core) = frontend(PRELUDE, &default_roots(Path::new(".")), &Config::from_env())?;
    let names: std::collections::HashSet<Sym> = core.0.fns.into_iter().map(|f| f.name).collect();
    let _ = CACHE.set(names.clone());
    Ok(names)
}

// Drop the prelude's functions from a core dump, leaving only the snippet's own
// declarations. The 300-plus prelude functions otherwise bury the user's code;
// the playground filters them the same way, so CLI `dump` matches it.
fn strip_prelude(core: Core, prelude: &std::collections::HashSet<Sym>) -> Core {
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
        .decls
        .iter()
        .map(|d| {
            let sym = Sym::new(&d.name);
            let fip = match fips.get(&sym) {
                Some(Fip::Fip) => "fip",
                Some(Fip::Fbip) => "fbip",
                _ => "",
            };
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

#[cfg(test)]
mod envelope_tests {
    #[cfg(feature = "native")]
    use std::collections::BTreeMap;
    #[cfg(feature = "native")]
    use std::path::Path;

    #[cfg(feature = "native")]
    use crate::resolve::{Root, SourceBundleIdentity};

    #[cfg(feature = "native")]
    use super::identity::native_kont_table_for;
    #[cfg(feature = "native")]
    use super::{default_roots, dump_on, Config, HASH_SCHEME};
    use super::{dump, EnvelopeHeader, WireKind, NAMESPACE_FORMAT};

    const STORE_PKG_NAME: &str = "StorePkg";
    #[cfg(feature = "native")]
    const STORE_PKG_SOURCE: &str = "pub fn answer() : Int = 41\n";
    #[cfg(feature = "native")]
    const STORE_PKG_ROOT: &str = "abc123";

    /// The five-kind family: textual tags are distinct, varints are the distinct
    /// contiguous discriminants the binary codec will reuse, and `parse` inverts
    /// `tag`. This checks the family so the text header and the future body cannot
    /// drift out of a shared ordering.
    #[test]
    fn kind_family_is_pinned() {
        let all = [
            WireKind::Value,
            WireKind::Def,
            WireKind::Protocol,
            WireKind::Kont,
            WireKind::Cert,
        ];
        for (i, k) in all.into_iter().enumerate() {
            assert_eq!(WireKind::parse(k.tag()), Some(k));
            assert_eq!(usize::from(k.varint()), i);
        }
        assert_eq!(WireKind::parse("gremlin"), None);
    }

    /// A `dump namespace` export parses back to its header: scheme accepted, kind
    /// and contract digest recoverable, format matched.
    #[test]
    fn namespace_header_round_trips() {
        let out = dump("namespace", "let main = 1\n").expect("namespace export");
        let doc: serde_json::Value = serde_json::from_str(&out).expect("valid json export");
        let hdr = EnvelopeHeader::parse(&doc).expect("header parses");
        assert_eq!(hdr.kind, WireKind::Def);
        assert_eq!(hdr.format, NAMESPACE_FORMAT);
        assert!(!hdr.contract.is_empty());
    }

    #[test]
    fn artifact_identity_fingerprint_names_roots() {
        let identity = super::Config::default()
            .artifact_identity_for("llvm")
            .with_source_root("source123")
            .with_stdlib_root("std456")
            .with_package_roots([format!("{STORE_PKG_NAME}@prism-core-hash-v1:pkg789")]);
        let fingerprint = identity.fingerprint();
        assert!(fingerprint.contains("source-root=prism-core-hash-v1:source123;"));
        assert!(fingerprint.contains("stdlib-root=prism-core-hash-v1:std456;"));
        assert!(fingerprint.contains(&format!(
            "package-root={STORE_PKG_NAME}@prism-core-hash-v1:pkg789;"
        )));
    }

    /// Native kont serialization needs this table as its code-identity bridge:
    /// raw native symbols are paired with the same definition hashes used by the
    /// interpreter kont envelope.
    #[test]
    fn native_kont_table_names_native_symbols_by_hash() {
        let out = dump("native-kont-table", "fn main() = 1\n").expect("native kont table");
        assert!(out.starts_with("scheme  prism-core-hash-v1\nbundle  "));
        assert!(
            out.contains(&format!("compiler  {}\n", env!("CARGO_PKG_VERSION")))
                && out.contains(&format!("target  {}\n", env!("PRISM_TARGET")))
                && out.contains("backend  llvm\n")
                && out.contains("flag  scheduler  cooperative\n")
                && out.contains("flag  backend-opt  2\n")
                && out.contains("flag  effect-tier  auto\n"),
            "native table includes portable artifact identity:\n{out}"
        );
        assert!(
            !out.contains("native-cc-version"),
            "dumped native table must not embed host-specific C compiler strings:\n{out}"
        );
        assert!(
            out.contains("flag  source-root  prism-core-hash-v1:")
                && out.contains("flag  stdlib-root  prism-core-hash-v1:"),
            "native table names source and Std roots:\n{out}"
        );
        assert!(
            out.lines()
                .any(|line| line.starts_with("fn      prism_main  ") && line.ends_with("  main")),
            "native table includes the main symbol and its definition hash:\n{out}"
        );
    }

    #[cfg(feature = "native")]
    #[test]
    fn native_kont_table_names_package_source_roots() {
        let mut modules = BTreeMap::new();
        modules.insert(STORE_PKG_NAME.to_string(), STORE_PKG_SOURCE.to_string());
        let bundle_identity =
            SourceBundleIdentity::package(STORE_PKG_NAME, HASH_SCHEME, STORE_PKG_ROOT);
        let expected = format!("flag  package-root  {}\n", bundle_identity.descriptor());
        let roots = vec![
            Root::identified_source_bundle(
                format!("<package {STORE_PKG_NAME} {STORE_PKG_ROOT}>"),
                bundle_identity,
                modules,
            ),
            Root::Embedded(crate::stdlib::STDLIB),
        ];
        let out = native_kont_table_for(
            "import StorePkg (answer)\nfn main() : Int = answer() + 1\n",
            &roots,
            &Config::default(),
        )
        .expect("native kont table");
        assert!(
            out.contains(&expected),
            "native table names package roots:\n{out}"
        );
        assert!(
            out.contains("flag  native-cc  ")
                && out.contains("flag  native-cc-version  ")
                && out.contains("flag  native-cc-flags  "),
            "native build table names native linker inputs:\n{out}"
        );
    }

    #[cfg(feature = "native")]
    #[test]
    fn native_kont_state_map_names_entry_abi_words() {
        let out = dump(
            "native-kont-state-map",
            "fn count(i, last) = if i > last then i else count(i + 1, last)\n\nfn main() = count(1, 2)\n",
        )
        .expect("native kont state map");
        assert!(out.starts_with("state-map 1\nscheme  prism-core-hash-v1\nbundle  "));
        assert!(
            out.contains("slot-format prism-native-abi-word-v1")
                && out.contains("backend  llvm\n")
                && out.contains("flag  scheduler  cooperative\n")
                && out.contains("state prism_count ")
                && out.contains(" count arity 2 slots abi-word[arg0=%a0:word,arg1=%a1:word]"),
            "native state map includes concrete entry ABI words:\n{out}"
        );
    }

    // The other side of the instrumentation gate: under the DEFAULT flags the
    // metadata table must still be embedded while the enter/arg/leave calls and
    // shadow-name constants must be absent, so neither half of the opt-in can
    // silently flip.
    #[cfg(feature = "native")]
    #[test]
    fn llvm_dump_default_has_table_without_frame_instrumentation() {
        let out = dump("llvm", "fn main() = 1\n").expect("llvm dump");
        assert!(
            out.contains("@prism_native_kont_table = constant"),
            "default LLVM IR embeds the native kont table global:\n{out}"
        );
        assert!(
            !out.contains("@prism_native_kont_enter") && !out.contains(".kont.shadow."),
            "default LLVM IR must not carry opt-in frame instrumentation:\n{out}"
        );
    }

    #[cfg(feature = "native")]
    #[test]
    fn llvm_dump_embeds_native_kont_table_global() {
        // The native kont metadata globals are always emitted, but the enter/arg/leave
        // ABI instrumentation calls are gated behind `native_kont_frames`. Enable that
        // flag (leaving every other flag at the ambient default) so this dump exercises
        // both the metadata table and the instrumented lowering under one assertion set.
        let mut cfg = Config::from_env();
        cfg.flags.native_kont_frames = true;
        let roots = default_roots(Path::new("."));
        let llvm = |src: &str| dump_on("llvm", src, &roots, &cfg).expect("llvm dump");

        let out = llvm("fn main() = 1\n");
        assert!(
            out.contains("@prism_native_kont_table = constant"),
            "LLVM IR embeds the native kont table global:\n{out}"
        );
        assert!(
            out.contains("@prism_native_kont_state_map = constant")
                && out.contains("state-map 1")
                && out.contains("slot-format prism-native-abi-word-v1")
                && out.contains("slots abi-word[]"),
            "LLVM IR embeds the native kont state-map:\n{out}"
        );
        let out = llvm(
            "fn count(i, last) = if i > last then i else count(i + 1, last)\n\nfn main() = count(1, 2)\n",
        );
        assert!(
            out.contains("state prism_count ")
                && out.contains(" count arity 2 slots abi-word[arg0=%a0:word,arg1=%a1:word]"),
            "LLVM IR embeds concrete ABI-word slots for native arguments:\n{out}"
        );
        assert!(
            out.contains("call void @prism_native_kont_enter")
                && out.contains("call void @prism_native_kont_arg")
                && out.contains("call void @prism_native_kont_leave"),
            "LLVM IR instruments native kont entry ABI values:\n{out}"
        );
        assert!(
            out.contains("prism_main") && out.contains(" main\\0A"),
            "LLVM IR table includes the native main symbol and Core name:\n{out}"
        );
        assert!(
            out.contains("@prism_native_kont_ptrs = constant")
                && out.contains("@prism_native_kont_ptrs_len = constant")
                && out.contains("ptr @prism_main"),
            "LLVM IR embeds an exact function-pointer kont lookup table:\n{out}"
        );
    }

    /// A mismatched scheme is rejected on the header, before any body is decoded.
    #[test]
    fn foreign_scheme_is_rejected() {
        let doc = serde_json::json!({
            "envelope": {
                "scheme": "some-other-scheme-v9",
                "kind": WireKind::Def.tag(),
                "contract": "deadbeef",
                "format": NAMESPACE_FORMAT,
            },
        });
        assert_eq!(EnvelopeHeader::parse(&doc), None);
    }
}
