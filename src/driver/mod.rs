use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
#[cfg(feature = "mlir")]
use std::fs;
use std::path::Path;
#[cfg(feature = "mlir")]
use std::process::Command;

#[cfg(feature = "mlir")]
use crate::codegen::emit_mlir;
#[cfg(feature = "native")]
use crate::codegen::rt::RuntimeProfile;
#[cfg(feature = "native")]
use crate::codegen::{emit_llvm_bc_with_native_kont_table, emit_llvm_with_native_kont_table};
#[cfg(feature = "native")]
use crate::core::effect_lower::residual_effects;
use crate::core::fbip::{borrow_sigs, Fips, Sigs};
use crate::core::opt::PassStage;
use crate::core::{
    balanced, elaborate, fip_annots, hash_program, hash_root, insert_rc, lower_effects, pp_core,
    pp_core_pretty, reuse, run_opt, run_opt_spec, Comp, Core, CorePass, DepGraph, ElaboratedCore,
    LoweredCore, OpGrades, OptLevel, PassSpec, Value, HASH_SCHEME,
};
use crate::error::{Error, TypeError};
use crate::eval::{run, Rv};
use crate::flags::DynFlags;
use crate::lex::lex;
#[cfg(feature = "native")]
use crate::names::ENTRY_POINT;
use crate::parse::{parse, ParseResult};
use crate::resolve::{default_roots, resolve_modules_in, Root};
use crate::store::coherence::{self, CoherenceError};
use crate::store::disk::{self as store, CommitStats, DefMeta};
use crate::sym::Sym;
use crate::syntax::ast::{Core as CorePhase, Fip, Program, Span};
use crate::syntax::desugar::desugar;
use crate::types::{check as typecheck, show_effects, Checked, CtorInfo};

mod artifact;
mod dump;
mod execution;
mod front;
mod identity;
#[cfg(feature = "native")]
mod native;
mod timing;
mod verify;
pub use artifact::ArtifactIdentity;
pub use dump::{dump, dump_at, dump_on};
pub use execution::{
    debug_on, interpret, interpret_at, interpret_io_at, interpret_io_on, interpret_io_on_with_args,
    record_on, record_on_with_args, record_run_on, replay_on, replay_run_on, resume_on,
    step_ruler_on, suspend_line_cuts, suspend_on, RecordedRun, StepRuler, StepRulerRow, SuspendCut,
    SuspendResult, STEP_RULER_FORMAT,
};
use front::{run_front, Front, FrontOpts};
pub use identity::{
    namespace_identity, namespace_root, public_surface, stdlib_hash, NamespaceIdentity, PublicDef,
    StdlibHash,
};
#[cfg(feature = "native")]
use identity::{
    native_kont_table_for, native_kont_table_for_with_rows, native_kont_table_of,
    NativeKontIdentityRows,
};
pub(crate) use identity::{stdlib_driver_src, BuildIdentity, BuildRoot};
#[cfg(feature = "native")]
use native::cc_link;
#[cfg(feature = "mlir")]
use native::ir_failure;
pub use timing::TimingSink;
#[cfg(feature = "native")]
pub use verify::attest_on;
use verify::{fip_check, replayable_check};

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

/// Which cooperative scheduler `run_cooperative` resolves to (the `--scheduler`
/// flag).
///
/// `run_async` and `run_lifo` name a specific policy directly and are never
/// retargeted, so the flag only picks the default wrap, never the semantics of a
/// program that pins its own scheduler.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Scheduler {
    /// FIFO round-robin: `run_cooperative` stays its default alias for `run_async`.
    #[default]
    Cooperative,
    /// LIFO depth-first: retarget `run_cooperative` to `run_lifo`.
    Lifo,
}

impl Scheduler {
    /// Parse a `--scheduler` value: `cooperative`/`fifo`, or `lifo`.
    #[must_use]
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "cooperative" | "fifo" => Some(Self::Cooperative),
            "lifo" => Some(Self::Lifo),
            _ => None,
        }
    }

    /// The `Concurrent` entry `run_cooperative` retargets to, or `None` when the
    /// default (`run_async`) already is the choice and no rewrite is needed.
    #[must_use]
    const fn retarget(self) -> Option<&'static str> {
        match self {
            Self::Cooperative => None,
            Self::Lifo => Some(crate::names::RUN_LIFO),
        }
    }

    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::Cooperative => "cooperative",
            Self::Lifo => "lifo",
        }
    }
}

/// The backend optimization levels clang accepts via `-O`: the single source of
/// truth shared by the `--backend-opt` flag and the `PRISM_BACKEND_OPT` env knob.
pub const BACKEND_OPT_LEVELS: [&str; 6] = ["0", "1", "2", "3", "s", "z"];
/// Backend level used when neither the flag nor the env var picks one.
pub const DEFAULT_BACKEND_OPT: &str = "2";
#[cfg(feature = "native")]
const NATIVE_KONT_FRAME_FLAGS: [&str; 4] = [
    "-DPRISM_NATIVE_KONT_FRAMES",
    "-fno-omit-frame-pointer",
    "-funwind-tables",
    "-fno-optimize-sibling-calls",
];

/// Whether `s` is a backend level clang understands; both entry paths validate
/// against this so a bad `--backend-opt` or `PRISM_BACKEND_OPT` never reaches `cc`.
#[must_use]
pub fn valid_backend_opt(s: &str) -> bool {
    BACKEND_OPT_LEVELS.contains(&s)
}

#[derive(Clone, Debug)]
pub struct Config {
    /// The Core-to-Core optimization level (the CLI `-O` flag; default `O1`).
    pub opt: OptLevel,
    /// An explicit ordered pass list (the CLI `--passes` flag) that overrides
    /// `opt` when present. The two are mutually exclusive at the CLI.
    pub passes: Option<PassSpec>,
    /// The LLVM-backend optimization level handed to `cc` as `-O<level>` (the
    /// `--backend-opt` flag; default `"2"`). Tunes clang's own pipeline over the
    /// emitted bitcode, distinct from the Core-to-Core `opt` above.
    pub backend_opt: String,
    /// Core passes the caller turned off (the `--no-<pass>` flags), filtered out
    /// of whatever pipeline `opt`/`passes` selects.
    pub disabled: Vec<CorePass>,
    /// Which cooperative scheduler `run_cooperative` binds to (the `--scheduler`
    /// flag; default cooperative/FIFO).
    pub scheduler: Scheduler,
    /// The environment-derived compiler behavior knobs (effect backends, Core
    /// Lint, dumps). Read once from the process environment and threaded into the
    /// effect lowerer and optimizer, so no pass reads the environment itself.
    pub flags: DynFlags,
    /// The per-compile timing sink, present only when the CLI installs it for a
    /// top-level `--time-compile`/`PRISM_TIME_COMPILE` compile. Absent on every
    /// [`Config::from_env`] the internal re-elaboration helpers build, so those
    /// silent compiles never emit timing rows. When absent, the timing wrappers
    /// compile away to a bare call, so the feature is zero-cost off.
    pub timing: Option<TimingSink>,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            opt: OptLevel::default(),
            passes: None,
            backend_opt: DEFAULT_BACKEND_OPT.into(),
            disabled: Vec::new(),
            scheduler: Scheduler::default(),
            flags: DynFlags::default(),
            timing: None,
        }
    }
}

impl Config {
    /// The configuration implied by the process environment: the `PRISM_OPT_LEVEL`,
    /// `PRISM_BACKEND_OPT`, and `PRISM_NO_SPECIALIZE` escape hatches resolved into a
    /// value, everything else defaulted. The library entry points use this so a
    /// bare `prism::build` still honors the env knobs; the CLI starts here and
    /// overrides with its explicit flags.
    #[must_use]
    pub fn from_env() -> Self {
        // The environment is read once, into `DynFlags`; the Config-level fields
        // are projected out of it (the CLI later overrides them with its flags).
        let flags = DynFlags::from_env();
        let mut disabled = Vec::new();
        if flags.no_specialize {
            disabled.push(CorePass::Specialize);
        }
        Self {
            opt: flags.opt_level,
            passes: None,
            backend_opt: flags.backend_opt.clone(),
            disabled,
            scheduler: flags.scheduler,
            flags,
            // A timing sink is never installed from the environment: it is a
            // property of a top-level CLI compile, so only the CLI attaches one.
            // This is what keeps the internal re-elaboration helpers silent.
            timing: None,
        }
    }

    /// Structured identity for behavior-affecting compiler artifacts.
    #[must_use]
    pub fn artifact_identity_for(&self, backend: &str) -> ArtifactIdentity {
        ArtifactIdentity::from_config(self, backend)
    }
}
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
    let (program, checked, core) = elaborated(src, roots)?;
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
                    ty: format!("{} ! {}", d.ty.show(), show_effects(&d.effects)),
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
            CoherenceError::Conflict { span, msg } => Error::Type(TypeError::Other { span, msg }),
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

// Shared front-end and rc-balance ICE check for the interpreter entries. The
// interpreter runs the un-lowered core, but the balance check over the
// effect-lowered core still runs so a bad lowering is caught here too.
fn prepared_core(src: &str, roots: &[Root], cfg: &Config) -> Result<ElaboratedCore, Error> {
    let (program, checked, core) = frontend(src, roots, cfg)?;
    let sigs = borrow_sigs(&program);
    let (lowered, _, warning) = lower_opt(&core, &checked.ctors, &checked.op_grades(), cfg)?;
    emit_lower_warning(src, warning.as_deref(), cfg.flags.quiet);
    balanced(&reuse(&insert_rc(&lowered, &sigs)), &sigs)
        .map_err(|e| Error::Codegen(format!("ICE: rc imbalance: {e}")))?;
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
/// `selective-free-monad`). A perf snapshot pins this per corpus program so a
/// silent regression onto the slow free-monad path surfaces as a reviewable diff.
/// `full` carries the prelude.
///
/// # Errors
/// Fails on front-end errors.
pub fn effect_strategy_full(full: &str, base: &Path) -> Result<&'static str, Error> {
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
pub fn effect_strategy_on(full: &str, base: &Path, cfg: &Config) -> Result<&'static str, Error> {
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
            Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.iter().for_each(|f| scan_val(f, out)),
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
// snippet's IR dump.
fn prelude_fn_names() -> Result<std::collections::HashSet<Sym>, Error> {
    let (_, _, core) = frontend(PRELUDE, &default_roots(Path::new(".")), &Config::from_env())?;
    Ok(core.0.fns.into_iter().map(|f| f.name).collect())
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
#[cfg(feature = "native")]
fn compiled(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<(Checked, LoweredCore, BTreeMap<String, CtorInfo>), Error> {
    let (checked, lowered, ctors, sigs) = lowered_core(src, roots, cfg)?;
    residual_effects(&lowered).map_err(Error::Ice)?;
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
        Err(Error::Codegen("no main function to build".into()))
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
            .map_err(Error::Codegen)
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
    .map_err(Error::Codegen)
}

/// # Errors
/// Fails on front-end errors or an unbalanced rc insertion.
pub fn rc_balanced(src: &str) -> Result<(), Error> {
    let (_, lowered, _, sigs) =
        lowered_core(src, &default_roots(Path::new(".")), &Config::from_env())?;
    balanced(&reuse(&insert_rc(&lowered, &sigs)), &sigs).map_err(Error::Codegen)
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
    let mlir_text = emit_mlir(&core, &ctors).map_err(Error::Codegen)?;
    let mlir_file = out.with_extension("mlir");
    fs::write(&mlir_file, &mlir_text)?;

    let ll_file = out.with_extension("ll");
    let translate_out = Command::new("mlir-translate")
        .arg("--mlir-to-llvmir")
        .arg(&mlir_file)
        .output()
        .map_err(|e| {
            Error::Codegen(format!(
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

fn types_section(checked: &Checked) -> String {
    let mut s = String::new();
    for d in &checked.decls {
        writeln!(s, "{} : {}", d.name, d.ty.show()).unwrap();
    }
    s
}

#[must_use]
pub fn report(src: &str) -> String {
    report_at(src, Path::new("."))
}

#[must_use]
pub fn report_at(src: &str, base: &Path) -> String {
    report_on(src, &default_roots(base), &Config::from_env())
}

/// Like [`report_at`], but against an explicit module search path.
// `cfg` drives the native-only Core/codegen phases; on wasm those are compiled
// out, so it is unused there.
#[cfg_attr(not(feature = "native"), allow(unused_variables))]
#[must_use]
pub fn report_on(src: &str, roots: &[Root], cfg: &Config) -> String {
    // Render a phase failure with the same span-aware ariadne report the CLI
    // shows for `run`/`build`/`check`, so `report` does not degrade to a bare
    // message.
    let render = |e: Error| e.render_plain(src, "<source>");
    let mut out = String::new();
    let tokens = match lex(src) {
        Ok((t, _)) => t,
        Err(e) => return render(e.into()),
    };
    let toks: Vec<String> = tokens.iter().map(|(_, t, _)| format!("{t:?}")).collect();
    section(&mut out, "tokens", &toks.join(" "));

    let ParseResult { program, .. } = match parse(src) {
        Ok(r) => r,
        Err(e) => {
            section(&mut out, "parse", &render(e.into()));
            return out;
        }
    };
    section(&mut out, "ast", &format!("{program:#?}"));

    let program = match resolve_modules_in(program, roots) {
        Ok(p) => p,
        Err(e) => {
            section(&mut out, "resolve", &render(e));
            return out;
        }
    };

    let program = match desugar(program) {
        Ok(p) => p,
        Err(e) => {
            section(&mut out, "types", &render(e.into()));
            return out;
        }
    };
    let checked = match typecheck(&program) {
        Ok(c) => c,
        Err(e) => {
            section(&mut out, "types", &render(e.into()));
            return out;
        }
    };
    section(&mut out, "types", types_section(&checked).trim_end());

    let core = match elaborate(&program, &checked) {
        Ok(c) => ElaboratedCore(c),
        Err(e) => {
            section(&mut out, "core (cbpv)", &render(e));
            return out;
        }
    };
    section(&mut out, "core (cbpv)", pp_core(&core).trim_end());

    if let Err(e) = fip_check(&program, &checked, &core) {
        section(&mut out, "fip", &render(e));
        return out;
    }

    if let Err(e) = replayable_check(&program, &checked) {
        section(&mut out, "replayable", &render(e));
        return out;
    }

    let sigs = borrow_sigs(&program);
    section(
        &mut out,
        "fbip (rc)",
        pp_core(&reuse(&insert_rc(&core, &sigs))).trim_end(),
    );

    #[cfg(feature = "native")]
    match lower_opt(&core, &checked.ctors, &checked.op_grades(), cfg) {
        Ok((lowered, ctors, _)) => {
            let hashes = hash_program(&core, &hash_meta(&checked, &sigs, &fip_annots(&program)));
            match native_kont_table_of(&hashes, roots, cfg, NativeKontIdentityRows::Portable)
                .and_then(|native_kont_table| {
                    emit_llvm_with_native_kont_table(
                        &LoweredCore(reuse(&insert_rc(&lowered, &sigs))),
                        &ctors,
                        &native_kont_table,
                        cfg.flags.native_kont_frames,
                    )
                    .map_err(Error::Codegen)
                }) {
                Ok(ir) => section(&mut out, "llvm", strip_target(&ir).trim_end()),
                Err(e) => section(&mut out, "llvm", &format!("(skipped: {e})")),
            }
        }
        Err(e) => section(&mut out, "llvm", &format!("(skipped: {e})")),
    }

    match run(&core) {
        Ok(r) => {
            let outs: Vec<String> = r.out.iter().map(Rv::show).collect();
            section(
                &mut out,
                "run",
                &format!("output: [{}]\nresult: {}", outs.join(", "), r.value.show()),
            );
        }
        Err(e) => section(&mut out, "run", &format!("error: {e}")),
    }
    out
}

/// The structural shape digest of every datatype and effect a source defines
/// (prelude included), keyed by name, full-length.
///
/// This is the format-identity gate primitive: commit the digests a persisted
/// type produces and a later edit that changes the wire layout (a new
/// constructor, a reordered field, a changed component type) moves the digest and
/// fails the committed golden, while a cosmetic edit leaves it untouched. A caller
/// snapshots or asserts on the entries for the types it persists.
///
/// # Errors
/// Fails if `src` does not parse, resolve, or type-check.
pub fn shape_digests_of(src: &str) -> Result<BTreeMap<String, String>, Error> {
    let (program, _, _) = frontend(src, &default_roots(Path::new(".")), &Config::from_env())?;
    Ok(crate::core::shape_digests(&program.types, &program.effects))
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
    let entries: BTreeMap<String, String> = hash_program(core, &meta)
        .into_iter()
        .map(|(sym, hash)| (sym.as_str().to_string(), hash))
        .collect();
    hash_root(&entries)
}

/// Answer a dependency-graph query over a program (prelude included), the
/// read-only face of the codebase-as-a-database.
///
/// `kind` is one of `callers`
/// (direct), `dependents` (the transitive Merkle closure, the exact set a change
/// to `target` would force to re-check), `deps` (what `target` transitively
/// depends on), or `uses-type` (definitions whose inferred type mentions the type
/// named `target`).
///
/// # Errors
/// Fails on front-end errors, an unknown `kind`, or a `target` that names no
/// definition (or, for the graph queries, an ambiguous unqualified name).
pub fn query_on(
    kind: &str,
    target: &str,
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<String, Error> {
    match kind {
        "callers" | "dependents" | "deps" => {
            let (_, _, core) = frontend(src, roots, cfg)?;
            let graph = DepGraph::of(&core);
            let sym = resolve_query_target(&graph, target)?;
            let set = match kind {
                "callers" => graph.direct_callers(sym),
                "dependents" => graph.dependents(sym),
                _ => graph.dependencies(sym),
            };
            let mut names: Vec<&str> = set.iter().map(|s| s.as_str()).collect();
            names.sort_unstable();
            let mut out = String::new();
            writeln!(out, "{kind} of {} ({})", sym.as_str(), names.len()).unwrap();
            for n in names {
                writeln!(out, "  {n}").unwrap();
            }
            Ok(out)
        }
        "uses-type" => {
            let checked = check_on(src, roots)?;
            let mut hits: Vec<String> = checked
                .decls
                .iter()
                .filter(|d| type_mentions(&d.ty.show(), target))
                .map(|d| format!("  {} : {}", d.name, d.ty.show()))
                .collect();
            hits.sort_unstable();
            hits.dedup();
            let mut out = String::new();
            writeln!(out, "uses-type {target} ({})", hits.len()).unwrap();
            out.push_str(&hits.join("\n"));
            out.push('\n');
            Ok(out)
        }
        other => Err(Error::Codegen(format!(
            "unknown query {other}; try callers | dependents | deps | uses-type"
        ))),
    }
}

// One revision's per-definition hashes and dependency graph. `deep` is the
// Merkle-substituted behavior identity (the regime `core-hash`, `namespace`, and
// the store commit all share, over pre-optimizer elaborated Core); `shallow` is
// each definition's own-content hash with dependencies by name, which attributes
// a deep-hash move to the definition actually edited rather than to a ripple
// through it (under the deep hash, editing one definition moves every transitive
// dependent's hash too).
struct Revision {
    deep: crate::core::Hashes,
    shallow: crate::core::Hashes,
    graph: DepGraph,
}

fn program_hashes(src: &str, roots: &[Root]) -> Result<Revision, Error> {
    let (program, checked, core) = elaborated(src, roots)?;
    let meta = hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program));
    let deep = hash_program(&core, &meta);
    let shallow = crate::core::shallow_hashes(&core, &meta);
    let graph = DepGraph::of(&core);
    Ok(Revision {
        deep,
        shallow,
        graph,
    })
}

// The prelude's own definition symbols, under the same pre-optimizer regime the
// diff hashes both revisions with, so they can be filtered out: the prelude is
// identical in both sources and would otherwise bury the user's own changes and
// inflate the unchanged count.
fn prelude_hash_names(roots: &[Root]) -> Result<std::collections::HashSet<Sym>, Error> {
    let (_, _, core) = elaborated(PRELUDE, roots)?;
    Ok(core.0.fns.into_iter().map(|f| f.name).collect())
}

/// A behavior diff between two revisions of a source.
///
/// Because every definition is content-addressed, two revisions diff
/// *semantically*: match definitions by name, compare content hashes, and report
/// what changed in behavior rather than in bytes. A pure refactor (renamed
/// locals, renamed `var`s, reordered definitions, reformatting) leaves every
/// hash fixed and so diffs to zero changed.
///
/// A real logic edit reports the exact set of definitions a developer *edited*
/// (their own content moved, detected by the shallow hash) plus the dependents
/// cone those edits affect (via [`DepGraph::dependents`] over the new revision).
/// The split matters because the deep behavior hash is Merkle: editing one
/// definition moves the hash of every transitive dependent, so a deep-hash
/// comparison alone cannot tell the edit apart from its ripple. The shallow hash
/// isolates the edit; the graph gives the blast radius.
///
/// This is store-independent: both sides are hashed in memory, so no
/// `PRISM_STORE` and no on-disk commit are involved. Prelude definitions are
/// filtered from both sides (they are identical in both and are not the subject
/// of a diff).
///
/// # Errors
/// Fails on any front-end error in either revision.
/// One definition whose behavior hash moved between two revisions.
#[derive(Debug, Clone, serde::Serialize)]
pub struct DiffChangedDef {
    pub name: String,
    pub old: String,
    pub new: String,
}

/// One definition named by a hash on one side only, or held-but-respelled.
#[derive(Debug, Clone, serde::Serialize)]
pub struct DiffNamedDef {
    pub name: String,
    pub hash: String,
}

/// The structured behavior diff between two source revisions.
///
/// Carries what moved behaviorally (deep hash), what was added or removed,
/// which dependents sit in the edited set's cone, and, the classification only
/// source text can see, which definitions changed spelling while the
/// canonicalized hash held.
#[derive(Debug, Clone, serde::Serialize)]
pub struct SourceDiff {
    pub format: &'static str,
    pub behavioral: Vec<DiffChangedDef>,
    pub added: Vec<DiffNamedDef>,
    pub removed: Vec<DiffNamedDef>,
    pub text_only: Vec<DiffNamedDef>,
    pub dependents: Vec<String>,
    pub unchanged: usize,
}

/// The format tag `SourceDiff` serializes under.
pub const SOURCE_DIFF_FORMAT: &str = "prism-source-diff-v1";

// Per-definition source slices, for the text-only classification: bare name to
// the trimmed span text of each top-level function. Parse-only, no checking.
fn decl_slices(src: &str) -> Result<std::collections::BTreeMap<String, String>, Error> {
    let parsed = parse(src)?;
    Ok(parsed
        .program
        .fns
        .iter()
        .filter_map(|d| {
            let text = src.get(d.span.start..d.span.end)?;
            Some((d.name.clone(), text.trim().to_string()))
        })
        .collect())
}

/// The structured diff behind `prism diff` over two source revisions.
///
/// # Errors
/// Fails when either revision fails the frontend.
pub fn source_diff_on(
    old_src: &str,
    new_src: &str,
    roots: &[Root],
    _cfg: &Config,
) -> Result<SourceDiff, Error> {
    let prelude = prelude_hash_names(roots)?;
    let old = program_hashes(old_src, roots)?;
    let new = program_hashes(new_src, roots)?;

    let is_user = |s: &Sym| !prelude.contains(s);
    let names = |hs: &crate::core::Hashes| -> BTreeSet<Sym> {
        hs.keys().copied().filter(is_user).collect()
    };
    let old_names = names(&old.deep);
    let new_names = names(&new.deep);

    // A definition present in both revisions is *edited* when its own content
    // moved (shallow hash), *unchanged* when its behavior held (deep hash), and
    // otherwise only rippled by a dependency (it lands in the cone below, not
    // here). Edited lines carry the deep (behavior) hashes, the identity that
    // actually moved.
    let mut changed: Vec<(Sym, String, String)> = Vec::new();
    let mut unchanged = 0usize;
    for sym in old_names.intersection(&new_names) {
        if old.deep[sym] == new.deep[sym] {
            unchanged += 1;
        } else if old.shallow[sym] != new.shallow[sym] {
            changed.push((*sym, old.deep[sym].clone(), new.deep[sym].clone()));
        }
    }
    let mut added: Vec<(Sym, String)> = new_names
        .difference(&old_names)
        .map(|s| (*s, new.deep[s].clone()))
        .collect();
    let mut removed: Vec<(Sym, String)> = old_names
        .difference(&new_names)
        .map(|s| (*s, old.deep[s].clone()))
        .collect();

    // The dependents cone of the edited set over the new revision's graph: every
    // user definition transitively affected by an edit. Edited and added
    // definitions are reported on their own lines, so they are excluded from the
    // cone, as is the prelude (which never depends on user code).
    let edited: BTreeSet<Sym> = changed.iter().map(|(s, _, _)| *s).collect();
    let added_set: BTreeSet<Sym> = added.iter().map(|(s, _)| *s).collect();
    let mut cone: BTreeSet<Sym> = BTreeSet::new();
    for sym in &edited {
        cone.extend(new.graph.dependents(*sym));
    }
    cone.retain(|s| is_user(s) && !edited.contains(s) && !added_set.contains(s));

    changed.sort_by(|a, b| a.0.as_str().cmp(b.0.as_str()));
    added.sort_by(|a, b| a.0.as_str().cmp(b.0.as_str()));
    removed.sort_by(|a, b| a.0.as_str().cmp(b.0.as_str()));

    // The classification hashes cannot see: a definition whose canonicalized
    // hashes held on both sides but whose written text moved (a rename, a
    // reformat, a comment). Only definitions visible in both parses classify;
    // canonical (module-qualified) names match a parsed bare name by tail.
    let old_text = decl_slices(old_src)?;
    let new_text = decl_slices(new_src)?;
    let bare = |s: &str| s.rsplit_once('.').map_or(s, |(_, t)| t).to_string();
    let mut text_only: Vec<DiffNamedDef> = Vec::new();
    for sym in old_names.intersection(&new_names) {
        if old.deep[sym] != new.deep[sym] || old.shallow[sym] != new.shallow[sym] {
            continue;
        }
        let key = bare(sym.as_str());
        if let (Some(a), Some(b)) = (old_text.get(&key), new_text.get(&key)) {
            if a != b {
                text_only.push(DiffNamedDef {
                    name: sym.as_str().to_string(),
                    hash: new.deep[sym].clone(),
                });
            }
        }
    }
    text_only.sort_by(|a, b| a.name.cmp(&b.name));

    let mut dependents: Vec<String> = cone.iter().map(|s| s.as_str().to_string()).collect();
    dependents.sort_unstable();

    Ok(SourceDiff {
        format: SOURCE_DIFF_FORMAT,
        behavioral: changed
            .into_iter()
            .map(|(s, o, n)| DiffChangedDef {
                name: s.as_str().to_string(),
                old: o,
                new: n,
            })
            .collect(),
        added: added
            .into_iter()
            .map(|(s, h)| DiffNamedDef {
                name: s.as_str().to_string(),
                hash: h,
            })
            .collect(),
        removed: removed
            .into_iter()
            .map(|(s, h)| DiffNamedDef {
                name: s.as_str().to_string(),
                hash: h,
            })
            .collect(),
        text_only,
        dependents,
        unchanged,
    })
}

/// The human behavior diff between two source revisions, rendered from
/// [`source_diff_on`]'s structured result.
///
/// # Errors
/// Fails when either revision fails the frontend.
pub fn diff_on(
    old_src: &str,
    new_src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<String, Error> {
    let d = source_diff_on(old_src, new_src, roots, cfg)?;

    let short = |h: &str| h[..crate::core::HASH_PREFIX_HEX].to_string();
    let mut out = String::new();
    writeln!(
        out,
        "diff: {} changed, {} added, {} removed, {} unchanged",
        d.behavioral.len(),
        d.added.len(),
        d.removed.len(),
        d.unchanged,
    )
    .unwrap();
    for c in &d.behavioral {
        writeln!(
            out,
            "  ~ {}  {} -> {}",
            c.name,
            short(&c.old),
            short(&c.new)
        )
        .unwrap();
    }
    for a in &d.added {
        writeln!(out, "  + {}  {}", a.name, short(&a.hash)).unwrap();
    }
    for r in &d.removed {
        writeln!(out, "  - {}  {}", r.name, short(&r.hash)).unwrap();
    }
    // Spelling moved, behavior held: named so a pure refactor reads as exactly
    // that, zero behavioral changes with the text movement accounted for.
    if !d.text_only.is_empty() {
        let names: Vec<&str> = d.text_only.iter().map(|t| t.name.as_str()).collect();
        writeln!(
            out,
            "text-only: {} respelled, behavior held ({})",
            names.len(),
            names.join(", ")
        )
        .unwrap();
    }
    if d.dependents.is_empty() {
        writeln!(out, "cone: 0 affected").unwrap();
    } else {
        writeln!(
            out,
            "cone: {} affected ({})",
            d.dependents.len(),
            d.dependents.join(", ")
        )
        .unwrap();
    }
    Ok(out)
}

// Resolve a query target name to a single definition, reporting no-match and
// ambiguity as errors so the caller can qualify.
fn resolve_query_target(graph: &DepGraph, target: &str) -> Result<Sym, Error> {
    let mut candidates = graph.resolve(target);
    match candidates.len() {
        1 => Ok(candidates.remove(0)),
        0 => Err(Error::Codegen(format!("no definition named `{target}`"))),
        _ => {
            candidates.sort_by_key(|s| s.as_str());
            let list: Vec<&str> = candidates.iter().map(|s| s.as_str()).collect();
            Err(Error::Codegen(format!(
                "`{target}` is ambiguous; qualify one of: {}",
                list.join(", ")
            )))
        }
    }
}

// Whether a shown type string mentions the type named `name` as a whole token,
// so `List` matches `List(Int)` but not `Listable`.
fn type_mentions(ty: &str, name: &str) -> bool {
    ty.split(|c: char| !c.is_alphanumeric() && c != '_')
        .any(|tok| tok == name)
}

// The module's target triple and data layout are host-derived, so they differ
// between machines. They are irrelevant to the snapshotted pipeline (clang
// re-derives them at link time), so drop them from the dump.
#[cfg(feature = "native")]
fn strip_target(ir: &str) -> String {
    ir.lines()
        .filter(|l| !l.starts_with("target datalayout") && !l.starts_with("target triple"))
        .collect::<Vec<_>>()
        .join("\n")
}

fn section(out: &mut String, title: &str, body: &str) {
    writeln!(out, "== {title} ==").unwrap();
    writeln!(out, "{body}").unwrap();
    out.push('\n');
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
    use super::{default_roots, dump_on, native_kont_table_for, Config, HASH_SCHEME};
    use super::{dump, EnvelopeHeader, WireKind, NAMESPACE_FORMAT};

    const STORE_PKG_NAME: &str = "StorePkg";
    #[cfg(feature = "native")]
    const STORE_PKG_SOURCE: &str = "pub fn answer() : Int = 41\n";
    #[cfg(feature = "native")]
    const STORE_PKG_ROOT: &str = "abc123";

    /// The five-kind family: textual tags are distinct, varints are the distinct
    /// contiguous discriminants the binary codec will reuse, and `parse` inverts
    /// `tag`. This pins the family so the text header and the future body cannot
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
