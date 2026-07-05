use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::Path;
#[cfg(feature = "native")]
use std::process::Command;
#[cfg(feature = "native")]
use std::{env, fs};

#[cfg(feature = "mlir")]
use crate::codegen::emit_mlir;
#[cfg(feature = "native")]
use crate::codegen::{emit_llvm, emit_llvm_bc};
#[cfg(feature = "native")]
use crate::core::effect_lower::residual_effects;
use crate::core::fbip::{borrow_sigs, Fips, Sigs};
use crate::core::opt::PassStage;
use crate::core::{
    balanced, check_fip, check_fip_linear, elaborate, fip_annots, hash_program, insert_rc,
    lower_effects, newtype_ctors, pp_core, pp_core_pretty, replayable_annots, reuse, run_opt,
    run_opt_spec, Comp, Core, CorePass, DepGraph, OpGrades, OptLevel, PassSpec, Value,
};
use crate::debug::trace;
use crate::error::{Error, TypeError};
use crate::eval::{run, run_traced, Run, Rv, Tape};
use crate::flags::DynFlags;
use crate::lex::lex;
#[cfg(feature = "native")]
use crate::names::ENTRY_POINT;
use crate::parse::{parse, ParseResult};
#[cfg(feature = "native")]
use crate::pkg::transport::{DiskTransport, Transport};
#[cfg(feature = "native")]
use crate::pkg::trust::{parse_index, verify_signature, Verdict};
use crate::resolve::{default_roots, resolve_modules_in, Root};
#[cfg(feature = "native")]
use crate::store::cert::{emit, parity_cert, BACKEND_LLVM, CLAIM_PARITY_PASSED_NAME};
use crate::store::coherence::{self, CoherenceError};
use crate::store::disk::{self as store, CommitStats, DefMeta};
use crate::sym::Sym;
use crate::syntax::ast::{Core as CorePhase, Fip, Program, Span};
use crate::syntax::desugar::desugar;
use crate::types::{check as typecheck, show_effects, Checked, CtorInfo};

pub const PRELUDE: &str = include_str!("../../lib/prelude.pr");

/// The source file extension. Modules `import Foo` resolve to `Foo.pr`.
pub const SOURCE_EXT: &str = "pr";

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
        if env.get("scheme")?.as_str()? != crate::core::HASH_SCHEME {
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
}

/// The backend optimization levels clang accepts via `-O`: the single source of
/// truth shared by the `--backend-opt` flag and the `PRISM_BACKEND_OPT` env knob.
pub const BACKEND_OPT_LEVELS: [&str; 6] = ["0", "1", "2", "3", "s", "z"];
/// Backend level used when neither the flag nor the env var picks one.
pub const DEFAULT_BACKEND_OPT: &str = "2";

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
        }
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
    let ParseResult { program, .. } = parse(src)?;
    let program = resolve_modules_in(program, roots)?;
    let lints = lint_surface(src, &program);
    let program = desugar(program)?;
    let mut checked = typecheck(&program)?;
    checked.warnings.extend(lints);
    emit_warnings(src, &checked);
    Ok(checked)
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

fn frontend(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<(Program<CorePhase>, Checked, Core), Error> {
    let ParseResult { program, .. } = parse(src)?;
    let program = resolve_modules_in(program, roots)?;
    let lints = lint_surface(src, &program);
    let mut program = desugar(program)?;
    // The `--scheduler` choice retargets only the policy-neutral `run_cooperative`
    // entry; a program that pins `run_async`/`run_lifo` is untouched.
    if let Some(target) = cfg.scheduler.retarget() {
        crate::syntax::desugar::retarget_cooperative(&mut program, target);
    }
    let mut checked = typecheck(&program)?;
    checked.warnings.extend(lints);
    emit_warnings(src, &checked);
    let core = elaborate(&program, &checked)?;
    fip_check(&program, &checked, &core)?;
    replayable_check(&program, &checked)?;
    reconcile_effects(&checked, &core)?;
    // Mid-level Core-to-Core optimization tier. Runs above the interpreter/native
    // fork so both backends consume the same optimized Core (the parity oracle
    // holds by construction). Placed after the fip/effect validators so they
    // still judge the program as written. Newtype erasure is mandatory (a
    // representation both backends depend on); specialization is opt-out via
    // `PRISM_NO_SPECIALIZE`. The level comes from the CLI `-O` flag (default O1),
    // unless an explicit `--passes` spec overrides it with its pre-stage list.
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
        |spec| run_opt_spec(&core, &nt, &spec.pre, &cfg.disabled, &cfg.flags),
    );
    Ok((program, checked, core))
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
    core: &Core,
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
    Ok((core, hashes, metas))
}

/// The namespace root of a program: the Merkle fold over its
/// `def <name> -> content-hash` entries.
///
/// This is the single value a published package tag maps to and `prism audit`
/// re-derives: the same digest a `dump namespace` export carries as its contract,
/// and the same fold shape [`stdlib_hash`] uses for the whole standard library. A
/// tag names a root; the root names the exact set of behaviors under it.
///
/// # Errors
/// Fails on any front-end error.
pub fn namespace_root(src: &str, roots: &[Root]) -> Result<String, Error> {
    let (program, checked, core) = elaborated(src, roots)?;
    let hashes = hash_program(
        &core,
        &hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program)),
    );
    Ok(namespace_root_of(&hashes))
}

// The namespace-root fold over an already-computed `name -> content-hash` map. The
// one definition of the fold, shared by `namespace_root`, the `dump namespace`
// contract digest, and the package tag pointer, so all three agree by
// construction.
pub(crate) fn namespace_root_of(hashes: &crate::core::Hashes) -> String {
    crate::core::hash_root(
        &hashes
            .iter()
            .map(|(sym, h)| {
                (
                    format!("{} {}", WireKind::Def.tag(), sym.as_str()),
                    h.clone(),
                )
            })
            .collect(),
    )
}

// The composed source that pulls in the entire documented standard library:
// the always-on prelude (which glob-imports the `Data.*` modules) plus every
// module it does not open. Docs and the stdlib hash share this one definition
// of "the stdlib", so a module missing here silently gets no hash badge in the
// generated docs (its types and functions never reach the elaborated Core the
// hash is taken from). Qualified-only (no `(..)`): the driver body never
// names anything from these modules directly, and opening them all
// unqualified collides (`Concurrent.Outcome` vs `Quickcheck.Outcome`); a
// bare import still resolves and elaborates the module.
pub(crate) fn stdlib_driver_src() -> String {
    with_prelude(
        "import Data.Checked\n\
         import Data.Vec\n\
         import Replay\n\
         import Concurrent\n\
         import Blit\n\
         import Incr\n\
         import Quickcheck\n\
         import Test\n\
         import Wire\n",
    )
}

// Elaborate a source to Core *before* the Core-to-Core optimizer runs: the one
// canonical identity surface. Every content hash is taken here, so the store
// commit, the `core-hash`/`dupes`/`namespace` dumps, the stdlib root, and the
// `store_def_inputs` re-hash front door all agree by construction. Pre-opt Core
// is used so identity cannot depend on an env-toggled pass (`Specialize`) or
// move when the optimizer is tuned, and so it holds every top-level definition
// exactly once (the optimizer has no whole-program DCE). Quiet: no warning
// emission, no surface lints.
fn elaborated(src: &str, roots: &[Root]) -> Result<(Program<CorePhase>, Checked, Core), Error> {
    let ParseResult { program, .. } = parse(src)?;
    let program = resolve_modules_in(program, roots)?;
    let program = desugar(program)?;
    let checked = typecheck(&program)?;
    let core = elaborate(&program, &checked)?;
    Ok((program, checked, core))
}

/// A content-addressed fingerprint of the whole standard library.
///
/// One namespace root (a branch-hash-style fold) over every documented
/// definition's behavior hash and every datatype/effect's shape digest, tagged
/// with the hashing scheme and the compiler version that produced it.
#[derive(Debug)]
pub struct StdlibHash {
    /// The single fold over every entry below; the value anchored in the docs.
    pub root: String,
    /// The hashing scheme tag every constituent hash commits to.
    pub scheme: &'static str,
    /// The compiler version that produced this fingerprint.
    pub version: &'static str,
    /// Per-definition behavior hashes (term level).
    pub defs: crate::core::Hashes,
    /// Per-declaration structural shape digests (datatypes and effects).
    pub shapes: BTreeMap<String, String>,
    /// Per-class interface digests (name, superclasses, method signatures).
    pub classes: BTreeMap<String, String>,
    /// Per-instance identity digests (class, head, method behavior hashes).
    pub instances: BTreeMap<String, String>,
}

/// Compute the standard-library fingerprint. See [`StdlibHash`].
///
/// # Errors
/// Fails only if the embedded stdlib does not parse, type-check, or elaborate,
/// which would be a compiler bug.
pub fn stdlib_hash() -> Result<StdlibHash, Error> {
    let src = stdlib_driver_src();
    let (program, checked, mut core) = elaborated(&src, &[Root::Embedded(crate::stdlib::STDLIB)])?;
    // Top-level constants (`let`) are inlined at use sites, so they are not in the
    // compiled Core. Elaborate them as zero-param CoreFns so each gets its own
    // behavior hash (addressable and displayable), then hash the whole set.
    core.fns.extend(crate::core::konst_fns(&program, &checked)?);
    let defs = hash_program(
        &core,
        &hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program)),
    );
    let shapes = crate::core::shape_digests(&program.types, &program.effects);
    let classes = crate::core::class_digests(&program.classes);
    // An instance's identity folds its already-computed method behavior hashes
    // (the `i@<inst>@<method>` CoreFns) with its class and head. This is nearly
    // free and doubles as the coherence seed: the `(class, head) -> hash` value.
    let defs_str: BTreeMap<String, String> = defs
        .iter()
        .map(|(k, v)| (k.as_str().to_string(), v.clone()))
        .collect();
    let mut instances: BTreeMap<String, String> = BTreeMap::new();
    for inst in &program.instances {
        let prefix = crate::names::instance_method_prefix(&inst.name);
        let methods: BTreeMap<String, String> = defs_str
            .iter()
            .filter_map(|(k, v)| k.strip_prefix(&prefix).map(|m| (m.to_string(), v.clone())))
            .collect();
        instances.insert(
            inst.name.clone(),
            crate::core::instance_digest(&inst.class, &inst.head, &methods),
        );
    }
    // Merge every kind into one name -> hash map, then fold to a single root.
    // Namespace the keys by kind so declarations that share a name across
    // namespaces (a value and an instance are both lowercase) cannot collide.
    let mut entries: BTreeMap<String, String> = BTreeMap::new();
    for (sym, h) in &defs {
        entries.insert(format!("def {}", sym.as_str()), h.clone());
    }
    for (name, h) in &shapes {
        entries.insert(format!("shape {name}"), h.clone());
    }
    for (name, h) in &classes {
        entries.insert(format!("class {name}"), h.clone());
    }
    for (name, h) in &instances {
        entries.insert(format!("instance {name}"), h.clone());
    }
    Ok(StdlibHash {
        root: crate::core::hash_root(&entries),
        scheme: crate::core::HASH_SCHEME,
        version: env!("CARGO_PKG_VERSION"),
        defs,
        shapes,
        classes,
        instances,
    })
}

// Cross-check the two effect engines as a real assertion (not a debug_assert):
// the op-keyed call-graph fixpoint used by effect lowering (`latent_ops`)
// against each function's inferred row (the effect labels of its checked type,
// `DeclInfo::effects`). The agreed direction is containment: every effect a
// function can still perform must appear in its inferred row. A violation means
// the checker under-reported an effect a later pass will still try to lower, an
// internal-consistency bug surfaced here rather than as a miscompile.
// Synthesized ops that are not type-level effects are skipped rather than
// flagged.
fn reconcile_effects(checked: &Checked, core: &Core) -> Result<(), Error> {
    let latent = crate::core::effect_lower::latent_ops(core);
    let empty = BTreeSet::new();
    // Validate against each function's inferred row (the labels of its checked
    // type), not the set-pass `effects` seed: the seed cannot count the scoped
    // masking that lets a `mask`ed effect tunnel past its handler, so only the
    // inferred row reflects what the function actually leaves unhandled.
    let inferred_rows: std::collections::BTreeMap<&str, &crate::types::Effects> = checked
        .decls
        .iter()
        .map(|d| (d.name.as_str(), &d.effects))
        .collect();
    for f in &core.fns {
        let Some(ops) = latent.get(&f.name) else {
            continue;
        };
        // An instance method is absent from `checked.decls` (those are the
        // top-level `fn`s); its effect discipline is enforced against the class
        // signature at `check_instance`, where an effect-polymorphic method may
        // legitimately perform the effects flowing through its row variable. It
        // has no standalone inferred row to reconcile against, so validating it
        // here against an empty row would spuriously flag that permitted effect.
        if crate::names::is_instance_method(f.name.as_str()) {
            continue;
        }
        let inferred = inferred_rows
            .get(f.name.as_str())
            .copied()
            .unwrap_or(&empty);
        let extra: Vec<&str> = ops
            .iter()
            .filter_map(|op| checked.eff_ops.get(op.as_str()))
            .map(|info| info.effect_name)
            .filter(|e| !inferred.contains(e))
            .collect::<BTreeSet<_>>()
            .iter()
            .map(|s| s.as_str())
            .collect();
        if !extra.is_empty() {
            let row: Vec<&str> = inferred.iter().map(|s| s.as_str()).collect();
            return Err(Error::Ice(format!(
                "effect reconciliation: `{}` can still perform {extra:?} after lowering, \
                 but its inferred row is {row:?}",
                f.name
            )));
        }
    }
    Ok(())
}

// Check the FP^2 discipline of every `fip`/`fbip`-annotated function. Linearity
// is a property of the SOURCE term, so it is checked on the raw elaborated core
// (`check_fip_linear`), using the typechecker's param/field types to exempt
// scalars (a `dup` on an immediate is a runtime no-op). Zero-allocation, the
// callee closure, and bounded stack are properties of the COMPILED term, so they
// are checked on the reuse-lowered core (`check_fip`). Runs on every
// check/build/interpret (shared `frontend`); pure annotated functions are
// unaffected by effect lowering, so this un-effect-lowered core matches
// `dump fbip`.
fn fip_check(program: &Program<CorePhase>, checked: &Checked, core: &Core) -> Result<(), Error> {
    let annots = fip_annots(program);
    if annots.is_empty() {
        return Ok(());
    }
    let to_err = |msg: String| {
        // Point the diagnostic at the offending annotated function: its name
        // appears backtick-quoted in the message, so the first annotated decl
        // whose name occurs there owns the span.
        let owner = program
            .fns
            .iter()
            .filter(|d| annots.contains_key(&Sym::from(&d.name)))
            .find(|d| msg.contains(&format!("`{}`", d.name)));
        let span = owner.map_or_else(marginalia::Span::default, |d| d.span);
        // A `without alloc` function checks with `fbip` semantics, so the shared
        // checker phrases its message with `fbip`. Restore the surface spelling
        // for a function that used the `without alloc` suffix, and for a lifted
        // `without alloc { .. }` block refer to the block rather than leak its
        // synthetic function name (the span already points at the source block).
        let msg = match owner {
            Some(d) if d.no_alloc && d.fip == Fip::No => {
                let wa = format!("{} {}", crate::kw::WITHOUT, crate::kw::ALLOC);
                let m = msg.replace("`fbip`", &format!("`{wa}`"));
                if crate::names::is_without_alloc_block(&d.name) {
                    m.replace(
                        &format!("function `{}` is marked `{wa}` but", d.name),
                        &format!("the `{wa}` block"),
                    )
                    .replace(&format!("`{}`", d.name), &format!("the `{wa}` block"))
                } else {
                    m
                }
            }
            _ => msg,
        };
        Error::Type(TypeError::Other { span, msg })
    };
    let sigs = borrow_sigs(program);
    let users: std::collections::BTreeSet<Sym> = core.fns.iter().map(|f| f.name).collect();
    check_fip_linear(core, &annots, &checked.decls, &checked.ctors).map_err(to_err)?;
    check_fip(&reuse(&insert_rc(core, &sigs)), &annots, &sigs, &users).map_err(to_err)
}

// Check every `replayable`-annotated function. The certificate is on the inferred
// principal row: it must stay within the recordable capabilities (`Console`,
// `FileSystem`, `Random`, `Env`, `Output`) plus the deterministic builtin effects
// (`Exn`, `Fail`). `Output` is admitted because replay/durable suppress it during
// the replayed prefix, so re-running it is sound. A row containing `IO` (un-logged
// nondeterminism: the system clock, srand) or any user-defined effect cannot be
// reproduced from a trace, so it is rejected with a caret at the function naming
// the offending effect(s).
fn replayable_check(program: &Program<CorePhase>, checked: &Checked) -> Result<(), Error> {
    let annots = replayable_annots(program);
    if annots.is_empty() {
        return Ok(());
    }
    let allowed: std::collections::BTreeSet<Sym> = crate::names::INPUT_CAPABILITY_EFFECTS
        .iter()
        .copied()
        .chain([
            crate::names::OUTPUT_EFFECT,
            crate::names::EXN_EFFECT,
            crate::names::FAIL_EFFECT,
        ])
        .map(Sym::from)
        .collect();
    let inferred: std::collections::BTreeMap<&str, &crate::types::ty::Effects> = checked
        .decls
        .iter()
        .map(|i| (i.name.as_str(), &i.effects))
        .collect();
    for d in &program.fns {
        if !annots.contains(&Sym::from(&d.name)) {
            continue;
        }
        let Some(row) = inferred.get(d.name.as_str()).copied() else {
            continue;
        };
        let offending: Vec<&str> = row
            .iter()
            .filter(|e| !allowed.contains(*e))
            .map(|e| e.as_str())
            .collect();
        if !offending.is_empty() {
            let msg = format!(
                "function `{}` is marked `replayable` but performs non-replayable {} `{}`; \
                 a replayable function may use only Console, FileSystem, Random, Env, Clock, Output, Exn, Fail",
                d.name,
                if offending.len() == 1 {
                    "effect"
                } else {
                    "effects"
                },
                offending.join("`, `")
            );
            return Err(Error::Type(TypeError::Other { span: d.span, msg }));
        }
    }
    Ok(())
}

/// # Examples
/// ```
/// let src = prism::with_prelude("fn main() = print(1 + 2)");
/// let run = prism::interpret(&src).unwrap();
/// assert_eq!(run.out[0].show(), "3");
/// ```
///
/// # Errors
/// Fails on front-end errors or a runtime fault.
pub fn interpret(src: &str) -> Result<Run, Error> {
    interpret_at(src, Path::new("."))
}

/// Like [`interpret`], resolving any module imports relative to `base`.
///
/// Captures all `print` output into the returned [`Run`]'s `term` (the
/// differential oracle and wasm path); nothing reaches real stdio.
///
/// # Errors
/// Fails on front-end errors or a runtime fault.
pub fn interpret_at(src: &str, base: &Path) -> Result<Run, Error> {
    let core = prepared_core(src, &default_roots(base), &Config::from_env())?;
    run(&core).map_err(Error::Runtime)
}

/// Like [`interpret_at`], but streams `print` to `out_sink` and reads `input`.
///
/// The native CLI passes real stdout/stdin so program output is live and
/// `read_*` reaches the terminal; `term` still carries the exact transcript and
/// `Run::exit` carries any `exit(code)`.
///
/// # Errors
/// Fails on front-end errors or a runtime fault.
pub fn interpret_io_at(
    src: &str,
    base: &Path,
    out_sink: &mut dyn std::io::Write,
    input: &mut dyn std::io::BufRead,
) -> Result<Run, Error> {
    interpret_io_on(
        src,
        &default_roots(base),
        out_sink,
        input,
        &Config::from_env(),
    )
}

/// Like [`interpret_io_at`], but against an explicit module search path (a
/// project's source root, its path dependencies, and the stdlib).
///
/// # Errors
/// Fails on front-end errors or a runtime fault.
pub fn interpret_io_on(
    src: &str,
    roots: &[Root],
    out_sink: &mut dyn std::io::Write,
    input: &mut dyn std::io::BufRead,
    cfg: &Config,
) -> Result<Run, Error> {
    let core = prepared_core(src, roots, cfg)?;
    crate::eval::run_io(&core, out_sink, input).map_err(Error::Runtime)
}

/// Run `src` against the real world, recording every capability observation.
///
/// Streams output live (like `interpret_io_on`) and returns the process exit
/// code, if any, plus the encoded `.replay` trace to persist and its length.
///
/// # Errors
/// Fails on any front-end error or an evaluation fault.
pub fn record_on(
    src: &str,
    roots: &[Root],
    out_sink: &mut dyn std::io::Write,
    input: &mut dyn std::io::BufRead,
    cfg: &Config,
) -> Result<(Option<i32>, String, usize), Error> {
    let core = prepared_core(src, roots, cfg)?;
    let run =
        run_traced(&core, out_sink, input, Tape::Record(Vec::new())).map_err(Error::Runtime)?;
    Ok((run.exit, trace::encode(&run.frames), run.frames.len()))
}

/// Replay `src` against a recorded `.replay` trace, performing no real reads.
///
/// Reproduces the original run's output byte for byte (a corollary of the
/// determinism contract) and returns the process exit code, if any.
///
/// # Errors
/// Fails on a front-end error, a malformed trace, an evaluation fault, or a
/// trace that does not match the program.
pub fn replay_on(
    src: &str,
    roots: &[Root],
    out_sink: &mut dyn std::io::Write,
    trace: &str,
    cfg: &Config,
) -> Result<Option<i32>, Error> {
    let core = prepared_core(src, roots, cfg)?;
    let frames = trace::decode(trace).map_err(Error::Runtime)?;
    let mut empty = std::io::Cursor::new(Vec::new());
    let run = run_traced(
        &core,
        out_sink,
        &mut empty,
        Tape::Replay {
            frames,
            cursor: 0,
            budget: None,
        },
    )
    .map_err(Error::Runtime)?;
    Ok(run.exit)
}

/// Drive the terminal reverse-step debugger over `src` and a recorded trace:
/// read stepping commands from `cmds`, write the debugger UI to `ui`.
///
/// # Errors
/// Fails on a front-end error, a malformed trace, an I/O error, or a trace that
/// does not match the program.
pub fn debug_on(
    src: &str,
    roots: &[Root],
    trace: &str,
    cmds: &mut dyn std::io::BufRead,
    ui: &mut dyn std::io::Write,
    cfg: &Config,
) -> Result<(), Error> {
    let core = prepared_core(src, roots, cfg)?;
    let frames = trace::decode(trace).map_err(Error::Runtime)?;
    crate::debug::run_repl(&core, &frames, cmds, ui).map_err(Error::Runtime)
}

/// The outcome of a suspendable run: the program either finished (nothing to
/// snapshot) or paused, yielding the encoded `kont` envelope to persist.
#[derive(Debug)]
pub enum SuspendResult {
    /// Ran to completion before the step budget; carries any `exit(code)`.
    Done(Option<i32>),
    /// Paused at the budget; carries the serialized `kont` envelope.
    Suspended(Vec<u8>),
}

/// Run `src` under a step budget, streaming its prefix output to `out_sink` and
/// snapshotting the whole suspended program as a `kont` envelope when it pauses.
///
/// The snapshot is tagged with the program's code-identity digest (its namespace
/// root), which [`resume_on`] re-derives and checks. If a captured value cannot
/// cross the suspend boundary (too deeply nested, the fingerprint of an
/// unserializable capture), the refusal is raised here, at suspend time, naming
/// the value.
///
/// # Errors
/// Fails on any front-end error, an evaluation fault before the budget, or a value
/// that cannot be serialized.
pub fn suspend_on(
    src: &str,
    roots: &[Root],
    out_sink: &mut dyn std::io::Write,
    input: &mut dyn std::io::BufRead,
    budget: usize,
    cfg: &Config,
) -> Result<SuspendResult, Error> {
    let bundle = namespace_root(src, roots)?;
    let core = prepared_core(src, roots, cfg)?;
    match crate::eval::run_suspending(&core, bundle, budget, out_sink, input)
        .map_err(Error::Runtime)?
    {
        crate::eval::Checkpoint::Done(run) => Ok(SuspendResult::Done(run.exit)),
        crate::eval::Checkpoint::Suspended(kont) => {
            let bytes =
                crate::eval::kont::encode_kont(&kont).map_err(|e| Error::Runtime(e.to_string()))?;
            Ok(SuspendResult::Suspended(bytes))
        }
    }
}

// A hard cap on the line-cut scan so a nonterminating program cannot spin the
// mapping forever. Any real demo program prints its lines in far fewer steps.
const MAX_LINE_CUT_STEPS: usize = 8192;

/// The machine-step budget at which each successive output line first appears.
///
/// Compiles `src` once, then re-runs it under growing step budgets and records,
/// for each printed line, the smallest budget after which that line has been
/// emitted. The `i`th entry is the budget to pass [`suspend_on`] to pause exactly
/// after line `i + 1` has printed, so a caller can cut on a legible line boundary
/// instead of an opaque step count. The final line's boundary is omitted: pausing
/// there is completion, with nothing left to suspend.
///
/// # Errors
/// Fails on any front-end error or an evaluation fault before the program ends.
pub fn suspend_line_cuts(src: &str, roots: &[Root], cfg: &Config) -> Result<Vec<usize>, Error> {
    let bundle = namespace_root(src, roots)?;
    let core = prepared_core(src, roots, cfg)?;
    // Build the global table once: it deep-clones every function body, so rebuilding
    // it per budget would make the scan quadratic in that clone.
    let g = crate::eval::globals(&core);
    let mut cuts: Vec<usize> = Vec::new();
    for budget in 1..=MAX_LINE_CUT_STEPS {
        let mut out: Vec<u8> = Vec::new();
        let mut input = std::io::Cursor::new(Vec::new());
        let checkpoint =
            crate::eval::run_suspending_in(&g, bundle.clone(), budget, &mut out, &mut input)
                .map_err(Error::Runtime)?;
        let lines = out.iter().fold(0usize, |n, &b| n + usize::from(b == b'\n'));
        while cuts.len() < lines {
            cuts.push(budget);
        }
        if matches!(checkpoint, crate::eval::Checkpoint::Done(_)) {
            break;
        }
    }
    // Drop the last line's boundary: a cut there is a completed run.
    cuts.pop();
    Ok(cuts)
}

/// Resume a `kont` envelope against `src`, running the continuation to completion
/// and streaming its suffix output to `out_sink`.
///
/// The envelope is decoded totally (any malformed or hostile bytes are rejected),
/// then its bundle digest is checked against `src`'s freshly derived code identity:
/// a snapshot captured against a different program is refused before a single step
/// runs. The suffix output, following the suspend run's prefix, reproduces an
/// uninterrupted run byte for byte.
///
/// # Errors
/// Fails on a front-end error, a malformed envelope, a code-identity mismatch, or
/// an evaluation fault after the resume point.
pub fn resume_on(
    src: &str,
    roots: &[Root],
    snapshot: &[u8],
    out_sink: &mut dyn std::io::Write,
    input: &mut dyn std::io::BufRead,
    cfg: &Config,
) -> Result<Option<i32>, Error> {
    let kont = crate::eval::kont::decode_kont(snapshot)
        .map_err(|e| Error::Runtime(format!("resume: malformed snapshot: {e}")))?;
    let bundle = namespace_root(src, roots)?;
    if kont.bundle != bundle {
        return Err(Error::Runtime(format!(
            "resume: code-identity mismatch: this snapshot was captured against a \
             different program (snapshot bundle {}, this program {})",
            kont.bundle, bundle
        )));
    }
    let core = prepared_core(src, roots, cfg)?;
    let run = crate::eval::resume_kont(&core, kont, out_sink, input).map_err(Error::Runtime)?;
    Ok(run.exit)
}

// Run a freshly built native binary on empty stdin, returning its stdout bytes.
#[cfg(feature = "native")]
fn run_native(bin: &Path) -> Result<Vec<u8>, Error> {
    let out = Command::new(bin)
        .stdin(std::process::Stdio::null())
        .output()
        .map_err(Error::Io)?;
    if out.status.success() {
        Ok(out.stdout)
    } else {
        Err(Error::Codegen(format!(
            "attest: {} exited with {}",
            bin.display(),
            out.status
        )))
    }
}

// The interpreter transcript for `src` on empty stdin: the reference oracle a
// native backend's output must match, and the second oracle when MLIR is absent.
#[cfg(feature = "native")]
fn interp_transcript(src: &str, roots: &[Root], cfg: &Config) -> Result<Vec<u8>, Error> {
    let mut out: Vec<u8> = Vec::new();
    let mut input = std::io::Cursor::new(Vec::new());
    interpret_io_on(src, roots, &mut out, &mut input, cfg)?;
    Ok(out)
}

// The signed-index cross-check line for a root, or empty when no store, index, or
// matching pointer is present. Read-only against the package index.
#[cfg(feature = "native")]
fn attest_index_line(root: &str, cfg: &Config) -> String {
    let store_root = store::resolve_store_path(cfg.flags.store_path.as_deref());
    let Ok(dst) = DiskTransport::open(&store_root) else {
        return String::new();
    };
    let Ok(Some(artifact)) = dst.index_artifact() else {
        return String::new();
    };
    let rows = parse_index(&artifact.body);
    let Some(row) = rows.iter().find(|r| r.root == root) else {
        return String::new();
    };
    let sig = match verify_signature(&artifact, &cfg.flags) {
        Verdict::Valid { identity: Some(id) } => format!("valid ({id})"),
        Verdict::Valid { identity: None } => "valid".to_string(),
        Verdict::Unsigned => "unsigned (dev mode)".to_string(),
        Verdict::Invalid(m) => format!("INVALID: {m}"),
        Verdict::Unavailable(m) => format!("unverifiable: {m}"),
    };
    format!("  index: {}@{} signature {sig}\n", row.name, row.tag)
}

// The second, independent backend for attestation: MLIR native when the feature
// and toolchain are present, otherwise the interpreter as the second oracle with
// the limitation named.
// The `Result` is load-bearing under the `mlir` feature (`build_mlir_on` and the
// native run can fail); the fallback path is infallible, so clippy sees an
// unnecessary wrap only in the default build.
#[cfg(feature = "native")]
#[allow(clippy::unnecessary_wraps)]
fn attest_second(
    src: &str,
    roots: &[Root],
    cfg: &Config,
    tmp: &Path,
    stem: &str,
    interp: &[u8],
) -> Result<(&'static str, Vec<u8>, Option<String>), Error> {
    #[cfg(feature = "mlir")]
    {
        let has_tool = Command::new("mlir-translate")
            .arg("--version")
            .output()
            .is_ok_and(|o| o.status.success());
        if has_tool {
            let bin = tmp.join(format!("{stem}_mlir"));
            build_mlir_on(src, roots, &bin, cfg)?;
            let out = run_native(&bin)?;
            let _ = fs::remove_file(&bin);
            return Ok(("MLIR", out, None));
        }
    }
    let _ = (src, roots, cfg, tmp, stem);
    Ok((
        "interpreter",
        interp.to_vec(),
        Some(
            "MLIR backend unavailable (build with --features mlir and install mlir-translate); \
             the interpreter is the independent second oracle"
                .to_string(),
        ),
    ))
}

/// Diverse double compilation: compile and run `src` through two independent
/// backends and confirm their output is byte-identical, attested by the shared
/// content hash (the whole-program namespace root).
///
/// This is Thompson's "Trusting Trust" defeated by construction and Wheeler's
/// diverse double compilation, made a standing check rather than a heroic
/// one-off: the same source, compiled two independent ways, must observably agree
/// to the byte, and the content hash names the identity both compiled. When the
/// MLIR toolchain is present the two backends are LLVM and MLIR; otherwise the
/// interpreter is the independent second oracle and the limitation is printed. If
/// a signed-index pointer exists for the root, its name, tag, and signature
/// verdict are cross-checked and reported.
///
/// # Errors
/// A front-end error, a codegen or link failure, or a divergence between the
/// backends (the attestation's whole point is that this never happens).
#[cfg(feature = "native")]
pub fn attest_on(src: &str, roots: &[Root], cfg: &Config) -> Result<String, Error> {
    let root = namespace_root(src, roots)?;
    let interp = interp_transcript(src, roots, cfg)?;

    let tmp = std::env::temp_dir();
    let stem = format!("prism_attest_{}", std::process::id());
    let llvm_bin = tmp.join(format!("{stem}_llvm"));
    build_on(src, roots, &llvm_bin, cfg)?;
    let llvm_out = run_native(&llvm_bin)?;
    let _ = fs::remove_file(&llvm_bin);

    let (second_name, second_out, limitation) =
        attest_second(src, roots, cfg, &tmp, &stem, &interp)?;

    // The two backends must agree byte for byte; the interpreter oracle backstops
    // both, so a three-way agreement is what the green line asserts.
    if llvm_out != second_out || llvm_out != interp {
        return Err(Error::Codegen(format!(
            "attest: backends diverged for root {root}; LLVM and {second_name} are not \
             byte-identical (this is the invariant the attestation exists to catch)"
        )));
    }

    let mut out = format!("attested: {root} identical across LLVM, {second_name}\n");
    if let Some(l) = limitation {
        let _ = writeln!(out, "  note: {l}");
    }
    out.push_str(&attest_index_line(&root, cfg));
    out.push_str(&attest_cert_line(&root, second_name, cfg));
    Ok(out)
}

// Emit (or find) the parity certificate for a successfully attested root, and
// report which. Never load-bearing: a store that cannot be opened or written
// simply yields no line, so a certificate failure never fails the attestation the
// byte-identity check already established.
#[cfg(feature = "native")]
fn attest_cert_line(root: &str, second_name: &str, cfg: &Config) -> String {
    let store_root = store::resolve_store_path(cfg.flags.store_path.as_deref());
    let Ok(store) = store::Store::open_or_create(&store_root) else {
        return String::new();
    };
    let cert = parity_cert(root, (BACKEND_LLVM, second_name));
    match emit(&store, &cert) {
        Ok(store::Written::New) => {
            format!(
                "  cert: emitted {CLAIM_PARITY_PASSED_NAME}@{}\n",
                cert.scheme
            )
        }
        Ok(store::Written::Hit) => {
            format!(
                "  cert: reused existing {CLAIM_PARITY_PASSED_NAME}@{}\n",
                cert.scheme
            )
        }
        Err(_) => String::new(),
    }
}

// Shared front-end and rc-balance ICE check for the interpreter entries. The
// interpreter runs the un-lowered core, but the balance check over the
// effect-lowered core still runs so a bad lowering is caught here too.
fn prepared_core(src: &str, roots: &[Root], cfg: &Config) -> Result<Core, Error> {
    let (program, checked, core) = frontend(src, roots, cfg)?;
    let sigs = borrow_sigs(&program);
    let (lowered, _, warning) = lower_opt(&core, &checked.ctors, &checked.op_grades(), cfg)?;
    emit_lower_warning(src, warning.as_deref(), cfg.flags.quiet);
    balanced(&reuse(&insert_rc(&lowered, &sigs)), &sigs)
        .map_err(|e| Error::Codegen(format!("ICE: rc imbalance: {e}")))?;
    Ok(core)
}

// The effect-lowered core, its constructor table, and any fallback warning.
type Lowered = (Core, BTreeMap<String, CtorInfo>, Option<String>);

// Effect-lower `core`, then run the late (post-lowering) optimization passes on
// the result. The late stage is where the simplifier lives: lowering has already
// fixed the var/State fusion strategy, so simplifying here cannot defeat it. Every
// path that produces or shows the lowered native core goes through this, so the
// compiled binary and the `lowered`/`llvm`/`mlir` dumps stay in step.
fn lower_opt(
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
    grades: &OpGrades,
    cfg: &Config,
) -> Result<Lowered, Error> {
    let (lowered, ctors, warning) = lower_effects(core, ctors, &cfg.flags, grades)?;
    let empty = std::collections::BTreeSet::new();
    let (lowered, _stats) = cfg.passes.as_ref().map_or_else(
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
        |spec| run_opt_spec(&lowered, &empty, &spec.late, &cfg.disabled, &cfg.flags),
    );
    Ok((lowered, ctors, warning))
}

fn lowered_core(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<(Checked, Core, BTreeMap<String, CtorInfo>, Sigs), Error> {
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
    Ok(core)
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
    Ok(core.fns.into_iter().map(|f| f.name).collect())
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
) -> Result<(Checked, Core, BTreeMap<String, CtorInfo>), Error> {
    let (checked, lowered, ctors, sigs) = lowered_core(src, roots, cfg)?;
    residual_effects(&lowered).map_err(Error::Ice)?;
    Ok((checked, reuse(&insert_rc(&lowered, &sigs)), ctors))
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

/// Like [`build_at`], but against an explicit module search path (a project's
/// source root, its path dependencies, and the stdlib).
///
/// # Errors
/// Fails on front-end errors, codegen failure, or when linking with cc fails.
#[cfg(feature = "native")]
pub fn build_on(src: &str, roots: &[Root], out: &Path, cfg: &Config) -> Result<(), Error> {
    let (checked, core, ctors) = compiled(src, roots, cfg)?;
    require_main(&checked)?;
    let bc = out.with_extension("bc");
    emit_llvm_bc(&core, &ctors, &bc).map_err(Error::Codegen)?;
    cc_link(&bc, out, cfg)?;
    // A successful build populates the store when the knob is on. Re-elaboration
    // is cheap relative to codegen and only happens under the opt-in flag; the
    // store is a cache, so a failure here would not invalidate the build (but is
    // surfaced rather than swallowed).
    if cfg.flags.store {
        commit_to_store(src, roots, cfg)?;
    }
    Ok(())
}

// Save the offending IR at a stable path so a clang parse error points at
// something inspectable. The happy path stays a single clang invocation.
#[cfg(feature = "native")]
fn ir_failure(tool: &str, ir: &Path, stderr: &[u8]) -> Error {
    let ext = ir.extension().and_then(|e| e.to_str()).unwrap_or("ll");
    let kept = env::temp_dir().join(format!("prism_failed.{ext}"));
    let _ = fs::copy(ir, &kept);
    let text = String::from_utf8_lossy(stderr);
    let head: Vec<&str> = text.lines().take(8).collect();
    Error::Codegen(format!(
        "{tool} rejected generated IR, kept at {}:\n{}",
        kept.display(),
        head.join("\n")
    ))
}

#[cfg(feature = "native")]
fn cc_link(ir: &Path, out: &Path, cfg: &Config) -> Result<(), Error> {
    // Default to the exact compiler that built the interpreter's runtime + libm
    // (baked by build.rs), not a bare "clang": musl's transcendentals are not
    // correctly-rounded, so native and interpreter must use the identical toolchain
    // or their float results diverge by a ULP. `PRISM_CC` still overrides (e.g. the
    // sanitizer job), but then it is the caller's job to match the build.
    let cc = env::var("PRISM_CC").unwrap_or_else(|_| env!("PRISM_BUILD_CC").into());
    // Materialize the embedded runtime (the split C modules and their headers)
    // into a per-output directory and compile every source in one clang
    // invocation, so ThinLTO still inlines the runtime into the generated code.
    // The directory is unique to `out`, so concurrent builds do not collide.
    let rt_dir = out.with_extension("prism_rt.d");
    let sources = crate::codegen::rt::write_runtime(&rt_dir)?;
    // The vendored libm is linked as the one pre-built archive (compiled once by
    // build.rs, the same bytes the interpreter uses), never recompiled here: the
    // transcendentals are not correctly-rounded, so a second, differently-invoked
    // compile diverges by a ULP and breaks parity. It links after the objects that
    // reference it (`prism_libm.c`), so the archive resolves their `sin`/`atan`/...
    let libm_archive = crate::codegen::rt::write_libm_archive(&rt_dir)?;
    // Extra cc flags, whitespace-split. CI sets this to -fsanitize=undefined so
    // the corpus runs under UBSan and any new runtime UB aborts the program.
    let extra = env::var("PRISM_CC_FLAGS").unwrap_or_default();
    // ThinLTO stays on at every level: it is what inlines the C runtime into the
    // generated code. The `-O` level (default `-O2`) is the one user-facing knob;
    // a trailing `PRISM_CC_FLAGS` token still wins, since clang takes the last
    // `-O` it sees.
    let olevel = format!("-O{}", cfg.backend_opt);
    // Opt-in structural backstop: compile the runtime with its cell-validity
    // checks (`PRISM_RT_CHECKS`). Off by default so release builds and the parity
    // oracle stay zero-overhead and byte-identical.
    let rt_checks: &[&str] = if cfg.flags.rt_checks {
        &["-DPRISM_RT_DEBUG"]
    } else {
        &[]
    };
    // FP contraction is pinned off on every native compile: letting the C
    // compiler fuse `a*b+c` into an FMA on one platform and not another
    // diverges the last bit of float arithmetic, and byte-for-byte parity with
    // the interpreter (which never fuses) is the language's contract.
    let res = Command::new(&cc)
        .args([
            olevel.as_str(),
            "-flto=thin",
            "-ffp-contract=off",
            "-Wno-override-module",
        ])
        .args(rt_checks)
        .args(extra.split_whitespace())
        .arg(ir)
        .args(&sources)
        .arg(&libm_archive)
        .arg("-o")
        .arg(out)
        .output()
        .map_err(|e| Error::Codegen(format!("running {cc}: {e} (is clang installed?)")));
    let _ = fs::remove_dir_all(&rt_dir);
    let cc_out = res?;
    if cc_out.status.success() {
        if !cc_out.stderr.is_empty() {
            eprint!("{}", String::from_utf8_lossy(&cc_out.stderr));
        }
        Ok(())
    } else {
        Err(ir_failure(&cc, ir, &cc_out.stderr))
    }
}

/// # Errors
/// Fails on front-end errors or codegen failure.
#[cfg(feature = "native")]
pub fn emit_ir(src: &str) -> Result<String, Error> {
    let (_, core, ctors) = compiled(src, &default_roots(Path::new(".")), &Config::from_env())?;
    emit_llvm(&core, &ctors).map_err(Error::Codegen)
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

    let res = cc_link(&ll_file, out, cfg);
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
        Ok(c) => c,
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
        Ok((lowered, ctors, _)) => match emit_llvm(&reuse(&insert_rc(&lowered, &sigs)), &ctors) {
            Ok(ir) => section(&mut out, "llvm", strip_target(&ir).trim_end()),
            Err(e) => section(&mut out, "llvm", &format!("(skipped: {e})")),
        },
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

/// # Errors
/// Fails on front-end errors or an unknown phase name.
pub fn dump(phase: &str, src: &str) -> Result<String, Error> {
    dump_at(phase, src, Path::new("."))
}

/// Like [`dump`], resolving any module imports relative to `base`.
///
/// # Errors
/// Fails on front-end errors or an unknown phase name.
pub fn dump_at(phase: &str, src: &str, base: &Path) -> Result<String, Error> {
    dump_on(phase, src, &default_roots(base), &Config::from_env())
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
// fip/fbip annotation, and the borrow mask. The last two are load-bearing for
// codegen (the mask drives `insert_rc`, fip pins the loop lowering), so a change
// to either must change the hash even when the Core body is byte-identical.
fn hash_meta(checked: &Checked, sigs: &Sigs, fips: &Fips) -> BTreeMap<Sym, String> {
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

/// Like [`dump_at`], but against an explicit module search path.
///
/// # Errors
/// Fails on front-end errors or an unknown phase name.
pub fn dump_on(phase: &str, src: &str, roots: &[Root], cfg: &Config) -> Result<String, Error> {
    match phase {
        "tokens" => {
            let (t, _) = lex(src)?;
            Ok(t.iter()
                .map(|(_, t, _)| format!("{t:?}"))
                .collect::<Vec<_>>()
                .join(" "))
        }
        "ast" => Ok(format!("{:#?}", parse(src)?.program)),
        "types" => Ok(types_section(&check_on(src, roots)?)),
        "core" => {
            let (_, _, core) = frontend(src, roots, cfg)?;
            Ok(pp_core_pretty(&strip_prelude(core, &prelude_fn_names()?)))
        }
        "core-json" => {
            let (_, _, core) = frontend(src, roots, cfg)?;
            Ok(crate::core::core_to_json(&core))
        }
        "core-hash" => {
            let (program, checked, core) = elaborated(src, roots)?;
            let hashes = hash_program(
                &core,
                &hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program)),
            );
            let mut names: Vec<&Sym> = hashes.keys().collect();
            names.sort_by_key(|s| s.as_str());
            let mut out = String::new();
            for name in names {
                writeln!(
                    out,
                    "{}  {}",
                    &hashes[name][..crate::core::HASH_PREFIX_HEX],
                    name.as_str()
                )
                .unwrap();
            }
            Ok(out)
        }
        // Structural shape digests of the file's datatypes and effects (prelude
        // included, like `core-hash` shows prelude fns). One line per declaration.
        "shape" => {
            let (program, _, _) = frontend(src, roots, cfg)?;
            let shapes = crate::core::shape_digests(&program.types, &program.effects);
            let mut out = String::new();
            for (name, h) in &shapes {
                writeln!(out, "{}  {name}", &h[..crate::core::HASH_PREFIX_HEX]).unwrap();
            }
            Ok(out)
        }
        // Structural duplicates: definitions that hash identically are the same
        // behavior under different names (a user `fact` and the prelude
        // `factorial`, say). One line per group of clones, `<hash>  a, b, c`.
        "dupes" => {
            let (program, checked, core) = elaborated(src, roots)?;
            let hashes = hash_program(
                &core,
                &hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program)),
            );
            let mut by_hash: BTreeMap<&str, Vec<&Sym>> = BTreeMap::new();
            for (sym, h) in &hashes {
                by_hash.entry(h.as_str()).or_default().push(sym);
            }
            let mut groups: Vec<(&&str, &Vec<&Sym>)> =
                by_hash.iter().filter(|(_, v)| v.len() > 1).collect();
            groups.sort_by_key(|(_, v)| v.iter().map(|s| s.as_str()).min().unwrap_or(""));
            let mut out = String::new();
            for (h, members) in groups {
                let mut names: Vec<&str> = members.iter().map(|s| s.as_str()).collect();
                names.sort_unstable();
                writeln!(
                    out,
                    "{}  {}",
                    &h[..crate::core::HASH_PREFIX_HEX],
                    names.join(", ")
                )
                .unwrap();
            }
            if out.is_empty() {
                out.push_str("no structural duplicates\n");
            }
            Ok(out)
        }
        // The two-layer store shape as a read-only export, wrapped in the one wire
        // envelope: a header of the hash scheme tag, the kind (`def`,
        // this being the store's definition layer), and the contract digest (the
        // namespace's own Merkle root), plus the export layout version and the
        // producing compiler version, so a persisted export is self-describing
        // about its format and its content address from the first bytes. Each
        // definition carries its content hash, the anonymous layer (the direct
        // dependency hashes, names erased, which is what the hash actually commits
        // to), and the metadata layer (the human name and inferred type). Docs and
        // spans belong to the metadata layer too and join it when the on-disk
        // store lands.
        "namespace" => {
            let (program, checked, core) = elaborated(src, roots)?;
            let hashes = hash_program(
                &core,
                &hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program)),
            );
            let graph = DepGraph::of(&core);
            let types: BTreeMap<&str, String> = checked
                .decls
                .iter()
                .map(|d| (d.name.as_str(), d.ty.show()))
                .collect();
            let mut names: Vec<&Sym> = hashes.keys().collect();
            names.sort_by_key(|s| s.as_str());
            let entries: Vec<serde_json::Value> = names
                .iter()
                .map(|name| {
                    let mut deps: Vec<&str> = graph
                        .direct_deps(**name)
                        .iter()
                        .filter_map(|d| hashes.get(d).map(String::as_str))
                        .collect();
                    deps.sort_unstable();
                    serde_json::json!({
                        "hash": hashes[name],
                        "meta": { "name": name.as_str(), "type": types.get(name.as_str()) },
                        "anon": { "deps": deps },
                    })
                })
                .collect();
            // The one envelope header: scheme tag, kind, contract
            // digest, then the body. This export is the store's `def` layer, so
            // its kind is `def`; its contract digest is the namespace's own root,
            // a Merkle fold over the sorted `name -> content-hash` entries (the
            // same fold `stdlib_hash` uses), so the digest moves under any content
            // change and is checkable before the body is read.
            let contract = namespace_root_of(&hashes);
            let doc = serde_json::json!({
                "envelope": {
                    "scheme": crate::core::HASH_SCHEME,
                    "kind": WireKind::Def.tag(),
                    "contract": contract,
                    "format": NAMESPACE_FORMAT,
                    "compiler": env!("CARGO_PKG_VERSION"),
                },
                "defs": entries,
            });
            Ok(serde_json::to_string_pretty(&doc).unwrap_or_default())
        }
        // The whole standard library's fingerprint. Ignores `src`/`roots`: the
        // stdlib is embedded, so the file argument is only a CLI placeholder.
        "stdlib-hash" => {
            let h = stdlib_hash()?;
            let mut out = String::new();
            writeln!(out, "scheme    {}", h.scheme).unwrap();
            writeln!(out, "version   {}", h.version).unwrap();
            writeln!(out, "root      {}", h.root).unwrap();
            let mut defs: Vec<&Sym> = h.defs.keys().collect();
            defs.sort_by_key(|s| s.as_str());
            for name in defs {
                writeln!(
                    out,
                    "def   {}  {}",
                    &h.defs[name][..crate::core::HASH_PREFIX_HEX],
                    name.as_str()
                )
                .unwrap();
            }
            for (name, dg) in &h.shapes {
                writeln!(out, "shape {}  {name}", &dg[..crate::core::HASH_PREFIX_HEX]).unwrap();
            }
            for (name, dg) in &h.classes {
                writeln!(out, "class {}  {name}", &dg[..crate::core::HASH_PREFIX_HEX]).unwrap();
            }
            for (name, dg) in &h.instances {
                writeln!(out, "inst  {}  {name}", &dg[..crate::core::HASH_PREFIX_HEX]).unwrap();
            }
            Ok(out)
        }
        "fbip" => {
            let (program, _, core) = frontend(src, roots, cfg)?;
            let sigs = borrow_sigs(&program);
            Ok(pp_core_pretty(&reuse(&insert_rc(&core, &sigs))))
        }
        "lowered" => {
            let (_, lowered, _, _) = lowered_core(src, roots, cfg)?;
            Ok(pp_core_pretty(&lowered))
        }
        // The effect-lowering tier this program's handlers lower to (`pure`,
        // `evidence`, `state-fusion`, `local-partial`, `selective-free-monad`,
        // `whole-program-free-monad`). A pure cost classification, never
        // observable in output; `tests/perf_gate.rs` pins it per corpus program
        // so a silent fusion-to-free-monad collapse surfaces as a reviewable diff.
        "tier" => {
            let (_, checked, core) = frontend(src, roots, cfg)?;
            Ok(format!(
                "{}\n",
                crate::core::effect_strategy(
                    &core,
                    &checked.ctors,
                    &cfg.flags,
                    &checked.op_grades()
                )?
            ))
        }
        #[cfg(feature = "native")]
        "llvm" => {
            let (_, core, ctors) = compiled(src, roots, cfg)?;
            emit_llvm(&core, &ctors).map_err(Error::Codegen)
        }
        #[cfg(feature = "mlir")]
        "mlir" => {
            let (_, core, ctors) = compiled(src, roots, cfg)?;
            emit_mlir(&core, &ctors).map_err(Error::Codegen)
        }
        other => Err(Error::Codegen(format!("unknown phase {other}"))),
    }
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
    Ok(core.fns.into_iter().map(|f| f.name).collect())
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
pub fn diff_on(
    old_src: &str,
    new_src: &str,
    roots: &[Root],
    _cfg: &Config,
) -> Result<String, Error> {
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

    let short = |h: &str| h[..crate::core::HASH_PREFIX_HEX].to_string();
    let mut out = String::new();
    writeln!(
        out,
        "diff: {} changed, {} added, {} removed, {unchanged} unchanged",
        changed.len(),
        added.len(),
        removed.len(),
    )
    .unwrap();
    for (sym, oh, nh) in &changed {
        writeln!(out, "  ~ {}  {} -> {}", sym.as_str(), short(oh), short(nh)).unwrap();
    }
    for (sym, nh) in &added {
        writeln!(out, "  + {}  {}", sym.as_str(), short(nh)).unwrap();
    }
    for (sym, oh) in &removed {
        writeln!(out, "  - {}  {}", sym.as_str(), short(oh)).unwrap();
    }
    if cone.is_empty() {
        writeln!(out, "cone: 0 affected").unwrap();
    } else {
        // Sort by name: `cone` is a `BTreeSet<Sym>`, whose order is intern id, not
        // lexicographic, so a stable human listing must sort the strings.
        let mut names: Vec<&str> = cone.iter().map(|s| s.as_str()).collect();
        names.sort_unstable();
        writeln!(out, "cone: {} affected ({})", names.len(), names.join(", ")).unwrap();
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
    use super::{dump, EnvelopeHeader, WireKind, NAMESPACE_FORMAT};

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
