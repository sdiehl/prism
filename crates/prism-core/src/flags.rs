//! Dynamic compiler flags: the one place every environment-derived behavior knob
//! is read.
//!
//! Historically each toggle was read with a
//! `std::env::var` at its point of use, buried deep in the effect lowerer and the
//! optimizer, so the full set was undiscoverable and a flag could be sampled at an
//! arbitrary point in a compile. Instead the process environment is parsed exactly
//! once here (via [`DynFlags::from_env`]) and the resulting value is threaded down
//! into the passes that need it. A front end (the CLI, the REPL, a test) may build
//! a [`DynFlags`] however it likes and hand it in; nothing below the driver reads
//! the environment.
//!
//! Each field documents its env var, default, and effect. Booleans that gate a
//! shipping fast path default on (opt out with `=0`); debug/telemetry switches
//! default off (opt in by being present).
//!
//! This is the home for *compile-time behavior* knobs only. Two other `PRISM_*`
//! families live elsewhere by design: runtime knobs the running program observes
//! (read by the C runtime, mirrored by the interpreter), and the C-toolchain seam
//! (`PRISM_CC` / `PRISM_CC_FLAGS`, centralized in the native backend's
//! `codegen::rt`). The
//! env-knob audit (`tests/env_knobs.rs`) catalogues all three and fails if any
//! knob is read from an undocumented site.

use std::ffi::OsString;
use std::path::PathBuf;

use crate::core::{EffectStrategy, OptLevel, EFFECT_TIERS};

/// Sequential fallback when the host's parallelism cannot be queried.
const SEQUENTIAL_QUERY_THREADS: usize = 1;

/// Ceiling on the auto-detected query worker count. Each worker can hold a
/// live compiler subprocess (an SCC shard object compile) plus its inputs in
/// memory, so the default fan-out stays bounded on high-core machines. An
/// explicit override (env, CLI, or prism.toml) may exceed it.
const MAX_AUTO_QUERY_THREADS: usize = 8;

/// Default worker count for independent compiler queries: the host's available
/// parallelism, capped. Worker count is a pure cost decision; artifacts must be
/// byte-identical at any value, which `tests/native/compiler_cache.rs` enforces
/// by diffing sequential and parallel builds.
fn default_query_threads() -> usize {
    std::thread::available_parallelism().map_or(SEQUENTIAL_QUERY_THREADS, |threads| {
        threads.get().min(MAX_AUTO_QUERY_THREADS)
    })
}

/// The lowest rung of the effect-lowering cascade a compile is allowed to take.
///
/// Used by differential tests to force a costlier lowering without changing
/// program behavior. Each non-`auto` value names the cheapest admitted rung.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum EffectTier {
    /// The full cascade: every rung tried in cost order (the shipping default).
    #[default]
    Auto,
    /// Skip evidence fusion: state fusion is the first rung tried.
    StateFusion,
    /// Skip evidence and state fusion: local confinement is the first rung tried.
    LocalPartial,
    /// Skip every fusion rung: effects reify into the free monad, confined to
    /// handler regions where the plan finds them closed.
    FreeMonad,
    /// Skip the confinement too: the whole program runs in the monad. The
    /// costliest rung, and the only one legal for every program, which is why
    /// it is forceable while its selective sibling is not.
    WholeProgramFreeMonad,
}

impl EffectTier {
    /// Every position, for the tier-parity sweep and for diagnostics that list
    /// the accepted spellings.
    pub const ALL: [Self; 5] = [
        Self::Auto,
        Self::StateFusion,
        Self::LocalPartial,
        Self::FreeMonad,
        Self::WholeProgramFreeMonad,
    ];

    /// Parse a `PRISM_EFFECT_TIER` spelling.
    #[must_use]
    pub fn parse(s: &str) -> Option<Self> {
        let s = s.trim().to_ascii_lowercase();
        Self::ALL.into_iter().find(|tier| tier.label() == s)
    }

    /// Stable spelling used in artifact identity rows. Every position but
    /// `auto` is named by the rung it floors at, so the knob cannot drift from
    /// the ladder's own vocabulary.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self.floor() {
            None => "auto",
            Some(rung) => rung.label(),
        }
    }

    /// The cheapest rung this tier admits, or `None` for the full cascade.
    const fn floor(self) -> Option<EffectStrategy> {
        match self {
            Self::Auto => None,
            Self::StateFusion => Some(EffectStrategy::StateFusion),
            Self::LocalPartial => Some(EffectStrategy::LocalPartial),
            Self::FreeMonad => Some(EffectStrategy::SelectiveFreeMonad),
            Self::WholeProgramFreeMonad => Some(EffectStrategy::WholeProgramFreeMonad),
        }
    }

    /// Whether the cascade may take `rung`. Rungs cheaper than the floor are
    /// skipped; cost comes from the ladder's own `Ord`, which is total, so a
    /// rung can never be denied because a lookup failed to place it.
    #[must_use]
    pub fn admits(self, rung: EffectStrategy) -> bool {
        self.floor().is_none_or(|floor| rung >= floor)
    }
}

/// An experimental set of rungs the cascade skips even when the floor admits
/// them, forcing each affected program down to the next rung.
///
/// Unlike [`EffectTier`], this can remove one middle rung for measurements. The
/// default excludes nothing.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct RungExclude([bool; EffectStrategy::COUNT]);

impl RungExclude {
    /// A strategy's index is its position on the cost ladder, so the set never
    /// re-spells the ladder's order.
    fn index(rung: EffectStrategy) -> usize {
        EFFECT_TIERS
            .iter()
            .position(|&tier| tier == rung)
            .expect("every strategy sits on the cost ladder")
    }

    /// Whether `rung` is excluded.
    #[must_use]
    pub fn excludes(self, rung: EffectStrategy) -> bool {
        self.0[Self::index(rung)]
    }

    /// Parse a `PRISM_EFFECT_EXCLUDE` list: strategy [`label`](EffectStrategy::label)
    /// spellings separated by commas or whitespace (`state-fusion, local-partial`).
    /// An empty or unset value excludes nothing. A token that names no rung, or
    /// names one of the two terminals the knob cannot skip (see
    /// [`is_excludable`](EffectStrategy::is_excludable)), is ignored: the set only
    /// ever records an exclusion the cascade will actually honor, so the knob has
    /// no silently dropped middle ground.
    #[must_use]
    pub fn parse(s: &str) -> Self {
        let mut set = [false; EffectStrategy::COUNT];
        for tok in s
            .split([',', ' ', '\t'])
            .map(str::trim)
            .filter(|t| !t.is_empty())
        {
            if let Some(rung) = EFFECT_TIERS
                .iter()
                .copied()
                .find(|tier| tier.label() == tok && tier.is_excludable())
            {
                set[Self::index(rung)] = true;
            }
        }
        Self(set)
    }
}

/// Which external tool signs and verifies the package-identity-to-root index.
///
/// Signing is never done in-process: Prism shells to a ubiquitous system tool
/// behind one narrow seam, so no cryptographic dependency enters the compiler.
/// `Unsigned` is an explicit development escape hatch, loudly marked in output
/// and refused by `prism audit` unless the operator opts in.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum SignMode {
    /// `ssh-keygen -Y sign` / `-Y verify`: namespaced signatures over the index,
    /// present on any machine with OpenSSH (the shipping default).
    #[default]
    Ssh,
    /// `minisign -S` / `-V`: an acceptable alternative behind the same seam when
    /// it is installed.
    Minisign,
    /// No signature: the index is emitted in the clear and marked UNSIGNED. A dev
    /// convenience only; `prism audit` treats an unsigned index as a failure
    /// unless told otherwise.
    Unsigned,
}

impl SignMode {
    /// Parse a `PRISM_SIGN_MODE` spelling (`ssh`, `minisign`, `unsigned`).
    #[must_use]
    pub fn parse(s: &str) -> Option<Self> {
        match s.trim().to_ascii_lowercase().as_str() {
            "ssh" | "ssh-keygen" => Some(Self::Ssh),
            "minisign" => Some(Self::Minisign),
            "unsigned" | "none" | "dev" => Some(Self::Unsigned),
            _ => None,
        }
    }

    /// The human label shown in `publish`/`audit` output.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::Ssh => "ssh-keygen",
            Self::Minisign => "minisign",
            Self::Unsigned => "unsigned (dev)",
        }
    }
}

/// How loudly a redundant-definition analysis speaks.
///
/// These analyses find a definition that duplicates something the program already
/// has: two definitions elaborating to the same behavior hash (the content address
/// `dump dupes` reports), a reimplementation of a standard library function, or a
/// top-level name the prelude had already opened into scope. `Warn` surfaces each
/// finding as a diagnostic; `Strict` turns it into a hard compile error with a
/// declaration-family E-code; `Off` does no analysis, so an ordinary build pays
/// nothing. Each analysis picks its own default (clone-group detection is
/// [`Off`](Self::Off); stdlib reimplementation and prelude capture are
/// [`Warn`](Self::Warn)); the [`Default`] here is only the enum's own zero value.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum WarnDupes {
    /// No analysis.
    #[default]
    Off,
    /// Report each finding as a warning.
    Warn,
    /// Fail the compile on any finding, with a declaration-family E-code.
    Strict,
}

impl WarnDupes {
    /// Parse a `PRISM_WARN_DUPES` / `--warn-dupes` spelling.
    #[must_use]
    pub fn parse(s: &str) -> Option<Self> {
        match s.trim().to_ascii_lowercase().as_str() {
            "off" | "0" | "false" | "no" | "none" => Some(Self::Off),
            "warn" | "on" | "1" | "true" | "yes" => Some(Self::Warn),
            "strict" | "deny" | "error" => Some(Self::Strict),
            _ => None,
        }
    }

    /// Stable spelling for diagnostics and toml round-tripping.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::Warn => "warn",
            Self::Strict => "strict",
        }
    }

    /// Whether any duplicate analysis should run at all.
    #[must_use]
    pub const fn enabled(self) -> bool {
        !matches!(self, Self::Off)
    }
}

/// Every environment-tunable compiler behavior knob, resolved once.
///
/// [`Default`] is the shipping configuration (every fast path on, every debug
/// switch off); [`DynFlags::from_env`] overlays the process environment onto it.
///
/// This is deliberately a flat bag of independent on/off knobs (the whole point is
/// one discoverable list), not a state machine, so the many-bools lint does not
/// apply.
#[allow(clippy::struct_excessive_bools)]
#[derive(Clone, Debug)]
pub struct DynFlags {
    /// `PRISM_NATIVE_EFFECTS` (default on): drive eligible closed handlers with a
    /// self-recursive `{n}@region` loop so a parameter-passing scheduler runs in
    /// constant native stack, instead of a continuation thunk re-entering a
    /// mutually recursive driver.
    pub native_effects: bool,
    /// `PRISM_TRAMPOLINE` (default on): defer every stack-growing monadic hop of
    /// the whole-program free-monad fallback into an `EBounce` driven by one
    /// `prism_drive` loop, so a deferred-resume scheduler runs in constant stack.
    /// A behaviorally transparent rewrite whose fast path leaves same-arity tail
    /// loops native.
    pub trampoline: bool,
    /// `PRISM_CORE_LINT` (default off): run Core Lint between optimization passes,
    /// panicking (naming the pass) if one produces ill-formed Core.
    ///
    /// Mutually exclusive with the typed-SCC query cache: a cache hit returns an
    /// already-optimized SCC without replaying the passes, so there is nothing to
    /// lint between. Setting this therefore forces the uncached route, which is
    /// why it belongs on runs that already disable the cache (the whole-corpus
    /// optimizer-equivalence sweep, the example compile) and not on a whole test
    /// suite, where it would disable the cache under test.
    pub core_lint: bool,
    /// `PRISM_RT_CHECKS` (default off): compile the native C runtime with
    /// `-DPRISM_RT_DEBUG`, inserting a cheap validity check at every cell
    /// dereference (non-null, aligned, live refcount, in-bounds field). Off by
    /// default so release builds and the parity oracle stay byte-identical and
    /// zero-overhead; opt in for an always-available structural backstop where
    /// ASan/UBSan are unavailable.
    pub rt_checks: bool,
    /// `PRISM_NATIVE_KONT_FRAMES` (default off): ask the native link step to
    /// preserve frame pointers, unwind tables, and non-mandatory call frames for
    /// experimental native kont frame capture. This build-mode backstop makes
    /// return-PC capture less dependent on the platform optimizer's defaults.
    pub native_kont_frames: bool,
    /// `PRISM_DUMP_CORE` (default none): sink for the per-pass Core dump.
    /// `stdout`/`stderr` stream a banner plus the block; an off spelling (`0`,
    /// `false`, `off`, `no`, empty) disables the dump; any other value is a base
    /// directory of one file per pass.
    pub dump_core: Option<OsString>,
    /// `PRISM_OPT_STATS` (default off): dump per-pass rewrite tick counts to
    /// stderr after the pipeline runs.
    pub opt_stats: bool,
    /// `PRISM_COMPILER_STATS` (default off): print command-scoped compiler-query
    /// hit, miss, and write counts.
    pub compiler_stats: bool,
    /// `PRISM_EXPLAIN_CACHE` (default off): report the final and backend-IR
    /// compiler-query decisions after a build.
    pub explain_cache: bool,
    /// `PRISM_QUERY_THREADS` (default: the host's available parallelism, capped
    /// at 8): bounded worker count for independent compiler queries. Collection
    /// order remains deterministic.
    pub query_threads: usize,
    /// `PRISM_SCC_BACKEND` (default on): emit and link SCC-granular backend
    /// modules. Disabling it forces the whole-program backend oracle; selection
    /// is contractually unobservable and does not participate in artifact identity.
    pub scc_backend: bool,
    /// `PRISM_TIME_COMPILE` (default off): emit one structured timing row per
    /// compiler phase to stderr. The knob only records the intent; the CLI reads
    /// it and installs the actual `TimingSink` onto the top-level compile's
    /// `Config`, so an internal
    /// re-elaboration (which builds its own [`from_env`](Self::from_env) config)
    /// stays silent. Program stdout is unaffected; rows go only to stderr.
    pub time_compile: bool,
    /// `PRISM_QUIET` (default off): silence the rare compiler-internal
    /// matcher-drift signal (an elaborated clause shape changed) on stderr.
    pub quiet: bool,
    /// `PRISM_VERBOSE` / `--verbose` (default off): print the effect-lowering
    /// fusion-fallback warning (a computation reaches `main` unhandled, or a
    /// handler reifies its continuation, so operations reify instead of fusing)
    /// to stderr. Off by default so an ordinary build or docs run stays quiet;
    /// the same warning is always available as structured data through the
    /// library API.
    pub verbose: bool,
    /// `PRISM_MDBOOK_STRICT` (default off): make the mdbook preprocessor fail the
    /// build when a doc code block that should type-check does not, instead of
    /// only warning on stderr.
    pub mdbook_strict: bool,
    /// `PRISM_OPT_LEVEL` (default `O1`): the Core-to-Core optimization level a
    /// library entry point uses when the CLI does not pass an explicit `-O`. The
    /// CLI overrides the derived `Config::opt`; this is the
    /// env-supplied seed.
    pub opt_level: OptLevel,
    /// `PRISM_BACKEND_OPT` (default `"2"`): the LLVM-backend `-O` level a library
    /// entry point hands `cc` when the CLI does not pass `--backend-opt`. An
    /// invalid value is reported once here and falls back to the default.
    pub backend_opt: BackendOpt,
    /// `PRISM_DIRECT_OBJECT` (default off): optimize and lower emitted LLVM
    /// bitcode to native objects inside Prism, omitting `ThinLTO` and retaining
    /// only the final platform `cc` link. This is a development-latency mode;
    /// release builds retain the optimizing `ThinLTO` path by default.
    pub direct_object: bool,
    /// `PRISM_NO_SPECIALIZE` (default off): turn off the `Specialize` Core pass.
    /// Presence-flagged, resolved into `Config::disabled`.
    pub no_specialize: bool,
    /// `PRISM_NO_HO_SPEC` (default off): turn off the `HoSpecialize` Core pass
    /// (higher-order specialization on constant callable arguments). Kept a
    /// separate toggle from `no_specialize` so a measurement can attribute a
    /// change to dictionary specialization or to higher-order specialization
    /// individually. Presence-flagged, resolved into `Config::disabled`.
    pub no_ho_spec: bool,
    /// `PRISM_FUSE` (default off): force the whole-program stream-fusion pass
    /// (`core/opt/fuse`) to run first in the pre-lowering stage, collapsing
    /// recognized pull-`Sequence` pipelines into allocation-free loops. Off by
    /// default because `-O2` already runs the pass; the knob only adds it at the
    /// lower levels, and `--no-fuse` removes it either way. A fused loop is a
    /// lowering tier, so the output is byte-identical with fusion on or off:
    /// `tests/native/fuse_parity.rs` diffs a fuse-on native build against the
    /// interpreter, and the optimizer-equivalence sweep runs `-O2` against
    /// `--no-fuse` over the whole corpus.
    pub fuse: bool,
    /// `PRISM_BORROW_INFER` (default on): infer per-parameter borrow masks for
    /// provably pure functions, so a read-only argument is loaned across the
    /// call instead of threading a retain and release pair. Augments the
    /// declared `borrow` annotations at the reference-count insertion boundary
    /// only; the inferred masks are a pure function of the checked source, so
    /// they are a cost decision like a lowering tier, never part of a
    /// definition's identity, and the output must not reveal the setting. The
    /// inserted reference-count operations do move the linked bytes, so like
    /// the effect tier the flag joins the artifact identity that keys
    /// byte-level artifact caches. `PRISM_BORROW_INFER=0` disables inference,
    /// leaving only the declared annotations.
    pub borrow_infer: bool,
    /// `PRISM_SCHEDULER` (default cooperative/FIFO): which shipped cooperative
    /// scheduler `run_cooperative` binds to when the CLI does not pass
    /// `--scheduler`.
    pub scheduler: Scheduler,
    /// `PRISM_EFFECT_TIER` (default `auto`): the lowest effect-lowering rung the
    /// cascade may take, one position per rung (see [`EffectTier`]). Capping the
    /// cascade is contractually unobservable; the tier-parity oracle forces
    /// every rung and diffs them against the interpreter. An invalid spelling is
    /// reported once and falls back to `auto` (the tier-parity test
    /// independently asserts the forcing engaged, so a typo cannot make the
    /// oracle silently vacuous).
    pub effect_tier: EffectTier,
    /// `PRISM_EFFECT_EXCLUDE` (default none): experimental per-rung exclusion set
    /// (see [`RungExclude`]). Skips the named fusion rungs even when the floor
    /// admits them, so one engine's marginal value can be measured by forcing its
    /// programs onto the next rung. Apparatus, not a supported surface; empty by
    /// default and, like the floor, unobservable in output.
    pub effect_exclude: RungExclude,
    /// `PRISM_ERASURES` (default on): run the var and loop-control erasures that
    /// precede the cascade. Off leaves those constructs for the cascade to lower
    /// as ordinary effects. Orthogonal to [`DynFlags::effect_tier`], so a forced
    /// run can move the erasures and the floor one at a time; like the floor,
    /// turning it off is a cost decision the output must not reveal.
    pub erasures: bool,
    /// `PRISM_COMPILER_CACHE` (default on): reuse byte-identical compiler
    /// artifacts from the content-addressed query store. Set to `0` for the
    /// from-scratch oracle or when investigating invalidation.
    pub compiler_cache: bool,
    /// `PRISM_STORE` (default off): after a successful compile, commit the
    /// program's definitions into the on-disk content-addressed store. The store
    /// is a cache, never required for correctness, so it is opt-in and does
    /// not perturb the oracles when off.
    pub store: bool,
    /// `PRISM_STORE_PATH` (default none): override the store root. Absent falls
    /// back to a user-wide cache directory, then `target/prism-store`; see the
    /// store's `disk::resolve_store_path`.
    pub store_path: Option<PathBuf>,
    /// `PRISM_TOOL_PACKAGES_ROOT` (default none): load compiler-owned Prism tool
    /// packages from this `packages/` directory while developing them. The
    /// installed default remains the sources embedded in the binary. This is an
    /// explicit developer input, never inferred from the checked project's
    /// manifest, so a project cannot select the checker or linter that judges it.
    pub tool_packages_root: Option<PathBuf>,
    /// `PRISM_SOLVER_TIMEOUT_MS` (default none): the per-obligation wall-clock
    /// budget `prism verify` gives an external solver before it kills the process
    /// and records an infrastructure timeout. Physical policy, never part of the
    /// logical query; absent uses the adapter's built-in default.
    pub solver_timeout_ms: Option<u64>,
    /// `PRISM_SIGN_MODE` (default `ssh`): which external tool signs and verifies
    /// the package-identity-to-root index. See [`SignMode`].
    pub sign_mode: SignMode,
    /// `PRISM_SIGN_KEY` (default none): the signing key handed to the signer
    /// (`ssh-keygen -Y sign -f <key>`, or `minisign -s <key>`). Required to
    /// `publish` a signed index; absent forces the unsigned path.
    pub sign_key: Option<PathBuf>,
    /// `PRISM_SIGN_IDENTITY` (default none): the signer principal recorded in the
    /// signature namespace (`ssh-keygen -Y sign -I`/`-n`) and matched on verify.
    pub sign_identity: Option<String>,
    /// `PRISM_SIGN_ALLOWED_SIGNERS` (default none): the `allowed_signers` file
    /// `ssh-keygen -Y verify` checks the index signature against (or a minisign
    /// public key). Required to verify a signed index during `audit`.
    pub sign_allowed_signers: Option<PathBuf>,
    /// `PRISM_WARN_DUPES` (default `off`): whether to flag a *clone group* of the
    /// user's own definitions that share one behavior hash (a copy-pasted helper).
    /// `warn` reports each group; `strict` fails the build. Off by default because a
    /// deliberate alias is common and harmless; opt in to hunt copies.
    /// A diagnostics-only knob: it never perturbs a content hash or an artifact.
    pub warn_dupes: WarnDupes,
    /// `PRISM_WARN_STDLIB_DUPES` (default `warn`): whether to flag a user definition
    /// that reimplements a standard-library function's behavior hash, naming the
    /// library function to call instead. On by default (a reimplementation is
    /// almost always an oversight); `strict` escalates it to a hard error, `off`
    /// silences it. Structurally inert when compiling the standard library itself, a
    /// definition that already *is* the named library function is never flagged. A
    /// diagnostics-only knob: it never perturbs a content hash or an artifact.
    pub warn_stdlib_dupes: WarnDupes,
    /// `PRISM_WARN_PRELUDE_CAPTURE` (default `warn`): whether to flag a top-level
    /// definition whose name the prelude had already opened into unqualified scope,
    /// naming the library symbol it displaces. On by default (the capture is silent
    /// otherwise, and it redirects every unqualified use in the file); `strict`
    /// escalates it to a hard error, `off` silences it. A diagnostics-only knob: it
    /// never perturbs a content hash or an artifact, and the name still resolves to
    /// the user's definition either way.
    pub warn_prelude_capture: WarnDupes,
}

impl Default for DynFlags {
    fn default() -> Self {
        Self {
            native_effects: true,
            trampoline: true,
            core_lint: false,
            rt_checks: false,
            native_kont_frames: false,
            dump_core: None,
            opt_stats: false,
            compiler_stats: false,
            explain_cache: false,
            query_threads: default_query_threads(),
            scc_backend: true,
            time_compile: false,
            quiet: false,
            verbose: false,
            mdbook_strict: false,
            opt_level: OptLevel::default(),
            backend_opt: BackendOpt::default(),
            direct_object: false,
            no_specialize: false,
            no_ho_spec: false,
            fuse: false,
            borrow_infer: true,
            scheduler: Scheduler::default(),
            effect_tier: EffectTier::default(),
            effect_exclude: RungExclude::default(),
            erasures: true,
            compiler_cache: true,
            store: false,
            store_path: None,
            tool_packages_root: None,
            solver_timeout_ms: None,
            sign_mode: SignMode::default(),
            sign_key: None,
            sign_identity: None,
            sign_allowed_signers: None,
            warn_dupes: WarnDupes::Off,
            warn_stdlib_dupes: WarnDupes::Warn,
            warn_prelude_capture: WarnDupes::Warn,
        }
    }
}

impl DynFlags {
    /// Whether the effect cascade may take `rung`: the floor
    /// ([`effect_tier`](Self::effect_tier)) admits it and the experimental
    /// exclusion set ([`effect_exclude`](Self::effect_exclude)) does not remove
    /// it. The cascade gates every middle rung through here so the two knobs
    /// compose in one place and default to plain [`EffectTier::admits`].
    #[must_use]
    pub fn rung_enabled(&self, rung: EffectStrategy) -> bool {
        self.effect_tier.admits(rung) && !self.effect_exclude.excludes(rung)
    }

    /// Parse the process environment into a [`DynFlags`], starting from
    /// [`Default`]. This is the single site that reads the environment for these
    /// knobs; call it once at process start and thread the result down.
    #[must_use]
    pub fn from_env() -> Self {
        Self::from_env_over(&Self::default())
    }

    /// Overlay the process environment onto `base`: each knob keeps `base`'s value
    /// unless its env var is set, in which case the env value wins. This is what
    /// lets a lower-precedence source (a project's `prism.toml`) feed `base` while
    /// the environment still overrides it. [`from_env`](Self::from_env) is this
    /// over [`Default`], so a bare env read is unchanged.
    ///
    /// Still the single site that reads the environment for these knobs.
    #[must_use]
    pub fn from_env_over(base: &Self) -> Self {
        Self {
            native_effects: env_bool("PRISM_NATIVE_EFFECTS", base.native_effects),
            trampoline: env_bool("PRISM_TRAMPOLINE", base.trampoline),
            core_lint: base.core_lint || env_present("PRISM_CORE_LINT"),
            rt_checks: base.rt_checks || env_present("PRISM_RT_CHECKS"),
            native_kont_frames: base.native_kont_frames || env_present("PRISM_NATIVE_KONT_FRAMES"),
            dump_core: std::env::var_os("PRISM_DUMP_CORE")
                .map_or_else(|| base.dump_core.clone(), dump_sink),
            opt_stats: base.opt_stats || env_present("PRISM_OPT_STATS"),
            compiler_stats: base.compiler_stats || env_present("PRISM_COMPILER_STATS"),
            explain_cache: base.explain_cache || env_present("PRISM_EXPLAIN_CACHE"),
            query_threads: query_threads_from_env(base.query_threads),
            scc_backend: env_bool("PRISM_SCC_BACKEND", base.scc_backend),
            time_compile: env_bool("PRISM_TIME_COMPILE", base.time_compile),
            quiet: base.quiet || env_present("PRISM_QUIET"),
            verbose: base.verbose || env_present("PRISM_VERBOSE"),
            mdbook_strict: base.mdbook_strict || env_present("PRISM_MDBOOK_STRICT"),
            opt_level: std::env::var("PRISM_OPT_LEVEL")
                .ok()
                .and_then(|s| OptLevel::parse(&s))
                .unwrap_or(base.opt_level),
            backend_opt: backend_opt_from_env(base.backend_opt),
            direct_object: env_bool("PRISM_DIRECT_OBJECT", base.direct_object),
            no_specialize: base.no_specialize || env_present("PRISM_NO_SPECIALIZE"),
            no_ho_spec: base.no_ho_spec || env_present("PRISM_NO_HO_SPEC"),
            fuse: env_bool("PRISM_FUSE", base.fuse),
            borrow_infer: env_bool("PRISM_BORROW_INFER", base.borrow_infer),
            scheduler: std::env::var("PRISM_SCHEDULER")
                .ok()
                .and_then(|s| Scheduler::parse(&s))
                .unwrap_or(base.scheduler),
            effect_tier: effect_tier_from_env(base.effect_tier),
            effect_exclude: std::env::var("PRISM_EFFECT_EXCLUDE")
                .map_or(base.effect_exclude, |s| RungExclude::parse(&s)),
            erasures: env_bool("PRISM_ERASURES", base.erasures),
            compiler_cache: env_bool("PRISM_COMPILER_CACHE", base.compiler_cache),
            store: base.store || env_present("PRISM_STORE"),
            store_path: std::env::var_os("PRISM_STORE_PATH")
                .map(PathBuf::from)
                .or_else(|| base.store_path.clone()),
            tool_packages_root: std::env::var_os("PRISM_TOOL_PACKAGES_ROOT")
                .map(PathBuf::from)
                .or_else(|| base.tool_packages_root.clone()),
            solver_timeout_ms: std::env::var("PRISM_SOLVER_TIMEOUT_MS")
                .ok()
                .and_then(|s| s.trim().parse().ok())
                .or(base.solver_timeout_ms),
            sign_mode: sign_mode_from_env(base.sign_mode),
            sign_key: std::env::var_os("PRISM_SIGN_KEY")
                .map(PathBuf::from)
                .or_else(|| base.sign_key.clone()),
            sign_identity: std::env::var("PRISM_SIGN_IDENTITY")
                .ok()
                .or_else(|| base.sign_identity.clone()),
            sign_allowed_signers: std::env::var_os("PRISM_SIGN_ALLOWED_SIGNERS")
                .map(PathBuf::from)
                .or_else(|| base.sign_allowed_signers.clone()),
            warn_dupes: warn_dupes_from_env("PRISM_WARN_DUPES", base.warn_dupes),
            warn_stdlib_dupes: warn_dupes_from_env(
                "PRISM_WARN_STDLIB_DUPES",
                base.warn_stdlib_dupes,
            ),
            warn_prelude_capture: warn_dupes_from_env(
                "PRISM_WARN_PRELUDE_CAPTURE",
                base.warn_prelude_capture,
            ),
        }
    }

    /// Overlay a project manifest's `[flags]` table onto these flags.
    ///
    /// The single home mapping a flag's stable kebab-case name to its field, shared
    /// by the manifest surface. An unknown key or an ill-typed value is an error,
    /// so a typo cannot silently drop a setting. Values match the CLI/env spellings
    /// (`opt-level = "2"`, `warn-dupes = "strict"`, `query-threads = 4`).
    ///
    /// # Errors
    /// Fails on an unknown flag name or a value of the wrong type.
    #[cfg(feature = "native")]
    pub fn apply_toml(&mut self, table: &toml::Table) -> Result<(), String> {
        for (key, val) in table {
            self.apply_toml_entry(key, val)?;
        }
        Ok(())
    }

    #[cfg(feature = "native")]
    fn apply_toml_entry(&mut self, key: &str, val: &toml::Value) -> Result<(), String> {
        match key {
            "native-effects" => self.native_effects = toml_bool(key, val)?,
            "trampoline" => self.trampoline = toml_bool(key, val)?,
            "core-lint" => self.core_lint = toml_bool(key, val)?,
            "rt-checks" => self.rt_checks = toml_bool(key, val)?,
            "native-kont-frames" => self.native_kont_frames = toml_bool(key, val)?,
            "opt-stats" => self.opt_stats = toml_bool(key, val)?,
            "compiler-stats" => self.compiler_stats = toml_bool(key, val)?,
            "explain-cache" => self.explain_cache = toml_bool(key, val)?,
            "scc-backend" => self.scc_backend = toml_bool(key, val)?,
            "time-compile" => self.time_compile = toml_bool(key, val)?,
            "quiet" => self.quiet = toml_bool(key, val)?,
            "verbose" => self.verbose = toml_bool(key, val)?,
            "no-specialize" => self.no_specialize = toml_bool(key, val)?,
            "no-ho-spec" => self.no_ho_spec = toml_bool(key, val)?,
            "fuse" => self.fuse = toml_bool(key, val)?,
            "borrow-infer" => self.borrow_infer = toml_bool(key, val)?,
            "compiler-cache" => self.compiler_cache = toml_bool(key, val)?,
            "store" => self.store = toml_bool(key, val)?,
            "query-threads" => self.query_threads = toml_pos_int(key, val)?,
            "opt-level" => self.opt_level = toml_parsed(key, val, OptLevel::parse)?,
            "backend-opt" => self.backend_opt = toml_parsed(key, val, BackendOpt::parse)?,
            "direct-object" => self.direct_object = toml_bool(key, val)?,
            "scheduler" => self.scheduler = toml_parsed(key, val, Scheduler::parse)?,
            "effect-tier" => self.effect_tier = toml_parsed(key, val, EffectTier::parse)?,
            "erasures" => self.erasures = toml_bool(key, val)?,
            "sign-mode" => self.sign_mode = toml_parsed(key, val, SignMode::parse)?,
            "warn-dupes" => self.warn_dupes = toml_parsed(key, val, WarnDupes::parse)?,
            "warn-stdlib-dupes" => {
                self.warn_stdlib_dupes = toml_parsed(key, val, WarnDupes::parse)?;
            }
            "warn-prelude-capture" => {
                self.warn_prelude_capture = toml_parsed(key, val, WarnDupes::parse)?;
            }
            "dump-core" => self.dump_core = dump_sink(toml_string(key, val)?.into()),
            "store-path" => self.store_path = Some(PathBuf::from(toml_string(key, val)?)),
            "solver-timeout-ms" => self.solver_timeout_ms = Some(toml_pos_int(key, val)? as u64),
            "sign-key" => self.sign_key = Some(PathBuf::from(toml_string(key, val)?)),
            "sign-identity" => self.sign_identity = Some(toml_string(key, val)?),
            "sign-allowed-signers" => {
                self.sign_allowed_signers = Some(PathBuf::from(toml_string(key, val)?));
            }
            _ => return Err(format!("prism.toml: unknown flag `{key}` in [flags]")),
        }
        Ok(())
    }
}

#[cfg(feature = "native")]
fn toml_bool(key: &str, val: &toml::Value) -> Result<bool, String> {
    val.as_bool()
        .ok_or_else(|| format!("prism.toml: flag `{key}` must be a boolean"))
}

#[cfg(feature = "native")]
fn toml_pos_int(key: &str, val: &toml::Value) -> Result<usize, String> {
    val.as_integer()
        .and_then(|n| usize::try_from(n).ok())
        .filter(|n| *n > 0)
        .ok_or_else(|| format!("prism.toml: flag `{key}` must be a positive integer"))
}

#[cfg(feature = "native")]
fn toml_string(key: &str, val: &toml::Value) -> Result<String, String> {
    val.as_str()
        .map(str::to_string)
        .ok_or_else(|| format!("prism.toml: flag `{key}` must be a string"))
}

#[cfg(feature = "native")]
fn toml_parsed<T>(
    key: &str,
    val: &toml::Value,
    parse: impl Fn(&str) -> Option<T>,
) -> Result<T, String> {
    let s = toml_string(key, val)?;
    parse(&s).ok_or_else(|| format!("prism.toml: invalid value for flag `{key}`: `{s}`"))
}

fn query_threads_from_env(base: usize) -> usize {
    std::env::var("PRISM_QUERY_THREADS").map_or(base, |value| {
        value.parse::<usize>().ok().filter(|n| *n > 0).unwrap_or_else(|| {
            eprintln!(
                "ignoring invalid PRISM_QUERY_THREADS={value:?} (expected a positive integer); using {base}"
            );
            base
        })
    })
}

// The signing seam from `PRISM_SIGN_MODE`. An unrecognized value is reported once
// and falls back to `base` rather than silently signing nothing.
fn sign_mode_from_env(base: SignMode) -> SignMode {
    std::env::var("PRISM_SIGN_MODE").map_or(base, |s| {
        SignMode::parse(&s).unwrap_or_else(|| {
            eprintln!(
                "ignoring invalid PRISM_SIGN_MODE={s:?} (expected ssh, minisign, unsigned); using {}",
                base.label()
            );
            base
        })
    })
}

// The accepted spellings of a knob, for the diagnostic an invalid value prints.
fn spellings(labels: impl IntoIterator<Item = &'static str>) -> String {
    labels.into_iter().collect::<Vec<_>>().join(", ")
}

// The effect-tier cap from `PRISM_EFFECT_TIER`. An unrecognized value is
// reported once and falls back to `base` rather than silently forcing (or
// silently not forcing) a tier.
fn effect_tier_from_env(base: EffectTier) -> EffectTier {
    std::env::var("PRISM_EFFECT_TIER").map_or(base, |s| {
        EffectTier::parse(&s).unwrap_or_else(|| {
            eprintln!(
                "ignoring invalid PRISM_EFFECT_TIER={s:?} (expected {}); using {}",
                spellings(EffectTier::ALL.map(EffectTier::label)),
                base.label()
            );
            base
        })
    })
}

// The LLVM-backend `-O` level from `PRISM_BACKEND_OPT`, validated against the
// levels clang accepts. An out-of-range value is reported once and falls back to
// `base` rather than reaching `cc`.
fn backend_opt_from_env(base: BackendOpt) -> BackendOpt {
    let Ok(s) = std::env::var("PRISM_BACKEND_OPT") else {
        return base;
    };
    BackendOpt::parse(&s).unwrap_or_else(|| {
        eprintln!(
            "ignoring invalid PRISM_BACKEND_OPT={s:?} (expected {}); using {}",
            BackendOpt::levels(),
            base.as_str()
        );
        base
    })
}

// A duplicate-detection severity from `var` (`PRISM_WARN_DUPES` for clone groups,
// `PRISM_WARN_STDLIB_DUPES` for stdlib reimplementations). An unrecognized value
// is reported once and falls back to `base`.
fn warn_dupes_from_env(var: &str, base: WarnDupes) -> WarnDupes {
    std::env::var(var).map_or(base, |s| {
        WarnDupes::parse(&s).unwrap_or_else(|| {
            eprintln!(
                "ignoring invalid {var}={s:?} (expected off, warn, strict); using {}",
                base.label()
            );
            base
        })
    })
}

// The spellings that switch a knob off, in one place so `NAME=0` means the same
// thing at every knob that can be switched off. Accepting the word spellings
// avoids the footgun where `NAME=false` reads as enabled on a soundness-relevant
// toggle, and accepting the empty string avoids `NAME=` reading as enabled.
const ENV_OFF: [&str; 5] = ["0", "false", "off", "no", ""];

// Whether a raw knob value is one of the off spellings (trimmed, case-insensitive).
fn env_off(value: &str) -> bool {
    ENV_OFF.contains(&value.trim().to_ascii_lowercase().as_str())
}

// An opt-out boolean flag: absent takes `default`; an off spelling is false,
// anything else true.
fn env_bool(name: &str, default: bool) -> bool {
    std::env::var(name).map_or(default, |v| !env_off(&v))
}

// The Core-dump sink from a raw knob value. An off spelling disables the dump
// instead of naming a base directory called `0`; a value that is not valid UTF-8
// cannot be an off spelling and is kept as a path.
fn dump_sink(value: OsString) -> Option<OsString> {
    match value.to_str() {
        Some(text) if env_off(text) => None,
        _ => Some(value),
    }
}

// A presence flag: any value (even empty) is true, absent is false.
fn env_present(name: &str) -> bool {
    std::env::var_os(name).is_some()
}

#[cfg(all(test, feature = "native"))]
mod tests {
    use std::ffi::OsString;

    use super::{dump_sink, DynFlags, WarnDupes};
    use crate::core::OptLevel;

    fn table(text: &str) -> toml::Table {
        toml::from_str(text).expect("valid toml")
    }

    #[test]
    fn toml_flags_layer_onto_defaults() {
        let mut flags = DynFlags::default();
        flags
            .apply_toml(&table(
                "warn-dupes = \"strict\"\nquery-threads = 4\nopt-level = \"0\"\nfuse = true",
            ))
            .expect("known flags apply");
        assert_eq!(flags.warn_dupes, WarnDupes::Strict);
        assert_eq!(flags.query_threads, 4);
        assert_eq!(flags.opt_level, OptLevel::O0);
        assert!(flags.fuse);
    }

    #[test]
    fn an_off_spelling_disables_the_core_dump_instead_of_naming_a_directory() {
        // The natural way to switch the knob off must not dump Core into `./0/`.
        for off in ["0", "false", "OFF", " no ", ""] {
            assert_eq!(dump_sink(off.into()), None, "{off:?} should disable");
        }
        assert_eq!(
            dump_sink("stdout".into()),
            Some(OsString::from("stdout")),
            "a real sink survives"
        );
    }

    #[test]
    fn unknown_toml_flag_is_rejected() {
        assert!(DynFlags::default()
            .apply_toml(&table("nonesuch = true"))
            .is_err());
    }

    #[test]
    fn direct_object_is_opt_in_and_manifest_settable() {
        let mut flags = DynFlags::default();
        assert!(!flags.direct_object);
        flags
            .apply_toml(&table("direct-object = true"))
            .expect("known direct-object flag applies");
        assert!(flags.direct_object);
    }

    #[test]
    fn illtyped_and_out_of_domain_toml_values_are_rejected() {
        // Wrong type, and a spelling outside the value set.
        assert!(DynFlags::default()
            .apply_toml(&table("warn-dupes = 3"))
            .is_err());
        assert!(DynFlags::default()
            .apply_toml(&table("warn-dupes = \"loud\""))
            .is_err());
        assert!(DynFlags::default()
            .apply_toml(&table("query-threads = 0"))
            .is_err());
    }

    #[test]
    fn cli_style_override_wins_last() {
        // The precedence main() applies: toml seeds the base, the environment
        // overlays it, and the explicit CLI value wins last regardless.
        let mut base = DynFlags::default();
        base.apply_toml(&table("warn-dupes = \"warn\"")).unwrap();
        let mut flags = DynFlags::from_env_over(&base);
        flags.warn_dupes = WarnDupes::Strict;
        assert_eq!(flags.warn_dupes, WarnDupes::Strict);
    }

    #[test]
    fn toml_shows_through_when_env_is_silent() {
        // env-over-toml: with the knob's env var unset, the toml/base value stands.
        if std::env::var_os("PRISM_WARN_DUPES").is_some() {
            return;
        }
        let base = DynFlags {
            warn_dupes: WarnDupes::Strict,
            ..DynFlags::default()
        };
        assert_eq!(DynFlags::from_env_over(&base).warn_dupes, WarnDupes::Strict);
    }

    #[test]
    fn stdlib_dupe_warning_is_on_by_default_and_independently_settable() {
        // The stdlib-reimplementation warning ships on; the own-clone warning ships
        // off. They are distinct knobs and toml sets each without touching the other.
        let flags = DynFlags::default();
        assert_eq!(flags.warn_stdlib_dupes, WarnDupes::Warn);
        assert_eq!(flags.warn_dupes, WarnDupes::Off);

        let mut flags = DynFlags::default();
        flags
            .apply_toml(&table(
                "warn-stdlib-dupes = \"strict\"\nwarn-dupes = \"warn\"",
            ))
            .expect("known flags apply");
        assert_eq!(flags.warn_stdlib_dupes, WarnDupes::Strict);
        assert_eq!(flags.warn_dupes, WarnDupes::Warn);
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
    pub const fn retarget(self) -> Option<&'static str> {
        match self {
            Self::Cooperative => None,
            Self::Lifo => Some(prism_syntax::names::RUN_LIFO),
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

/// A backend optimization level clang accepts via `-O`.
///
/// Parsed representation shared by the `--backend-opt` flag and the
/// `PRISM_BACKEND_OPT` env knob. An invalid level is unrepresentable; every
/// spelling flows through [`BackendOpt::as_str`], so the `-O` argument handed to
/// `cc` and the artifact-identity label can never drift apart or off the set.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum BackendOpt {
    O0,
    O1,
    #[default]
    O2,
    O3,
    Os,
    Oz,
}

impl BackendOpt {
    /// Every level in canonical order: the value set `--backend-opt` accepts.
    pub const ALL: [Self; 6] = [Self::O0, Self::O1, Self::O2, Self::O3, Self::Os, Self::Oz];

    /// The clang `-O` suffix. The single spelling used for both the `cc` argument
    /// and the artifact-identity label; kept byte-stable so hashes never move.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::O0 => "0",
            Self::O1 => "1",
            Self::O2 => "2",
            Self::O3 => "3",
            Self::Os => "s",
            Self::Oz => "z",
        }
    }

    /// The level named by `s`, or `None` for a value clang does not accept. Both
    /// entry paths (`--backend-opt`, `PRISM_BACKEND_OPT`) parse through here so a
    /// bad level never reaches `cc`.
    #[must_use]
    pub fn parse(s: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|o| o.as_str() == s)
    }

    /// The accepted levels as a comma-separated list, for diagnostics.
    #[must_use]
    pub fn levels() -> String {
        Self::ALL
            .iter()
            .map(|o| o.as_str())
            .collect::<Vec<_>>()
            .join(", ")
    }
}
