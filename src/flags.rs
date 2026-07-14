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

use std::ffi::OsString;
use std::path::PathBuf;

use crate::core::OptLevel;
use crate::driver::{BackendOpt, Scheduler};

const DEFAULT_QUERY_THREADS: usize = 1;

/// The lowest rung of the effect-lowering cascade a compile is allowed to take.
///
/// The cascade (`core/effect_lower`) is a cost-decreasing ladder: var/loop
/// erasure, evidence fusion, state fusion, local confinement, free monad. Tier
/// selection is contractually unobservable, so capping the ladder must never
/// change a program's output; this knob exists precisely to enforce that, by
/// letting a differential oracle (`tests/tier_parity.rs`) run one program on two
/// tiers and diff the results. It is a test/debug instrument, not a user-facing
/// performance switch.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum EffectTier {
    /// The full cascade: every rung tried in cost order (the shipping default).
    #[default]
    Auto,
    /// Skip evidence fusion: state fusion is the first rung tried.
    State,
    /// Skip var/loop-control erasure and every fusion rung: all effects reify
    /// into the free monad (the slowest, most general lowering).
    FreeMonad,
}

impl EffectTier {
    /// Parse a `PRISM_EFFECT_TIER` spelling (`auto`, `state`, `free-monad`).
    #[must_use]
    pub fn parse(s: &str) -> Option<Self> {
        match s.trim().to_ascii_lowercase().as_str() {
            "auto" => Some(Self::Auto),
            "state" => Some(Self::State),
            "free-monad" => Some(Self::FreeMonad),
            _ => None,
        }
    }

    /// Stable spelling used in artifact identity rows.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::Auto => "auto",
            Self::State => "state",
            Self::FreeMonad => "free-monad",
        }
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
    /// experimental native kont frame capture. This is not native resume; it is
    /// the build-mode backstop that makes return-PC capture less dependent on the
    /// platform optimizer's defaults.
    pub native_kont_frames: bool,
    /// `PRISM_DUMP_CORE` (default none): sink for the per-pass Core dump.
    /// `stdout`/`stderr` stream a banner plus the block; any other value is a base
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
    /// `PRISM_QUERY_THREADS` (default 1): bounded worker count for independent
    /// compiler queries. Collection order remains deterministic.
    pub query_threads: usize,
    /// `PRISM_SCC_BACKEND` (default on): emit and link SCC-granular backend
    /// modules. Disabling it forces the whole-program backend oracle; selection
    /// is contractually unobservable and does not participate in artifact identity.
    pub scc_backend: bool,
    /// `PRISM_TIME_COMPILE` (default off): emit one structured timing row per
    /// compiler phase to stderr. The knob only records the intent; the CLI reads
    /// it and installs the actual [`TimingSink`](crate::TimingSink) onto the
    /// top-level compile's [`Config`](crate::Config), so an internal
    /// re-elaboration (which builds its own [`from_env`](Self::from_env) config)
    /// stays silent. Program stdout is unaffected; rows go only to stderr.
    pub time_compile: bool,
    /// `PRISM_QUIET` (default off): silence the compiler-internal fallback
    /// warnings (fusion drift, free-monad fallback) on stderr.
    pub quiet: bool,
    /// `PRISM_OPT_LEVEL` (default `O1`): the Core-to-Core optimization level a
    /// library entry point uses when the CLI does not pass an explicit `-O`. The
    /// CLI overrides the derived [`Config::opt`](crate::Config::opt); this is the
    /// env-supplied seed.
    pub opt_level: OptLevel,
    /// `PRISM_BACKEND_OPT` (default `"2"`): the LLVM-backend `-O` level a library
    /// entry point hands `cc` when the CLI does not pass `--backend-opt`. An
    /// invalid value is reported once here and falls back to the default.
    pub backend_opt: BackendOpt,
    /// `PRISM_NO_SPECIALIZE` (default off): turn off the `Specialize` Core pass.
    /// Presence-flagged, resolved into [`Config::disabled`](crate::Config::disabled).
    pub no_specialize: bool,
    /// `PRISM_FUSE` (default off): run the whole-program stream-fusion pass
    /// (`core/opt/fuse`) first in the pre-lowering stage, collapsing recognized
    /// pull-`Sequence` pipelines into allocation-free loops. Off until the ON/OFF
    /// differential oracle and the full gate battery are green; a fused loop is a
    /// lowering tier, so it must produce byte-identical output either way.
    pub fuse: bool,
    /// `PRISM_SCHEDULER` (default cooperative/FIFO): which shipped cooperative
    /// scheduler `run_cooperative` binds to when the CLI does not pass
    /// `--scheduler`.
    pub scheduler: Scheduler,
    /// `PRISM_EFFECT_TIER` (default `auto`): the lowest effect-lowering rung the
    /// cascade may take (`auto`, `state`, `free-monad`). Capping the cascade is
    /// contractually unobservable; the tier-parity oracle forces the slow rungs
    /// and diffs them against the interpreter. An invalid spelling is reported
    /// once and falls back to `auto` (the tier-parity test independently asserts
    /// the forcing engaged, so a typo cannot make the oracle silently vacuous).
    pub effect_tier: EffectTier,
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
    /// back to a user-wide cache directory, then `target/prism-store`; see
    /// [`crate::store::disk::resolve_store_path`].
    pub store_path: Option<PathBuf>,
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
            query_threads: DEFAULT_QUERY_THREADS,
            scc_backend: true,
            time_compile: false,
            quiet: false,
            opt_level: OptLevel::default(),
            backend_opt: BackendOpt::default(),
            no_specialize: false,
            fuse: false,
            scheduler: Scheduler::default(),
            effect_tier: EffectTier::default(),
            compiler_cache: true,
            store: false,
            store_path: None,
            sign_mode: SignMode::default(),
            sign_key: None,
            sign_identity: None,
            sign_allowed_signers: None,
        }
    }
}

impl DynFlags {
    /// Parse the process environment into a [`DynFlags`], starting from
    /// [`Default`]. This is the single site that reads the environment for these
    /// knobs; call it once at process start and thread the result down.
    #[must_use]
    pub fn from_env() -> Self {
        Self {
            native_effects: env_bool("PRISM_NATIVE_EFFECTS", true),
            trampoline: env_bool("PRISM_TRAMPOLINE", true),
            core_lint: env_present("PRISM_CORE_LINT"),
            rt_checks: env_present("PRISM_RT_CHECKS"),
            native_kont_frames: env_present("PRISM_NATIVE_KONT_FRAMES"),
            dump_core: std::env::var_os("PRISM_DUMP_CORE"),
            opt_stats: env_present("PRISM_OPT_STATS"),
            compiler_stats: env_present("PRISM_COMPILER_STATS"),
            explain_cache: env_present("PRISM_EXPLAIN_CACHE"),
            query_threads: query_threads_from_env(),
            scc_backend: env_bool("PRISM_SCC_BACKEND", true),
            time_compile: env_bool("PRISM_TIME_COMPILE", false),
            quiet: env_present("PRISM_QUIET"),
            opt_level: std::env::var("PRISM_OPT_LEVEL")
                .ok()
                .and_then(|s| OptLevel::parse(&s))
                .unwrap_or_default(),
            backend_opt: backend_opt_from_env(),
            no_specialize: env_present("PRISM_NO_SPECIALIZE"),
            fuse: env_bool("PRISM_FUSE", false),
            scheduler: std::env::var("PRISM_SCHEDULER")
                .ok()
                .and_then(|s| Scheduler::parse(&s))
                .unwrap_or_default(),
            effect_tier: effect_tier_from_env(),
            compiler_cache: env_bool("PRISM_COMPILER_CACHE", true),
            store: env_present("PRISM_STORE"),
            store_path: std::env::var_os("PRISM_STORE_PATH").map(PathBuf::from),
            sign_mode: sign_mode_from_env(),
            sign_key: std::env::var_os("PRISM_SIGN_KEY").map(PathBuf::from),
            sign_identity: std::env::var("PRISM_SIGN_IDENTITY").ok(),
            sign_allowed_signers: std::env::var_os("PRISM_SIGN_ALLOWED_SIGNERS").map(PathBuf::from),
        }
    }
}

fn query_threads_from_env() -> usize {
    std::env::var("PRISM_QUERY_THREADS").map_or(DEFAULT_QUERY_THREADS, |value| {
        value.parse::<usize>().ok().filter(|n| *n > 0).unwrap_or_else(|| {
            eprintln!(
                "ignoring invalid PRISM_QUERY_THREADS={value:?} (expected a positive integer); using {DEFAULT_QUERY_THREADS}"
            );
            DEFAULT_QUERY_THREADS
        })
    })
}

// The signing seam from `PRISM_SIGN_MODE`. An unrecognized value is reported once
// and falls back to the default (ssh) rather than silently signing nothing.
fn sign_mode_from_env() -> SignMode {
    std::env::var("PRISM_SIGN_MODE").map_or_else(
        |_| SignMode::default(),
        |s| {
            SignMode::parse(&s).unwrap_or_else(|| {
                eprintln!(
                    "ignoring invalid PRISM_SIGN_MODE={s:?} (expected ssh, minisign, unsigned); using ssh"
                );
                SignMode::default()
            })
        },
    )
}

// The effect-tier cap from `PRISM_EFFECT_TIER`. An unrecognized value is
// reported once and falls back to `auto` rather than silently forcing (or
// silently not forcing) a tier.
fn effect_tier_from_env() -> EffectTier {
    std::env::var("PRISM_EFFECT_TIER").map_or_else(
        |_| EffectTier::default(),
        |s| {
            EffectTier::parse(&s).unwrap_or_else(|| {
                eprintln!(
                    "ignoring invalid PRISM_EFFECT_TIER={s:?} (expected auto, state, free-monad); using auto"
                );
                EffectTier::default()
            })
        },
    )
}

// The LLVM-backend `-O` level from `PRISM_BACKEND_OPT`, validated against the
// levels clang accepts. An out-of-range value is reported once and falls back to
// the default rather than reaching `cc`.
fn backend_opt_from_env() -> BackendOpt {
    let Ok(s) = std::env::var("PRISM_BACKEND_OPT") else {
        return BackendOpt::default();
    };
    BackendOpt::parse(&s).unwrap_or_else(|| {
        eprintln!(
            "ignoring invalid PRISM_BACKEND_OPT={s:?} (expected {}); using {}",
            BackendOpt::levels(),
            BackendOpt::default().as_str()
        );
        BackendOpt::default()
    })
}

// An opt-out boolean flag: absent takes `default`; a falsey spelling (`0`,
// `false`, `off`, `no`, empty, case-insensitive) is false, anything else true.
// Accepting the word spellings avoids the footgun where `NAME=false` reads as
// enabled on a soundness-relevant toggle.
fn env_bool(name: &str, default: bool) -> bool {
    std::env::var(name).map_or(default, |v| {
        !matches!(
            v.trim().to_ascii_lowercase().as_str(),
            "0" | "false" | "off" | "no" | ""
        )
    })
}

// A presence flag: any value (even empty) is true, absent is false.
fn env_present(name: &str) -> bool {
    std::env::var_os(name).is_some()
}
