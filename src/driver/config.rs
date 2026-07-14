//! The driver's configuration layer: the compile knobs the CLI and library
//! entry points thread into every phase. `Config` is the single behavior-bearing
//! bundle; `Scheduler` and `BackendOpt` are the two closed value sets it carries.
//! Split out of the driver so `mod.rs` holds the pipeline and this module holds
//! the types it is parameterized by. Every external path (`prism::Config`,
//! `prism::Scheduler`, `prism::BackendOpt`) resolves through the re-export in
//! `mod.rs`, so the split is invisible to callers.

use crate::core::{CorePass, OptLevel, PassSpec};
use crate::flags::DynFlags;

use super::{ArtifactIdentity, CompilerSession, TimingSink};

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
    pub(super) const fn retarget(self) -> Option<&'static str> {
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

/// A backend optimization level clang accepts via `-O`.
///
/// The single source of truth shared by the `--backend-opt` flag and the
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

#[derive(Clone, Debug, Default)]
pub struct Config {
    /// The Core-to-Core optimization level (the CLI `-O` flag; default `O1`).
    pub opt: OptLevel,
    /// An explicit ordered pass list (the CLI `--passes` flag) that overrides
    /// `opt` when present. The two are mutually exclusive at the CLI.
    pub passes: Option<PassSpec>,
    /// The LLVM-backend optimization level handed to `cc` as `-O<level>` (the
    /// `--backend-opt` flag; default `O2`). Tunes clang's own pipeline over the
    /// emitted bitcode, distinct from the Core-to-Core `opt` above.
    pub backend_opt: BackendOpt,
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
    /// Optional command-scoped compiler session. Reusing a config carrying the
    /// same session allows successful frontend queries to hit in memory; absence
    /// changes cost only, never compiler behavior.
    pub session: Option<CompilerSession>,
    /// The per-compile timing sink, present only when the CLI installs it for a
    /// top-level `--time-compile`/`PRISM_TIME_COMPILE` compile. Absent on every
    /// [`Config::from_env`] the internal re-elaboration helpers build, so those
    /// silent compiles never emit timing rows. When absent, the timing wrappers
    /// compile away to a bare call, so the feature is zero-cost off.
    pub timing: Option<TimingSink>,
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
            backend_opt: flags.backend_opt,
            disabled,
            scheduler: flags.scheduler,
            flags,
            session: None,
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
