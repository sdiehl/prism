//! The driver's configuration layer: the compile knobs the CLI and library
//! entry points thread into every phase. `Config` is the single behavior-bearing
//! bundle; `Scheduler` and `BackendOpt` are the two closed value sets it carries.
//! Split out of the driver so `mod.rs` holds the pipeline and this module holds
//! the types it is parameterized by. Every external path (`prism::Config`,
//! `prism::Scheduler`, `prism::BackendOpt`) resolves through the re-export in
//! `mod.rs`, so the split is invisible to callers.

pub use crate::flags::{BackendOpt, Scheduler};

use crate::core::{CorePass, OptLevel, PassSpec};
use crate::flags::DynFlags;

use super::{ArtifactIdentity, CompilerSession, TimingSink};

/// The explicit compilation mode.
///
/// Production removes test declarations before
/// production interface/body reachability and backend lowering; Test checks
/// them in their defining module and makes them available only to a synthetic
/// harness. An input to the queries whose output actually differs, never a
/// scattered `if test_mode` inside lowering.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum BuildMode {
    #[default]
    Production,
    Test,
}

#[derive(Clone, Debug, Default)]
pub struct Config {
    /// The explicit production/test compilation mode (default production;
    /// only `prism test` selects [`BuildMode::Test`]).
    pub mode: BuildMode,
    /// An explicit ordered pass list (the CLI `--passes` flag) that overrides
    /// `opt` when present. The two are mutually exclusive at the CLI.
    pub passes: Option<PassSpec>,
    /// Core passes the caller turned off (the `--no-<pass>` flags), filtered out
    /// of whatever pipeline `opt`/`passes` selects.
    pub disabled: Vec<CorePass>,
    /// The resolved compiler behavior knobs (opt level, backend `-O`, scheduler,
    /// effect backends, Core Lint, dumps), layered default -> manifest -> env ->
    /// CLI. This is the sole home for every knob: the optimization level, backend
    /// level, and scheduler are read through [`opt`](Self::opt),
    /// [`backend_opt`](Self::backend_opt), and [`scheduler`](Self::scheduler),
    /// which project them out of here rather than storing a second copy that a CLI
    /// override could leave disagreeing. No pass reads the environment itself.
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
        Self::from_flags(DynFlags::from_env())
    }

    /// Build a config by projecting the Config-level fields out of an already
    /// resolved [`DynFlags`]. The one place that projection lives, so a caller who
    /// has layered a manifest and the environment into a `DynFlags` (see
    /// [`DynFlags::from_env_over`]) gets the same derivation as [`from_env`](Self::from_env).
    #[must_use]
    pub fn from_flags(flags: DynFlags) -> Self {
        let mut disabled = Vec::new();
        if flags.no_specialize {
            disabled.push(CorePass::Specialize);
        }
        if flags.no_ho_spec {
            disabled.push(CorePass::HoSpecialize);
        }
        Self {
            // The mode is a CLI decision (`prism test`), never an env knob.
            mode: BuildMode::Production,
            passes: None,
            disabled,
            flags,
            session: None,
            // A timing sink is never installed from the environment: it is a
            // property of a top-level CLI compile, so only the CLI attaches one.
            // This is what keeps the internal re-elaboration helpers silent.
            timing: None,
        }
    }

    /// The Core-to-Core optimization level (the CLI `-O` flag; default `O1`).
    #[must_use]
    pub const fn opt(&self) -> OptLevel {
        self.flags.opt_level
    }

    /// Set the optimization level, returning the config. A builder convenience for
    /// tests and embeddings; the level is stored in [`flags`](Self::flags), so this
    /// is the counterpart to [`opt`](Self::opt) and can never disagree with it.
    #[must_use]
    pub const fn with_opt(mut self, opt: OptLevel) -> Self {
        self.flags.opt_level = opt;
        self
    }

    /// The LLVM-backend optimization level handed to `cc` as `-O<level>` (the
    /// `--backend-opt` flag; default `O2`). Tunes clang's own pipeline over the
    /// emitted bitcode, distinct from the Core-to-Core [`opt`](Self::opt).
    #[must_use]
    pub const fn backend_opt(&self) -> BackendOpt {
        self.flags.backend_opt
    }

    /// Whether LLVM bitcode is lowered to native objects in-process before one
    /// ordinary platform link, instead of being handed to Clang `ThinLTO`.
    #[must_use]
    pub const fn direct_object(&self) -> bool {
        self.flags.direct_object
    }

    /// Which cooperative scheduler `run_cooperative` binds to (the `--scheduler`
    /// flag; default cooperative/FIFO).
    #[must_use]
    pub const fn scheduler(&self) -> Scheduler {
        self.flags.scheduler
    }

    /// Structured identity for behavior-affecting compiler artifacts.
    #[must_use]
    pub fn artifact_identity_for(&self, backend: &str) -> ArtifactIdentity {
        ArtifactIdentity::from_config(self, backend)
    }
}
