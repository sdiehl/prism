//! The driver's configuration layer: the compile knobs the CLI and library
//! entry points thread into every phase. `Config` is the single behavior-bearing
//! bundle; `Scheduler` and `BackendOpt` are the two closed value sets it carries.
//! Split out of the driver so `mod.rs` holds the pipeline and this module holds
//! the types it is parameterized by. Every external path (`prism::Config`,
//! `prism::Scheduler`, `prism::BackendOpt`) resolves through the re-export in
//! `mod.rs`, so the split is invisible to callers.

pub use crate::flags::{BackendOpt, Scheduler};

use std::{ffi::OsString, io};

use crate::core::opt::{CorePass, OptLevel, OptimizationPlan, OptimizerOptions, PassSet};
use crate::flags::{DynFlags, EffectLowerOptions};
use crate::store::disk::{resolve_store_path, Store};

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

/// Diagnostic-only optimizer controls. Passing this narrow value makes it
/// impossible for a Core pass to start observing cache, backend, package, or
/// execution settings accidentally.
#[derive(Clone, Debug, Default)]
pub(super) struct OptimizerDiagnostics {
    pub core_lint: bool,
    pub dump_core: Option<OsString>,
    pub opt_stats: bool,
}

/// The driver's compile configuration.
///
/// Every field is private: callers read through the typed accessors and mutate
/// through the scoped setters, so a level policy and an explicit pass pipeline
/// can never be stored together and a flag edit can never leave the optimizer
/// selection disagreeing with the stored plan.
#[derive(Clone, Debug, Default)]
pub struct Config {
    /// The explicit production/test compilation mode (default production;
    /// only `prism test` selects [`BuildMode::Test`]).
    mode: BuildMode,
    /// The one stored optimizer policy: a level with its disabled passes, or an
    /// explicit ordered pipeline (the CLI `--passes` flag). The sole authority
    /// for pass selection and artifact identity; the legacy `opt_level`/`no_*`
    /// selectors in `flags` are projections kept in sync by
    /// [`set_optimization_plan`](Self::set_optimization_plan) and
    /// [`update_flags`](Self::update_flags), never a second store.
    plan: OptimizationPlan,
    /// The resolved compiler behavior knobs (opt level, backend `-O`, scheduler,
    /// effect backends, Core Lint, dumps), layered default -> manifest -> env ->
    /// CLI. This is the sole home for every knob: the optimization level, backend
    /// level, and scheduler are read through [`opt`](Self::opt),
    /// [`backend_opt`](Self::backend_opt), and [`scheduler`](Self::scheduler),
    /// which project them out of here rather than storing a second copy that a CLI
    /// override could leave disagreeing. No pass reads the environment itself.
    flags: DynFlags,
    /// Optional command-scoped compiler session. Reusing a config carrying the
    /// same session allows successful frontend queries to hit in memory; absence
    /// changes cost only, never compiler behavior.
    session: Option<CompilerSession>,
    /// The per-compile timing sink, present only when the CLI installs it for a
    /// top-level `--time-compile`/`PRISM_TIME_COMPILE` compile. Absent on every
    /// [`Config::from_env`] the internal re-elaboration helpers build, so those
    /// silent compiles never emit timing rows. When absent, the timing wrappers
    /// compile away to a bare call, so the feature is zero-cost off.
    timing: Option<TimingSink>,
}

impl Config {
    /// The checked production/test mode selected at the driver edge.
    #[must_use]
    pub const fn mode(&self) -> BuildMode {
        self.mode
    }

    /// Set the build mode without exposing the rest of the configuration bag.
    pub const fn set_mode(&mut self, mode: BuildMode) {
        self.mode = mode;
    }

    /// Builder form of [`Self::set_mode`].
    #[must_use]
    pub const fn with_mode(mut self, mode: BuildMode) -> Self {
        self.set_mode(mode);
        self
    }

    /// The fully resolved edge flags. Middle-end passes receive narrower
    /// projections instead of this compiler-wide input value.
    #[must_use]
    pub const fn flags(&self) -> &DynFlags {
        &self.flags
    }

    /// Mutate resolved edge flags as one scoped operation.
    ///
    /// Optimizer selectors are re-normalized before this returns, so changing a
    /// legacy `opt_level`/`no_*` input cannot leave an explicit pass pipeline or
    /// disabled-pass set disagreeing with it. Compiler passes should use their
    /// narrow option values instead of this edge adapter.
    pub fn update_flags(&mut self, update: impl FnOnce(&mut DynFlags)) {
        let selectors = optimizer_selectors(&self.flags);
        let mut candidate = self.flags.clone();
        update(&mut candidate);
        let selected = optimizer_selectors(&candidate);
        self.flags = candidate;
        if selectors != selected {
            let plan = level_plan_from_selector_edit(&self.optimization_plan(), &self.flags);
            self.set_optimization_plan(plan);
        }
    }

    /// The optional compile-scoped query/store session.
    #[must_use]
    pub const fn session(&self) -> Option<&CompilerSession> {
        self.session.as_ref()
    }

    /// Install or clear a compile-scoped session.
    pub fn set_session(&mut self, session: Option<CompilerSession>) {
        self.session = session;
    }

    /// Builder form for installing one compile-scoped session.
    #[must_use]
    pub fn with_session(mut self, session: CompilerSession) -> Self {
        self.set_session(Some(session));
        self
    }

    /// The presentation-only timing sink, when the command edge installed one.
    #[must_use]
    pub const fn timing(&self) -> Option<&TimingSink> {
        self.timing.as_ref()
    }

    /// Install or clear the presentation-only timing sink.
    pub fn set_timing(&mut self, timing: Option<TimingSink>) {
        self.timing = timing;
    }

    /// Builder form for installing one presentation-only timing sink.
    #[must_use]
    pub fn with_timing(mut self, timing: TimingSink) -> Self {
        self.set_timing(Some(timing));
        self
    }

    #[cfg(feature = "native")]
    pub(super) fn with_store_transaction(&self) -> io::Result<Self> {
        if !self.flags.compiler_cache || self.flags.store {
            return Ok(self.clone());
        }
        let mut config = self.clone();
        let session = config.session.clone().unwrap_or_default();
        config.session = Some(
            session
                .with_store_transaction(&resolve_store_path(config.flags.store_path.as_deref()))?,
        );
        Ok(config)
    }

    pub(super) fn open_store(&self) -> io::Result<Store> {
        let root = resolve_store_path(self.flags.store_path.as_deref());
        self.session.as_ref().map_or_else(
            || Store::open_or_create(&root),
            |session| session.open_store(&root),
        )
    }

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
        Self {
            // The mode is a CLI decision (`prism test`), never an env knob.
            mode: BuildMode::Production,
            plan: level_plan_from_flags(&flags),
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

    /// The one stored algebraic optimizer policy consumed by the middle end.
    #[must_use]
    pub fn optimization_plan(&self) -> OptimizationPlan {
        self.plan.clone()
    }

    /// Replace the stored optimizer policy with one normalized plan.
    ///
    /// The legacy `opt_level`/`no_*` selectors in `flags` are re-projected from
    /// the plan here, so a level and an explicit pipeline are never retained
    /// together and the selectors can never disagree with the plan.
    pub fn set_optimization_plan(&mut self, plan: OptimizationPlan) {
        canonicalize_optimizer_selectors(&mut self.flags, &plan);
        self.plan = plan;
    }

    /// Builder form of [`Self::set_optimization_plan`].
    #[must_use]
    pub fn with_optimization_plan(mut self, plan: OptimizationPlan) -> Self {
        self.set_optimization_plan(plan);
        self
    }

    /// Select a level and clear every explicit/disabled optimizer override.
    #[must_use]
    pub fn use_level(mut self, level: OptLevel) -> Self {
        self.set_optimization_plan(OptimizationPlan::level(level, PassSet::new()));
        self
    }

    /// Disable a pass in the currently normalized policy.
    ///
    /// # Errors
    /// Removing the sole pass from an explicit pipeline is rejected.
    pub fn disable_pass(&mut self, pass: CorePass) -> Result<(), String> {
        let mut plan = self.optimization_plan();
        plan.disable(pass)?;
        self.set_optimization_plan(plan);
        Ok(())
    }

    #[must_use]
    pub const fn optimizer_options(&self) -> OptimizerOptions {
        OptimizerOptions {
            force_fuse: self.flags.fuse,
        }
    }

    #[must_use]
    pub(super) fn optimizer_diagnostics(&self) -> OptimizerDiagnostics {
        OptimizerDiagnostics {
            core_lint: self.flags.core_lint,
            dump_core: self.flags.dump_core.clone(),
            opt_stats: self.flags.opt_stats,
        }
    }

    /// The only flags observable by typed effect lowering.
    #[must_use]
    pub fn effect_lower_options(&self) -> EffectLowerOptions {
        EffectLowerOptions::from(&self.flags)
    }

    /// Set the optimization level, returning the config. Existing pass disables
    /// on a level policy are retained; use [`Self::use_level`] to reset them.
    /// An explicit pipeline has no level policy to retain, so selecting a level
    /// replaces it with the level defaults.
    #[must_use]
    pub fn with_opt(mut self, opt: OptLevel) -> Self {
        let disabled = match self.optimization_plan() {
            OptimizationPlan::Level { disabled, .. } => disabled,
            OptimizationPlan::Explicit(_) => PassSet::new(),
        };
        self.set_optimization_plan(OptimizationPlan::level(opt, disabled));
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

const fn optimizer_selectors(flags: &DynFlags) -> (OptLevel, bool, bool, bool) {
    (
        flags.opt_level,
        flags.no_specialize,
        flags.no_ho_spec,
        flags.no_exact_size,
    )
}

const LEGACY_SELECTOR_PASSES: [CorePass; 3] = [
    CorePass::Specialize,
    CorePass::HoSpecialize,
    CorePass::ExactSize,
];

fn legacy_selectors(flags: &DynFlags) -> impl Iterator<Item = (bool, CorePass)> {
    [flags.no_specialize, flags.no_ho_spec, flags.no_exact_size]
        .into_iter()
        .zip(LEGACY_SELECTOR_PASSES)
}

fn level_plan_from_flags(flags: &DynFlags) -> OptimizationPlan {
    let disabled = legacy_selectors(flags)
        .filter_map(|(disabled, pass)| disabled.then_some(pass))
        .collect();
    OptimizationPlan::level(flags.opt_level, disabled)
}

fn level_plan_from_selector_edit(current: &OptimizationPlan, flags: &DynFlags) -> OptimizationPlan {
    let retained = match current {
        OptimizationPlan::Level { disabled, .. } => disabled
            .iter()
            .filter(|pass| !legacy_selector_pass(*pass))
            .collect(),
        OptimizationPlan::Explicit(_) => PassSet::new(),
    };
    let mut disabled: PassSet = retained;
    for (off, pass) in legacy_selectors(flags) {
        if off {
            disabled.insert(pass);
        }
    }
    OptimizationPlan::level(flags.opt_level, disabled)
}

fn legacy_selector_pass(pass: CorePass) -> bool {
    LEGACY_SELECTOR_PASSES.contains(&pass)
}

fn canonicalize_optimizer_selectors(flags: &mut DynFlags, plan: &OptimizationPlan) {
    match plan {
        OptimizationPlan::Level { level, disabled } => {
            flags.opt_level = *level;
            set_legacy_selectors(flags, Some(disabled));
        }
        OptimizationPlan::Explicit(_) => {
            flags.opt_level = OptLevel::default();
            set_legacy_selectors(flags, None);
        }
    }
}

fn set_legacy_selectors(flags: &mut DynFlags, disabled: Option<&PassSet>) {
    let [specialize, higher_order, exact_size] =
        LEGACY_SELECTOR_PASSES.map(|pass| disabled.is_some_and(|set| set.contains(pass)));
    flags.no_specialize = specialize;
    flags.no_ho_spec = higher_order;
    flags.no_exact_size = exact_size;
}

#[cfg(test)]
mod tests {
    use std::iter;

    use crate::core::opt::PassSpec;

    use super::{Config, CorePass, DynFlags, OptLevel, OptimizationPlan, PassSet};

    #[test]
    fn normalized_optimizer_policy_has_one_authority() {
        let explicit = PassSpec::try_new(vec![CorePass::EraseNewtypes], Vec::new())
            .expect("one pre-lowering pass is a valid explicit pipeline");
        let config = Config::default()
            .with_optimization_plan(OptimizationPlan::explicit(explicit))
            .use_level(OptLevel::O2);

        assert_eq!(
            config.optimization_plan(),
            OptimizationPlan::level(OptLevel::O2, PassSet::new())
        );
        assert_eq!(config.flags().opt_level, OptLevel::O2);
        assert!(!config.flags().no_specialize);
    }

    #[test]
    fn legacy_selector_edit_is_renormalized_before_returning() {
        let explicit = PassSpec::try_new(vec![CorePass::EraseNewtypes], Vec::new())
            .expect("one pre-lowering pass is a valid explicit pipeline");
        let mut config =
            Config::default().with_optimization_plan(OptimizationPlan::explicit(explicit));

        config.update_flags(|flags| {
            flags.opt_level = OptLevel::O2;
            flags.no_specialize = true;
        });

        assert_eq!(
            config.optimization_plan(),
            OptimizationPlan::level(OptLevel::O2, iter::once(CorePass::Specialize).collect())
        );
    }

    #[test]
    fn failed_flag_edit_cannot_publish_an_inconsistent_candidate() {
        let explicit = PassSpec::try_new(vec![CorePass::EraseNewtypes], Vec::new())
            .expect("one pre-lowering pass is a valid explicit pipeline");
        let mut config =
            Config::default().with_optimization_plan(OptimizationPlan::explicit(explicit.clone()));

        let failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            config.update_flags(|flags| {
                flags.opt_level = OptLevel::O2;
                panic!("abort the edge edit");
            });
        }));

        assert!(failed.is_err());
        assert_eq!(
            config.optimization_plan(),
            OptimizationPlan::explicit(explicit)
        );
        assert_eq!(config.flags().opt_level, OptLevel::O1);
    }

    #[test]
    fn explicit_pipeline_cannot_be_disabled_to_empty() {
        let explicit = PassSpec::try_new(vec![CorePass::EraseNewtypes], Vec::new())
            .expect("one pre-lowering pass is a valid explicit pipeline");
        let mut config =
            Config::default().with_optimization_plan(OptimizationPlan::explicit(explicit.clone()));

        assert!(config.disable_pass(CorePass::EraseNewtypes).is_err());
        assert_eq!(
            config.optimization_plan(),
            OptimizationPlan::explicit(explicit)
        );
    }

    #[test]
    fn selecting_a_level_clears_every_legacy_selector() {
        let flags = DynFlags {
            no_specialize: true,
            no_ho_spec: true,
            no_exact_size: true,
            ..DynFlags::default()
        };
        let mut config = Config::from_flags(flags).use_level(OptLevel::O2);
        config.update_flags(|flags| flags.verbose = true);

        assert_eq!(
            config.optimization_plan(),
            OptimizationPlan::level(OptLevel::O2, PassSet::new())
        );
        assert!(!config.flags().no_specialize);
        assert!(!config.flags().no_ho_spec);
        assert!(!config.flags().no_exact_size);
    }

    #[test]
    fn legacy_selector_edits_preserve_other_disabled_passes() {
        let mut config = Config::default();
        config
            .disable_pass(CorePass::Inline)
            .expect("a level pipeline can disable Inline");
        config.update_flags(|flags| flags.no_specialize = true);

        assert_eq!(
            config.optimization_plan(),
            OptimizationPlan::level(
                OptLevel::O1,
                [CorePass::Inline, CorePass::Specialize]
                    .into_iter()
                    .collect()
            )
        );
    }

    #[test]
    fn with_opt_preserves_existing_level_disables() {
        let flags = DynFlags {
            no_specialize: true,
            ..DynFlags::default()
        };
        let mut config = Config::from_flags(flags);
        config
            .disable_pass(CorePass::Inline)
            .expect("a level pipeline can disable Inline");
        let config = config.with_opt(OptLevel::O2);

        assert_eq!(
            config.optimization_plan(),
            OptimizationPlan::level(
                OptLevel::O2,
                [CorePass::Specialize, CorePass::Inline]
                    .into_iter()
                    .collect()
            )
        );
        assert!(config.flags().no_specialize);
    }

    #[test]
    fn an_explicit_pipeline_composes_with_a_disable() {
        let pipeline = PassSpec::try_new(vec![CorePass::EraseNewtypes], vec![CorePass::Inline])
            .expect("the explicit pipeline spans both pass stages");
        let mut config =
            Config::default().with_optimization_plan(OptimizationPlan::explicit(pipeline));
        config
            .disable_pass(CorePass::Inline)
            .expect("one pre-lowering pass remains");
        let expected = PassSpec::try_new(vec![CorePass::EraseNewtypes], Vec::new())
            .expect("one pre-lowering pass is a valid explicit pipeline");

        assert_eq!(
            config.optimization_plan(),
            OptimizationPlan::explicit(expected)
        );
    }
}
