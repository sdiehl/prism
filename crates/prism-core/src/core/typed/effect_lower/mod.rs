//! Typed effect lowering: the `Elaborated -> EffectLowered` phase transition.
//!
//! An explicit, witness-preserving builder consumes the input evidence, runs
//! the strategy cascade, and verifies the output against the extended
//! environment before the `EffectLowered` marker is stamped; the marker is
//! never forged around an unverified tree. This verified typed result,
//! including its constructor table, warning, and strategy, is the production
//! authority. Tests pin typed verification, explicit strategy/structure, and
//! erased observable behavior without a second lowering implementation.
//!
//! The supported set includes pure lowering, local-variable and loop-control
//! erasure, evidence lowering, and the selective/whole-program free-monad
//! strategies, including State fusion on its own and as the fused half of
//! `LocalPartial`.

#[cfg(any(test, feature = "test-hooks"))]
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::convert::Infallible;

pub mod abi;
pub mod analysis;
pub mod arena;
mod checks;
mod convention;
pub mod decline;
pub mod diagnostics;
mod erase_control;
mod erase_var;
pub mod evidence;
pub mod explain;
#[cfg(test)]
pub mod fixtures;
pub mod flow;
pub mod latent;
pub mod monadic;
pub mod plan;
pub mod residual;
pub mod state;
mod subtract;
pub mod trampoline;
pub mod walk;

use crate::core::effect_abi::{
    add_synthetic_ctor, EBIND, EBOUNCE, EOP, EPURE, ERESUME, QAPPLY, SDONE, SMORE, TQCONS, TQNIL,
};
use crate::core::{EffectStrategy, LoweredCore, OpGrades};
use crate::flags::{DynFlags, EffectLowerOptions};
use crate::types::ty::{EffRow, Label};
use crate::types::{CtorInfo, Type};
use prism_common::sym::Sym;
use prism_syntax::error::TypedCoreEffectLoweringFailure;
use prism_syntax::names::ENTRY_POINT;

use super::inline::calls_in;
use super::specialize_support::{free_comp_vars, Rewrite};
use super::traverse::Visit;
use super::verify::{instantiate_fn, union_rows, VerifyEnv};
use super::{
    audit, on_core_stack, verify, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType,
    CoreViolation, EffectLowered, Elaborated, ReuseLowered, TypedBinder, TypedComp, TypedCompKind,
    TypedCore, TypedCoreFn, TypedCorePhase, TypedPattern, TypedValue, TypedValueKind,
    UncheckedTypedCore,
};
use decline::Decline;
use diagnostics::DriftLog;
pub use plan::{raw_effects, EffectPlan};

/// A verified lowering.
///
/// The `EffectLowered` program, the environment it verifies under, the
/// constructor table extended with any synthetics the taken strategy
/// introduced, the free-monad fallback warning (if any), and the strategy label
/// the cascade decided.
#[derive(Debug)]
pub struct TypedLowering {
    core: TypedCore<EffectLowered>,
    env: VerifyEnv,
    ctors: BTreeMap<String, CtorInfo>,
    warning: Option<String>,
    strategy: EffectStrategy,
    /// Why a confined region was refused before this strategy was taken, when
    /// one was attempted and refused. The plan artifact renders it, so a tier
    /// nobody expected can be read back to the shape that caused it.
    confined_decline: Option<Decline>,
}

#[derive(Debug)]
struct LoweringFacts {
    env: VerifyEnv,
    ctors: BTreeMap<String, CtorInfo>,
    warning: Option<String>,
    strategy: EffectStrategy,
    confined_decline: Option<Decline>,
}

/// A downstream pass failed, or its output did not verify under the lowering's
/// retained authority.
#[derive(Debug)]
pub enum TypedLoweringTransitionError<E> {
    /// The downstream pass returned its own failure.
    Pass(E),
    /// The pass returned a value incompatible with the retained environment or
    /// final structural stage.
    Invariant(TypedCoreEffectLoweringFailure),
}

/// A fully consumed typed lowering and the decision metadata that belongs to it.
///
/// The driver creates this through [`TypedLowering::try_erase_core`] or
/// [`TypedLowering::try_finish_core`]. Both transitions recheck the typed value
/// under its retained environment and perform the final structural validation.
#[derive(Debug)]
pub struct FinishedLowering {
    core: LoweredCore,
    ctors: BTreeMap<String, CtorInfo>,
    warning: Option<String>,
    strategy: EffectStrategy,
    confined_decline: Option<Decline>,
}

impl FinishedLowering {
    /// The validated erased program at the final lowering stage.
    #[must_use]
    pub const fn core(&self) -> &LoweredCore {
        &self.core
    }

    /// The constructor table paired with the final program.
    #[must_use]
    pub const fn constructors(&self) -> &BTreeMap<String, CtorInfo> {
        &self.ctors
    }

    /// The fallback warning selected by the lowering cascade, when any.
    #[must_use]
    pub fn warning(&self) -> Option<&str> {
        self.warning.as_deref()
    }

    /// The strategy selected by the lowering cascade.
    #[must_use]
    pub const fn strategy(&self) -> EffectStrategy {
        self.strategy
    }

    /// The confined-region refusal that caused the cascade to widen, when any.
    #[must_use]
    pub const fn confined_decline(&self) -> Option<&Decline> {
        self.confined_decline.as_ref()
    }

    /// Consume the artifact at the explicit backend boundary.
    #[must_use]
    pub fn into_core(self) -> LoweredCore {
        self.core
    }

    /// Consume the final artifact for a backend that owns both products.
    #[must_use]
    pub fn into_core_and_constructors(self) -> (LoweredCore, BTreeMap<String, CtorInfo>) {
        (self.core, self.ctors)
    }
}

impl TypedLowering {
    fn into_core_and_facts(self) -> (TypedCore<EffectLowered>, LoweringFacts) {
        (
            self.core,
            LoweringFacts {
                env: self.env,
                ctors: self.ctors,
                warning: self.warning,
                strategy: self.strategy,
                confined_decline: self.confined_decline,
            },
        )
    }

    /// The verified effect-lowered program produced by the selected strategy.
    #[must_use]
    pub const fn core(&self) -> &TypedCore<EffectLowered> {
        &self.core
    }

    /// The verifier environment paired with [`Self::core`].
    #[must_use]
    pub const fn env(&self) -> &VerifyEnv {
        &self.env
    }

    /// The constructor table paired with [`Self::core`], including synthetics.
    #[must_use]
    pub const fn constructors(&self) -> &BTreeMap<String, CtorInfo> {
        &self.ctors
    }

    /// The fallback warning selected by the production cascade, when any.
    #[must_use]
    pub fn warning(&self) -> Option<&str> {
        self.warning.as_deref()
    }

    /// The strategy selected by the production cascade.
    #[must_use]
    pub const fn strategy(&self) -> EffectStrategy {
        self.strategy
    }

    /// The confined-region refusal that caused the cascade to widen, when any.
    #[must_use]
    pub const fn confined_decline(&self) -> Option<&Decline> {
        self.confined_decline.as_ref()
    }

    /// Rewrite the program while keeping it paired with the verifier context
    /// and lowering decision that produced it.
    ///
    /// The callback cannot replace the environment, constructors, warning, or
    /// strategy independently, so downstream passes do not need to dismantle
    /// this artifact merely to transform its Core program.
    ///
    /// # Errors
    /// Returns the callback's error, or an invariant failure when the rewritten
    /// tree does not verify under the retained environment.
    pub fn try_map_core<E>(
        self,
        rewrite: impl FnOnce(
            TypedCore<EffectLowered>,
            &VerifyEnv,
        ) -> Result<TypedCore<EffectLowered>, E>,
    ) -> Result<Self, TypedLoweringTransitionError<E>> {
        let (core, facts) = self.into_core_and_facts();
        let core = rewrite(core, &facts.env).map_err(TypedLoweringTransitionError::Pass)?;
        audit(&core, &facts.env)
            .map_err(|violations| verification_failure(&violations))
            .map_err(TypedLoweringTransitionError::Invariant)?;
        Ok(facts.with_core(core))
    }

    /// Consume the verified effect-lowered tree through canonical erasure.
    ///
    /// # Errors
    /// Returns an invariant failure if the retained typed authority or the
    /// erased structural stage no longer validates.
    pub fn try_erase_core(
        self,
    ) -> Result<FinishedLowering, TypedLoweringTransitionError<Infallible>> {
        let (core, facts) = self.into_core_and_facts();
        facts.finish(core)
    }

    /// Consume the program and its verifier authority in one final transition.
    ///
    /// The callback performs ownership and reuse lowering but returns the final
    /// typed stage. This method rechecks that stage under the retained
    /// environment, erases it, and validates the structural boundary.
    ///
    /// # Errors
    /// Returns the callback's error, or an invariant failure when its typed or
    /// erased output does not validate under the retained authority.
    pub fn try_finish_core<E>(
        self,
        finish: impl FnOnce(TypedCore<EffectLowered>, &VerifyEnv) -> Result<TypedCore<ReuseLowered>, E>,
    ) -> Result<FinishedLowering, TypedLoweringTransitionError<E>> {
        let (core, facts) = self.into_core_and_facts();
        let core = finish(core, &facts.env).map_err(TypedLoweringTransitionError::Pass)?;
        facts.finish(core)
    }
}

impl LoweringFacts {
    fn with_core(self, core: TypedCore<EffectLowered>) -> TypedLowering {
        TypedLowering {
            core,
            env: self.env,
            ctors: self.ctors,
            warning: self.warning,
            strategy: self.strategy,
            confined_decline: self.confined_decline,
        }
    }

    fn finish<P: TypedCorePhase, E>(
        self,
        core: TypedCore<P>,
    ) -> Result<FinishedLowering, TypedLoweringTransitionError<E>> {
        audit(&core, &self.env)
            .map_err(|violations| verification_failure(&violations))
            .map_err(TypedLoweringTransitionError::Invariant)?;
        let core = LoweredCore::validate(core.erase()).map_err(|violations| {
            TypedLoweringTransitionError::Invariant(TypedCoreEffectLoweringFailure::Internal {
                msg: format!(
                    "final lowered Core failed structural validation:\n{}",
                    violations.join("\n")
                ),
            })
        })?;
        Ok(FinishedLowering {
            core,
            ctors: self.ctors,
            warning: self.warning,
            strategy: self.strategy,
            confined_decline: self.confined_decline,
        })
    }
}

fn verification_failure(violations: &[CoreViolation]) -> TypedCoreEffectLoweringFailure {
    TypedCoreEffectLoweringFailure::Verification {
        first: violations
            .first()
            .map_or_else(String::new, ToString::to_string),
        count: violations.len(),
    }
}

#[cfg(test)]
mod transition_tests {
    use std::collections::BTreeMap;

    use prism_common::sym::Sym;
    use prism_syntax::error::TypedCoreEffectLoweringFailure;
    use prism_syntax::names::ENTRY_POINT;

    use crate::core::EffectStrategy;
    use crate::types::ty::EffRow;
    use crate::types::Type;

    use super::super::{
        verify, CompSig, ConstructorSig, CoreFnSig, CoreType, EffectLowered, ReuseLowered,
        TypedComp, TypedCompKind, TypedCore, TypedCoreFn, TypedCorePhase, TypedValue,
        TypedValueKind, UncheckedTypedCore, VerifyEnv,
    };
    use super::{TypedLowering, TypedLoweringTransitionError};

    fn foreign_core<P: TypedCorePhase>(env: &VerifyEnv) -> TypedCore<P> {
        let result = CoreType::Source(Type::Con(Sym::new("Foreign"), Vec::new()));
        let value = TypedValue::new(
            result.clone(),
            TypedValueKind::Ctor {
                name: Sym::new("Foreign"),
                tag: 0,
                instantiation: Vec::new(),
                fields: Vec::new(),
            },
        );
        let body = TypedComp::new(
            CompSig::new(result, EffRow::Empty),
            TypedCompKind::Return(value),
        );
        let function = TypedCoreFn::new(
            Sym::new(ENTRY_POINT),
            Vec::new(),
            body.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone()),
            0,
        );
        verify(UncheckedTypedCore::new(vec![function]), env).expect("foreign Core verifies")
    }

    fn foreign_env() -> VerifyEnv {
        let mut env = VerifyEnv::new();
        let result = CoreType::Source(Type::Con(Sym::new("Foreign"), Vec::new()));
        env.insert_constructor(
            Sym::new("Foreign"),
            ConstructorSig::new(Vec::new(), 0, Vec::new(), result),
        );
        env
    }

    fn empty_lowering() -> TypedLowering {
        let env = VerifyEnv::new();
        let core = verify(UncheckedTypedCore::new(Vec::new()), &env).expect("empty Core verifies");
        TypedLowering {
            core,
            env,
            ctors: BTreeMap::new(),
            warning: None,
            strategy: EffectStrategy::Pure,
            confined_decline: None,
        }
    }

    #[test]
    fn transitions_reject_core_verified_under_an_unrelated_environment() {
        let env = foreign_env();
        let rewritten = foreign_core::<EffectLowered>(&env);
        let error = empty_lowering()
            .try_map_core(|_, _| Ok::<_, ()>(rewritten))
            .expect_err("map must retain its original verifier environment");
        assert!(matches!(
            error,
            TypedLoweringTransitionError::Invariant(
                TypedCoreEffectLoweringFailure::Verification { .. }
            )
        ));

        let finished = foreign_core::<ReuseLowered>(&env);
        let error = empty_lowering()
            .try_finish_core(|_, _| Ok::<_, ()>(finished))
            .expect_err("finish must retain its original verifier environment");
        assert!(matches!(
            error,
            TypedLoweringTransitionError::Invariant(
                TypedCoreEffectLoweringFailure::Verification { .. }
            )
        ));
    }
}

/// One monadification attempt: the lowering it produced, or the refusal that
/// tells the caller to widen the plan.
type Attempt = Result<Decision, Decline>;

/// What the cascade decided.
///
/// The cascade performs classification and selects the lowering, avoiding a
/// second classifier that could drift from production.
#[derive(Debug)]
pub enum Decision {
    Lowered(Box<TypedLowering>),
}

/// Lower a verified `Elaborated` program into a verified `EffectLowered` one.
///
/// # Errors
/// [`TypedCoreEffectLoweringFailure::Verification`] if the built tree does not
/// verify (never stamped in that case).
pub fn lower_effects(
    core: TypedCore<Elaborated>,
    env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
    flags: &DynFlags,
    grades: &OpGrades,
) -> Result<TypedLowering, TypedCoreEffectLoweringFailure> {
    lower_effects_with_options(core, env, ctors, &EffectLowerOptions::from(flags), grades)
}

/// Lower with the normalized, responsibility-specific option value.
///
/// This is the compiler route; [`lower_effects`] remains a compatibility seam
/// for embeddings that still construct `DynFlags` directly.
///
/// # Errors
/// Returns a typed-lowering failure when preparation, rewriting, or verification
/// cannot preserve the Core invariants.
pub fn lower_effects_with_options(
    core: TypedCore<Elaborated>,
    env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
    options: &EffectLowerOptions,
    grades: &OpGrades,
) -> Result<TypedLowering, TypedCoreEffectLoweringFailure> {
    on_core_stack(|| match cascade(core, env, ctors, options, grades)? {
        Decision::Lowered(lowering) => Ok(*lowering),
    })
}

/// The strategy the cascade recognizes for `core`, or `None` when it declines
/// without classifying.
///
/// Reads the one cascade rather than re-deciding, so a recognized strategy
/// cannot drift from the lowering that produced it.
///
/// # Errors
/// As [`lower_effects`].
#[cfg(any(test, feature = "test-hooks"))]
pub fn recognized_strategy(
    core: TypedCore<Elaborated>,
    env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
    flags: &DynFlags,
    grades: &OpGrades,
) -> Result<Option<EffectStrategy>, TypedCoreEffectLoweringFailure> {
    let options = EffectLowerOptions::from(flags);
    Ok(match cascade(core, env, ctors, &options, grades)? {
        Decision::Lowered(lowering) => Some(lowering.strategy),
    })
}

/// Everything the cascade settles before it can classify: what is reachable,
/// where allocation happens, and which effects are left once local variables and
/// loop control are gone.
///
/// Separate from the cascade because a program's classification is a question
/// about this tree, not the source one, so anything that asks it has to start
/// here. Answering from the un-prepared tree is a different question with a
/// different answer.
#[derive(Debug)]
pub struct Prepared {
    fns: Vec<TypedCoreFn>,
    env: VerifyEnv,
    ctors: BTreeMap<String, CtorInfo>,
}

impl Prepared {
    /// Reachable functions after the preparation steps shared by every tier.
    #[must_use]
    pub fn functions(&self) -> &[TypedCoreFn] {
        &self.fns
    }

    /// The verifier environment paired with [`Self::functions`].
    #[must_use]
    pub const fn env(&self) -> &VerifyEnv {
        &self.env
    }

    /// The constructor table paired with [`Self::functions`].
    #[must_use]
    pub const fn constructors(&self) -> &BTreeMap<String, CtorInfo> {
        &self.ctors
    }
}

/// Narrow an elaborated program to what effect lowering must see: the
/// functions reachable from the entry point, with the environment and
/// constructor table they verify under.
///
/// # Errors
/// As [`lower_effects`].
pub fn prepare(
    core: TypedCore<Elaborated>,
    env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
    flags: &DynFlags,
    grades: &OpGrades,
) -> Result<Prepared, TypedCoreEffectLoweringFailure> {
    prepare_with_options(core, env, ctors, &EffectLowerOptions::from(flags), grades)
}

/// Prepare effect lowering from its narrow normalized option value.
///
/// # Errors
/// Returns a typed-lowering failure when preparation cannot preserve the Core
/// invariants.
pub fn prepare_with_options(
    core: TypedCore<Elaborated>,
    env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
    options: &EffectLowerOptions,
    grades: &OpGrades,
) -> Result<Prepared, TypedCoreEffectLoweringFailure> {
    on_core_stack(|| prepare_on_core_stack(core, env, ctors, options, grades))
}

fn prepare_on_core_stack(
    core: TypedCore<Elaborated>,
    env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
    options: &EffectLowerOptions,
    grades: &OpGrades,
) -> Result<Prepared, TypedCoreEffectLoweringFailure> {
    // Dead prelude code must not flip the program into monadic mode, so only
    // functions reachable from main are lowered (and kept) at all.
    let fns = core.into_unchecked().into_functions();
    let fns: Vec<TypedCoreFn> = if fns.iter().any(|f| f.name().as_str() == ENTRY_POINT) {
        let live = reachable(&fns);
        fns.into_iter()
            .filter(|f| live.contains(&f.name()))
            .collect()
    } else {
        fns
    };

    // Scope-directed arena lowering, before the tier branch so every tier reifies
    // the same allocations (the choice of allocator is tier-invariant): a
    // constructor built under a `with_arena` scope becomes `alloc` + `init_at`,
    // which the installed handler discharges into a `bump`, and each installer's
    // handler activation is bracketed with the runtime region hooks. The hook
    // builtins' verifier signatures are seeded here so every later phase
    // verifies the bracketed tree under the same environment. A no-op when no
    // `with_arena` is present, so the non-arena corpus stays byte-identical.
    let mut env = env.clone();
    arena::insert_builtin_sigs(&mut env);
    let arena = arena::prepare(fns, &env)?;
    let fns = convention::split(arena, &env)?
        .into_unchecked()
        .into_functions();

    // Erase escape-checked local `var` state to mutable cells before strategy
    // selection, so a var-only program has no residual effects and classifies
    // pure. Loop-control erasure follows before classification so recognized
    // control handlers do not leave raw effect nodes. Turning the erasures off
    // is its own knob position, independent of the cascade floor, so a forced
    // divergence names one of the two rather than both at once.
    let (fns, used_step) = if options.erasures() {
        let vars_gone = erase_var::erase_local_vars(
            &fns,
            grades,
            &EffectPlan::analyze(&fns),
            &env,
            &DriftLog::new(options.quiet()),
        );
        // Erase loop-control effects to direct control flow next, so a
        // recognized loop's control ops are gone before the strategy cascade
        // classifies the residual: a pure imperative loop then classifies
        // pure rather than reifying into the free monad. A plan is a fact
        // about one tree, so this one is recomputed: on the vars-gone tree an
        // erased `var` no longer reads as a latent effect that would make an
        // otherwise pure loop body look foreign.
        let erased = erase_control::erase_control(&vars_gone, &EffectPlan::analyze(&vars_gone));
        (erased.fns, erased.used_step)
    } else {
        (fns, false)
    };
    // The `SMore`/`SDone` constructors a `return` erasure threads must be on
    // the tables for every path below, the verifier's included.
    let ctors = if used_step {
        let mut c = ctors.clone();
        add_synthetic_ctor(&mut c, SMORE);
        add_synthetic_ctor(&mut c, SDONE);
        erase_control::insert_step_constructors(&mut env);
        c
    } else {
        ctors.clone()
    };
    Ok(Prepared { fns, env, ctors })
}

/// Assign operation ids once from the whole prepared program. Strategies may
/// lower disjoint subsets, but every subset keeps these ABI-visible numbers.
///
/// # Errors
/// [`TypedCoreEffectLoweringFailure::Internal`] when the program declares more
/// operations than an `i64` can number.
pub fn operation_ids(
    fns: &[TypedCoreFn],
) -> Result<evidence::OpIds, TypedCoreEffectLoweringFailure> {
    let mut ops = BTreeSet::new();
    for f in fns {
        walk::collect_ops(f.body(), &mut ops);
    }
    evidence::OpIds::assign(&ops).ok_or_else(|| TypedCoreEffectLoweringFailure::Internal {
        msg: "more than i64::MAX effect ops".into(),
    })
}

/// The threaded program with its witnesses intact, plus the environment it must
/// verify under in its final phase.
///
/// For the verifier-activation tests: this exposes the State phase builder
/// directly while keeping its witnesses.
///
/// # Errors
/// As [`lower_effects`].
#[cfg(any(test, feature = "test-hooks"))]
pub fn threaded_state_typed(
    core: TypedCore<Elaborated>,
    env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
    flags: &DynFlags,
    grades: &OpGrades,
) -> Result<Option<(TypedCore<EffectLowered>, VerifyEnv)>, TypedCoreEffectLoweringFailure> {
    let options = EffectLowerOptions::from(flags);
    let prepared = prepare_with_options(core, env, ctors, &options, grades)?;
    let ops = operation_ids(&prepared.fns)?;
    let latent = latent::latent_map(&prepared.fns);
    let thunk_flow = flow::analyze(&prepared.fns, &latent);
    let mut env = prepared.env;
    // The Step constructors an early-exit lowering mints must be on the
    // verifier's tables. State threading is the Elaborated -> EffectLowered
    // builder, so a checked
    // LoweredRepr in its output is legal by the output phase alone; no monadic
    // constructor universe is installed, because a pure state output emits none.
    erase_control::insert_step_constructors(&mut env);
    let analysis = state::StateAnalysis::new(&ops, &latent, &thunk_flow, &env);
    let Some(plan) = state::fold_uniform(&prepared.fns, &analysis) else {
        return Ok(None);
    };
    if !state::threads(&plan, &prepared.fns, &analysis) {
        return Ok(None);
    }
    let mut fresh = prism_common::fresh::Fresh::new();
    let Some(fns) = state::thread_program(
        &prepared.fns,
        &plan,
        &analysis,
        &DriftLog::new(options.quiet()),
        &mut fresh,
    ) else {
        return Ok(None);
    };
    verify(UncheckedTypedCore::<EffectLowered>::new(fns), &env)
        .map(|core| Some((core, env)))
        .map_err(|violations| verification_failure(&violations))
}

fn cascade(
    core: TypedCore<Elaborated>,
    env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
    options: &EffectLowerOptions,
    grades: &OpGrades,
) -> Result<Decision, TypedCoreEffectLoweringFailure> {
    let prepared = prepare_with_options(core, env, ctors, options, grades)?;
    let fns = prepared.fns;
    let env = &prepared.env;
    let ctors = &prepared.ctors;

    if !fns.iter().any(|f| raw_effects(f.body())) {
        return lowered(fns, env, ctors, None, EffectStrategy::Pure, None);
    }

    // The evidence rung: the Identity answer, tried first because it reifies
    // the least. It fully succeeds or declines with no state to undo. A floor
    // above it skips it to request a later rung directly.
    let ops = operation_ids(&fns)?;
    let latent = latent::latent_map(&fns);
    let thunk_flow = flow::analyze(&fns, &latent);
    let plan = EffectPlan::from_parts(&fns, latent, thunk_flow);
    let (latent, thunk_flow) = (plan.latent(), plan.flow());
    let state_analysis = state::StateAnalysis::new(&ops, latent, thunk_flow, env);
    let drift = DriftLog::new(options.quiet());
    let mut fresh = prism_common::fresh::Fresh::new();
    if options.rung_enabled(EffectStrategy::Evidence) {
        if let Some(threaded) =
            evidence::try_lower_ev(&fns, latent, thunk_flow, &ops, env, &drift, &mut fresh)
        {
            return lowered(threaded, env, ctors, None, EffectStrategy::Evidence, None);
        }
    }

    // The state rung: the State answer, for a program whose consumer handles its
    // operation by parameter passing (so its clause is not tail-resumptive and
    // the evidence rung above declined).
    //
    // A program can pass the gate and still decline below it: fold-uniformity
    // comes first, then the value-coincidence the threading runs under. Both
    // fall through to the next rung rather than failing, because a decline here
    // is a program this engine does not fit, not a defect.
    if options.rung_enabled(EffectStrategy::StateFusion) {
        if let Some(plan) = state::fold_uniform(&fns, &state_analysis) {
            if state::threads(&plan, &fns, &state_analysis) {
                if let Some(threaded) =
                    state::thread_program(&fns, &plan, &state_analysis, &drift, &mut fresh)
                {
                    let mut lowered_env = env.clone();
                    let mut lowered_ctors = ctors.clone();
                    install_step_runtime(&threaded, &mut lowered_env, &mut lowered_ctors);
                    return lowered(
                        threaded,
                        &lowered_env,
                        &lowered_ctors,
                        None,
                        EffectStrategy::StateFusion,
                        None,
                    );
                }
            }
        }
    }

    let analysis = LoweringAnalysis {
        ops: &ops,
        plan: &plan,
    };
    if options.rung_enabled(EffectStrategy::LocalPartial) {
        if let Some(local) = try_local_partial(&fns, env, ctors, &analysis, &drift, &mut fresh)? {
            return Ok(local);
        }
    }

    // A LocalPartial rest or boundary that honestly declined takes the ordinary
    // selective/whole free-monad fallback. The one cascade-owned fresh supply
    // retains every name consumed by that attempt, matching the executable
    // pass's late-decline behavior.
    monadic_fallback_with_options(&fns, env, ctors, options, &analysis, &mut fresh)
}

/// What every rung below the evidence engine reads: the operation numbering the
/// whole prepared program shares, and the one plan that answers reachability and
/// purity for it.
#[derive(Debug)]
pub struct LoweringAnalysis<'a> {
    pub ops: &'a evidence::OpIds,
    pub plan: &'a EffectPlan,
}

impl LoweringAnalysis<'_> {
    const fn latent(&self) -> &latent::Latent {
        self.plan.latent()
    }

    const fn flow(&self) -> &flow::ThunkFlow {
        self.plan.flow()
    }
}

#[derive(Debug)]
pub struct LocalPartialArtifacts {
    pub fns: Vec<TypedCoreFn>,
    pub env: VerifyEnv,
    pub ctors: BTreeMap<String, CtorInfo>,
    pub warning: Option<String>,
}

struct LocalEntryCalls<'a> {
    signatures: &'a BTreeMap<Sym, CoreFnSig>,
    error: Option<String>,
}

impl Rewrite for LocalEntryCalls<'_> {
    type Ctx = ();

    fn comp(&mut self, comp: &TypedComp, cx: &Self::Ctx) -> TypedComp {
        let TypedCompKind::Call {
            callee,
            instantiation,
            args,
        } = comp.kind()
        else {
            return self.descend_comp(comp, cx);
        };
        let args: Vec<TypedValue> = args.iter().map(|arg| self.value(arg, cx)).collect();
        let Some(signature) = self.signatures.get(callee) else {
            return TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::Call {
                    callee: *callee,
                    instantiation: instantiation.clone(),
                    args,
                },
            );
        };
        let ambient = Sym::from(prism_syntax::names::FREE_MONAD_ROW);
        if signature.quantifiers().len() != instantiation.len() + 1
            || signature.quantifiers().last() != Some(&CoreQuantifier::Row(ambient))
        {
            self.error.get_or_insert_with(|| {
                format!("LocalPartial entry `{callee}` has no final ambient-row quantifier")
            });
            return comp.clone();
        }
        let required = signature.body().effects().labels();
        let current = comp.sig().effects().labels();
        if required.iter().any(|label| !current.contains(label)) {
            self.error.get_or_insert_with(|| {
                format!("LocalPartial entry `{callee}` requires effects absent at its source call")
            });
            return comp.clone();
        }
        let ambient_argument = EffRow::canonical(
            current
                .into_iter()
                .filter(|label| !required.contains(label))
                .cloned(),
            comp.sig().effects().tail().clone(),
        );
        let mut instantiation = instantiation.clone();
        instantiation.push(CoreInstantiation::Row(ambient_argument));
        let Ok(applied) = instantiate_fn(signature, &instantiation) else {
            self.error.get_or_insert_with(|| {
                format!("LocalPartial entry `{callee}` ambient instantiation is invalid")
            });
            return comp.clone();
        };
        if applied.body() != comp.sig() {
            self.error.get_or_insert_with(|| {
                format!("LocalPartial entry `{callee}` changed its source boundary signature")
            });
            return comp.clone();
        }
        TypedComp::new(
            applied.body().clone(),
            TypedCompKind::Call {
                callee: *callee,
                instantiation,
                args,
            },
        )
    }
}

fn instantiate_local_entry_calls(
    functions: &mut [TypedCoreFn],
    signatures: &BTreeMap<Sym, CoreFnSig>,
) -> Result<(), String> {
    let mut rewrite = LocalEntryCalls {
        signatures,
        error: None,
    };
    for function in functions {
        *function = rewrite.function(function, &());
    }
    rewrite.error.map_or(Ok(()), Err)
}

#[derive(Debug)]
pub struct LocalSplit<'a> {
    pub region: &'a BTreeSet<Sym>,
    pub entries: &'a BTreeSet<Sym>,
}

#[cfg(any(test, feature = "test-hooks"))]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LocalDeclinePoint {
    AfterRestFusion,
    AfterBoundaryAssembly,
}

#[cfg(any(test, feature = "test-hooks"))]
thread_local! {
    static LOCAL_DECLINE_POINT: Cell<Option<LocalDeclinePoint>> = const {
        Cell::new(None)
    };
}

#[cfg(any(test, feature = "test-hooks"))]
pub fn with_local_decline<T>(point: LocalDeclinePoint, run: impl FnOnce() -> T) -> T {
    struct Reset(Option<LocalDeclinePoint>);

    impl Drop for Reset {
        fn drop(&mut self) {
            LOCAL_DECLINE_POINT.set(self.0);
        }
    }

    let reset = Reset(LOCAL_DECLINE_POINT.replace(Some(point)));
    let result = run();
    drop(reset);
    result
}

#[cfg(any(test, feature = "test-hooks"))]
fn declines_at(point: LocalDeclinePoint) -> bool {
    LOCAL_DECLINE_POINT.get() == Some(point)
}

fn try_local_partial(
    fns: &[TypedCoreFn],
    env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
    analysis: &LoweringAnalysis<'_>,
    drift: &DriftLog,
    fresh: &mut prism_common::fresh::Fresh,
) -> Result<Option<Decision>, TypedCoreEffectLoweringFailure> {
    let Some((region, entries)) = analysis::local_region(fns, analysis.plan) else {
        return Ok(None);
    };
    if region.contains(&Sym::from(ENTRY_POINT)) {
        return Ok(None);
    }
    let rest: Vec<TypedCoreFn> = fns
        .iter()
        .filter(|function| !region.contains(&function.name()))
        .cloned()
        .collect();
    let fused = if let Some(fused) = evidence::try_lower_ev(
        &rest,
        analysis.latent(),
        analysis.flow(),
        analysis.ops,
        env,
        drift,
        fresh,
    ) {
        fused
    } else {
        let state_analysis =
            state::StateAnalysis::new(analysis.ops, analysis.latent(), analysis.flow(), env);
        let Some(plan) = state::fold_uniform(&rest, &state_analysis) else {
            return Ok(None);
        };
        if !state::threads(&plan, &rest, &state_analysis) {
            return Ok(None);
        }
        let Some(fused) = state::thread_program(&rest, &plan, &state_analysis, drift, fresh) else {
            return Ok(None);
        };
        fused
    };
    #[cfg(any(test, feature = "test-hooks"))]
    if declines_at(LocalDeclinePoint::AfterRestFusion) {
        return Ok(None);
    }
    let split = LocalSplit {
        region: &region,
        entries: &entries,
    };
    let Some(artifacts) = assemble_local_partial(fns, fused, env, ctors, analysis, &split, fresh)?
    else {
        return Ok(None);
    };
    #[cfg(any(test, feature = "test-hooks"))]
    if declines_at(LocalDeclinePoint::AfterBoundaryAssembly) {
        return Ok(None);
    }
    lowered(
        artifacts.fns,
        &artifacts.env,
        &artifacts.ctors,
        artifacts.warning,
        EffectStrategy::LocalPartial,
        None,
    )
    .map(Some)
}

/// Assemble the confined-region artifact: the lowered region, the fused rest
/// re-instantiated against the region's entry signatures, and the runtime the
/// pair needs installed.
///
/// # Errors
/// [`TypedCoreEffectLoweringFailure::Internal`] when the residual rows cannot
/// be planned, the region cannot be lowered, or a call across the split cannot
/// be re-instantiated at the entry's new signature.
pub fn assemble_local_partial(
    fns: &[TypedCoreFn],
    mut fused: Vec<TypedCoreFn>,
    env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
    analysis: &LoweringAnalysis<'_>,
    split: &LocalSplit<'_>,
    fresh: &mut prism_common::fresh::Fresh,
) -> Result<Option<LocalPartialArtifacts>, TypedCoreEffectLoweringFailure> {
    let rows = residual::plan(fns, analysis.ops, env)
        .map_err(|msg| TypedCoreEffectLoweringFailure::Internal { msg })?;
    let region_functions =
        monadic::lower_region(fns, split.region, split.entries, analysis.ops, fresh, &rows)
            .map_err(|decline| TypedCoreEffectLoweringFailure::Internal {
                msg: decline.to_string(),
            })?;
    let entry_signatures: BTreeMap<Sym, CoreFnSig> = region_functions
        .iter()
        .filter(|function| split.entries.contains(&function.name()))
        .map(|function| (function.name(), function.sig().clone()))
        .collect();
    instantiate_local_entry_calls(&mut fused, &entry_signatures)
        .map_err(|msg| TypedCoreEffectLoweringFailure::Internal { msg })?;
    let mut monadic_names = split.region.clone();
    monadic_names.extend(region_functions.iter().map(TypedCoreFn::name));
    fused.extend(region_functions);
    fused.push(abi::ebind_fn());
    fused.push(abi::qapply_fn());
    monadic_names.extend([Sym::from(EBIND), Sym::from(QAPPLY)]);
    let refs: Vec<&TypedCoreFn> = fused.iter().collect();
    if checks::check_convention_boundaries(
        &fused,
        &refs,
        &monadic_names,
        checks::ThunkRule::AllMonadic,
        split.entries,
    )
    .is_err()
    {
        return Ok(None);
    }

    let (lowered_env, lowered_ctors) = install_monadic_runtime(&fused, env, ctors, false);
    Ok(Some(LocalPartialArtifacts {
        fns: fused,
        env: lowered_env,
        ctors: lowered_ctors,
        warning: diagnostics::free_monad_warning(fns, split.region, analysis.plan, None),
    }))
}

/// Run the free-monad rungs of the cascade.
///
/// The confined attempt goes first (unless the tier floor rules it out), then
/// the whole-program one, which carries the confined refusal into its artifact
/// and its warning.
///
/// # Errors
/// [`TypedCoreEffectLoweringFailure::Internal`] when the whole-program builder
/// declines too, since nothing is left to widen to.
pub fn monadic_fallback(
    fns: &[TypedCoreFn],
    env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
    flags: &DynFlags,
    analysis: &LoweringAnalysis<'_>,
    fresh: &mut prism_common::fresh::Fresh,
) -> Result<Decision, TypedCoreEffectLoweringFailure> {
    monadic_fallback_with_options(
        fns,
        env,
        ctors,
        &EffectLowerOptions::from(flags),
        analysis,
        fresh,
    )
}

fn monadic_fallback_with_options(
    fns: &[TypedCoreFn],
    env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
    options: &EffectLowerOptions,
    analysis: &LoweringAnalysis<'_>,
    fresh: &mut prism_common::fresh::Fresh,
) -> Result<Decision, TypedCoreEffectLoweringFailure> {
    // Denying the selective rung widens the plan to the whole program, whether a
    // floor sits above it or the exclusion knob skips it. That direction is
    // always legal, which is why it is the forceable one: narrowing a program
    // whose handlers escape would not be a cost decision. Routing through
    // `rung_enabled` (not `admits` alone) is what makes excluding the selective
    // rung honest instead of a silent no-op; the whole-program terminal below it
    // is the one rung no knob can skip, so nothing here can strand a program.
    let force_whole = !options.rung_enabled(EffectStrategy::SelectiveFreeMonad);
    let mut declined = None;
    if !force_whole {
        // A confined region is an optimization, so failing to build one is a
        // cost outcome, not an error: the same program still has the
        // whole-program lowering below it. Everything the confined attempt
        // refuses (a direct force of a thunk the region owns, a convention
        // boundary that does not verify) is refused precisely because the
        // widened plan is the correct answer for it. The refusal is carried
        // into the widened attempt so the artifact and the warning can say
        // which shape cost the program its confined region.
        match attempt_monadic(fns, env, ctors, options, analysis, fresh, false, None)? {
            Ok(decision) => return Ok(decision),
            Err(refusal) => declined = Some(refusal),
        }
    }
    attempt_monadic(fns, env, ctors, options, analysis, fresh, true, declined)?.map_err(|refusal| {
        TypedCoreEffectLoweringFailure::Internal {
            msg: format!("typed free-monad builder declined at whole-program scope: {refusal}"),
        }
    })
}

/// One monadification attempt at the requested scope. `Ok(Err(_))` reports a
/// refusal the caller can answer by widening the plan; only a refusal at
/// whole-program scope, where nothing is left to widen to, is an error.
///
/// `declined` is the refusal an earlier, narrower attempt reported, threaded in
/// so the widened lowering can explain itself.
#[allow(clippy::too_many_arguments)]
fn attempt_monadic(
    fns: &[TypedCoreFn],
    env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
    options: &EffectLowerOptions,
    analysis: &LoweringAnalysis<'_>,
    fresh: &mut prism_common::fresh::Fresh,
    force_whole: bool,
    declined: Option<Decline>,
) -> Result<Attempt, TypedCoreEffectLoweringFailure> {
    let plan = analysis::plan(fns, analysis.plan, force_whole);
    // Named in the warning: every function that still performs an operation,
    // plus every one whose capture the thunk signatures could not describe,
    // which is the fact that widens the region. A capture the signatures do
    // describe is reached through instead of swallowed, so naming it would
    // report a cost the program does not pay.
    let mut warning_members = analysis.plan.genuine().clone();
    warning_members.extend(analysis.plan.opaque_captures().iter().copied());
    let warning = diagnostics::free_monad_warning(fns, &warning_members, analysis.plan, declined);
    let residual = residual::plan(fns, analysis.ops, env)
        .map_err(|msg| TypedCoreEffectLoweringFailure::Internal { msg })?;
    let whole = plan.scope == analysis::MonadicScope::WholeProgram;
    let output = match plan.scope {
        analysis::MonadicScope::Selective => monadic::lower_selective(
            fns,
            analysis.ops,
            fresh,
            &residual,
            &monadic::Region {
                plan: &plan,
                latent: analysis.latent(),
                flow: analysis.flow(),
                native_enabled: options.native_effects(),
            },
        ),
        analysis::MonadicScope::WholeProgram => {
            monadic::lower_whole(fns, analysis.ops, fresh, &residual)
        }
    };
    let mut output = match output {
        Ok(output) => output,
        Err(refusal) => return Ok(Err(refusal)),
    };
    output.push(abi::ebind_fn());
    output.push(abi::qapply_fn());

    let monadic_members = if whole {
        output.iter().map(TypedCoreFn::name).collect()
    } else {
        plan.members.clone()
    };
    let boundary_functions: Vec<&TypedCoreFn> = output.iter().collect();
    let rule = if whole {
        checks::ThunkRule::AllMonadic
    } else {
        checks::ThunkRule::PerThunk
    };
    if let Err(refusal) = checks::check_convention_boundaries(
        &output,
        &boundary_functions,
        &monadic_members,
        rule,
        &plan.entries,
    ) {
        // A confined region that does not verify is refused and rebuilt at
        // whole-program scope. At whole-program scope there is nothing left to
        // widen to, so the same failure is the compiler's own bug.
        if !whole {
            return Ok(Err(refusal));
        }
        return Err(TypedCoreEffectLoweringFailure::Internal {
            msg: format!("monadification: {refusal}"),
        });
    }

    if options.trampoline() && whole {
        output = trampoline::trampolinize(&output, fresh).ok_or_else(|| {
            TypedCoreEffectLoweringFailure::Internal {
                msg: "typed trampoline declined after free-monad boundary verification".into(),
            }
        })?;
        output.push(trampoline::prism_drive_fn());
    }

    let (lowered_env, lowered_ctors) =
        install_monadic_runtime(&output, env, ctors, options.trampoline() && whole);
    lowered(
        output,
        &lowered_env,
        &lowered_ctors,
        warning,
        if whole {
            EffectStrategy::WholeProgramFreeMonad
        } else {
            EffectStrategy::SelectiveFreeMonad
        },
        declined,
    )
    .map(Ok)
}

fn install_monadic_runtime(
    functions: &[TypedCoreFn],
    env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
    include_bounce: bool,
) -> (VerifyEnv, BTreeMap<String, CtorInfo>) {
    let mut lowered_env = env.clone();
    abi::insert(&mut lowered_env);
    let mut lowered_ctors = ctors.clone();
    for name in [EPURE, EOP, TQNIL, TQCONS] {
        assert!(add_synthetic_ctor(&mut lowered_ctors, name));
    }
    if functions_use_constructor(functions, ERESUME) {
        assert!(add_synthetic_ctor(&mut lowered_ctors, ERESUME));
    }
    if include_bounce {
        assert!(add_synthetic_ctor(&mut lowered_ctors, EBOUNCE));
    }
    install_step_runtime(functions, &mut lowered_env, &mut lowered_ctors);
    (lowered_env, lowered_ctors)
}

// State fusion can introduce the same early-exit protocol as control erasure,
// including when it is the fused half of LocalPartial. Keep the verifier and
// executable constructor tables in lockstep, and add the pair together whenever
// either constructor is live.
fn install_step_runtime(
    functions: &[TypedCoreFn],
    env: &mut VerifyEnv,
    ctors: &mut BTreeMap<String, CtorInfo>,
) {
    if functions_use_constructor(functions, SMORE) || functions_use_constructor(functions, SDONE) {
        erase_control::insert_step_constructors(env);
        for name in [SMORE, SDONE] {
            if !ctors.contains_key(name) {
                assert!(add_synthetic_ctor(ctors, name));
            }
        }
    }
}

#[must_use]
pub fn functions_use_constructor(functions: &[TypedCoreFn], wanted: &str) -> bool {
    let mut scan = ConstructorUse {
        wanted,
        found: false,
    };
    for function in functions {
        scan.walk_comp(function.body());
        if scan.found {
            break;
        }
    }
    scan.found
}

struct ConstructorUse<'a> {
    wanted: &'a str,
    found: bool,
}

impl Visit for ConstructorUse<'_> {
    fn comp(&mut self, _comp: &TypedComp) -> bool {
        !self.found
    }

    fn value(&mut self, value: &TypedValue) -> bool {
        if let TypedValueKind::Ctor { name, .. } = value.kind() {
            self.found = name.as_str() == self.wanted;
        }
        !self.found
    }

    fn pattern(&mut self, pattern: &TypedPattern) {
        if let TypedPattern::Ctor { name, .. } = pattern {
            self.found = name.as_str() == self.wanted;
        }
    }
}

// Verify the built program, then stamp the phase marker. The marker is never
// forged around an unverified tree.
fn lowered(
    fns: Vec<TypedCoreFn>,
    env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
    warning: Option<String>,
    strategy: EffectStrategy,
    confined_decline: Option<Decline>,
) -> Result<Decision, TypedCoreEffectLoweringFailure> {
    let out = verify(UncheckedTypedCore::<EffectLowered>::new(fns), env)
        .map_err(|violations| verification_failure(&violations))?;
    Ok(Decision::Lowered(Box::new(TypedLowering {
        core: out,
        env: env.clone(),
        ctors: ctors.clone(),
        warning,
        strategy,
        confined_decline,
    })))
}

// The functions reachable from the entry point, over direct calls and
// first-class references to top-level names.
fn reachable(fns: &[TypedCoreFn]) -> BTreeSet<Sym> {
    let map: BTreeMap<Sym, &TypedCoreFn> = fns.iter().map(|f| (f.name(), f)).collect();
    let mut visited: BTreeSet<Sym> = BTreeSet::new();
    let mut queue = vec![Sym::new(ENTRY_POINT)];
    while let Some(name) = queue.pop() {
        if visited.contains(&name) {
            continue;
        }
        visited.insert(name);
        if let Some(f) = map.get(&name) {
            queue.extend(calls_in(f.body()));
            queue.extend(
                free_comp_vars(f.body())
                    .into_iter()
                    .filter(|n| map.contains_key(n)),
            );
        }
    }
    visited
}

// A value looked through any Reinterpret/NewtypeRepr wrapper. Rewrites keep the
// original wrapped value.
#[must_use]
pub fn peel(mut value: &TypedValue) -> &TypedValue {
    loop {
        match &value.kind {
            TypedValueKind::Reinterpret(inner)
            | TypedValueKind::NewtypeRepr { value: inner, .. } => value = inner,
            _ => return value,
        }
    }
}

// The variable a value names once representation wrappers are peeled.
#[must_use]
pub fn as_var(value: &TypedValue) -> Option<Sym> {
    match &peel(value).kind {
        TypedValueKind::Var { name, .. } => Some(*name),
        _ => None,
    }
}

#[must_use]
pub fn binder_var(binder: &TypedBinder) -> TypedValue {
    TypedValue::new(
        binder.ty().clone(),
        TypedValueKind::Var {
            name: binder.name(),
            instantiation: Vec::new(),
        },
    )
}

#[must_use]
pub const fn unit_value() -> TypedValue {
    TypedValue::new(CoreType::Source(Type::Unit), TypedValueKind::Unit)
}

// Test-only bridge for sibling typed passes that must prove they remain
// transparent to the phase-private representation wrapper without widening
// production construction authority.
#[cfg(any(test, feature = "test-hooks"))]
#[must_use]
pub fn test_lowered_repr(value: TypedValue, ty: CoreType) -> TypedValue {
    abi::lowered_repr(value, ty)
}

// The verified row union for rebuilt sigs. Everything the erasures rebuild
// carries compatible rows, so a `union_rows` failure is an internal invariant
// violation unreachable on well-typed input, never a real program.
//
// It must not be a release panic: the erasures run on every rung including the
// terminal free-monad fallback, and a crash there is maximally observable,
// exactly the tier-dependence the determinism contract forbids. So on the
// unreachable failure path we widen to the multiset union of both children's
// rows (keeping every effect at its per-label MAX multiplicity, never discarding
// or collapsing one child's) under the left tail, which is byte-identical to
// `union_rows` on every valid program because that path is never taken there.
// The `debug_assert!` keeps the invariant loud in development and tests; the
// loud release-mode teeth are the verifier's strict `row_included`, which runs
// in the release cold gate and rejects any row whose multiplicity a producer got
// wrong, so the honest failure is gate-visible without a tier-observable crash.
#[must_use]
pub fn union_effects(left: &EffRow, right: &EffRow) -> EffRow {
    match union_rows(left, right) {
        Ok(row) => row,
        Err(error) => {
            debug_assert!(
                false,
                "typed effect-lowering row union invariant: {error}; left={}, right={}",
                left.show(),
                right.show()
            );
            widen_union(left, right)
        }
    }
}

// The total, conservative row widening `union_effects` degrades to when its
// exact union declines: the multiset union of both rows (per-label MAX
// multiplicity, the more-applied label winning an args clash, matching
// `union_rows`) under the left tail. Never discards an effect and never
// collapses a repeat; only reachable on already-broken input.
fn widen_union(left: &EffRow, right: &EffRow) -> EffRow {
    // Per name: the more-applied label plus each side's occurrence count.
    let mut names: BTreeMap<Sym, (Label, usize, usize)> = BTreeMap::new();
    for (label, is_left) in left
        .labels()
        .into_iter()
        .map(|l| (l, true))
        .chain(right.labels().into_iter().map(|l| (l, false)))
    {
        match names.get_mut(&label.name) {
            Some((existing, cl, cr)) => {
                if existing.args.is_empty() && !label.args.is_empty() {
                    existing.args.clone_from(&label.args);
                }
                *(if is_left { cl } else { cr }) += 1;
            }
            None => {
                names.insert(
                    label.name,
                    (label.clone(), usize::from(is_left), usize::from(!is_left)),
                );
            }
        }
    }
    let mut out: Vec<Label> = Vec::new();
    for (label, cl, cr) in names.into_values() {
        for _ in 0..cl.max(cr) {
            out.push(label.clone());
        }
    }
    EffRow::canonical(out, left.tail().clone())
}
