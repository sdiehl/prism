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
use crate::core::{EffectStrategy, OpGrades};
use crate::flags::DynFlags;
use crate::types::ty::{EffRow, Label};
use crate::types::{CtorInfo, Type};
use prism_common::sym::Sym;
use prism_syntax::error::TypedCoreEffectLoweringFailure;
use prism_syntax::names::ENTRY_POINT;

use super::inline::calls_in;
use super::specialize_support::{free_comp_vars, Rewrite};
use super::verify::{instantiate_fn, union_rows, VerifyEnv};
use super::{
    verify, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, EffectLowered, Elaborated,
    TypedBinder, TypedComp, TypedCompKind, TypedCore, TypedCoreFn, TypedPattern, TypedValue,
    TypedValueKind, UncheckedTypedCore,
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
    pub core: TypedCore<EffectLowered>,
    pub env: VerifyEnv,
    pub ctors: BTreeMap<String, CtorInfo>,
    pub warning: Option<String>,
    pub strategy: EffectStrategy,
    /// Why a confined region was refused before this strategy was taken, when
    /// one was attempted and refused. The plan artifact renders it, so a tier
    /// nobody expected can be read back to the shape that caused it.
    pub confined_decline: Option<Decline>,
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
    match cascade(core, env, ctors, flags, grades)? {
        Decision::Lowered(lowering) => Ok(*lowering),
    }
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
    Ok(match cascade(core, env, ctors, flags, grades)? {
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
    pub fns: Vec<TypedCoreFn>,
    pub env: VerifyEnv,
    pub ctors: BTreeMap<String, CtorInfo>,
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
    let (fns, used_step) = if flags.erasures {
        let vars_gone = erase_var::erase_local_vars(&fns, grades, &EffectPlan::analyze(&fns), &env);
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
    let prepared = prepare(core, env, ctors, flags, grades)?;
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
        &DriftLog::new(flags.quiet),
        &mut fresh,
    ) else {
        return Ok(None);
    };
    verify(UncheckedTypedCore::<EffectLowered>::new(fns), &env)
        .map(|core| Some((core, env)))
        .map_err(|violations| TypedCoreEffectLoweringFailure::Verification {
            first: violations
                .first()
                .map_or_else(String::new, ToString::to_string),
            count: violations.len(),
        })
}

fn cascade(
    core: TypedCore<Elaborated>,
    env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
    flags: &DynFlags,
    grades: &OpGrades,
) -> Result<Decision, TypedCoreEffectLoweringFailure> {
    let prepared = prepare(core, env, ctors, flags, grades)?;
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
    let drift = DriftLog::new(flags.quiet);
    let mut fresh = prism_common::fresh::Fresh::new();
    if flags.effect_tier.admits(EffectStrategy::Evidence) {
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
    if flags.effect_tier.admits(EffectStrategy::StateFusion) {
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
    if flags.effect_tier.admits(EffectStrategy::LocalPartial) {
        if let Some(local) = try_local_partial(&fns, env, ctors, &analysis, &drift, &mut fresh)? {
            return Ok(local);
        }
    }

    // A LocalPartial rest or boundary that honestly declined takes the ordinary
    // selective/whole free-monad fallback. The one cascade-owned fresh supply
    // retains every name consumed by that attempt, matching the executable
    // pass's late-decline behavior.
    monadic_fallback(&fns, env, ctors, flags, &analysis, &mut fresh)
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
    // A floor above the selective rung widens the plan to the whole program.
    // That direction is always legal, which is why it is the forceable one:
    // narrowing a program whose handlers escape would not be a cost decision.
    let force_whole = !flags.effect_tier.admits(EffectStrategy::SelectiveFreeMonad);
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
        match attempt_monadic(fns, env, ctors, flags, analysis, fresh, false, None)? {
            Ok(decision) => return Ok(decision),
            Err(refusal) => declined = Some(refusal),
        }
    }
    attempt_monadic(fns, env, ctors, flags, analysis, fresh, true, declined)?.map_err(|refusal| {
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
    flags: &DynFlags,
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
                native_enabled: flags.native_effects,
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

    if flags.trampoline && whole {
        output = trampoline::trampolinize(&output, fresh).ok_or_else(|| {
            TypedCoreEffectLoweringFailure::Internal {
                msg: "typed trampoline declined after free-monad boundary verification".into(),
            }
        })?;
        output.push(trampoline::prism_drive_fn());
    }

    let (lowered_env, lowered_ctors) =
        install_monadic_runtime(&output, env, ctors, flags.trampoline && whole);
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
    functions
        .iter()
        .any(|function| comp_uses_constructor(function.body(), wanted))
}

fn comp_uses_constructor(comp: &TypedComp, wanted: &str) -> bool {
    let mut found = false;
    walk::each_value(comp, &mut |value| {
        found |= value_uses_constructor(value, wanted);
    });
    if let TypedCompKind::Case(_, arms) = comp.kind() {
        found |= arms.iter().any(|(pattern, _)| {
            matches!(pattern, TypedPattern::Ctor { name, .. } if name.as_str() == wanted)
        });
    }
    walk::each_subcomp(comp, &mut |child| {
        found |= comp_uses_constructor(child, wanted);
    });
    found
}

fn value_uses_constructor(value: &TypedValue, wanted: &str) -> bool {
    match &value.kind {
        TypedValueKind::Ctor { name, fields, .. } => {
            name.as_str() == wanted
                || fields
                    .iter()
                    .any(|field| value_uses_constructor(field, wanted))
        }
        TypedValueKind::Thunk(body) => comp_uses_constructor(body, wanted),
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr { value: inner, .. }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => value_uses_constructor(inner, wanted),
        TypedValueKind::Tuple(fields) | TypedValueKind::UnboxedTuple(fields) => fields
            .iter()
            .any(|field| value_uses_constructor(field, wanted)),
        TypedValueKind::UnboxedRecord(fields) => fields
            .iter()
            .any(|(_, field)| value_uses_constructor(field, wanted)),
        TypedValueKind::Var { .. }
        | TypedValueKind::Unit
        | TypedValueKind::Int(_)
        | TypedValueKind::I64(_)
        | TypedValueKind::U64(_)
        | TypedValueKind::Bool(_)
        | TypedValueKind::Float(_)
        | TypedValueKind::Str(_) => false,
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
    let out = verify(UncheckedTypedCore::<EffectLowered>::new(fns), env).map_err(|violations| {
        TypedCoreEffectLoweringFailure::Verification {
            first: violations
                .first()
                .map_or_else(String::new, ToString::to_string),
            count: violations.len(),
        }
    })?;
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
pub fn peel(value: &TypedValue) -> &TypedValue {
    match &value.kind {
        TypedValueKind::Reinterpret(inner) | TypedValueKind::NewtypeRepr { value: inner, .. } => {
            peel(inner)
        }
        _ => value,
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
// unreachable failure path we widen to the union of both children's label sets
// (keeping every effect, never discarding one child's) under the left tail,
// which is byte-identical to `union_rows` on every valid program because that
// path is never taken there. The `debug_assert!` keeps the invariant loud in
// development and tests.
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
// exact union declines: the union of both label sets (the more-applied label
// wins a name clash, matching `union_rows`) under the left tail. Never discards
// an effect; only reachable on already-broken input.
fn widen_union(left: &EffRow, right: &EffRow) -> EffRow {
    let mut labels: BTreeMap<Sym, Label> = BTreeMap::new();
    for label in left.labels().into_iter().chain(right.labels()) {
        match labels.get(&label.name) {
            Some(existing) if !existing.args.is_empty() => {}
            _ => {
                labels.insert(label.name, label.clone());
            }
        }
    }
    EffRow::canonical(labels.into_values(), left.tail().clone())
}
