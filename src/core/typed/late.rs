//! Ordered optimizer execution over effect-lowered typed Core.
//!
//! The caller supplies the exact pass sequence. Every occurrence is retained,
//! checked at both boundaries, and recorded independently so repeated passes
//! remain observable to compatibility checks.

use crate::core::opt::CorePass;
use crate::error::TypedCoreSimplifyFailure;

use super::cse::cse;
use super::inline::inline;
use super::simplify::simplify;
use super::verify::{verify, CoreViolation, VerifyEnv};
use super::{EffectLowered, TypedCore};

/// One optimizer occurrence and its rewrite count.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct LatePassStats {
    pass: CorePass,
    ticks: u64,
}

#[cfg(test)]
impl LatePassStats {
    /// The pass run at this position.
    pub(crate) const fn pass(self) -> CorePass {
        self.pass
    }

    /// Rewrites fired by this occurrence only.
    pub(crate) const fn ticks(self) -> u64 {
        self.ticks
    }
}

/// Ordered rewrite counts for one late optimizer run.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct LateStats {
    entries: Vec<LatePassStats>,
}

#[cfg(test)]
impl LateStats {
    /// One entry per supplied occurrence, in the supplied order.
    pub(crate) fn entries(&self) -> &[LatePassStats] {
        &self.entries
    }

    /// Rewrites fired across all occurrences.
    pub(crate) fn total(&self) -> u64 {
        self.entries.iter().map(|entry| entry.ticks).sum()
    }
}

/// The verifier boundary at which execution stopped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LateVerificationPoint {
    /// The empty sequence still checks that its returned artifact is valid.
    EmptyInput,
    /// Immediately before one pass occurrence.
    Before { occurrence: usize, pass: CorePass },
    /// Immediately after one pass occurrence.
    After { occurrence: usize, pass: CorePass },
}

/// A structural refusal from the ordered late optimizer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum LateExecutorFailure {
    /// The sequence contains a pass this executor does not own.
    UnsupportedPass { occurrence: usize, pass: CorePass },
    /// A typed artifact failed proof checking at a named boundary.
    Verification {
        point: LateVerificationPoint,
        violations: Vec<CoreViolation>,
    },
    /// Fixed-point simplification exceeded its convergence bound.
    Simplify {
        occurrence: usize,
        failure: TypedCoreSimplifyFailure,
    },
}

/// Run an exact ordered sequence of post-lowering typed optimizations.
///
/// No pass is filtered, de-duplicated, or inferred from an optimization level.
/// The returned ledger therefore has exactly one entry for every supplied pass.
pub(crate) fn execute(
    mut core: TypedCore<EffectLowered>,
    env: &VerifyEnv,
    passes: &[CorePass],
) -> Result<(TypedCore<EffectLowered>, LateStats), LateExecutorFailure> {
    for (occurrence, &pass) in passes.iter().enumerate() {
        if !matches!(pass, CorePass::Simplify | CorePass::Inline | CorePass::Cse) {
            return Err(LateExecutorFailure::UnsupportedPass { occurrence, pass });
        }
    }

    if passes.is_empty() {
        verify(&core, env).map_err(|violations| LateExecutorFailure::Verification {
            point: LateVerificationPoint::EmptyInput,
            violations,
        })?;
    }

    let mut entries = Vec::with_capacity(passes.len());
    for (occurrence, &pass) in passes.iter().enumerate() {
        verify(&core, env).map_err(|violations| LateExecutorFailure::Verification {
            point: LateVerificationPoint::Before { occurrence, pass },
            violations,
        })?;

        let (next, ticks) = match pass {
            CorePass::Simplify => {
                let (next, stats) =
                    simplify(core).map_err(|failure| LateExecutorFailure::Simplify {
                        occurrence,
                        failure,
                    })?;
                (next, stats.ticks())
            }
            CorePass::Inline => {
                let (next, stats) = inline(core);
                (next, stats.ticks())
            }
            CorePass::Cse => {
                let (next, stats) = cse(core);
                (next, stats.ticks())
            }
            CorePass::Fuse | CorePass::EraseNewtypes | CorePass::Specialize => {
                unreachable!("the ordered pass sequence was validated before execution")
            }
        };

        verify(&next, env).map_err(|violations| LateExecutorFailure::Verification {
            point: LateVerificationPoint::After { occurrence, pass },
            violations,
        })?;
        core = next;
        entries.push(LatePassStats { pass, ticks });
    }

    Ok((core, LateStats { entries }))
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use crate::core::opt::{pipeline, run_spec_stage, OptLevel, PassStage};
    use crate::core::CoreOp;
    use crate::core::{EffectStrategy, OpGrades};
    use crate::flags::{DynFlags, EffectTier};
    use crate::sym::Sym;
    use crate::types::ty::{EffRow, Label};
    use crate::types::Type;

    use super::super::effect_lower::{lower_effects, TypedLowering};
    use super::super::verify::OperationSig;
    use super::super::{
        CompSig, CoreFnSig, CoreType, Elaborated, TypedBinder, TypedComp, TypedCompKind,
        TypedCoreFn, TypedValue, TypedValueKind,
    };
    use super::*;

    fn sym(name: &str) -> Sym {
        Sym::new(name)
    }

    fn source(ty: Type) -> CoreType {
        CoreType::Source(ty)
    }

    fn pure(result: CoreType) -> CompSig {
        CompSig::new(result, EffRow::Empty)
    }

    fn var(name: &str) -> TypedValue {
        TypedValue::new(
            source(Type::Int),
            TypedValueKind::Var {
                name: sym(name),
                instantiation: Vec::new(),
            },
        )
    }

    fn int(value: i64) -> TypedValue {
        TypedValue::new(source(Type::Int), TypedValueKind::Int(value))
    }

    fn ret(value: TypedValue) -> TypedComp {
        TypedComp::new(pure(value.ty.clone()), TypedCompKind::Return(value))
    }

    fn prim(op: CoreOp, left: TypedValue, right: TypedValue) -> TypedComp {
        TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Prim(op, left, right),
        )
    }

    fn production_lowered_fixture() -> (TypedCore<EffectLowered>, VerifyEnv) {
        let operation = sym("ask");
        let effect = sym("Ask");
        let mut env = VerifyEnv::new();
        env.insert_operation(
            operation,
            OperationSig::new(
                Vec::new(),
                Vec::new(),
                source(Type::Int),
                Label::bare(effect),
            ),
        );

        let repeated_product = || prim(CoreOp::Mul, var("n"), var("n"));
        let kernel_body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(repeated_product()),
                TypedBinder::new(sym("p"), source(Type::Int)),
                Box::new(TypedComp::new(
                    pure(source(Type::Int)),
                    TypedCompKind::Bind(
                        Box::new(repeated_product()),
                        TypedBinder::new(sym("q"), source(Type::Int)),
                        Box::new(prim(CoreOp::Add, var("p"), var("q"))),
                    ),
                )),
            ),
        );
        let kernel = TypedCoreFn::new(
            sym("kernel"),
            vec![TypedBinder::new(sym("n"), source(Type::Int))],
            kernel_body,
            CoreFnSig::new(Vec::new(), vec![source(Type::Int)], pure(source(Type::Int))),
            0,
        );

        let wrapper_body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(ret(var("value"))),
                TypedBinder::new(sym("copy"), source(Type::Int)),
                Box::new(TypedComp::new(
                    pure(source(Type::Int)),
                    TypedCompKind::Call {
                        callee: sym("kernel"),
                        instantiation: Vec::new(),
                        args: vec![var("copy")],
                    },
                )),
            ),
        );
        let wrapper = TypedCoreFn::new(
            sym("wrapper"),
            vec![TypedBinder::new(sym("value"), source(Type::Int))],
            wrapper_body,
            CoreFnSig::new(Vec::new(), vec![source(Type::Int)], pure(source(Type::Int))),
            0,
        );

        let effects = EffRow::singleton(effect);
        let performed = TypedComp::new(
            CompSig::new(source(Type::Int), effects.clone()),
            TypedCompKind::Do {
                operation,
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let continuation = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(ret(var("performed_answer"))),
                TypedBinder::new(sym("answer"), source(Type::Int)),
                Box::new(TypedComp::new(
                    pure(source(Type::Int)),
                    TypedCompKind::Call {
                        callee: sym("wrapper"),
                        instantiation: Vec::new(),
                        args: vec![var("answer")],
                    },
                )),
            ),
        );
        let main_body = TypedComp::new(
            CompSig::new(source(Type::Int), effects.clone()),
            TypedCompKind::Bind(
                Box::new(performed),
                TypedBinder::new(sym("performed_answer"), source(Type::Int)),
                Box::new(continuation),
            ),
        );
        let main = TypedCoreFn::new(
            sym("main"),
            Vec::new(),
            main_body,
            CoreFnSig::new(
                Vec::new(),
                Vec::new(),
                CompSig::new(source(Type::Int), effects),
            ),
            0,
        );

        let input = TypedCore::<Elaborated>::new(vec![kernel, wrapper, main]);
        assert_eq!(verify(&input, &env), Ok(()));
        let flags = DynFlags {
            effect_tier: EffectTier::FreeMonad,
            quiet: true,
            ..DynFlags::default()
        };
        let TypedLowering {
            core,
            env,
            ctors,
            warning: _,
            strategy,
        } = lower_effects(input, &env, &BTreeMap::new(), &flags, &OpGrades::new())
            .expect("fixture lowers through the production effect path");
        assert_eq!(strategy, EffectStrategy::SelectiveFreeMonad);
        assert!(ctors.contains_key("EOp"));
        assert!(crate::core::pretty::pp_core(&core.clone().erase()).contains("EOp"));
        assert_eq!(verify(&core, &env), Ok(()));
        (core, env)
    }

    fn late_passes(level: OptLevel) -> Vec<CorePass> {
        pipeline(level)
            .into_iter()
            .filter(|pass| pass.stage() == PassStage::Late)
            .collect()
    }

    fn assert_ordered_differential(level: OptLevel) -> LateStats {
        let passes = late_passes(level);
        let (input, env) = production_lowered_fixture();
        let legacy_input = input.clone().erase();
        let (expected, legacy_stats) = run_spec_stage(
            &legacy_input,
            &BTreeSet::new(),
            &passes,
            PassStage::Late,
            &[],
            &DynFlags::default(),
        );

        let (actual, stats) = execute(input, &env, &passes).expect("ordered typed execution");
        assert_eq!(verify(&actual, &env), Ok(()));
        assert_eq!(actual.erase(), expected);
        assert_eq!(stats.entries().len(), passes.len());
        assert_eq!(
            stats
                .entries()
                .iter()
                .map(|entry| entry.pass())
                .collect::<Vec<_>>(),
            passes
        );
        assert_eq!(
            stats
                .entries()
                .iter()
                .map(|entry| (entry.pass().name(), entry.ticks()))
                .collect::<Vec<_>>(),
            legacy_stats.entries()
        );
        assert_eq!(stats.total(), legacy_stats.total());
        stats
    }

    #[test]
    fn default_order_preserves_every_repeated_occurrence() {
        let stats = assert_ordered_differential(OptLevel::O1);
        assert_eq!(
            stats
                .entries()
                .iter()
                .filter(|entry| entry.pass() == CorePass::Simplify)
                .count(),
            3
        );
        assert!(
            stats
                .entries()
                .iter()
                .find(|entry| entry.pass() == CorePass::Inline)
                .expect("default sequence contains Inline")
                .ticks()
                > 0
        );
        assert!(
            stats
                .entries()
                .iter()
                .find(|entry| entry.pass() == CorePass::Cse)
                .expect("default sequence contains Cse")
                .ticks()
                > 0
        );
    }

    #[test]
    fn extended_order_retains_both_inline_occurrences() {
        let stats = assert_ordered_differential(OptLevel::O2);
        assert_eq!(
            stats
                .entries()
                .iter()
                .filter(|entry| entry.pass() == CorePass::Inline)
                .count(),
            2
        );
        assert_eq!(
            stats
                .entries()
                .iter()
                .filter(|entry| entry.pass() == CorePass::Simplify)
                .count(),
            4
        );
    }

    #[test]
    fn rejects_a_pre_lowering_pass_at_its_exact_occurrence() {
        let (input, env) = production_lowered_fixture();
        let error = execute(input, &env, &[CorePass::Simplify, CorePass::EraseNewtypes])
            .expect_err("a pre-lowering pass is not silently skipped");
        assert!(matches!(
            error,
            LateExecutorFailure::UnsupportedPass {
                occurrence: 1,
                pass: CorePass::EraseNewtypes,
            }
        ));
    }

    #[test]
    fn rejects_an_invalid_input_before_the_first_occurrence() {
        let effect = sym("StillSource");
        let body = TypedComp::new(
            CompSig::new(source(Type::Int), EffRow::singleton(effect)),
            TypedCompKind::Do {
                operation: sym("still_source"),
                instantiation: Vec::new(),
                args: vec![int(0)],
            },
        );
        let core = TypedCore::<EffectLowered>::new(vec![TypedCoreFn::new(
            sym("main"),
            Vec::new(),
            body.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone()),
            0,
        )]);
        let error = execute(core, &VerifyEnv::new(), &[CorePass::Simplify])
            .expect_err("source effect syntax is illegal after lowering");
        assert!(matches!(
            error,
            LateExecutorFailure::Verification {
                point: LateVerificationPoint::Before {
                    occurrence: 0,
                    pass: CorePass::Simplify,
                },
                ..
            }
        ));
    }
}
