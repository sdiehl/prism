//! Ordered optimizer execution over elaborated typed Core.
//!
//! The caller supplies the exact pre-lowering pass sequence together with the
//! constructor facts already established by elaboration. Every occurrence is
//! retained, checked at both boundaries, and recorded independently.

use std::collections::BTreeSet;

use crate::core::opt::CorePass;
use crate::error::TypedCoreSpecializationFailure;
use crate::sym::Sym;

use super::fuse::fuse;
use super::newtypes::erase_newtypes;
use super::specialize::specialize;
use super::verify::{verify, CoreViolation, VerifyEnv};
use super::{Elaborated, TypedCore};

/// One optimizer occurrence and its rewrite count.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PrePassStats {
    pass: CorePass,
    ticks: u64,
}

#[cfg(test)]
impl PrePassStats {
    /// The pass run at this position.
    pub(crate) const fn pass(self) -> CorePass {
        self.pass
    }

    /// Rewrites fired by this occurrence only.
    pub(crate) const fn ticks(self) -> u64 {
        self.ticks
    }
}

/// Ordered rewrite counts for one pre-lowering optimizer run.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct PreStats {
    entries: Vec<PrePassStats>,
}

#[cfg(test)]
impl PreStats {
    /// One entry per supplied occurrence, in the supplied order.
    pub(crate) fn entries(&self) -> &[PrePassStats] {
        &self.entries
    }

    /// Rewrites fired across all occurrences.
    pub(crate) fn total(&self) -> u64 {
        self.entries.iter().map(|entry| entry.ticks).sum()
    }
}

/// The verifier boundary at which execution stopped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PreVerificationPoint {
    /// The empty sequence still checks that its returned artifact is valid.
    EmptyInput,
    /// Immediately before one pass occurrence.
    Before { occurrence: usize, pass: CorePass },
    /// Immediately after one pass occurrence.
    After { occurrence: usize, pass: CorePass },
}

/// A structural refusal from the ordered pre-lowering optimizer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum PreExecutorFailure {
    /// The sequence contains a pass this executor does not own.
    UnsupportedPass { occurrence: usize, pass: CorePass },
    /// A typed artifact failed proof checking at a named boundary.
    Verification {
        point: PreVerificationPoint,
        violations: Vec<CoreViolation>,
    },
    /// Dictionary specialization could not preserve a declared scheme.
    Specialize {
        occurrence: usize,
        failure: TypedCoreSpecializationFailure,
    },
}

/// Run an exact ordered sequence of pre-lowering typed optimizations.
///
/// No pass is filtered, de-duplicated, or inferred from an optimization level.
/// Newtype and verification facts are borrowed from elaboration and are never
/// reconstructed from the transformed term.
pub(crate) fn execute(
    mut core: TypedCore<Elaborated>,
    env: &VerifyEnv,
    newtype_ctors: &BTreeSet<Sym>,
    passes: &[CorePass],
) -> Result<(TypedCore<Elaborated>, PreStats), PreExecutorFailure> {
    for (occurrence, &pass) in passes.iter().enumerate() {
        if !matches!(
            pass,
            CorePass::Fuse | CorePass::EraseNewtypes | CorePass::Specialize
        ) {
            return Err(PreExecutorFailure::UnsupportedPass { occurrence, pass });
        }
    }

    if passes.is_empty() {
        verify(&core, env).map_err(|violations| PreExecutorFailure::Verification {
            point: PreVerificationPoint::EmptyInput,
            violations,
        })?;
    }

    let mut entries = Vec::with_capacity(passes.len());
    for (occurrence, &pass) in passes.iter().enumerate() {
        verify(&core, env).map_err(|violations| PreExecutorFailure::Verification {
            point: PreVerificationPoint::Before { occurrence, pass },
            violations,
        })?;

        let (next, ticks) = match pass {
            CorePass::Fuse => {
                let (next, stats) = fuse(core);
                (next, stats.ticks())
            }
            CorePass::EraseNewtypes => {
                let (next, stats) = erase_newtypes(core, newtype_ctors, env);
                (next, stats.ticks())
            }
            CorePass::Specialize => {
                let (next, stats) =
                    specialize(core).map_err(|failure| PreExecutorFailure::Specialize {
                        occurrence,
                        failure,
                    })?;
                (next, stats.ticks())
            }
            CorePass::Simplify | CorePass::Inline | CorePass::Cse => {
                unreachable!("the ordered pass sequence was validated before execution")
            }
        };

        verify(&next, env).map_err(|violations| PreExecutorFailure::Verification {
            point: PreVerificationPoint::After { occurrence, pass },
            violations,
        })?;
        core = next;
        entries.push(PrePassStats { pass, ticks });
    }

    Ok((core, PreStats { entries }))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::core::opt::{run_spec_stage, PassStage};
    use crate::flags::DynFlags;
    use crate::resolve::Root;
    use crate::stdlib::STDLIB;
    use crate::types::ty::EffRow;
    use crate::types::Type;

    use super::super::{
        CompSig, CoreFnSig, CoreType, TypedComp, TypedCompKind, TypedCoreFn, TypedValue,
        TypedValueKind,
    };
    use super::*;

    const FUSION_SOURCE: &str = r"
import Sequence as Seq

fn main() : Unit ! {IO} =
  println(Seq.product(Seq.map(Seq.range(1, 7), \(x) -> x + 1)))
";

    const NEWTYPE_SPECIALIZATION_SOURCE: &str = r"
newtype Wrap = Wrap(Int)

class Score(a)
  score : (a) -> Int

instance scoreWrap : Score(Wrap)
  fn score(w) =
    match w of
      Wrap(n) => n

fn total(x : a) : Int given Score(a) = score(x)

fn main() : Unit ! {IO} = println(total(Wrap(42)))
";

    fn production_elaborated_fixture(
        source: &str,
    ) -> (TypedCore<Elaborated>, VerifyEnv, BTreeSet<Sym>) {
        let full = crate::driver::with_prelude(source);
        let parsed = crate::parse::parse(&full).expect("fixture parses").program;
        let roots = [Root::Embedded(STDLIB)];
        let resolved = crate::resolve::resolve_modules_in(parsed, &roots)
            .expect("fixture resolves through embedded modules");
        let program = crate::syntax::desugar::desugar(resolved).expect("fixture desugars");
        let checked = crate::types::check(&program).expect("fixture typechecks");
        let newtypes = crate::core::newtype_ctors(&program);
        let elaboration = crate::core::elaborate_typed(&program, &checked)
            .expect("fixture reaches typed elaboration");
        let (compatibility, typed, env) = elaboration.into_parts();
        assert_eq!(verify(&typed, &env), Ok(()));
        assert_eq!(typed.clone().erase(), compatibility);
        (typed, env, newtypes)
    }

    fn assert_ordered_differential(source: &str, passes: &[CorePass]) -> PreStats {
        let (input, env, newtypes) = production_elaborated_fixture(source);
        let legacy_input = input.clone().erase();
        let (expected, legacy_stats) = run_spec_stage(
            &legacy_input,
            &newtypes,
            passes,
            PassStage::PreLowering,
            &[],
            &DynFlags::default(),
        );

        let (actual, stats) =
            execute(input, &env, &newtypes, passes).expect("ordered typed pre-lowering execution");
        assert_eq!(verify(&actual, &env), Ok(()));
        assert_eq!(actual.erase(), expected);
        assert_eq!(stats.entries().len(), passes.len());
        assert_eq!(
            stats
                .entries()
                .iter()
                .map(|entry| entry.pass())
                .collect::<Vec<_>>(),
            passes.to_vec()
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
    fn production_fusion_retains_repeated_occurrences() {
        let stats = assert_ordered_differential(
            FUSION_SOURCE,
            &[CorePass::Fuse, CorePass::Fuse, CorePass::Fuse],
        );
        assert_eq!(stats.entries().len(), 3);
        assert!(stats.entries()[0].ticks() > 0, "the first Fuse must fire");
    }

    #[test]
    fn production_newtype_and_specialization_repeats_stay_positional() {
        let stats = assert_ordered_differential(
            NEWTYPE_SPECIALIZATION_SOURCE,
            &[
                CorePass::EraseNewtypes,
                CorePass::Specialize,
                CorePass::EraseNewtypes,
                CorePass::Specialize,
            ],
        );
        assert!(
            stats.entries()[0].ticks() > 0,
            "the source newtype must erase"
        );
        assert!(
            stats.entries()[1].ticks() > 0,
            "the concrete dictionary call must specialize"
        );
    }

    #[test]
    fn rejects_a_late_pass_at_its_exact_occurrence() {
        let (input, env, newtypes) = production_elaborated_fixture(NEWTYPE_SPECIALIZATION_SOURCE);
        let error = execute(
            input,
            &env,
            &newtypes,
            &[CorePass::EraseNewtypes, CorePass::Simplify],
        )
        .expect_err("a late pass is not silently skipped");
        assert!(matches!(
            error,
            PreExecutorFailure::UnsupportedPass {
                occurrence: 1,
                pass: CorePass::Simplify,
            }
        ));
    }

    #[test]
    fn rejects_an_invalid_input_before_the_first_occurrence() {
        let int = CoreType::Source(Type::Int);
        let body = TypedComp::new(
            CompSig::new(int.clone(), EffRow::Empty),
            TypedCompKind::Return(TypedValue::new(int, TypedValueKind::Int(1))),
        );
        let core = TypedCore::<Elaborated>::new(vec![TypedCoreFn::new(
            Sym::new("main"),
            Vec::new(),
            body,
            CoreFnSig::new(
                Vec::new(),
                Vec::new(),
                CompSig::new(CoreType::Source(Type::Bool), EffRow::Empty),
            ),
            0,
        )]);
        let error = execute(core, &VerifyEnv::new(), &BTreeSet::new(), &[CorePass::Fuse])
            .expect_err("an invalid elaborated artifact must not enter Fuse");
        assert!(matches!(
            error,
            PreExecutorFailure::Verification {
                point: PreVerificationPoint::Before {
                    occurrence: 0,
                    pass: CorePass::Fuse,
                },
                ..
            }
        ));
    }

    #[test]
    fn an_empty_sequence_still_verifies_and_returns_the_input() {
        let (input, env, newtypes) = production_elaborated_fixture(NEWTYPE_SPECIALIZATION_SOURCE);
        let expected = input.clone().erase();
        let (actual, stats) =
            execute(input, &env, &newtypes, &[]).expect("an empty verified run succeeds");
        assert_eq!(actual.erase(), expected);
        assert!(stats.entries().is_empty());
        assert_eq!(stats.total(), 0);
    }
}
