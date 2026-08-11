//! The cost explainer: one sentence per region saying which rung it lowered to
//! and which fact put it there.
//!
//! Nothing here decides anything. The rung is the one the cascade took, the
//! region split is the one the cascade planned, and every cause is a set the
//! [`EffectPlan`] already holds or a refusal the confined attempt already
//! recorded. This module owns only the prose: it turns those facts into a line
//! a reader can act on, so "why is this program on the free monad" is answered
//! from the same data the tier decision was made from rather than from a second
//! opinion about the program.
//!
//! The vocabulary lives in `Cause`, one claim per fact, so a definition's
//! sentence and the program's sentence say the same words about the same fact.

use std::collections::BTreeSet;
use std::fmt::Write;

use prism_common::sym::Sym;

use crate::core::EffectStrategy;

use super::super::TypedCoreFn;
use super::analysis;
use super::decline::{Decline, PROGRAM};
use super::plan::EffectPlan;

/// What a definition contributed to the tier decision, one claim per fact the
/// plan records. Ordered widest first: the renderer reports the first that
/// holds, which is the fact that decided the rung when several do.
#[derive(Clone, Copy)]
enum Cause {
    /// [`EffectPlan::escaping`].
    Escapes,
    /// [`EffectPlan::opaque_captures`].
    OpaqueCapture,
    /// [`EffectPlan::tracked_captures`].
    TrackedCapture,
    /// [`EffectPlan::genuine`], rendered with the operations themselves.
    Performs,
    /// None of the above, with a non-empty [`EffectPlan::ops`]: it can run an
    /// operation, and discharges every one of them itself.
    Handled,
    /// None of the above, reaching no operation at all.
    Quiet,
}

impl Cause {
    /// The claim, phrased to follow the subject: `it {claim}` for a definition's
    /// own sentence, ``` `name` {claim} ``` for the program's.
    const fn claim(self) -> &'static str {
        match self {
            Self::Escapes => {
                "lets an effectful computation escape where no signature can follow it"
            }
            Self::OpaqueCapture => "captures an effectful computation the signatures cannot follow",
            Self::TrackedCapture => "captures an effectful computation the signatures follow",
            Self::Performs => "still performs",
            Self::Handled => "handles every operation it can run",
            Self::Quiet => "performs no operation",
        }
    }
}

/// The program-wide claim when no definition carries a fact that costs the
/// program anything. Phrased as the absence of a record rather than as an
/// absence of causes: the explainer reports the facts the cascade wrote down,
/// and a rung a cheaper engine simply declined leaves none behind.
const NOTHING_BLOCKED: &str = "no recorded fact forced a costlier rung";

/// The operation stand-in for a definition the plan calls performing while its
/// latent set names nothing, so the sentence is never left dangling.
const AN_OPERATION: &str = "an operation";

/// Explain one program's lowering: the rung the cascade took, then one sentence
/// per definition it classified, in name order.
///
/// `strategy` and `declined` come from the lowering that decided them; `plan`
/// is the plan for the same prepared tree.
#[must_use]
pub fn explain(
    functions: &[TypedCoreFn],
    plan: &EffectPlan,
    strategy: EffectStrategy,
    declined: Option<Decline>,
) -> String {
    let region = region(functions, plan, strategy);
    let mut out = String::new();
    writeln!(
        out,
        "{PROGRAM}: lowered to {strategy} because {}.",
        program_cause(plan, declined)
    )
    .unwrap();
    let mut names: Vec<Sym> = plan.functions().collect();
    names.sort_unstable_by_key(|name| name.as_str());
    for name in names {
        let cause = definition_cause(plan, name);
        // A definition the cascade left outside the region is not lowered by
        // this rung at all, so its sentence says where it stands rather than
        // claiming a rung the cascade never gave it.
        if region
            .as_ref()
            .is_some_and(|region| !region.contains(&name))
        {
            writeln!(
                out,
                "{}: stays off the {strategy} path because it {cause}.",
                name.as_str()
            )
            .unwrap();
        } else {
            writeln!(
                out,
                "{}: lowered to {strategy} because it {cause}.",
                name.as_str()
            )
            .unwrap();
        }
    }
    out
}

/// The definitions this rung lowers, when it lowers only some of them.
///
/// `None` means the rung has no split to report: every definition is lowered
/// the same way, either because no region was carved (the fused rungs) or
/// because the region is the whole program.
fn region(
    functions: &[TypedCoreFn],
    plan: &EffectPlan,
    strategy: EffectStrategy,
) -> Option<BTreeSet<Sym>> {
    match strategy {
        EffectStrategy::Pure
        | EffectStrategy::Evidence
        | EffectStrategy::StateFusion
        | EffectStrategy::WholeProgramFreeMonad => None,
        EffectStrategy::LocalPartial => {
            analysis::local_region(functions, plan).map(|(region, _)| region)
        }
        EffectStrategy::SelectiveFreeMonad => Some(analysis::plan(functions, plan, false).members),
    }
}

/// Why the program as a whole landed on its rung: the refusal the confined
/// attempt recorded when there is one, otherwise the widest fact any definition
/// carries, named after the definition carrying it.
fn program_cause(plan: &EffectPlan, declined: Option<Decline>) -> String {
    // A refused confined region is the most specific cause there is: it names
    // the one site that cost the program the narrower lowering.
    if let Some(declined) = declined {
        return declined.to_string();
    }
    for (set, cause) in [
        (plan.escaping(), Cause::Escapes),
        (plan.opaque_captures(), Cause::OpaqueCapture),
        (plan.genuine(), Cause::Performs),
    ] {
        if let Some(name) = set.iter().min_by_key(|name| name.as_str()) {
            return format!("`{}` {}", name.as_str(), clause(plan, *name, cause));
        }
    }
    NOTHING_BLOCKED.to_string()
}

/// The clause for one definition: the first fact it carries, widest first.
fn definition_cause(plan: &EffectPlan, name: Sym) -> String {
    for (set, cause) in [
        (plan.escaping(), Cause::Escapes),
        (plan.opaque_captures(), Cause::OpaqueCapture),
        (plan.tracked_captures(), Cause::TrackedCapture),
        (plan.genuine(), Cause::Performs),
    ] {
        if set.contains(&name) {
            return clause(plan, name, cause);
        }
    }
    // Nothing survives here, but the reach set still separates a definition that
    // runs no operation from one that runs operations and handles them all: the
    // second is why a program full of effects can sit on a cheap rung.
    if plan.ops(name).is_empty() {
        Cause::Quiet.claim().to_string()
    } else {
        Cause::Handled.claim().to_string()
    }
}

/// One cause as a clause, with the operations spelled out where the claim ends
/// in them.
fn clause(plan: &EffectPlan, name: Sym, cause: Cause) -> String {
    match cause {
        Cause::Performs => format!("{} {}", cause.claim(), operations(plan, name)),
        _ => cause.claim().to_string(),
    }
}

/// The operations a definition still performs, read off the latent map the plan
/// was built from, mask depth dropped: the question is which effect, not how
/// many handlers of it are still to be skipped.
fn operations(plan: &EffectPlan, name: Sym) -> String {
    let ops: BTreeSet<&str> = plan
        .latent()
        .get(&name)
        .into_iter()
        .flatten()
        .map(|masked| masked.id.as_str())
        .collect();
    if ops.is_empty() {
        return AN_OPERATION.to_string();
    }
    ops.into_iter()
        .map(|op| format!("`{op}`"))
        .collect::<Vec<String>>()
        .join(", ")
}
