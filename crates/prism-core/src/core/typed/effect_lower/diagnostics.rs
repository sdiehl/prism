//! Typed free-monad fallback diagnostics.

use std::cell::RefCell;
use std::collections::BTreeSet;

use prism_common::sym::Sym;
use prism_syntax::names::ENTRY_POINT;

use super::decline::Decline;
use super::plan::{open_resume_escapes, EffectPlan};
use super::walk::each_subterm;
use super::{TypedComp, TypedCompKind, TypedCoreFn};

/// Per-lowering reporter for a typed fast-path matcher whose accepted input
/// violates its own post-condition.
#[derive(Debug)]
pub struct DriftLog {
    quiet: bool,
    warned: RefCell<BTreeSet<&'static str>>,
}

impl DriftLog {
    #[must_use]
    pub const fn new(quiet: bool) -> Self {
        Self {
            quiet,
            warned: RefCell::new(BTreeSet::new()),
        }
    }

    pub fn shape_drift(&self, matcher: &'static str) {
        if !self.should_report(matcher) {
            return;
        }
        eprintln!(
            "warning: effect-lowering matcher drift in `{matcher}`: an elaborated clause shape \
             changed, so a fusion fast path was skipped (output is correct but un-fused). This is \
             a compiler-internal signal; please report it."
        );
    }

    // Test the once/quiet policy without capturing stderr. The guard is scoped
    // to one lowering so a long-lived host does not silence later compilations.
    fn should_report(&self, matcher: &'static str) -> bool {
        !self.quiet && self.warned.borrow_mut().insert(matcher)
    }
}

/// Produce the user-visible performance warning from the typed tree whose
/// convention plan drives this lowering.
#[must_use]
pub fn free_monad_warning(
    functions: &[TypedCoreFn],
    monadified: &BTreeSet<Sym>,
    plan: &EffectPlan,
    declined: Option<Decline>,
) -> Option<String> {
    let mut names: Vec<&str> = monadified.iter().map(|name| name.as_str()).collect();
    names.sort_unstable();
    if names.is_empty() {
        return None;
    }
    let mut causes = free_monad_causes(functions, monadified, plan);
    // A refused confined region is the most specific cause there is: it names
    // the one site that cost the program the narrower lowering, which the
    // plan-level facts above can only describe in aggregate.
    if let Some(declined) = declined {
        causes.push(declined.to_string());
    }
    let why = if causes.is_empty() {
        "a handler reifies its continuation (not tail-resumptive)".to_string()
    } else {
        causes.join("; ")
    };
    Some(format!(
        "effect lowering fell off the fused path: {why}. {} function(s) now reify into \
         EOp cells per operation instead of fusing: {}. Call effectful functions directly \
         instead of through a first-class value, or restructure the handler, to refuse.",
        names.len(),
        names.join(", ")
    ))
}

// Why the fallback fired, read off the plan rather than re-derived: the causes
// a user is shown are the same facts that decided the tier.
fn free_monad_causes(
    functions: &[TypedCoreFn],
    monadified: &BTreeSet<Sym>,
    plan: &EffectPlan,
) -> Vec<String> {
    let latent = plan.latent();
    let mut causes = Vec::new();
    for function in functions
        .iter()
        .filter(|function| monadified.contains(&function.name()))
    {
        // Only a capture the thunk signatures cannot follow is a cause. A
        // tracked capture keeps its region confined, so naming it here would
        // blame the user for a shape that costs them nothing.
        if plan.opaque_captures().contains(&function.name()) {
            causes.push(format!(
                "`{}` captures an effectful computation in a first-class closure \
                 the signatures cannot follow",
                function.name()
            ));
        }
        if open_resume_escapes(function.body(), latent) {
            causes.push(format!(
                "`{}` has a handler whose resume escapes",
                function.name()
            ));
        }
        if contains_mask(function.body()) {
            causes.push(format!(
                "`{}` uses `mask`, which disables fusion",
                function.name()
            ));
        }
    }
    let entry = Sym::new(ENTRY_POINT);
    if monadified.contains(&entry) && latent.get(&entry).is_some_and(|ops| !ops.is_empty()) {
        causes.push("an effect reaches `main` unhandled".to_string());
    }
    causes
}

fn contains_mask(comp: &TypedComp) -> bool {
    if matches!(comp.kind(), TypedCompKind::Mask(..)) {
        return true;
    }
    let mut found = false;
    each_subterm(comp, &mut |child| found |= contains_mask(child));
    found
}

#[cfg(test)]
mod tests {
    use super::DriftLog;

    #[test]
    fn drift_report_is_once_per_matcher_per_lowering() {
        let log = DriftLog::new(false);
        assert!(log.should_report("state_clause"), "first drift warns");
        assert!(!log.should_report("state_clause"), "same matcher deduped");
        assert!(log.should_report("strip_resume"), "distinct matcher warns");

        let quiet = DriftLog::new(true);
        assert!(!quiet.should_report("state_clause"), "quiet is silent");

        let next = DriftLog::new(false);
        assert!(
            next.should_report("state_clause"),
            "a fresh lowering is not silenced by a prior one"
        );
    }
}
