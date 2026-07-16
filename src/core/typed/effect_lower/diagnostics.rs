//! Typed free-monad fallback diagnostics.

use std::cell::RefCell;
use std::collections::BTreeSet;

use crate::names::ENTRY_POINT;
use crate::sym::Sym;

use super::analysis::open_resume_escapes;
use super::latent::Latent;
use super::walk;
use super::{raw_effects, TypedComp, TypedCompKind, TypedCoreFn};

/// Per-lowering reporter for a typed fast-path matcher whose accepted input
/// violates its own post-condition.
pub(super) struct DriftLog {
    quiet: bool,
    warned: RefCell<BTreeSet<&'static str>>,
}

impl DriftLog {
    pub(super) const fn new(quiet: bool) -> Self {
        Self {
            quiet,
            warned: RefCell::new(BTreeSet::new()),
        }
    }

    pub(super) fn shape_drift(&self, matcher: &'static str) {
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

pub(super) fn genuine_effects(latent: &Latent) -> BTreeSet<Sym> {
    latent
        .iter()
        .filter_map(|(name, operations)| (!operations.is_empty()).then_some(*name))
        .collect()
}

/// Produce the user-visible performance warning from the typed tree whose
/// convention plan drives this lowering.
pub(super) fn free_monad_warning(
    functions: &[TypedCoreFn],
    monadified: &BTreeSet<Sym>,
    latent: &Latent,
) -> Option<String> {
    let mut names: Vec<&str> = monadified.iter().map(|name| name.as_str()).collect();
    names.sort_unstable();
    if names.is_empty() {
        return None;
    }
    let causes = free_monad_causes(functions, monadified, latent);
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

fn free_monad_causes(
    functions: &[TypedCoreFn],
    monadified: &BTreeSet<Sym>,
    latent: &Latent,
) -> Vec<String> {
    let effectful = genuine_effects(latent);
    let mut causes = Vec::new();
    for function in functions
        .iter()
        .filter(|function| monadified.contains(&function.name()))
    {
        let mut thunks = Vec::new();
        walk::thunks_in_comp(function.body(), &mut thunks);
        let captures_effect = thunks.iter().any(|body| {
            let mut calls = BTreeSet::new();
            all_calls(body, &mut calls);
            !calls.is_disjoint(&effectful) || raw_effects(body)
        });
        if captures_effect {
            causes.push(format!(
                "`{}` captures an effectful computation in a first-class closure",
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

fn all_calls(comp: &TypedComp, calls: &mut BTreeSet<Sym>) {
    if let TypedCompKind::Call { callee, .. } = comp.kind() {
        calls.insert(*callee);
    }
    walk::each_subcomp(comp, &mut |child| all_calls(child, calls));
}

fn contains_mask(comp: &TypedComp) -> bool {
    if matches!(comp.kind(), TypedCompKind::Mask(..)) {
        return true;
    }
    let mut found = false;
    walk::each_value(comp, &mut |value| {
        let mut thunks = Vec::new();
        walk::thunks_in_value(value, &mut thunks);
        found |= thunks.iter().any(|thunk| contains_mask(thunk));
    });
    walk::each_subcomp(comp, &mut |child| found |= contains_mask(child));
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
