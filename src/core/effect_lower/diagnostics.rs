//! Free-monad fallback diagnostics.

use std::cell::RefCell;
use std::collections::BTreeSet;

use super::analysis::open_resume_escapes;
use super::checks::{all_calls, raw_effects};
use super::walk::{contains_mask, thunks_in_comp};
use super::Latent;
use crate::core::cbpv::Core;
use crate::names::ENTRY_POINT;
use crate::sym::Sym;

// Diagnostic for the free-monad fallback. Falling off the fused evidence/state
// path is a real performance event (handlers reify into per-op `EOp` cells
// instead of fusing), so the driver surfaces this through the standard warning
// framework rather than letting the fallback happen silently. It names the
// monadified functions and the specific cause, so a hot pipeline can be steered
// back onto a fused path. It is produced only in the fallback, so a fully fused
// program yields `None` (zero false positives). `monadified` is the set that
// actually reified into EOp cells: in whole-program mode the genuinely effectful
// functions, in local mode just the entangled component (so the warning names
// the few functions that lost fusion, not the whole program). Causes are
// reported only for those functions, so a fused pipeline is never blamed.
pub(super) fn free_monad_warning(
    core: &Core,
    monadified: &BTreeSet<Sym>,
    fl: &Latent,
) -> Option<String> {
    let mut names: Vec<&str> = monadified.iter().map(|s| s.as_str()).collect();
    names.sort_unstable();
    if names.is_empty() {
        return None;
    }
    let causes = free_monad_causes(core, monadified, fl);
    let why = if causes.is_empty() {
        // No structural cause matched: a reachable handler is not tail-resumptive
        // (it captures or multiply-applies `resume`), so its continuation is reified.
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

// Per-lowering reporter for effect-lowering matcher drift. A fast-path matcher
// (`strip_resume` / `state_clause`) accepted a clause but then found its own
// post-condition violated: a `resume` reference survived a strip that is supposed
// to erase the continuation. That can only happen if upstream elaboration drifted
// from the ANF shape these matchers recognize. In debug builds the call site's
// `debug_assert!` panics so the drift is caught in development; in release the
// matcher rejects the clause and the caller falls back to the correct (non-fused)
// lowering. That fallback is silent, so a benign elaborator refactor would read as
// an unexplained performance cliff. This surfaces the drift on stderr once per
// matcher: a compiler-internal signal, not a user error, and output stays correct.
//
// The once-guard is scoped to a single lowering, not a process-global static, and
// `quiet` comes from `DynFlags` (read once in `DynFlags::from_env`) rather than a
// second raw `PRISM_QUIET` env read here. So the stderr diagnostic is a
// deterministic function of (source, flags) within every compilation, including a
// long-lived host that lowers many programs in one process. It stays off the
// byte-checked stdout channel like the other fallback warnings.
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

    // Whether this drift should reach stderr: never when quiet, and only the first
    // time this lowering sees this matcher. Split out so the once/quiet policy is
    // testable without capturing stderr (the drift itself is unreachable from
    // well-formed source: a `debug_assert` guards it and it fires only on internal
    // ANF drift).
    fn should_report(&self, matcher: &'static str) -> bool {
        !self.quiet && self.warned.borrow_mut().insert(matcher)
    }
}

// The genuinely effectful functions: those with a non-empty latent set. This is
// the natural per-function monadic set, before any whole-program inflation.
pub(super) fn genuine_eff(fl: &Latent) -> BTreeSet<Sym> {
    fl.iter()
        .filter(|(_, s)| !s.is_empty())
        .map(|(n, _)| *n)
        .collect()
}

// The reasons a program fell to the free monad, each naming the offending
// function and the construct (an effectful closure at an apply site, a raw
// do/handle captured in a thunk, or an open handler whose resume escapes). Only
// the `monadified` functions are scanned, so a fused combinator in the same
// program (whose thunk legitimately performs effects) is not falsely blamed. The
// Core IR carries no source spans, so the function name is the locator.
fn free_monad_causes(core: &Core, monadified: &BTreeSet<Sym>, fl: &Latent) -> Vec<String> {
    let eff = genuine_eff(fl);
    let mut causes = Vec::new();
    for f in core.fns.iter().filter(|f| monadified.contains(&f.name)) {
        let mut thunks = Vec::new();
        thunks_in_comp(&f.body, &mut thunks);
        let captures_effect = thunks.iter().any(|body| {
            let mut heads = BTreeSet::new();
            all_calls(body, &mut heads);
            !heads.is_disjoint(&eff) || raw_effects(body)
        });
        if captures_effect {
            causes.push(format!(
                "`{}` captures an effectful computation in a first-class closure",
                f.name
            ));
        }
        if open_resume_escapes(&f.body, fl) {
            causes.push(format!("`{}` has a handler whose resume escapes", f.name));
        }
        if contains_mask(&f.body) {
            causes.push(format!("`{}` uses `mask`, which disables fusion", f.name));
        }
    }
    // An effect that reaches `main` unhandled is monadified to trap at the top
    // (the interpreter's unhandled-effect error), the same as today.
    if monadified.contains(&Sym::new(ENTRY_POINT))
        && fl
            .get(&Sym::new(ENTRY_POINT))
            .is_some_and(|s| !s.is_empty())
    {
        causes.push("an effect reaches `main` unhandled".to_string());
    }
    causes
}

#[cfg(test)]
mod tests {
    use super::DriftLog;

    // The drift warning is silent under quiet and, per lowering, fires at most once
    // per matcher; a fresh lowering reports again. This is the property the old
    // process-global `AtomicBool` broke (it silenced every later compilation in a
    // long-lived host), so it is the one worth pinning.
    #[test]
    fn drift_report_is_once_per_matcher_per_lowering() {
        let log = DriftLog::new(false);
        assert!(log.should_report("state_clause"), "first drift warns");
        assert!(!log.should_report("state_clause"), "same matcher deduped");
        assert!(log.should_report("strip_resume"), "distinct matcher warns");

        // Quiet silences unconditionally.
        let quiet = DriftLog::new(true);
        assert!(!quiet.should_report("state_clause"), "quiet is silent");

        // A separate lowering (a new program in the same process) warns again.
        let next = DriftLog::new(false);
        assert!(
            next.should_report("state_clause"),
            "a fresh lowering is not silenced by a prior one"
        );
    }
}
