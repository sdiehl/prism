mod expect;
mod phase;
mod state;
mod walk;

use std::collections::{BTreeMap, BTreeSet};
use std::marker::PhantomData;

use prism_common::sym::Sym;

use super::super::{CoreFnSig, CoreType, TypedCoreFn};
use super::{CoreViolation, VerifyEnv};
use state::ReuseShell;

pub use phase::TypedCorePhase;

/// Check all stored Core judgments without inference or unification.
///
/// # Errors
/// Returns every independently observed violation. Errors at a parent whose
/// premise is already invalid may be omitted to avoid cascading diagnostics.
pub(in crate::core::typed) fn check_functions<P: TypedCorePhase>(
    functions: &[TypedCoreFn],
    env: &VerifyEnv,
) -> Result<(), Vec<CoreViolation>> {
    let mut globals = BTreeMap::new();
    let mut duplicate_globals = BTreeSet::new();
    for function in functions {
        if globals
            .insert(function.name(), function.sig().clone())
            .is_some()
        {
            duplicate_globals.insert(function.name());
        }
    }

    let mut violations = Vec::new();
    for function in functions {
        let mut checker = Checker::<P>::new(function.name(), env, &globals);
        if duplicate_globals.contains(&function.name()) {
            checker.fail(super::Violation::DuplicateGlobal);
        }
        checker.function(function);
        violations.extend(checker.violations);
    }

    if violations.is_empty() {
        Ok(())
    } else {
        Err(violations)
    }
}

struct Checker<'a, P> {
    function: Sym,
    env: &'a VerifyEnv,
    globals: &'a BTreeMap<Sym, CoreFnSig>,
    // Each binding records the suspension depth it was introduced at, so a
    // reference from a deeper depth is known to read a closure capture slot.
    locals: BTreeMap<Sym, Vec<(CoreType, usize)>>,
    thunk_depth: usize,
    token_uses: BTreeMap<Sym, Vec<u8>>,
    token_capacities: BTreeMap<Sym, Vec<usize>>,
    reuse_shells: BTreeMap<Sym, Vec<ReuseShell>>,
    allowed_types: BTreeSet<Sym>,
    allowed_rows: BTreeSet<Sym>,
    path: Vec<String>,
    violations: Vec<CoreViolation>,
    phase: PhantomData<P>,
}
