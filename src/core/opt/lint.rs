//! Core Lint: the core-to-core sanity net.
//!
//! A well-formedness check run between optimization passes (under
//! `PRISM_CORE_LINT`, and unconditionally in the test harness). A failure is a
//! compiler bug, an optimization pass that produced ill-formed Core, attributed
//! to the offending function so the culprit pass is obvious.
//!
//! The foundation checks scoping, the single most valuable invariant and the one
//! a buggy rewrite (a captured binder, a clone referencing a freed name) breaks
//! first: every free variable of a function body must be a parameter or a
//! top-level function (referenced first-class). This rides `fv`, which already
//! subtracts every internal binder (let, lambda, case pattern, handler
//! return/op/resume, reuse token), so a leak shows up as an unexpected free var.
//! Richer checks (constructor arity, ANF argument shape, reuse freed-once) are
//! future additions; the harness is built to grow them.

use std::collections::BTreeSet;

use super::super::cbpv::Core;
use super::super::fv;
use crate::sym::Sym;

/// Lint `core`, returning one message per violation. `Ok(())` means well-formed.
///
/// # Errors
/// Returns the list of well-formedness violations (currently out-of-scope free
/// variables), one message per offending function.
pub fn lint(core: &Core) -> Result<(), Vec<String>> {
    let top: BTreeSet<Sym> = core.fns.iter().map(|f| f.name).collect();
    let mut errs = Vec::new();
    for f in &core.fns {
        let mut allowed = top.clone();
        allowed.extend(f.params.iter().copied());
        for v in fv::comp(&f.body) {
            if !allowed.contains(&v) {
                errs.push(format!(
                    "fn `{}`: unbound variable `{}` (escaped binder or dangling reference)",
                    f.name, v
                ));
            }
        }
    }
    if errs.is_empty() {
        Ok(())
    } else {
        Err(errs)
    }
}
