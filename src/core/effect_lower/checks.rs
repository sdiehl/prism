//! Post-lowering convention/residual-effect invariant checks.

use std::collections::{BTreeMap, BTreeSet};

use super::walk::{each_subcomp, each_value, thunks_in_comp};
use super::{EOP, EPURE};
use crate::core::cbpv::{Comp, Core, CoreFn, Value};
use crate::error::TypeError;
use crate::names::ENTRY_POINT;
use crate::sym::Sym;

// Convention-boundary rail, run in both selective and whole-program mode. A
// monadic context must end in an Eff value at every tail: an EPure/EOp
// construction, a saturated call to a program function (itself Eff-tailed by
// induction or because it is the direct callee a monadic context EPure-wrapped),
// a dynamic application of a monadified closure, or a diverging Error. A function
// the rewrite should have monadified but did not shows up here as an ICE, exactly
// where the old whole-program uniformity used to make a missed boundary
// impossible, rather than as a miscompile at a distant dynamic call site.
//
// Whole-program mode (`full`): every function, generated driver, and thunk body
// is monadic, so all are checked, including under their lambda binders. Selective
// mode: only the `monadic` program functions are; their top-level tail is checked
// (their interior mixes monadic continuation thunks with direct data thunks, so a
// blanket thunk check would false-positive). `main` is exempt either way because
// `unwrap_main` strips its final EPure.
pub(super) fn check_convention_boundaries(
    arity_fns: &[CoreFn],
    check: &[&CoreFn],
    monadic: &BTreeSet<Sym>,
    blanket: bool,
    exempt: &BTreeSet<Sym>,
) -> Result<(), TypeError> {
    let arities: BTreeMap<&str, usize> = arity_fns
        .iter()
        .map(|f| (f.name.as_str(), f.params.len()))
        .collect();
    for f in check {
        if !monadic.contains(&f.name) || exempt.contains(&f.name) {
            continue;
        }
        check_tails(f.name.as_str(), &f.body, &arities)?;
        if blanket {
            // A full-style monadic function monadifies every thunk body too, so
            // each (under its lambda binder) must also be Eff-tailed.
            let mut ts = Vec::new();
            thunks_in_comp(&f.body, &mut ts);
            for t in ts {
                let b = if let Comp::Lam(_, b) = t { b } else { t };
                check_tails(f.name.as_str(), b, &arities)?;
            }
        }
    }
    Ok(())
}

fn check_tails(fname: &str, c: &Comp, arities: &BTreeMap<&str, usize>) -> Result<(), TypeError> {
    match c {
        Comp::Bind(_, _, n) => check_tails(fname, n, arities)?,
        Comp::If(_, t, e) => {
            check_tails(fname, t, arities)?;
            check_tails(fname, e, arities)?;
        }
        Comp::Case(_, arms) => {
            for (_, b) in arms {
                check_tails(fname, b, arities)?;
            }
        }
        Comp::Return(Value::Ctor(n, ..)) if n == EPURE || n == EOP => {}
        Comp::Call(g, args) if g != ENTRY_POINT && arities.get(g.as_str()) == Some(&args.len()) => {
        }
        Comp::App(..) | Comp::Error(_) => {}
        other => {
            return Err(TypeError::Ice {
                msg: format!(
                    "monadification: `{fname}` tail is not Eff-shaped: {}",
                    other.kind()
                ),
            });
        }
    }
    Ok(())
}

// Invariant check: between selective and whole-program mode, lowering must
// eliminate every `do` and `handle`. A survivor is a compiler bug.
/// # Errors
/// Fails if any `do` or `handle` survives lowering.
pub fn residual_effects(core: &Core) -> Result<(), String> {
    for f in &core.fns {
        if raw_effects(&f.body) {
            return Err(format!("residual effect in `{}` after lowering", f.name));
        }
    }
    Ok(())
}

pub(super) fn raw_effects(c: &Comp) -> bool {
    if matches!(c, Comp::Do(..) | Comp::Handle { .. } | Comp::Mask(..)) {
        return true;
    }
    let mut found = false;
    each_value(c, &mut |v| found |= raw_effects_value(v));
    each_subcomp(c, &mut |sc| found |= raw_effects(sc));
    found
}

fn raw_effects_value(v: &Value) -> bool {
    match v {
        Value::Thunk(c) => raw_effects(c),
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.iter().any(raw_effects_value),
        _ => false,
    }
}

pub(super) fn all_calls(c: &Comp, out: &mut BTreeSet<Sym>) {
    if let Comp::Call(g, _) = c {
        out.insert(*g);
    }
    each_subcomp(c, &mut |sc| all_calls(sc, out));
}
