use std::collections::{BTreeMap, BTreeSet};

use crate::sym::Sym;
use crate::syntax::ast::{Core as CorePhase, Program};

use super::cbpv::Value;
use super::fv::comp as freev;

mod balance;
mod check;
mod rc;
mod reuse;

pub use balance::balanced;
pub use check::{check_fip, check_fip_linear, fip_annots, replayable_annots, Fips};
pub use rc::insert_rc;
pub use reuse::reuse;

// Compile-time precise reference counting. Function parameters and
// every let-bound result are owned; each owned value is consumed exactly once on
// every control path. A second consuming use inserts dup; a value that dies
// unused inserts drop. Pattern-extracted fields are dup'd live at the match so
// they own a reference independent of the scrutinee, which is then dropped once
// dead (the dup precedes the drop so a freed cell never strands a live field).
// Closure captures stay owned by the closure cell, so inside a lambda body they
// are borrowed: a consuming use dups first and the body never drops them. Sound
// under pointer tagging: inc/dec are no-ops on immediates, so dup/drop on a
// non-cell is harmless. The `fbip` dump shows the ops; a run under
// PRISM_CHECK_LEAKS reports zero live cells at exit.

type Set = BTreeSet<Sym>;

// Per-function borrow mask, one bool per param in order. A borrow parameter is
// borrowed by the callee (never dropped, dup'd before any consuming use) and
// retained by the caller (not transferred at the call). Only pure functions may
// carry a borrow param, so they all go through the untouched `lower_comp` path
// and reach this pass as ordinary positional calls. Functions absent from the
// map default to all-owned.
pub type Sigs = BTreeMap<Sym, Vec<bool>>;

#[must_use]
pub fn borrow_sigs(prog: &Program<CorePhase>) -> Sigs {
    prog.fns
        .iter()
        .filter(|d| d.params.iter().any(|p| p.borrow))
        .map(|d| {
            (
                d.name.clone().into(),
                d.params.iter().map(|p| p.borrow).collect(),
            )
        })
        .collect()
}

// A borrow-position call arg is always a `Value::Var` (call sites bind every
// argument to a let before the call, so the caller's dead-variable analysis
// drops it when dead), and the caller retains ownership across the call, so it
// is not a consuming use and is skipped here.
fn borrow_mask(name: Sym, sigs: &Sigs) -> Option<&[bool]> {
    sigs.get(&name).map(Vec::as_slice)
}

// Whether parameter/argument `i` is borrowed under the given mask. A missing
// mask, a short mask, or a `false` entry all mean owned.
fn borrowed_at(mask: Option<&[bool]>, i: usize) -> bool {
    mask.is_some_and(|m| m.get(i).copied().unwrap_or(false))
}

fn count_val(v: &Value, out: &mut BTreeMap<Sym, usize>) {
    match v {
        Value::Var(x) => *out.entry(*x).or_default() += 1,
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.iter().for_each(|f| count_val(f, out)),
        Value::Thunk(c) => {
            for x in freev(c) {
                *out.entry(x).or_default() += 1;
            }
        }
        _ => {}
    }
}
