use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;
use prism_syntax::{
    ast::{Core as CorePhase, Program},
    names,
};

use super::cbpv::Value;
use super::fv::comp as freev;
use crate::types::scalar_plan;

mod balance;
mod borrow;
mod callable;
mod check;
mod imbalance;
mod rc;
mod reuse;

pub use balance::balanced;
pub use borrow::infer_borrow_sigs;
pub use callable::{callable_requirements, check_callable_flow, CallableRequirements};
pub use check::{
    bounded_stack_annots, check_alloc, check_bounded_stack, check_linear, fip_annots,
    linear_annots, replayable_annots, subsumes, Alloc, ClaimError, ClaimErrorKind, ClaimOrigin,
    Fips,
};
pub use imbalance::{Imbalance, TokenFault};
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

// Per-function borrow mask, one bool per elaborated Core parameter in order
// (including leading typeclass dictionaries). A borrow parameter is borrowed by
// the callee (never dropped, dup'd before any consuming use) and retained by the
// caller (not transferred at the call). Only pure functions may carry a borrow
// param, so they all go through the untouched `lower_comp` path and reach this
// pass as ordinary positional calls. Functions absent from the map default to
// all-owned.
pub type Sigs = BTreeMap<Sym, Vec<bool>>;

#[must_use]
pub fn borrow_sigs(prog: &Program<CorePhase>) -> Sigs {
    let functions = prog
        .fns
        .iter()
        .filter(|decl| decl.params.iter().any(|param| param.borrow))
        .map(|decl| {
            let mut mask = vec![false; decl.constraints.len()];
            mask.extend(decl.params.iter().map(|param| param.borrow));
            (decl.name.clone().into(), mask)
        });
    let methods = prog.instances.iter().flat_map(|instance| {
        let superclasses = prog
            .classes
            .iter()
            .find(|class| class.name == instance.class)
            .map_or(0, |class| class.supers.len());
        let dictionary_arity = instance.context.len() + superclasses;
        instance
            .methods
            .iter()
            .filter(|method| method.params.iter().any(|param| param.borrow))
            .map(move |method| {
                let mut mask = vec![false; dictionary_arity];
                mask.extend(method.params.iter().map(|param| param.borrow));
                (
                    names::instance_method(&instance.name, &method.name).into(),
                    mask,
                )
            })
    });
    functions.chain(methods).collect()
}

// A borrow mask is indexed by the elaborated Core parameter list. Typeclass
// dictionaries precede the explicit source parameters and are always owned, so
// `borrow_sigs` prepends one `false` entry per dictionary. Keeping the mask in
// Core order prevents a constrained function from accidentally borrowing its
// last dictionary/first user argument while consuming the parameter that was
// actually declared `borrow`.

// A borrow-position call arg is normally a `Value::Var`: the caller retains one
// ownership token through the call and drops it afterward when the loan is its
// last use. Mandatory newtype erasure and scalar folding may expose a literal
// directly at the call, and that is fine only when the literal's encoding plan
// owns no fresh heap cell: a zero or tagged word, or the static cell a `Str`
// literal names. A literal whose plan mints a fresh cell per use needs an
// owner at a borrowed position: the typed RC pass anchors it to a binder, and
// here, like every other cell-owning value, an unanchored one is an invariant
// error rather than a silently leaking temporary. Mirrors the typed pass's
// `scalar_without_cell`, reading the same representation authority.
fn scalar_without_cell(value: &Value) -> bool {
    value
        .literal_scalar_type()
        .and_then(|ty| scalar_plan(&ty).ok())
        .is_some_and(|plan| !plan.owns_fresh_cell())
}

fn borrow_mask(name: Sym, sigs: &Sigs) -> Option<&[bool]> {
    sigs.get(&name).map(Vec::as_slice)
}

// Whether parameter/argument `i` is borrowed under the given mask. A missing
// mask, a short mask, or a `false` entry all mean owned.
fn borrowed_at(mask: Option<&[bool]>, i: usize) -> bool {
    mask.is_some_and(|m| m.get(i).copied().unwrap_or(false))
}

fn borrowed_call_vars(name: Sym, args: &[Value], sigs: &Sigs) -> Result<Set, TokenFault> {
    let mask = borrow_mask(name, sigs);
    args.iter()
        .enumerate()
        .filter(|(index, _)| borrowed_at(mask, *index))
        .filter_map(|(_, arg)| match arg {
            Value::Var(var) => Some(Ok(*var)),
            value if scalar_without_cell(value) => None,
            _ => Some(Err(TokenFault::BorrowedArgNotBound {
                callee: name,
                arg: Box::new(arg.clone()),
            })),
        })
        .collect()
}

fn count_val(v: &Value, out: &mut BTreeMap<Sym, usize>) {
    let mut values = vec![v];
    while let Some(value) = values.pop() {
        match value {
            Value::Var(name) => *out.entry(*name).or_default() += 1,
            Value::Ctor(_, _, fields) | Value::Tuple(fields) | Value::UnboxedTuple(fields) => {
                values.extend(fields.iter().rev());
            }
            Value::UnboxedRecord(fields) => {
                values.extend(fields.iter().rev().map(|(_, field)| field));
            }
            Value::Thunk(comp) => {
                for name in freev(comp) {
                    *out.entry(name).or_default() += 1;
                }
            }
            Value::Int(_)
            | Value::I64(_)
            | Value::U64(_)
            | Value::Float(_)
            | Value::Bool(_)
            | Value::Unit
            | Value::Str(_) => {}
        }
    }
}
