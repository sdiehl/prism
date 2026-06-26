//! Latent-effect and CBPV-shape analysis driving strategy choice.

use std::collections::{BTreeMap, BTreeSet};

use super::checks::{all_calls, raw_effects};
use super::walk::{collect_ops, each_subcomp, each_value, latent, thunks_in_comp, thunks_in_value};
use super::{Latent, MaskOp};
use crate::core::cbpv::{Comp, Core, CoreFn, Value};
use crate::core::fv;
use crate::names::ENTRY_POINT;
use crate::sym::Sym;

// Per-function set of effect ops still latent in its body, with the mask depth
// dropped: the op identities the call-graph fixpoint believes each function can
// still perform. Exposed for the driver's effect-engine reconciliation check.
#[must_use]
pub fn latent_ops(core: &Core) -> BTreeMap<Sym, BTreeSet<Sym>> {
    latent_map(core)
        .into_iter()
        .map(|(f, ops)| (f, ops.into_iter().map(|o| o.id).collect()))
        .collect()
}

pub(super) fn latent_map(core: &Core) -> Latent {
    // The latent ops of each function are a least fixpoint over the call graph:
    // a function's set is the ops it performs directly plus those latent in its
    // callees. `least_fixpoint` grows each set monotonically to convergence, so
    // termination is structural (no iteration ceiling needed).
    let seed: Latent = core.fns.iter().map(|f| (f.name, BTreeSet::new())).collect();
    let bodies: BTreeMap<Sym, &Comp> = core.fns.iter().map(|f| (f.name, &f.body)).collect();
    crate::fixpoint::least_fixpoint(seed, |name, cur| {
        let mut s = BTreeSet::new();
        latent(bodies[name], cur, &mut s);
        s
    })
}

// Selective mode monadifies only functions that perform or propagate an
// effect. When effectful code escapes first-class through a thunk (a call to
// an effectful function, or a raw do/handle inside a closure body), dynamic
// call sites cannot tell conventions apart, so switch to whole-program mode and
// monadify everything. `try_local` first tries to confine that whole-program
// answer to the escaping component; this is its fallback. check_convention_boundaries
// enforces the resulting invariant after the rewrite.
pub(super) fn monadic_set(core: &Core, fl: &Latent) -> (BTreeSet<Sym>, bool) {
    let eff: BTreeSet<Sym> = fl
        .iter()
        .filter(|(_, s)| !s.is_empty())
        .map(|(n, _)| *n)
        .collect();
    let mut thunks = Vec::new();
    for f in &core.fns {
        thunks_in_comp(&f.body, &mut thunks);
    }
    let escapes = thunks.iter().any(|body| {
        let mut heads = BTreeSet::new();
        all_calls(body, &mut heads);
        !heads.is_disjoint(&eff) || raw_effects(body)
    }) || core.fns.iter().any(|f| open_resume_escapes(&f.body, fl));
    if escapes {
        (core.fns.iter().map(|f| f.name).collect(), true)
    } else {
        (eff, false)
    }
}

// The monadic region for local monadification: the component of functions that
// must be free-monad lowered because an effectful closure escapes inside it,
// together with its entry functions (the ones a fused caller invokes, which need
// a bare-returning, unwrapped convention). Returns None when the split is not
// clean enough to keep the rest fused, so the caller falls back to whole-program.
//
// Built as the connected component of the escaping functions under two closures:
// downward over the call graph (every function an escaping one calls, so the
// closure that is applied dynamically and the data path it flows through are all
// monadic together), and over a shared effect op (a function that performs or
// handles an op the region performs joins it, so the handler that drives the
// region's `EOp` cells is inside it). The region is therefore downward-closed:
// it calls no function outside itself, so the only boundary is the rest calling
// in at entries. With its effect ops disjoint from the rest (checked below) and
// no first-class closure crossing at an entry, the two calling conventions never
// meet on a value, so the rest stays fused.
pub(super) fn monadic_region(
    core: &Core,
    fl: &Latent,
    escaping: &BTreeSet<Sym>,
) -> Option<(BTreeSet<Sym>, BTreeSet<Sym>)> {
    let by_name: BTreeMap<Sym, &CoreFn> = core.fns.iter().map(|f| (f.name, f)).collect();
    let footprint: BTreeMap<Sym, BTreeSet<Sym>> = core
        .fns
        .iter()
        .map(|f| {
            let mut ops = BTreeSet::new();
            collect_ops(&f.body, &mut ops);
            if let Some(s) = fl.get(&f.name) {
                ops.extend(s.iter().map(|m| m.id));
            }
            (f.name, ops)
        })
        .collect();
    // Closure-inert functions: no effect and no dynamic application anywhere in
    // their downward call-graph. A monadified closure can flow through one as
    // opaque data (it is never forced) and the function returns a bare value, so
    // it is convention-agnostic and stays shared in the fused rest rather than
    // being pulled into the region (which would falsely conflict whenever the
    // rest also calls it, e.g. a prelude helper like `length`). Greatest fixpoint:
    // start all-inert, drop any that applies a value, performs/propagates an
    // effect, or calls a non-inert function.
    let mut inert: BTreeSet<Sym> = core.fns.iter().map(|f| f.name).collect();
    loop {
        let mut changed = false;
        for f in &core.fns {
            if !inert.contains(&f.name) {
                continue;
            }
            let mut callees = BTreeSet::new();
            all_calls(&f.body, &mut callees);
            let disqualified = has_app(&f.body)
                || !footprint[&f.name].is_empty()
                || callees
                    .iter()
                    .any(|g| by_name.contains_key(g) && !inert.contains(g));
            if disqualified {
                inert.remove(&f.name);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut region: BTreeSet<Sym> = escaping.clone();
    loop {
        let mut changed = false;
        // Downward: every named, non-inert callee of a region function (the
        // dynamic-apply and data-flow reach of the escaping closure). Inert
        // callees stay shared in the rest.
        for name in region.clone() {
            if let Some(f) = by_name.get(&name) {
                let mut heads = BTreeSet::new();
                all_calls(&f.body, &mut heads);
                for g in heads {
                    if by_name.contains_key(&g) && !inert.contains(&g) {
                        changed |= region.insert(g);
                    }
                }
            }
        }
        // Over a shared effect op: anything performing or handling an op the
        // region touches (the handler that drives its EOp cells, a co-performer).
        let tainted: BTreeSet<Sym> = region
            .iter()
            .flat_map(|f| footprint[f].iter().copied())
            .collect();
        for f in &core.fns {
            if !footprint[&f.name].is_disjoint(&tainted) {
                changed |= region.insert(f.name);
            }
        }
        if !changed {
            break;
        }
    }
    let entry_point = Sym::new(ENTRY_POINT);
    // Disjoint effects: no rest function may touch an op the region does, else a
    // boundary call would cross a live effect with mismatched conventions.
    let region_ops: BTreeSet<Sym> = region
        .iter()
        .flat_map(|f| footprint[f].iter().copied())
        .collect();
    for f in core.fns.iter().filter(|f| !region.contains(&f.name)) {
        if !footprint[&f.name].is_disjoint(&region_ops) {
            return None;
        }
    }

    // Entries: region functions a non-region (fused) function calls, plus `main`
    // when it is in the region (the runtime is its caller).
    let mut entries = BTreeSet::new();
    for f in &core.fns {
        if region.contains(&f.name) {
            continue;
        }
        let mut heads = BTreeSet::new();
        all_calls(&f.body, &mut heads);
        entries.extend(heads.into_iter().filter(|g| region.contains(g)));
    }
    if region.contains(&entry_point) {
        entries.insert(entry_point);
    }
    // An entry also called from within the region would need two conventions
    // (bare for the fused caller, Eff for the region caller). `main` is never
    // called by program code, so it is exempt.
    for f in core.fns.iter().filter(|f| region.contains(&f.name)) {
        let mut heads = BTreeSet::new();
        all_calls(&f.body, &mut heads);
        if heads
            .iter()
            .any(|g| *g != entry_point && entries.contains(g))
        {
            return None;
        }
    }
    // A closure crossing the boundary as a call argument, or returned from an
    // entry, would mix conventions: the rest threads bare-returning thunks while
    // the region monadifies thunk bodies into Eff. Reject either.
    for f in &core.fns {
        let in_region = region.contains(&f.name);
        let mut crosses_thunk = false;
        for_each_call(&f.body, &mut |g, args| {
            if in_region != region.contains(&g) && args.iter().any(carries_thunk) {
                crosses_thunk = true;
            }
        });
        if crosses_thunk {
            return None;
        }
    }
    for e in entries.iter().filter(|e| **e != entry_point) {
        if let Some(f) = core.fns.iter().find(|f| f.name == *e) {
            // A closure returned to, or dynamically applied from, a fused caller
            // mixes conventions on a value the syntactic argument check (which
            // only sees literal thunks, not ones bound to a variable) cannot rule
            // out, so reject a higher-order entry outright.
            let params: BTreeSet<Sym> = f.params.iter().copied().collect();
            if tail_returns_thunk(&f.body) || applies_param(&f.body, &params) {
                return None;
            }
        }
    }
    Some((region, entries))
}

// Whether a computation dynamically applies any value (an `App` node anywhere,
// including inside a thunk it builds). A function with no `App` in its whole
// body never forces a closure, so a monadified closure can pass through it as
// opaque data without a convention clash.
fn has_app(c: &Comp) -> bool {
    if matches!(c, Comp::App(..)) {
        return true;
    }
    let mut found = false;
    each_value(c, &mut |v| {
        let mut ts = Vec::new();
        thunks_in_value(v, &mut ts);
        for t in ts {
            found |= has_app(t);
        }
    });
    each_subcomp(c, &mut |sc| found |= has_app(sc));
    found
}

// A value that carries a first-class closure (directly or nested in a
// constructor or tuple): the convention-sensitive shape at a region boundary.
fn carries_thunk(v: &Value) -> bool {
    match v {
        Value::Thunk(_) => true,
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.iter().any(carries_thunk),
        _ => false,
    }
}

// Visit every `Call` head and its arguments, descending into thunk bodies.
fn for_each_call<'a>(c: &'a Comp, f: &mut impl FnMut(Sym, &'a [Value])) {
    if let Comp::Call(g, args) = c {
        f(*g, args);
    }
    each_value(c, &mut |v| {
        let mut ts = Vec::new();
        thunks_in_value(v, &mut ts);
        for t in ts {
            for_each_call(t, f);
        }
    });
    each_subcomp(c, &mut |sc| for_each_call(sc, f));
}

// Whether a computation dynamically applies one of `params` (forcing it as a
// call head), tracking `let`-aliases of a param. A region entry that does this is
// higher-order over a value its fused caller supplies, whose convention the
// region cannot assume, so such entries are rejected.
fn applies_param(c: &Comp, params: &BTreeSet<Sym>) -> bool {
    match c {
        Comp::App(f, _) => {
            matches!(f.as_ref(), Comp::Force(Value::Var(p)) if params.contains(p))
                || applies_param(f, params)
        }
        Comp::Bind(m, x, n) => {
            if applies_param(m, params) {
                return true;
            }
            // `let x = p` makes x an alias of the param p.
            if let Comp::Return(Value::Var(v)) = m.as_ref() {
                if params.contains(v) {
                    let mut p2 = params.clone();
                    p2.insert(*x);
                    return applies_param(n, &p2);
                }
            }
            applies_param(n, params)
        }
        Comp::If(_, t, e) => applies_param(t, params) || applies_param(e, params),
        Comp::Case(_, arms) => arms.iter().any(|(_, b)| applies_param(b, params)),
        Comp::Lam(_, b) | Comp::Mask(_, b) => applies_param(b, params),
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            applies_param(body, params)
                || return_body
                    .as_ref()
                    .is_some_and(|rb| applies_param(rb, params))
                || ops.iter().any(|op| applies_param(&op.body, params))
        }
        _ => false,
    }
}

// Whether a computation can return a closure at a tail (result) position, the
// value an entry hands back to its fused caller.
fn tail_returns_thunk(c: &Comp) -> bool {
    match c {
        Comp::Return(v) => carries_thunk(v),
        Comp::Bind(_, _, n) => tail_returns_thunk(n),
        Comp::If(_, t, e) => tail_returns_thunk(t) || tail_returns_thunk(e),
        Comp::Case(_, arms) => arms.iter().any(|(_, b)| tail_returns_thunk(b)),
        Comp::Mask(_, b) => tail_returns_thunk(b),
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            tail_returns_thunk(body)
                || return_body
                    .as_ref()
                    .is_some_and(|rb| tail_returns_thunk(rb))
                || ops.iter().any(|op| tail_returns_thunk(&op.body))
        }
        _ => false,
    }
}

// An open handler whose resume escapes into a closure (the parameter-passing
// k(v)(s) idiom with a foreign effect passing through) has a function-typed
// answer that surfaces Eff values when forced later, so its applications need
// the uniform whole-program calling convention.
pub(super) fn open_resume_escapes(c: &Comp, fl: &Latent) -> bool {
    if let Comp::Handle { body, ops, .. } = c {
        let mut s = BTreeSet::new();
        latent(body, fl, &mut s);
        for op in ops {
            s.remove(&MaskOp {
                id: op.name,
                depth: 0,
            });
        }
        if !s.is_empty() && ops.iter().any(|op| resume_in_thunk(&op.body, op.resume)) {
            return true;
        }
    }
    let mut found = false;
    each_subcomp(c, &mut |sc| found |= open_resume_escapes(sc, fl));
    found
}

fn resume_in_thunk(c: &Comp, resume: Sym) -> bool {
    let mut found = false;
    each_value(c, &mut |v| {
        let mut ts = Vec::new();
        thunks_in_value(v, &mut ts);
        for t in ts {
            found |= fv::comp(t).contains(&resume);
        }
    });
    each_subcomp(c, &mut |sc| found |= resume_in_thunk(sc, resume));
    found
}
