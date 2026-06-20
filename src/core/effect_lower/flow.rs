//! Interprocedural thunk-effect flow for stream fusion.
//!
//! A stream combinator returns a thunk whose body performs effects only once
//! forced (`srange(lo,hi) = \u -> srange_go(lo,hi)`), so the free-monad escape
//! analysis would push the whole program into monadic mode. Instead the active
//! evidence is threaded to each thunk at its force site. That needs, for every
//! function, the op signature of the thunk it returns (`ret`) and of each
//! thunk-valued parameter (`param`); a least fixpoint over the call graph
//! computes both. `ret` reads only the latent map, but a parameter's signature
//! flows from its call sites, whose arguments may themselves be parameters, so
//! the two are solved together.

use std::collections::{BTreeMap, BTreeSet};

use super::{latent, Latent, MaskOp};
use crate::core::cbpv::{Comp, Core, Value};
use crate::sym::Sym;

// Op set a thunk performs when forced (mask-aware, like `latent`).
pub(super) type Sig = BTreeSet<MaskOp>;
// Signatures of the thunk-valued variables in scope.
pub(super) type Loc = BTreeMap<Sym, Sig>;

pub(super) struct ThunkFlow {
    pub ret: BTreeMap<Sym, Sig>,
    pub param: BTreeMap<Sym, Vec<Sig>>,
}

pub(super) fn analyze(core: &Core, lat: &Latent) -> ThunkFlow {
    let mut flow = ThunkFlow {
        ret: core.fns.iter().map(|f| (f.name, Sig::new())).collect(),
        param: core
            .fns
            .iter()
            .map(|f| (f.name, vec![Sig::new(); f.params.len()]))
            .collect(),
    };
    loop {
        let mut upd: BTreeMap<Sym, Vec<Sig>> = core
            .fns
            .iter()
            .map(|f| (f.name, vec![Sig::new(); f.params.len()]))
            .collect();
        let mut ret = BTreeMap::new();
        for f in &core.fns {
            let loc: Loc = f
                .params
                .iter()
                .copied()
                .zip(flow.param[&f.name].iter().cloned())
                .collect();
            ret.insert(f.name, props(&f.body, &loc, lat, &flow, &mut upd));
        }
        // `ret`/`upd` are rebuilt each pass from `core.fns`, so they carry the
        // same key sets as `flow.ret`/`flow.param`. BTreeMaps with equal keys
        // iterate in the same order, so zipping their values aligns each
        // function's accumulated signature with its freshly computed one without
        // a fallible lookup.
        let mut changed = false;
        for (slot, new) in flow.ret.values_mut().zip(ret.values()) {
            changed |= merge(slot, new);
        }
        for (ps, new) in flow.param.values_mut().zip(upd.values()) {
            for (slot, new) in ps.iter_mut().zip(new) {
                changed |= merge(slot, new);
            }
        }
        if !changed {
            break;
        }
    }
    flow
}

fn merge(into: &mut Sig, from: &Sig) -> bool {
    let before = into.len();
    into.extend(from.iter().copied());
    into.len() != before
}

// The op signature of a value: a lambda thunk performs the ops latent in its
// body; a variable carries whatever signature flowed to it. Anything else (an
// effectful thunk nested in a constructor, a non-lambda thunk) reports nothing
// here and is rejected by the trackability guard before lowering commits.
pub(super) fn value_sig(v: &Value, loc: &Loc, lat: &Latent) -> Sig {
    match v {
        Value::Thunk(c) => {
            let body = if let Comp::Lam(_, b) = c.as_ref() {
                b
            } else {
                c
            };
            let mut s = Sig::new();
            latent(body, lat, &mut s);
            s
        }
        Value::Var(x) => loc.get(x).cloned().unwrap_or_default(),
        _ => Sig::new(),
    }
}

// Whether any effectful thunk escapes into a position the rewrite cannot
// thread evidence to: buried in a constructor or tuple (extracted later by a
// `case` the flow does not follow), or handed to a dynamic application or
// effect op (whose callee is not a statically known function). When this holds
// the program is not evidence-eligible and falls back to the free monad.
// Effectful thunks that only flow through static call arguments, returns, and
// let-bindings are tracked precisely, so they do not escape.
pub(super) fn escapes(core: &Core, lat: &Latent, flow: &ThunkFlow) -> bool {
    core.fns.iter().any(|f| {
        let loc: Loc = f
            .params
            .iter()
            .copied()
            .zip(flow.param[&f.name].iter().cloned())
            .collect();
        esc(&f.body, &loc, lat, flow)
    })
}

// An effectful thunk buried inside a constructor or tuple (a top-level thunk
// value is not buried: it is tracked wherever it flows).
fn buried(v: &Value, loc: &Loc, lat: &Latent) -> bool {
    match v {
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs
            .iter()
            .any(|f| !value_sig(f, loc, lat).is_empty() || buried(f, loc, lat)),
        _ => false,
    }
}

fn esc(c: &Comp, loc: &Loc, lat: &Latent, flow: &ThunkFlow) -> bool {
    match c {
        Comp::Return(v) => buried(v, loc, lat) || in_thunk(v, loc, lat, flow),
        Comp::Call(_, args) => args
            .iter()
            .any(|a| buried(a, loc, lat) || in_thunk(a, loc, lat, flow)),
        Comp::App(_, args) | Comp::Do(_, args) => args
            .iter()
            .any(|a| !value_sig(a, loc, lat).is_empty() || buried(a, loc, lat)),
        Comp::Bind(m, x, n) => {
            esc(m, loc, lat, flow) || {
                let mut loc2 = loc.clone();
                loc2.insert(*x, result_sig(m, loc, lat, flow));
                esc(n, &loc2, lat, flow)
            }
        }
        Comp::If(_, t, e) => esc(t, loc, lat, flow) || esc(e, loc, lat, flow),
        Comp::Case(_, arms) => arms.iter().any(|(_, b)| esc(b, loc, lat, flow)),
        Comp::Lam(ps, b) => {
            let mut loc2 = loc.clone();
            for p in ps {
                loc2.insert(*p, Sig::new());
            }
            esc(b, &loc2, lat, flow)
        }
        Comp::Mask(_, b) => esc(b, loc, lat, flow),
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            esc(body, loc, lat, flow)
                || return_body
                    .as_ref()
                    .is_some_and(|rb| esc(rb, loc, lat, flow))
                || ops.iter().any(|op| esc(&op.body, loc, lat, flow))
        }
        _ => {
            let mut found = false;
            super::each_value(c, &mut |v| found |= in_thunk(v, loc, lat, flow));
            found
        }
    }
}

// Recurse into a thunk's own body looking for escapes there.
fn in_thunk(v: &Value, loc: &Loc, lat: &Latent, flow: &ThunkFlow) -> bool {
    match v {
        Value::Thunk(c) => {
            if let Comp::Lam(ps, b) = c.as_ref() {
                let mut loc2 = loc.clone();
                for p in ps {
                    loc2.insert(*p, Sig::new());
                }
                esc(b, &loc2, lat, flow)
            } else {
                esc(c, loc, lat, flow)
            }
        }
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.iter().any(|f| in_thunk(f, loc, lat, flow)),
        _ => false,
    }
}

// The signature of the thunk a computation returns, in a context where `loc`
// gives the signatures of the thunk-valued variables in scope. Read-only twin
// of `props`'s result path, used by the rewrite to track let-bound thunks.
pub(super) fn result_sig(c: &Comp, loc: &Loc, lat: &Latent, flow: &ThunkFlow) -> Sig {
    match c {
        Comp::Return(v) => value_sig(v, loc, lat),
        Comp::Call(g, _) => flow.ret.get(g).cloned().unwrap_or_default(),
        Comp::Bind(m, x, n) => {
            let rm = result_sig(m, loc, lat, flow);
            let mut loc2 = loc.clone();
            loc2.insert(*x, rm);
            result_sig(n, &loc2, lat, flow)
        }
        Comp::If(_, t, e) => {
            let mut s = result_sig(t, loc, lat, flow);
            merge(&mut s, &result_sig(e, loc, lat, flow));
            s
        }
        Comp::Case(_, arms) => {
            let mut s = Sig::new();
            for (_, b) in arms {
                merge(&mut s, &result_sig(b, loc, lat, flow));
            }
            s
        }
        _ => Sig::new(),
    }
}

// Full traversal: thread the local thunk-signature environment, record the
// signature each call site demands of its callee's parameters, and return the
// signature of the value this computation ultimately returns.
fn props(
    c: &Comp,
    loc: &Loc,
    lat: &Latent,
    flow: &ThunkFlow,
    upd: &mut BTreeMap<Sym, Vec<Sig>>,
) -> Sig {
    match c {
        Comp::Return(v) => {
            visit_value(v, loc, lat, flow, upd);
            value_sig(v, loc, lat)
        }
        Comp::Call(g, args) => {
            for (i, a) in args.iter().enumerate() {
                visit_value(a, loc, lat, flow, upd);
                if let Some(slots) = upd.get_mut(g) {
                    if let Some(slot) = slots.get_mut(i) {
                        merge(slot, &value_sig(a, loc, lat));
                    }
                }
            }
            flow.ret.get(g).cloned().unwrap_or_default()
        }
        Comp::Bind(m, x, n) => {
            let rm = props(m, loc, lat, flow, upd);
            let mut loc2 = loc.clone();
            loc2.insert(*x, rm);
            props(n, &loc2, lat, flow, upd)
        }
        Comp::If(_, t, e) => {
            let mut s = props(t, loc, lat, flow, upd);
            merge(&mut s, &props(e, loc, lat, flow, upd));
            s
        }
        Comp::Case(_, arms) => {
            let mut s = Sig::new();
            for (_, b) in arms {
                merge(&mut s, &props(b, loc, lat, flow, upd));
            }
            s
        }
        Comp::Lam(ps, b) => {
            let mut loc2 = loc.clone();
            for p in ps {
                loc2.insert(*p, Sig::new());
            }
            props(b, &loc2, lat, flow, upd);
            Sig::new()
        }
        Comp::App(f, args) => {
            props(f, loc, lat, flow, upd);
            for a in args {
                visit_value(a, loc, lat, flow, upd);
            }
            Sig::new()
        }
        Comp::Mask(_, b) => props(b, loc, lat, flow, upd),
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            props(body, loc, lat, flow, upd);
            if let Some(rb) = return_body {
                props(rb, loc, lat, flow, upd);
            }
            for op in ops {
                props(&op.body, loc, lat, flow, upd);
            }
            Sig::new()
        }
        _ => {
            super::each_value(c, &mut |v| visit_value(v, loc, lat, flow, upd));
            Sig::new()
        }
    }
}

fn visit_value(
    v: &Value,
    loc: &Loc,
    lat: &Latent,
    flow: &ThunkFlow,
    upd: &mut BTreeMap<Sym, Vec<Sig>>,
) {
    match v {
        Value::Thunk(c) => {
            if let Comp::Lam(ps, b) = c.as_ref() {
                let mut loc2 = loc.clone();
                for p in ps {
                    loc2.insert(*p, Sig::new());
                }
                props(b, &loc2, lat, flow, upd);
            } else {
                props(c, loc, lat, flow, upd);
            }
        }
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => {
            for f in fs {
                visit_value(f, loc, lat, flow, upd);
            }
        }
        _ => {}
    }
}
