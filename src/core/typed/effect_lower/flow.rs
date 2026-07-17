//! Typed interprocedural thunk-effect flow.
//!
//! A stream combinator returns a thunk whose body performs effects only once
//! forced, so the free-monad escape analysis would push the whole program into
//! monadic mode. Instead the active evidence is threaded to each thunk at its
//! force site, which needs, for every function, the op signature of the thunk
//! it returns (`ret`) and of each thunk-valued parameter (`param`). `ret` reads
//! only the latent map, but a parameter's signature flows from its call sites,
//! whose arguments may themselves be parameters, so the two are solved
//! together as one fixpoint.

use std::collections::{BTreeMap, BTreeSet};

use crate::sym::Sym;

use super::super::{
    TypedBinder, TypedComp, TypedCompKind, TypedCoreFn, TypedValue, TypedValueKind,
};
use super::latent::{latent, Latent, MaskOp};
use super::peel;
use super::walk::each_value;

/// The op set a thunk performs when forced (mask-aware, like `latent`).
pub(super) type Sig = BTreeSet<MaskOp>;
/// Signatures of the thunk-valued variables in scope.
pub(super) type Loc = BTreeMap<Sym, Sig>;

pub(super) struct ThunkFlow {
    pub(super) ret: BTreeMap<Sym, Sig>,
    pub(super) param: BTreeMap<Sym, Vec<Sig>>,
}

pub(super) fn analyze(fns: &[TypedCoreFn], lat: &Latent) -> ThunkFlow {
    let mut flow = ThunkFlow {
        ret: fns.iter().map(|f| (f.name(), Sig::new())).collect(),
        param: fns
            .iter()
            .map(|f| (f.name(), vec![Sig::new(); f.params().len()]))
            .collect(),
    };
    loop {
        let mut upd: BTreeMap<Sym, Vec<Sig>> = fns
            .iter()
            .map(|f| (f.name(), vec![Sig::new(); f.params().len()]))
            .collect();
        let mut ret = BTreeMap::new();
        for f in fns {
            let loc: Loc = f
                .params()
                .iter()
                .map(TypedBinder::name)
                .zip(flow.param[&f.name()].iter().cloned())
                .collect();
            ret.insert(f.name(), props(f.body(), &loc, lat, &flow, &mut upd));
        }
        // `ret`/`upd` are rebuilt each pass from the same function list, so
        // they carry the same key sets as `flow.ret`/`flow.param`. BTreeMaps
        // with equal keys iterate in the same order, so zipping their values
        // aligns each function's accumulated signature with its freshly
        // computed one without a fallible lookup.
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

/// The op signature of a value: a lambda thunk performs the ops latent in its
/// body; a variable carries whatever signature flowed to it. Anything else
/// reports nothing here and is rejected by the trackability guard before
/// lowering commits.
pub(super) fn value_sig(v: &TypedValue, loc: &Loc, lat: &Latent) -> Sig {
    match &peel(v).kind {
        TypedValueKind::Thunk(c) => {
            let body = match c.kind() {
                TypedCompKind::Lam(_, b) => b.as_ref(),
                _ => c.as_ref(),
            };
            let mut s = Sig::new();
            latent(body, lat, &mut s);
            s
        }
        TypedValueKind::Var { name, .. } => loc.get(name).cloned().unwrap_or_default(),
        _ => Sig::new(),
    }
}

/// Whether any effectful thunk escapes into a position the rewrite cannot
/// thread evidence to: buried in a constructor or tuple (extracted later by a
/// `case` the flow does not follow), or handed to a dynamic application or
/// effect op (whose callee is not a statically known function). When this
/// holds the program is not evidence-eligible and falls back to the free
/// monad.
pub(super) fn escapes(fns: &[TypedCoreFn], lat: &Latent, flow: &ThunkFlow) -> bool {
    !escaping_fns(fns, lat, flow).is_empty()
}

/// The functions whose body lets an effectful thunk escape untrackably (the
/// per-function witnesses of [`escapes`]). Local monadification seeds its
/// monadic region from these.
pub(super) fn escaping_fns(fns: &[TypedCoreFn], lat: &Latent, flow: &ThunkFlow) -> BTreeSet<Sym> {
    fns.iter()
        .filter(|f| {
            let loc: Loc = f
                .params()
                .iter()
                .map(TypedBinder::name)
                .zip(flow.param[&f.name()].iter().cloned())
                .collect();
            esc(f.body(), &loc, lat, flow)
        })
        .map(TypedCoreFn::name)
        .collect()
}

// An effectful thunk buried inside a constructor or tuple (a top-level thunk
// value is not buried: it is tracked wherever it flows).
fn buried(v: &TypedValue, loc: &Loc, lat: &Latent) -> bool {
    match &peel(v).kind {
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => fields
            .iter()
            .any(|f| !value_sig(f, loc, lat).is_empty() || buried(f, loc, lat)),
        TypedValueKind::UnboxedRecord(fields) => fields
            .iter()
            .any(|(_, f)| !value_sig(f, loc, lat).is_empty() || buried(f, loc, lat)),
        _ => false,
    }
}

fn esc(c: &TypedComp, loc: &Loc, lat: &Latent, flow: &ThunkFlow) -> bool {
    match c.kind() {
        TypedCompKind::Return(v) => buried(v, loc, lat) || in_thunk(v, loc, lat, flow),
        TypedCompKind::Call { args, .. } => args
            .iter()
            .any(|a| buried(a, loc, lat) || in_thunk(a, loc, lat, flow)),
        TypedCompKind::App { args, .. } | TypedCompKind::Do { args, .. } => args
            .iter()
            .any(|a| !value_sig(a, loc, lat).is_empty() || buried(a, loc, lat)),
        TypedCompKind::Bind(m, x, n) => {
            esc(m, loc, lat, flow) || {
                let mut loc2 = loc.clone();
                loc2.insert(x.name(), result_sig(m, loc, lat, flow));
                esc(n, &loc2, lat, flow)
            }
        }
        TypedCompKind::If(_, t, e) => esc(t, loc, lat, flow) || esc(e, loc, lat, flow),
        TypedCompKind::Case(_, arms) => arms.iter().any(|(_, b)| esc(b, loc, lat, flow)),
        TypedCompKind::Lam(ps, b) => {
            let mut loc2 = loc.clone();
            for p in ps {
                loc2.insert(p.name(), Sig::new());
            }
            esc(b, &loc2, lat, flow)
        }
        TypedCompKind::Mask(_, b) => esc(b, loc, lat, flow),
        TypedCompKind::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            esc(body, loc, lat, flow)
                || return_body
                    .as_ref()
                    .is_some_and(|rb| esc(rb, loc, lat, flow))
                || ops.arms().iter().any(|op| esc(op.body(), loc, lat, flow))
        }
        _ => {
            let mut found = false;
            each_value(c, &mut |v| found |= in_thunk(v, loc, lat, flow));
            found
        }
    }
}

// Recurse into a thunk's own body looking for escapes there.
fn in_thunk(v: &TypedValue, loc: &Loc, lat: &Latent, flow: &ThunkFlow) -> bool {
    match &peel(v).kind {
        TypedValueKind::Thunk(c) => {
            if let TypedCompKind::Lam(ps, b) = c.kind() {
                let mut loc2 = loc.clone();
                for p in ps {
                    loc2.insert(p.name(), Sig::new());
                }
                esc(b, &loc2, lat, flow)
            } else {
                esc(c, loc, lat, flow)
            }
        }
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => {
            fields.iter().any(|f| in_thunk(f, loc, lat, flow))
        }
        TypedValueKind::UnboxedRecord(fields) => {
            fields.iter().any(|(_, f)| in_thunk(f, loc, lat, flow))
        }
        _ => false,
    }
}

/// The signature of the thunk a computation returns, in a context where `loc`
/// gives the signatures of the thunk-valued variables in scope. Read-only twin
/// of `props`'s result path, used by the rewrite to track let-bound thunks.
pub(super) fn result_sig(c: &TypedComp, loc: &Loc, lat: &Latent, flow: &ThunkFlow) -> Sig {
    match c.kind() {
        TypedCompKind::Return(v) => value_sig(v, loc, lat),
        TypedCompKind::Call { callee, .. } => flow.ret.get(callee).cloned().unwrap_or_default(),
        TypedCompKind::Bind(m, x, n) => {
            let rm = result_sig(m, loc, lat, flow);
            let mut loc2 = loc.clone();
            loc2.insert(x.name(), rm);
            result_sig(n, &loc2, lat, flow)
        }
        TypedCompKind::If(_, t, e) => {
            let mut s = result_sig(t, loc, lat, flow);
            merge(&mut s, &result_sig(e, loc, lat, flow));
            s
        }
        TypedCompKind::Case(_, arms) => {
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
    c: &TypedComp,
    loc: &Loc,
    lat: &Latent,
    flow: &ThunkFlow,
    upd: &mut BTreeMap<Sym, Vec<Sig>>,
) -> Sig {
    match c.kind() {
        TypedCompKind::Return(v) => {
            visit_value(v, loc, lat, flow, upd);
            value_sig(v, loc, lat)
        }
        TypedCompKind::Call { callee, args, .. } => {
            for (i, a) in args.iter().enumerate() {
                visit_value(a, loc, lat, flow, upd);
                if let Some(slots) = upd.get_mut(callee) {
                    if let Some(slot) = slots.get_mut(i) {
                        merge(slot, &value_sig(a, loc, lat));
                    }
                }
            }
            flow.ret.get(callee).cloned().unwrap_or_default()
        }
        TypedCompKind::Bind(m, x, n) => {
            let rm = props(m, loc, lat, flow, upd);
            let mut loc2 = loc.clone();
            loc2.insert(x.name(), rm);
            props(n, &loc2, lat, flow, upd)
        }
        TypedCompKind::If(_, t, e) => {
            let mut s = props(t, loc, lat, flow, upd);
            merge(&mut s, &props(e, loc, lat, flow, upd));
            s
        }
        TypedCompKind::Case(_, arms) => {
            let mut s = Sig::new();
            for (_, b) in arms {
                merge(&mut s, &props(b, loc, lat, flow, upd));
            }
            s
        }
        TypedCompKind::Lam(ps, b) => {
            let mut loc2 = loc.clone();
            for p in ps {
                loc2.insert(p.name(), Sig::new());
            }
            props(b, &loc2, lat, flow, upd);
            Sig::new()
        }
        TypedCompKind::App { callee, args, .. } => {
            props(callee, loc, lat, flow, upd);
            for a in args {
                visit_value(a, loc, lat, flow, upd);
            }
            Sig::new()
        }
        TypedCompKind::Mask(_, b) => props(b, loc, lat, flow, upd),
        TypedCompKind::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            props(body, loc, lat, flow, upd);
            if let Some(rb) = return_body {
                props(rb, loc, lat, flow, upd);
            }
            for op in ops.arms() {
                props(op.body(), loc, lat, flow, upd);
            }
            Sig::new()
        }
        _ => {
            each_value(c, &mut |v| visit_value(v, loc, lat, flow, upd));
            Sig::new()
        }
    }
}

fn visit_value(
    v: &TypedValue,
    loc: &Loc,
    lat: &Latent,
    flow: &ThunkFlow,
    upd: &mut BTreeMap<Sym, Vec<Sig>>,
) {
    match &peel(v).kind {
        TypedValueKind::Thunk(c) => {
            if let TypedCompKind::Lam(ps, b) = c.kind() {
                let mut loc2 = loc.clone();
                for p in ps {
                    loc2.insert(p.name(), Sig::new());
                }
                props(b, &loc2, lat, flow, upd);
            } else {
                props(c, loc, lat, flow, upd);
            }
        }
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => {
            for f in fields {
                visit_value(f, loc, lat, flow, upd);
            }
        }
        TypedValueKind::UnboxedRecord(fields) => {
            for (_, f) in fields {
                visit_value(f, loc, lat, flow, upd);
            }
        }
        _ => {}
    }
}
