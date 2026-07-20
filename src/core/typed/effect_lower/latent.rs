//! Typed latent-effect analysis: which ops each function can still perform.
//!
//! Mask depth is explicit: a `MaskOp { id, depth }` means `depth` handlers of
//! the op's effect must still be skipped. A handler removes its ops at depth 0
//! and peels one level off deeper ones; a mask pushes its ops one level down.
//! The per-function sets are the least fixpoint over the call graph, so
//! termination is structural.

use std::collections::{BTreeMap, BTreeSet};

use crate::sym::Sym;

use super::super::{TypedComp, TypedCompKind, TypedCoreFn, TypedHandler};

/// A latent op with the mask depth at which it is in flight.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) struct MaskOp {
    pub(super) id: Sym,
    pub(super) depth: u32,
}

/// Per-function set of effect ops still latent in a body.
pub(super) type Latent = BTreeMap<Sym, BTreeSet<MaskOp>>;

/// The latent map: each function's ops plus those latent in its callees, as a
/// least fixpoint over the call graph.
pub(super) fn latent_map(fns: &[TypedCoreFn]) -> Latent {
    let seed: Latent = fns.iter().map(|f| (f.name(), BTreeSet::new())).collect();
    let bodies: BTreeMap<Sym, &TypedComp> = fns.iter().map(|f| (f.name(), f.body())).collect();
    crate::util::fixpoint::least_fixpoint(seed, |name, cur| {
        let mut s = BTreeSet::new();
        latent(bodies[name], cur, &mut s);
        s
    })
}

/// Each function's latent op identities, with the mask depth dropped.
pub(super) fn latent_ops(fns: &[TypedCoreFn]) -> BTreeMap<Sym, BTreeSet<Sym>> {
    latent_map(fns)
        .into_iter()
        .map(|(f, ops)| (f, ops.into_iter().map(|o| o.id).collect()))
        .collect()
}

/// The ops `c` can still perform in its enclosing context.
pub(super) fn latent(c: &TypedComp, fl: &Latent, out: &mut BTreeSet<MaskOp>) {
    match c.kind() {
        TypedCompKind::Do { operation, .. } => {
            out.insert(MaskOp {
                id: *operation,
                depth: 0,
            });
        }
        TypedCompKind::Call { callee, .. } => {
            if let Some(s) = fl.get(callee) {
                out.extend(s.iter().copied());
            }
        }
        TypedCompKind::Bind(m, _, n) => {
            latent(m, fl, out);
            latent(n, fl, out);
        }
        TypedCompKind::If(_, t, e) => {
            latent(t, fl, out);
            latent(e, fl, out);
        }
        TypedCompKind::Case(_, arms) => {
            for (_, b) in arms {
                latent(b, fl, out);
            }
        }
        TypedCompKind::App { callee, .. } => latent(callee, fl, out),
        TypedCompKind::Handle {
            body,
            return_body,
            ops,
            ..
        } => handle_escapes(body, return_body.as_deref(), ops, fl, out),
        TypedCompKind::Mask(ops, body) => {
            let mut inner = BTreeSet::new();
            latent(body, fl, &mut inner);
            out.extend(inner.into_iter().map(|l| {
                if ops.contains(&l.id) {
                    MaskOp {
                        id: l.id,
                        depth: l.depth + 1,
                    }
                } else {
                    l
                }
            }));
        }
        _ => {}
    }
}

/// The escape set of a `handle`: every op its evaluation can still perform in
/// the enclosing context. Ops the handler catches are removed at depth 0 (a
/// masked occurrence peels one level instead). The return and op clauses run
/// in the enclosing context, not under the handler, so their latents flow out
/// unmasked: a clause re-performing this handler's own op escapes outward
/// exactly like a foreign op.
// The escape set contributed by the handled action alone: `latent(body)` with
// the handler's own ops removed at depth 0 (a masked occurrence peels one level
// instead). This is the whole escape set the compatibility warning diagnostic
// looks at; the clause and return-body contributions handle_escapes adds are for
// convention planning, not that diagnostic.
pub(super) fn body_escapes(
    body: &TypedComp,
    ops: &TypedHandler,
    fl: &Latent,
    out: &mut BTreeSet<MaskOp>,
) {
    let mut inner = BTreeSet::new();
    latent(body, fl, &mut inner);
    for op in ops.arms() {
        inner.remove(&MaskOp {
            id: op.name(),
            depth: 0,
        });
    }
    out.extend(inner.into_iter().map(|l| {
        if ops.arms().iter().any(|op| op.name() == l.id) {
            MaskOp {
                id: l.id,
                depth: l.depth - 1,
            }
        } else {
            l
        }
    }));
}

pub(super) fn handle_escapes(
    body: &TypedComp,
    return_body: Option<&TypedComp>,
    ops: &TypedHandler,
    fl: &Latent,
    out: &mut BTreeSet<MaskOp>,
) {
    body_escapes(body, ops, fl, out);
    if let Some(rb) = return_body {
        latent(rb, fl, out);
    }
    for op in ops.arms() {
        // A parameter-passing clause returns a transformer thunk the handler
        // driver then applies, so the ops it re-performs are latent here, not
        // hidden behind the thunk.
        match op.body().kind() {
            TypedCompKind::Return(v) => {
                if let Some(inner) = thunk_body(v) {
                    let target = match inner.kind() {
                        TypedCompKind::Lam(_, b) => b.as_ref(),
                        _ => inner,
                    };
                    latent(target, fl, out);
                } else {
                    latent(op.body(), fl, out);
                }
            }
            _ => latent(op.body(), fl, out),
        }
    }
}

// The computation under a thunk value, looking through representation
// wrappers that do not change thunk flow.
fn thunk_body(v: &super::super::TypedValue) -> Option<&TypedComp> {
    match &super::peel(v).kind {
        super::super::TypedValueKind::Thunk(c) => Some(c),
        _ => None,
    }
}
