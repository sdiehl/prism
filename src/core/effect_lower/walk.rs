//! Generic CBPV traversal/query combinators.

use std::collections::BTreeSet;

use super::{Latent, MaskOp};
use crate::core::cbpv::{Comp, HandleOp, Value};
use crate::sym::Sym;

pub(super) fn thunks_in_comp<'a>(c: &'a Comp, out: &mut Vec<&'a Comp>) {
    each_value(c, &mut |v| thunks_in_value(v, out));
    each_subcomp(c, &mut |sc| thunks_in_comp(sc, out));
}

pub(super) fn thunks_in_value<'a>(v: &'a Value, out: &mut Vec<&'a Comp>) {
    match v {
        Value::Thunk(c) => {
            out.push(c);
            thunks_in_comp(c, out);
        }
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => {
            for f in fs {
                thunks_in_value(f, out);
            }
        }
        _ => {}
    }
}

pub(super) fn each_value<'a>(c: &'a Comp, f: &mut impl FnMut(&'a Value)) {
    match c {
        Comp::Return(v)
        | Comp::Force(v)
        | Comp::Error(v)
        | Comp::FloatBuiltin(_, v)
        | Comp::Neg(_, v)
        | Comp::Dup(v)
        | Comp::Drop(v)
        // Reuse nodes only arise after this pass; keep the traversal total. The
        // freed cell and the reuse constructor are the value positions.
        | Comp::WithReuse { freed: v, .. }
        | Comp::Reuse(_, v)
        // Ref ops arise from `erase_local_vars` at the top of `lower`, so the
        // analyses below must visit their values (e.g. a thunk a var holds whose
        // body still performs another effect).
        | Comp::RefNew(v)
        | Comp::RefGet(v)
        | Comp::If(v, ..)
        | Comp::Case(v, _) => f(v),
        Comp::Prim(_, a, b) | Comp::RefSet(a, b) => {
            f(a);
            f(b);
        }
        Comp::App(_, args)
        | Comp::Call(_, args)
        | Comp::Do(_, args)
        | Comp::StrBuiltin(_, args)
        | Comp::Io(_, args) => {
            for a in args {
                f(a);
            }
        }
        _ => {}
    }
}

pub(super) fn each_subcomp<'a>(c: &'a Comp, f: &mut impl FnMut(&'a Comp)) {
    match c {
        Comp::Bind(m, _, n) => {
            f(m);
            f(n);
        }
        Comp::Lam(_, b) | Comp::Mask(_, b) | Comp::WithReuse { body: b, .. } => f(b),
        Comp::App(g, _) => f(g),
        Comp::If(_, t, e) => {
            f(t);
            f(e);
        }
        Comp::Case(_, arms) => {
            for (_, b) in arms {
                f(b);
            }
        }
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            f(body);
            if let Some(rb) = return_body {
                f(rb);
            }
            for o in ops {
                f(&o.body);
            }
        }
        _ => {}
    }
}

pub(super) fn contains_mask(c: &Comp) -> bool {
    if matches!(c, Comp::Mask(..)) {
        return true;
    }
    let mut found = false;
    each_value(c, &mut |v| {
        let mut ts = Vec::new();
        thunks_in_value(v, &mut ts);
        found |= ts.iter().any(|t| contains_mask(t));
    });
    each_subcomp(c, &mut |sc| found |= contains_mask(sc));
    found
}

// Latent sets track mask depth in a `MaskOp { id, depth }`: depth d means d
// handlers of the op's effect must still be skipped. A handler removes its ops
// at depth 0 and peels one level off deeper ones; a mask pushes its ops one
// level down.
pub(super) fn latent(c: &Comp, fl: &Latent, out: &mut BTreeSet<MaskOp>) {
    match c {
        Comp::Do(op, _) => {
            out.insert(MaskOp { id: *op, depth: 0 });
        }
        Comp::Call(g, _) => {
            if let Some(s) = fl.get(g) {
                out.extend(s.iter().copied());
            }
        }
        Comp::Bind(m, _, n) => {
            latent(m, fl, out);
            latent(n, fl, out);
        }
        Comp::If(_, t, e) => {
            latent(t, fl, out);
            latent(e, fl, out);
        }
        Comp::Case(_, arms) => {
            for (_, b) in arms {
                latent(b, fl, out);
            }
        }
        Comp::App(f, _) => latent(f, fl, out),
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => handle_escapes(body, return_body.as_deref(), ops, fl, out),
        Comp::Mask(ops, body) => {
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

// The escape set of a `handle`: every op its evaluation can still perform in
// the enclosing context. Ops the handler catches are removed from the body's
// latents at depth 0 (a masked occurrence peels one level instead). The
// return clause and the op clauses run in the enclosing context, not under
// the handler (a deep handler reinstalls itself only around `resume`), so
// their latents flow out unmasked: a clause that re-performs this handler's
// own op escapes it outward exactly like a foreign op. Both `latent` and
// `is_open` classify from this one set, so interprocedural flow and
// open/closed classification cannot drift.
pub(super) fn handle_escapes(
    body: &Comp,
    return_body: Option<&Comp>,
    ops: &[HandleOp],
    fl: &Latent,
    out: &mut BTreeSet<MaskOp>,
) {
    let mut inner = BTreeSet::new();
    latent(body, fl, &mut inner);
    for op in ops {
        inner.remove(&MaskOp {
            id: op.name,
            depth: 0,
        });
    }
    out.extend(inner.into_iter().map(|l| {
        if ops.iter().any(|op| op.name == l.id) {
            MaskOp {
                id: l.id,
                depth: l.depth - 1,
            }
        } else {
            l
        }
    }));
    if let Some(rb) = return_body {
        latent(rb, fl, out);
    }
    for op in ops {
        // A parameter-passing clause returns a transformer thunk that the
        // handler driver then applies, so the ops it re-performs (a
        // `stake`-style `\acc -> { do op(..); resume(..) }`) are latent
        // here, not hidden behind the thunk.
        match &op.body {
            Comp::Return(Value::Thunk(t)) => {
                let inner = if let Comp::Lam(_, b) = t.as_ref() {
                    b
                } else {
                    t
                };
                latent(inner, fl, out);
            }
            _ => latent(&op.body, fl, out),
        }
    }
}

pub(super) fn collect_ops(c: &Comp, out: &mut BTreeSet<Sym>) {
    match c {
        Comp::Do(op, _) => {
            out.insert(*op);
        }
        Comp::Handle { ops, .. } => {
            for op in ops {
                out.insert(op.name);
            }
        }
        Comp::Mask(ops, _) => out.extend(ops.iter().copied()),
        _ => {}
    }
    each_value(c, &mut |v| {
        let mut ts = Vec::new();
        thunks_in_value(v, &mut ts);
        for t in ts {
            collect_ops(t, out);
        }
    });
    each_subcomp(c, &mut |sc| collect_ops(sc, out));
}
