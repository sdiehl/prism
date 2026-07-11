use std::collections::BTreeMap;

use crate::sym::Sym;

use super::super::cbpv::{Comp, Core, CoreFn, CorePat, HandleOp, Value};
use super::super::fv::{comp as freev, pat_vars};
use super::{borrow_mask, borrowed_at, count_val, Set, Sigs};

#[must_use]
pub fn insert_rc(core: &Core, sigs: &Sigs) -> Core {
    Core {
        fns: core
            .fns
            .iter()
            .map(|f| {
                let mask = sigs.get(&f.name).map(Vec::as_slice);
                let owned: Set = f
                    .params
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| !borrowed_at(mask, *i))
                    .map(|(_, p)| *p)
                    .collect();
                let borrowed: Set = f
                    .params
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| borrowed_at(mask, *i))
                    .map(|(_, p)| *p)
                    .collect();
                CoreFn {
                    name: f.name,
                    params: f.params.clone(),
                    dict_arity: f.dict_arity,
                    body: rc(&f.body, &owned, &borrowed, sigs),
                }
            })
            .collect(),
    }
}

// Emit dup/drop in a name-stable order. `Sym` orders by intern id (first-seen),
// so iterating a `Set` directly would make the inserted ops depend on interning
// order. Sorting by name keeps codegen output byte-stable.
fn by_name(syms: impl IntoIterator<Item = Sym>) -> Vec<Sym> {
    let mut v: Vec<Sym> = syms.into_iter().collect();
    v.sort_by(|a, b| a.as_str().cmp(b.as_str()));
    v
}

fn seq(op: Comp, k: Comp) -> Comp {
    Comp::Bind(Box::new(op), "_".into(), Box::new(k))
}

fn dup(v: Sym, k: Comp) -> Comp {
    seq(Comp::Dup(Value::Var(v)), k)
}

fn drop_(v: Sym, k: Comp) -> Comp {
    seq(Comp::Drop(Value::Var(v)), k)
}

fn rc(c: &Comp, owned: &Set, borrowed: &Set, sigs: &Sigs) -> Comp {
    match c {
        Comp::Bind(m, x, n) => {
            let fm = freev(m);
            let mut fnn = freev(n);
            fnn.remove(x);
            let owned_m: Set = owned.intersection(&fm).copied().collect();
            let owned_n: Set = owned.intersection(&fnn).copied().collect();
            let shared = by_name(owned_m.intersection(&owned_n).copied());
            let dead = by_name(
                owned
                    .iter()
                    .filter(|v| !fm.contains(*v) && !fnn.contains(*v))
                    .copied(),
            );
            let borrowed_m: Set = borrowed.intersection(&fm).copied().collect();
            let borrowed_n: Set = borrowed.intersection(&fnn).copied().collect();
            let m2 = rc(m, &owned_m, &borrowed_m, sigs);
            let mut owned_n2 = owned_n;
            owned_n2.insert(*x);
            let n2 = rc(n, &owned_n2, &borrowed_n, sigs);
            let mut out = Comp::Bind(Box::new(m2), *x, Box::new(n2));
            for v in shared {
                out = dup(v, out);
            }
            for v in dead {
                out = drop_(v, out);
            }
            out
        }
        Comp::If(v, t, e) => Comp::If(
            v.clone(),
            Box::new(rc(t, owned, borrowed, sigs)),
            Box::new(rc(e, owned, borrowed, sigs)),
        ),
        Comp::Case(scrut, arms) => Comp::Case(
            scrut.clone(),
            arms.iter()
                .map(|(p, body)| (p.clone(), rc_arm(p, body, owned, borrowed, sigs)))
                .collect(),
        ),
        Comp::Lam(ps, body) => {
            let ps_set: Set = ps.iter().copied().collect();
            let caps: Set = freev(body).difference(&ps_set).copied().collect();
            Comp::Lam(ps.clone(), Box::new(rc(body, &ps_set, &caps, sigs)))
        }
        // Reachable only via the pre-lowering `dump fbip` display path,
        // compiled pipelines always lower handles first.
        Comp::Mask(ops, b) => Comp::Mask(ops.clone(), Box::new(rc(b, owned, borrowed, sigs))),
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => Comp::Handle {
            body: Box::new(rc(body, &Set::new(), &Set::new(), sigs)),
            return_var: *return_var,
            return_body: return_body.as_deref().map(|rb| {
                let o = return_var.iter().copied().collect();
                Box::new(rc(rb, &o, &Set::new(), sigs))
            }),
            ops: ops.rebuild(|op| {
                let o = op.params.iter().copied().collect();
                HandleOp {
                    name: op.name,
                    params: op.params.clone(),
                    resume: op.resume,
                    body: rc(&op.body, &o, &Set::new(), sigs),
                }
            }),
        },
        leaf => {
            let mut counts = BTreeMap::new();
            leaf_counts(leaf, &mut counts, sigs);
            let mut out = rc_thunks(leaf, sigs);
            for v in by_name(owned.iter().copied()) {
                match counts.get(&v).copied().unwrap_or(0) {
                    0 => out = drop_(v, out),
                    k => {
                        for _ in 1..k {
                            out = dup(v, out);
                        }
                    }
                }
            }
            for v in by_name(borrowed.iter().copied()) {
                for _ in 0..counts.get(&v).copied().unwrap_or(0) {
                    out = dup(v, out);
                }
            }
            out
        }
    }
}

// A thunk is a closure: its free vars are captured by the cell and borrowed
// inside the body (the cell owns them, a consuming use dups first, the body never
// drops them). rc never descends into values, so without this the body of every
// `\..` passed as an argument would keep its raw elaborated form and consume a
// borrowed capture with no dup, freeing a shared spine out from under the caller.
// A Lam recomputes its own params/captures; a bare suspended computation borrows
// all of its free vars.
fn rc_value(v: &Value, sigs: &Sigs) -> Value {
    match v {
        Value::Thunk(c) => Value::Thunk(Box::new(rc(c, &Set::new(), &freev(c), sigs))),
        Value::Ctor(t, i, fs) => {
            Value::Ctor(*t, *i, fs.iter().map(|f| rc_value(f, sigs)).collect())
        }
        Value::Tuple(fs) => Value::Tuple(fs.iter().map(|f| rc_value(f, sigs)).collect()),
        other => other.clone(),
    }
}

fn rc_thunks(c: &Comp, sigs: &Sigs) -> Comp {
    let rv = |v: &Value| rc_value(v, sigs);
    match c {
        Comp::Return(v) => Comp::Return(rv(v)),
        Comp::Force(v) => Comp::Force(rv(v)),
        Comp::Error(v) => Comp::Error(rv(v)),
        Comp::Io(op, args) => Comp::Io(*op, args.iter().map(rv).collect()),
        Comp::FloatBuiltin(op, v) => Comp::FloatBuiltin(*op, rv(v)),
        Comp::Neg(l, v) => Comp::Neg(*l, rv(v)),
        Comp::Prim(op, a, b) => Comp::Prim(*op, rv(a), rv(b)),
        Comp::Call(n, args) => Comp::Call(*n, args.iter().map(rv).collect()),
        Comp::Do(n, args) => Comp::Do(*n, args.iter().map(rv).collect()),
        Comp::StrBuiltin(b, args) => Comp::StrBuiltin(*b, args.iter().map(rv).collect()),
        Comp::App(f, args) => {
            Comp::App(Box::new(rc_thunks(f, sigs)), args.iter().map(rv).collect())
        }
        Comp::RefNew(v) => Comp::RefNew(rv(v)),
        Comp::RefGet(v) => Comp::RefGet(rv(v)),
        Comp::RefSet(c, v) => Comp::RefSet(rv(c), rv(v)),
        other => other.clone(),
    }
}

fn rc_arm(p: &CorePat, body: &Comp, owned: &Set, borrowed: &Set, sigs: &Sigs) -> Comp {
    let fb = freev(body);
    let mut fields = Set::new();
    pat_vars(p, &mut fields);
    let live = by_name(fields.intersection(&fb).copied());
    let dead = by_name(owned.iter().filter(|v| !fb.contains(*v)).copied());
    let mut owned_b: Set = owned.intersection(&fb).copied().collect();
    owned_b.extend(live.iter().copied());
    let borrowed_b: Set = borrowed.intersection(&fb).copied().collect();
    let mut out = rc(body, &owned_b, &borrowed_b, sigs);
    for v in &dead {
        out = drop_(*v, out);
    }
    for v in live.iter().rev() {
        out = dup(*v, out);
    }
    out
}

fn leaf_counts(c: &Comp, out: &mut BTreeMap<Sym, usize>, sigs: &Sigs) {
    match c {
        Comp::Return(v)
        | Comp::Force(v)
        | Comp::Error(v)
        | Comp::FloatBuiltin(_, v)
        | Comp::Neg(_, v)
        // A `var` cell flows as an ordinary owned value: each read/write consumes
        // a reference (the rc pass dups so each use has one), and `ref_set`
        // overwrites the cell in place. So a Ref op counts its cell and value like
        // any other consuming leaf.
        | Comp::RefNew(v)
        | Comp::RefGet(v) => count_val(v, out),
        Comp::RefSet(c, v) => {
            count_val(c, out);
            count_val(v, out);
        }
        Comp::App(f, args) => {
            for x in freev(f) {
                *out.entry(x).or_default() += 1;
            }
            for a in args {
                count_val(a, out);
            }
        }
        Comp::Prim(_, a, b) => {
            count_val(a, out);
            count_val(b, out);
        }
        Comp::Call(g, args) => {
            let mask = borrow_mask(*g, sigs);
            for (i, a) in args.iter().enumerate() {
                if !borrowed_at(mask, i) {
                    count_val(a, out);
                }
            }
        }
        Comp::Do(_, args) | Comp::StrBuiltin(_, args) | Comp::Io(_, args) => {
            for a in args {
                count_val(a, out);
            }
        }
        _ => {}
    }
}
