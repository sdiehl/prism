use std::collections::BTreeMap;

use crate::fresh::Fresh;
use crate::names;
use crate::sym::Sym;

use super::super::cbpv::{Comp, Core, CoreFn, CorePat, HandleOp, Value};
use super::super::fv::{comp as freev, pat_vars};
use super::{borrow_mask, borrowed_at, borrowed_call_vars, count_val, Set, Sigs};

#[must_use]
pub fn insert_rc(core: &Core, sigs: &Sigs) -> Core {
    let mut fresh = Fresh::new();
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
                    body: rc(&f.body, &owned, &borrowed, sigs, &mut fresh),
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

fn after_borrowed_call(call: Comp, deferred: &[Sym], fresh: &mut Fresh) -> Comp {
    if deferred.is_empty() {
        return call;
    }
    let result_name = names::fresh_binder(names::FRESH_RC, fresh.bump());
    let result = Sym::from(result_name.as_str());
    let mut post = Comp::Return(Value::Var(result));
    for var in deferred {
        post = drop_(*var, post);
    }
    Comp::Bind(Box::new(call), result, Box::new(post))
}

fn rc(c: &Comp, owned: &Set, borrowed: &Set, sigs: &Sigs, fresh: &mut Fresh) -> Comp {
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
            let m2 = rc(m, &owned_m, &borrowed_m, sigs, fresh);
            let mut owned_n2 = owned_n;
            owned_n2.insert(*x);
            let n2 = rc(n, &owned_n2, &borrowed_n, sigs, fresh);
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
            Box::new(rc(t, owned, borrowed, sigs, fresh)),
            Box::new(rc(e, owned, borrowed, sigs, fresh)),
        ),
        Comp::Case(scrut, arms) => Comp::Case(
            scrut.clone(),
            arms.iter()
                .map(|(p, body)| (p.clone(), rc_arm(p, body, owned, borrowed, sigs, fresh)))
                .collect(),
        ),
        Comp::Lam(ps, body) => {
            let ps_set: Set = ps.iter().copied().collect();
            let caps: Set = freev(body).difference(&ps_set).copied().collect();
            Comp::Lam(ps.clone(), Box::new(rc(body, &ps_set, &caps, sigs, fresh)))
        }
        // Reachable only via the pre-lowering `dump fbip` display path,
        // compiled pipelines always lower handles first.
        Comp::Mask(ops, b) => {
            Comp::Mask(ops.clone(), Box::new(rc(b, owned, borrowed, sigs, fresh)))
        }
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => Comp::Handle {
            body: Box::new(rc(body, &Set::new(), &Set::new(), sigs, fresh)),
            return_var: *return_var,
            return_body: return_body.as_deref().map(|rb| {
                let o = return_var.iter().copied().collect();
                Box::new(rc(rb, &o, &Set::new(), sigs, fresh))
            }),
            ops: ops.rebuild(|op| {
                let o = op.params.iter().copied().collect();
                HandleOp {
                    name: op.name,
                    params: op.params.clone(),
                    resume: op.resume,
                    body: rc(&op.body, &o, &Set::new(), sigs, fresh),
                }
            }),
        },
        leaf => {
            let mut counts = BTreeMap::new();
            leaf_counts(leaf, &mut counts, sigs);
            let borrowed_uses = match leaf {
                Comp::Call(name, args) => borrowed_call_vars(*name, args, sigs)
                    .unwrap_or_else(|error| panic!("invalid RC input: {error}")),
                _ => Set::new(),
            };
            let deferred = by_name(owned.intersection(&borrowed_uses).copied());
            let mut out = rc_thunks(leaf, sigs, fresh);
            out = after_borrowed_call(out, &deferred, fresh);
            for v in by_name(owned.iter().copied()) {
                let count = counts.get(&v).copied().unwrap_or(0);
                if borrowed_uses.contains(&v) {
                    for _ in 0..count {
                        out = dup(v, out);
                    }
                } else {
                    match count {
                        0 => out = drop_(v, out),
                        k => {
                            for _ in 1..k {
                                out = dup(v, out);
                            }
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
fn rc_value(v: &Value, sigs: &Sigs, fresh: &mut Fresh) -> Value {
    match v {
        Value::Thunk(c) => Value::Thunk(Box::new(rc(c, &Set::new(), &freev(c), sigs, fresh))),
        Value::Ctor(t, i, fs) => Value::Ctor(
            *t,
            *i,
            fs.iter().map(|f| rc_value(f, sigs, fresh)).collect(),
        ),
        Value::Tuple(fs) => Value::Tuple(fs.iter().map(|f| rc_value(f, sigs, fresh)).collect()),
        Value::UnboxedTuple(fs) => {
            Value::UnboxedTuple(fs.iter().map(|f| rc_value(f, sigs, fresh)).collect())
        }
        Value::UnboxedRecord(fs) => Value::UnboxedRecord(
            fs.iter()
                .map(|(name, field)| (*name, rc_value(field, sigs, fresh)))
                .collect(),
        ),
        other => other.clone(),
    }
}

fn rc_thunks(c: &Comp, sigs: &Sigs, fresh: &mut Fresh) -> Comp {
    match c {
        Comp::Return(v) => Comp::Return(rc_value(v, sigs, fresh)),
        Comp::Force(v) => Comp::Force(rc_value(v, sigs, fresh)),
        Comp::Error(v) => Comp::Error(rc_value(v, sigs, fresh)),
        Comp::Io(op, args) => {
            Comp::Io(*op, args.iter().map(|v| rc_value(v, sigs, fresh)).collect())
        }
        Comp::FloatBuiltin(op, v) => Comp::FloatBuiltin(*op, rc_value(v, sigs, fresh)),
        Comp::Neg(l, v) => Comp::Neg(*l, rc_value(v, sigs, fresh)),
        Comp::Prim(op, a, b) => {
            let a = rc_value(a, sigs, fresh);
            let b = rc_value(b, sigs, fresh);
            Comp::Prim(*op, a, b)
        }
        Comp::Call(n, args) => {
            Comp::Call(*n, args.iter().map(|v| rc_value(v, sigs, fresh)).collect())
        }
        Comp::Do(n, args) => Comp::Do(*n, args.iter().map(|v| rc_value(v, sigs, fresh)).collect()),
        Comp::StrBuiltin(b, args) => {
            Comp::StrBuiltin(*b, args.iter().map(|v| rc_value(v, sigs, fresh)).collect())
        }
        Comp::App(f, args) => {
            let callee = rc_thunks(f, sigs, fresh);
            Comp::App(
                Box::new(callee),
                args.iter().map(|v| rc_value(v, sigs, fresh)).collect(),
            )
        }
        Comp::RefNew(v) => Comp::RefNew(rc_value(v, sigs, fresh)),
        Comp::RefGet(v) => Comp::RefGet(rc_value(v, sigs, fresh)),
        Comp::RefSet(c, v) => {
            let c = rc_value(c, sigs, fresh);
            let v = rc_value(v, sigs, fresh);
            Comp::RefSet(c, v)
        }
        Comp::InitAt(cell, ctor) => {
            let cell = rc_value(cell, sigs, fresh);
            let ctor = rc_value(ctor, sigs, fresh);
            Comp::InitAt(cell, ctor)
        }
        other => other.clone(),
    }
}

fn rc_arm(
    p: &CorePat,
    body: &Comp,
    owned: &Set,
    borrowed: &Set,
    sigs: &Sigs,
    fresh: &mut Fresh,
) -> Comp {
    let fb = freev(body);
    let mut fields = Set::new();
    pat_vars(p, &mut fields);
    let live = by_name(fields.intersection(&fb).copied());
    let dead = by_name(owned.iter().filter(|v| !fb.contains(*v)).copied());
    let mut owned_b: Set = owned.intersection(&fb).copied().collect();
    owned_b.extend(live.iter().copied());
    let borrowed_b: Set = borrowed.intersection(&fb).copied().collect();
    let mut out = rc(body, &owned_b, &borrowed_b, sigs, fresh);
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
        // `InitAt` consumes its cell (moved into the result) and every
        // constructor field (moved into the cell), exactly like the `Return(Ctor)`
        // it replaced consumes its fields. Missing this would drop a field the
        // cell now owns, a double free.
        Comp::InitAt(cell, ctor) => {
            count_val(cell, out);
            count_val(ctor, out);
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

#[cfg(test)]
mod tests {
    use super::super::balanced;
    use super::*;

    fn sym(name: &str) -> Sym {
        Sym::new(name)
    }

    fn function(name: &str, params: &[&str], body: Comp) -> CoreFn {
        CoreFn {
            name: sym(name),
            params: params.iter().map(|param| sym(param)).collect(),
            body,
            dict_arity: 0,
        }
    }

    #[test]
    fn last_borrow_drops_after_the_call_returns() {
        let borrowed = sym("borrowed");
        let retained = sym("retained");
        let observe = sym("observe");
        let input = Core {
            fns: vec![
                function("observe", &["borrowed"], Comp::Return(Value::Var(borrowed))),
                function(
                    "caller",
                    &["retained"],
                    Comp::Call(observe, vec![Value::Var(retained)]),
                ),
            ],
        };
        let sigs = std::iter::once((observe, vec![true])).collect();
        let output = insert_rc(&input, &sigs);

        let Comp::Bind(call, result, post) = &output.fns[1].body else {
            panic!("borrowed call result must delimit its loan cleanup");
        };
        assert_eq!(result.as_str(), "%rc0");
        assert!(matches!(
            &**call,
            Comp::Call(name, args)
                if *name == observe
                    && matches!(args.as_slice(), [Value::Var(arg)] if *arg == retained)
        ));
        assert!(matches!(
            &**post,
            Comp::Bind(drop, binder, rest)
                if binder.as_str() == "_"
                    && matches!(&**drop, Comp::Drop(Value::Var(var)) if *var == retained)
                    && matches!(&**rest, Comp::Return(Value::Var(var)) if var == result)
        ));
        assert_eq!(balanced(&output, &sigs), Ok(()));
    }

    #[test]
    fn consume_and_borrow_of_one_value_retains_a_call_lifetime_token() {
        let owned = sym("owned");
        let borrowed = sym("borrowed");
        let retained = sym("retained");
        let inspect = sym("inspect");
        let input = Core {
            fns: vec![
                function(
                    "inspect",
                    &["owned", "borrowed"],
                    Comp::Return(Value::Tuple(vec![Value::Var(owned), Value::Var(borrowed)])),
                ),
                function(
                    "caller",
                    &["retained"],
                    Comp::Call(inspect, vec![Value::Var(retained), Value::Var(retained)]),
                ),
            ],
        };
        let sigs = std::iter::once((inspect, vec![false, true])).collect();
        let output = insert_rc(&input, &sigs);

        let Comp::Bind(dup, binder, call_and_cleanup) = &output.fns[1].body else {
            panic!("owned+borrow alias must retain a loan token");
        };
        assert_eq!(binder.as_str(), "_");
        assert!(matches!(
            &**dup,
            Comp::Dup(Value::Var(var)) if *var == retained
        ));
        let Comp::Bind(call, result, post) = &**call_and_cleanup else {
            panic!("call must precede its retained-token cleanup");
        };
        assert_eq!(result.as_str(), "%rc0");
        assert!(matches!(&**call, Comp::Call(name, _) if *name == inspect));
        assert!(matches!(
            &**post,
            Comp::Bind(drop, _, rest)
                if matches!(&**drop, Comp::Drop(Value::Var(var)) if *var == retained)
                    && matches!(&**rest, Comp::Return(Value::Var(var)) if var == result)
        ));
        assert_eq!(balanced(&output, &sigs), Ok(()));
    }
}
