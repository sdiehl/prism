//! Common subexpression elimination (late pass, O2).
//!
//! Eliminates a repeated pure scalar computation that the inliner or case-of-case
//! exposed, by pointing the later binder at the earlier one (the simplifier's
//! copy-prop and dead-let then collapse it). It is deliberately narrow: only a
//! `Prim` over non-trapping operators is shared (comparisons and `Add`/`Sub`/`Mul`,
//! never `Div`/`Rem`, whose divide-by-zero trap is observable). Constructors,
//! tuples, thunks, effects, refs, and calls are never shared: CSE runs before
//! reference counting, so sharing a heap cell would change ownership and could
//! defeat FBIP in-place reuse. Widening CSE to allocations is an open question
//! kept out of this landing; `tests/perf_gate.rs`'s reuse ratchets are the gate.
//!
//! Runs after effect lowering (a late pass) so it cannot disturb the var/State
//! fusion.

use std::collections::BTreeMap;

use super::super::cbpv::{Comp, Core, CoreFn, CoreOp, CorePat, HandleOp, Value};
use super::super::traverse::Rewrite;
use crate::sym::Sym;

/// Eliminate repeated pure scalar subexpressions, returning the result and the
/// number eliminated.
pub(crate) fn cse_counted(core: &Core) -> (Core, u64) {
    let mut c = Cse { ticks: 0 };
    let fns = core
        .fns
        .iter()
        .map(|f| CoreFn {
            name: f.name,
            params: f.params.clone(),
            body: c.comp(&f.body, &Avail::new()),
        })
        .collect();
    (Core { fns }, c.ticks)
}

// A key for a value usable as a `Prim` operand. `Float` keys on the bit pattern so
// the map stays total and `Ord`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum VKey {
    Var(Sym),
    Int(i64),
    I64(i64),
    U64(u64),
    Float(u64),
    Bool(bool),
    Unit,
    Str(String),
}

fn vkey(v: &Value) -> Option<VKey> {
    Some(match v {
        Value::Var(x) => VKey::Var(*x),
        Value::Int(n) => VKey::Int(*n),
        Value::I64(n) => VKey::I64(*n),
        Value::U64(n) => VKey::U64(*n),
        Value::Float(f) => VKey::Float(f.to_bits()),
        Value::Bool(b) => VKey::Bool(*b),
        Value::Unit => VKey::Unit,
        Value::Str(s) => VKey::Str(s.clone()),
        Value::Thunk(_) | Value::Ctor(..) | Value::Tuple(_) => return None,
    })
}

// The names a key mentions, for invalidation when one is rebound.
fn key_vars(k: &PrimKey) -> Vec<Sym> {
    let mut out = Vec::new();
    if let VKey::Var(x) = k.1 {
        out.push(x);
    }
    if let VKey::Var(x) = k.2 {
        out.push(x);
    }
    out
}

type PrimKey = (CoreOp, VKey, VKey);
type Avail = BTreeMap<PrimKey, Sym>;

// The shareable key of a `rhs`, if it is a pure non-trapping `Prim` over keyable
// operands.
fn shareable(rhs: &Comp) -> Option<PrimKey> {
    let Comp::Prim(op, a, b) = rhs else {
        return None;
    };
    if matches!(op, CoreOp::Div | CoreOp::Rem) {
        return None;
    }
    Some((*op, vkey(a)?, vkey(b)?))
}

// Drop available entries a binder invalidates: those whose key mentions a rebound
// name, and those whose holding binder is itself rebound.
fn narrow(avail: &Avail, bs: &[Sym]) -> Avail {
    if bs.is_empty() {
        return avail.clone();
    }
    avail
        .iter()
        .filter(|(k, v)| !bs.contains(v) && key_vars(k).iter().all(|n| !bs.contains(n)))
        .map(|(k, v)| (k.clone(), *v))
        .collect()
}

fn pat_binders(p: &CorePat) -> Vec<Sym> {
    match p {
        CorePat::Var(s) => vec![*s],
        CorePat::Ctor(_, bs) | CorePat::Tuple(bs) => bs.iter().flatten().copied().collect(),
        CorePat::Wild => Vec::new(),
    }
}

struct Cse {
    ticks: u64,
}

impl Rewrite for Cse {
    type Ctx = Avail;

    fn comp(&mut self, c: &Comp, avail: &Avail) -> Comp {
        match c {
            Comp::Bind(rhs, x, body) => {
                let rhs2 = self.comp(rhs, avail);
                if let Some(key) = shareable(&rhs2) {
                    if let Some(prev) = avail.get(&key) {
                        // CSE hit: reuse the earlier binder; copy-prop/dead-let
                        // then erase this binding.
                        self.ticks += 1;
                        let rebind = Comp::Return(Value::Var(*prev));
                        let body2 = self.comp(body, &narrow(avail, &[*x]));
                        return Comp::Bind(Box::new(rebind), *x, Box::new(body2));
                    }
                    let mut a2 = narrow(avail, &[*x]);
                    a2.insert(key, *x);
                    return Comp::Bind(Box::new(rhs2), *x, Box::new(self.comp(body, &a2)));
                }
                let a2 = narrow(avail, &[*x]);
                Comp::Bind(Box::new(rhs2), *x, Box::new(self.comp(body, &a2)))
            }
            Comp::Lam(ps, b) => {
                let a = narrow(avail, ps);
                Comp::Lam(ps.clone(), Box::new(self.comp(b, &a)))
            }
            Comp::Case(scrut, arms) => Comp::Case(
                scrut.clone(),
                arms.iter()
                    .map(|(p, b)| {
                        let a = narrow(avail, &pat_binders(p));
                        (p.clone(), self.comp(b, &a))
                    })
                    .collect(),
            ),
            Comp::Handle {
                body,
                return_var,
                return_body,
                ops,
            } => Comp::Handle {
                body: Box::new(self.comp(body, avail)),
                return_var: *return_var,
                return_body: return_body.as_ref().map(|b| {
                    let a = narrow(avail, &return_var.iter().copied().collect::<Vec<_>>());
                    Box::new(self.comp(b, &a))
                }),
                ops: ops
                    .iter()
                    .map(|o| {
                        let mut bs = o.params.clone();
                        bs.push(o.resume);
                        let a = narrow(avail, &bs);
                        HandleOp {
                            name: o.name,
                            params: o.params.clone(),
                            resume: o.resume,
                            body: self.comp(&o.body, &a),
                        }
                    })
                    .collect(),
            },
            Comp::WithReuse { token, freed, body } => {
                let a = narrow(avail, &[*token]);
                Comp::WithReuse {
                    token: *token,
                    freed: freed.clone(),
                    body: Box::new(self.comp(body, &a)),
                }
            }
            _ => self.descend_comp(c, avail),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::cse_counted;
    use crate::core::cbpv::{Comp, Core, CoreFn, CoreOp, Value};
    use crate::sym::Sym;

    fn s(n: &str) -> Sym {
        Sym::new(n)
    }

    // A repeated pure scalar `Prim` is shared: the second `a*b` becomes a copy of
    // the first's binder. `fn f(a,b) = let p = a*b in let q = a*b in p + q`.
    #[test]
    fn repeated_pure_prim_is_shared() {
        let mul = |x, y| Comp::Prim(CoreOp::Mul, Value::Var(s(x)), Value::Var(s(y)));
        let body = Comp::Bind(
            Box::new(mul("a", "b")),
            s("p"),
            Box::new(Comp::Bind(
                Box::new(mul("a", "b")),
                s("q"),
                Box::new(Comp::Prim(
                    CoreOp::Add,
                    Value::Var(s("p")),
                    Value::Var(s("q")),
                )),
            )),
        );
        let core = Core {
            fns: vec![CoreFn {
                name: s("f"),
                params: vec![s("a"), s("b")],
                body,
            }],
        };
        let (out, ticks) = cse_counted(&core);
        assert_eq!(ticks, 1);
        // q's rhs is now `return p` (a copy of the earlier binder).
        match &out.fns[0].body {
            Comp::Bind(_, _, inner) => match inner.as_ref() {
                Comp::Bind(qrhs, _, _) => {
                    assert!(matches!(qrhs.as_ref(), Comp::Return(Value::Var(v)) if *v == s("p")));
                }
                other => panic!("expected inner bind, got {other:?}"),
            },
            other => panic!("expected outer bind, got {other:?}"),
        }
    }

    // A divide is never shared (its trap is observable), so nothing fires.
    #[test]
    fn divide_is_not_shared() {
        let div = |x, y| Comp::Prim(CoreOp::Div, Value::Var(s(x)), Value::Var(s(y)));
        let body = Comp::Bind(
            Box::new(div("a", "b")),
            s("p"),
            Box::new(Comp::Bind(
                Box::new(div("a", "b")),
                s("q"),
                Box::new(Comp::Return(Value::Var(s("q")))),
            )),
        );
        let core = Core {
            fns: vec![CoreFn {
                name: s("f"),
                params: vec![s("a"), s("b")],
                body,
            }],
        };
        let (_, ticks) = cse_counted(&core);
        assert_eq!(ticks, 0);
    }
}
