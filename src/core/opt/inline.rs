//! Bounded inliner (late pass).
//!
//! Inlines a non-recursive top-level function at its call site when doing so
//! cannot blow up code size. The first cut inlines only a function called exactly
//! once (a single `Call` head, and never referenced first-class), so its body
//! moves rather than duplicates: no size growth, and no question of duplicating a
//! side-effecting computation. The callee's binders are alpha-renamed to fresh
//! names so nothing captures or collides at the call site; its free variables are
//! top-level function names (Core Lint's invariant), in scope everywhere.
//!
//! It runs after effect lowering (a late pass) so it cannot disturb the var/State
//! fusion, on the lowered, pre-reference-counting core (so no rc nodes appear). It
//! is gated to O2: the fresh `%n` names from `Sym::fresh` are process-global, so
//! they must not reach the O1-default snapshots; promotion to O1 needs a
//! deterministic fresh-name supply first.

use std::collections::{BTreeMap, BTreeSet};

use super::super::cbpv::{calls_in, Comp, Core, CoreFn, CorePat, HandleOp, Value};
use super::super::fv;
use super::super::traverse::Rewrite;
use crate::names::ENTRY_POINT;
use crate::sym::Sym;

/// Inline single-call-site non-recursive functions, returning the result and the
/// number of call sites inlined.
pub(crate) fn inline_counted(core: &Core) -> (Core, u64) {
    let names: BTreeSet<Sym> = core.fns.iter().map(|f| f.name).collect();

    // Per-function call-site count (Call heads) and whether it is ever used
    // first-class (as a value, e.g. a dictionary field), across all bodies.
    let mut call_count: BTreeMap<Sym, usize> = BTreeMap::new();
    let mut first_class: BTreeSet<Sym> = BTreeSet::new();
    for f in &core.fns {
        let mut heads = Vec::new();
        calls_in(&f.body, &mut heads);
        for h in heads {
            *call_count.entry(h).or_default() += 1;
        }
        for v in fv::comp(&f.body) {
            if names.contains(&v) {
                first_class.insert(v);
            }
        }
    }

    let recursive = recursive_set(core, &names);
    let entry = Sym::new(ENTRY_POINT);
    let inlinable: BTreeSet<Sym> = names
        .iter()
        .copied()
        .filter(|n| {
            *n != entry
                && !recursive.contains(n)
                && !first_class.contains(n)
                && call_count.get(n).copied() == Some(1)
        })
        .collect();
    if inlinable.is_empty() {
        return (core.clone(), 0);
    }

    let mut inl = Inliner {
        fns: core.fns.iter().map(|f| (f.name, f.clone())).collect(),
        inlinable,
        ticks: 0,
    };
    let fns = core
        .fns
        .iter()
        .map(|f| CoreFn {
            name: f.name,
            params: f.params.clone(),
            body: inl.comp(&f.body, &()),
        })
        .collect();
    (Core { fns }, inl.ticks)
}

// The functions that (transitively) call themselves. Never inlined: it would not
// terminate and would reshape the spines `tailrec` and native codegen expect.
fn recursive_set(core: &Core, names: &BTreeSet<Sym>) -> BTreeSet<Sym> {
    let mut edges: BTreeMap<Sym, BTreeSet<Sym>> = BTreeMap::new();
    for f in &core.fns {
        let mut heads = Vec::new();
        calls_in(&f.body, &mut heads);
        edges.insert(
            f.name,
            heads.into_iter().filter(|h| names.contains(h)).collect(),
        );
    }
    let mut rec = BTreeSet::new();
    for &start in names {
        let mut seen = BTreeSet::new();
        let mut stack: Vec<Sym> = edges.get(&start).into_iter().flatten().copied().collect();
        while let Some(n) = stack.pop() {
            if n == start {
                rec.insert(start);
                break;
            }
            if seen.insert(n) {
                stack.extend(edges.get(&n).into_iter().flatten().copied());
            }
        }
    }
    rec
}

struct Inliner {
    fns: BTreeMap<Sym, CoreFn>,
    inlinable: BTreeSet<Sym>,
    ticks: u64,
}

impl Rewrite for Inliner {
    type Ctx = ();

    fn comp(&mut self, c: &Comp, cx: &()) -> Comp {
        if let Comp::Call(name, args) = c {
            if self.inlinable.contains(name) {
                let callee = self.fns[name].clone();
                if callee.params.len() == args.len() {
                    let args2: Vec<Value> = args.iter().map(|a| self.value(a, cx)).collect();
                    self.ticks += 1;
                    let spliced = inline_call(&callee, &args2);
                    // Recurse into the spliced body: a single-call-site callee
                    // it in turn calls is still single-site (its one site just
                    // moved here), so one sweep inlines the whole chain.
                    return self.comp(&spliced, cx);
                }
            }
        }
        self.descend_comp(c, cx)
    }
}

// The callee body with every binder freshened and its parameters bound to the
// argument values: `let p0' = a0 in ... let pk' = ak in <freshened body>`. The
// trivial-let copy-prop and dead-let in the simplifier then erase the parameter
// lets (arguments are ANF values).
fn inline_call(callee: &CoreFn, args: &[Value]) -> Comp {
    let mut ren: BTreeMap<Sym, Sym> = BTreeMap::new();
    for p in &callee.params {
        ren.insert(*p, Sym::fresh());
    }
    let mut out = Freshen.comp(&callee.body, &ren);
    for i in (0..callee.params.len()).rev() {
        let p = ren[&callee.params[i]];
        out = Comp::Bind(Box::new(Comp::Return(args[i].clone())), p, Box::new(out));
    }
    out
}

// Alpha-renames every bound name in a term to a fresh symbol, threading the
// old->new map and substituting variable uses. Free variables (top-level function
// names) are left untouched.
struct Freshen;

// Record a fresh rename for `s` and return the fresh name.
fn fresh_for(s: Sym, ren: &mut BTreeMap<Sym, Sym>) -> Sym {
    let n = Sym::fresh();
    ren.insert(s, n);
    n
}

impl Rewrite for Freshen {
    type Ctx = BTreeMap<Sym, Sym>;

    fn value(&mut self, v: &Value, ren: &Self::Ctx) -> Value {
        if let Value::Var(x) = v {
            if let Some(n) = ren.get(x) {
                return Value::Var(*n);
            }
        }
        self.descend_value(v, ren)
    }

    fn comp(&mut self, c: &Comp, ren: &Self::Ctx) -> Comp {
        match c {
            Comp::Bind(rhs, x, body) => {
                let rhs2 = self.comp(rhs, ren);
                let nx = Sym::fresh();
                let mut r2 = ren.clone();
                r2.insert(*x, nx);
                Comp::Bind(Box::new(rhs2), nx, Box::new(self.comp(body, &r2)))
            }
            Comp::Lam(ps, b) => {
                let mut r2 = ren.clone();
                let nps: Vec<Sym> = ps
                    .iter()
                    .map(|p| {
                        let n = Sym::fresh();
                        r2.insert(*p, n);
                        n
                    })
                    .collect();
                Comp::Lam(nps, Box::new(self.comp(b, &r2)))
            }
            Comp::Case(scrut, arms) => {
                let scrut2 = self.value(scrut, ren);
                let arms2 = arms
                    .iter()
                    .map(|(p, b)| {
                        let mut r2 = ren.clone();
                        let np = match p {
                            CorePat::Wild => CorePat::Wild,
                            CorePat::Var(s) => {
                                let n = Sym::fresh();
                                r2.insert(*s, n);
                                CorePat::Var(n)
                            }
                            CorePat::Ctor(c, bs) => CorePat::Ctor(
                                *c,
                                bs.iter().map(|b| b.map(|s| fresh_for(s, &mut r2))).collect(),
                            ),
                            CorePat::Tuple(bs) => CorePat::Tuple(
                                bs.iter().map(|b| b.map(|s| fresh_for(s, &mut r2))).collect(),
                            ),
                        };
                        (np, self.comp(b, &r2))
                    })
                    .collect();
                Comp::Case(scrut2, arms2)
            }
            Comp::Handle {
                body,
                return_var,
                return_body,
                ops,
            } => {
                let body2 = Box::new(self.comp(body, ren));
                let (rv, rb) = match return_var {
                    Some(v) => {
                        let n = Sym::fresh();
                        let mut r2 = ren.clone();
                        r2.insert(*v, n);
                        (Some(n), return_body.as_ref().map(|b| Box::new(self.comp(b, &r2))))
                    }
                    None => (None, return_body.as_ref().map(|b| Box::new(self.comp(b, ren)))),
                };
                let ops2 = ops
                    .iter()
                    .map(|o| {
                        let mut r2 = ren.clone();
                        let nps: Vec<Sym> = o
                            .params
                            .iter()
                            .map(|p| {
                                let n = Sym::fresh();
                                r2.insert(*p, n);
                                n
                            })
                            .collect();
                        let nres = Sym::fresh();
                        r2.insert(o.resume, nres);
                        HandleOp {
                            name: o.name,
                            params: nps,
                            resume: nres,
                            body: self.comp(&o.body, &r2),
                        }
                    })
                    .collect();
                Comp::Handle {
                    body: body2,
                    return_var: rv,
                    return_body: rb,
                    ops: ops2,
                }
            }
            Comp::WithReuse { token, freed, body } => {
                let freed2 = self.value(freed, ren);
                let nt = Sym::fresh();
                let mut r2 = ren.clone();
                r2.insert(*token, nt);
                Comp::WithReuse {
                    token: nt,
                    freed: freed2,
                    body: Box::new(self.comp(body, &r2)),
                }
            }
            Comp::Reuse(tok, v) => {
                let nt = ren.get(tok).copied().unwrap_or(*tok);
                Comp::Reuse(nt, self.value(v, ren))
            }
            _ => self.descend_comp(c, ren),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::inline_counted;
    use crate::core::cbpv::{Comp, Core, CoreFn, Value};
    use crate::sym::Sym;

    fn s(n: &str) -> Sym {
        Sym::new(n)
    }

    // A wrapper called exactly once is inlined and its parameter let-bound to the
    // argument; the wrapper call is gone, replaced by the (freshened) forwarded
    // call. `main` calls `wrap(x)`; `wrap(a) = g(a)`.
    #[test]
    fn single_call_site_wrapper_is_inlined() {
        let core = Core {
            fns: vec![
                CoreFn {
                    name: s("main"),
                    params: vec![s("x")],
                    body: Comp::Call(s("wrap"), vec![Value::Var(s("x"))]),
                },
                CoreFn {
                    name: s("wrap"),
                    params: vec![s("a")],
                    body: Comp::Call(s("g"), vec![Value::Var(s("a"))]),
                },
            ],
        };
        let (out, ticks) = inline_counted(&core);
        assert_eq!(ticks, 1);
        let main = &out.fns.iter().find(|f| f.name == s("main")).unwrap().body;
        // main no longer calls wrap; the body is now `let a' = x in g(a')`.
        match main {
            Comp::Bind(rhs, _, body) => {
                assert!(matches!(rhs.as_ref(), Comp::Return(Value::Var(v)) if *v == s("x")));
                assert!(matches!(body.as_ref(), Comp::Call(g, _) if *g == s("g")));
            }
            other => panic!("expected inlined `let a = x in g(a)`, got {other:?}"),
        }
    }

    // A recursive function is never inlined, even at a lone call site.
    #[test]
    fn recursive_function_is_not_inlined() {
        let core = Core {
            fns: vec![CoreFn {
                name: s("loop"),
                params: vec![],
                body: Comp::Call(s("loop"), vec![]),
            }],
        };
        let (_, ticks) = inline_counted(&core);
        assert_eq!(ticks, 0);
    }
}
