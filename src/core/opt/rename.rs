//! Capture-avoiding alpha-renaming, shared by the duplicating passes.
//!
//! When a pass duplicates a term that contains binders into a context that has
//! free variables (the inliner splicing a callee body at a call site, the
//! specializer materializing a shared method body), the duplicated binders must
//! be renamed to fresh names or one of them can capture a free variable of the
//! surrounding context. This is the one blessed place that renaming lives: every
//! duplication site freshens through here rather than re-deriving capture
//! handling, so the invariant holds by construction.
//!
//! Fresh names are `{prefix}{n}` (see [`names::fresh_binder`]) drawn from a
//! caller-threaded counter and assigned in deterministic traversal order, so the
//! output is byte-identical across runs (the `%` prefix cannot collide with a
//! source identifier, and a per-pass suffix keeps the passes' names disjoint).
//! Free variables (top-level function names) are left untouched.

use std::collections::BTreeMap;

use super::super::cbpv::{Comp, CorePat, HandleOp, Value};
use super::super::traverse::Rewrite;
use crate::names;
use crate::sym::Sym;

/// Mint the next fresh binder name for `prefix`, bumping the caller's counter.
pub(crate) fn next(counter: &mut u32, prefix: &'static str) -> Sym {
    let n = *counter;
    *counter += 1;
    Sym::from(&names::fresh_binder(prefix, n))
}

/// Alpha-rename every binder in `c` to a fresh name, so the result can be spliced
/// into any scope (or have its free variables substituted) with no risk of
/// capture. Free variables are left untouched.
pub(crate) fn freshen(c: &Comp, counter: &mut u32, prefix: &'static str) -> Comp {
    freshen_with(c, &BTreeMap::new(), counter, prefix)
}

/// As [`freshen`], but seeded with `ren` (e.g. a callee's parameters pre-mapped
/// to fresh names minted by [`next`]); variables absent from it and from every
/// inner binder are left as-is.
pub(crate) fn freshen_with(
    c: &Comp,
    ren: &BTreeMap<Sym, Sym>,
    counter: &mut u32,
    prefix: &'static str,
) -> Comp {
    Freshen { counter, prefix }.comp(c, ren)
}

struct Freshen<'a> {
    counter: &'a mut u32,
    prefix: &'static str,
}

impl Freshen<'_> {
    fn next(&mut self) -> Sym {
        next(self.counter, self.prefix)
    }

    // Record a fresh rename for `s` and return the fresh name.
    fn fresh_for(&mut self, s: Sym, ren: &mut BTreeMap<Sym, Sym>) -> Sym {
        let n = self.next();
        ren.insert(s, n);
        n
    }
}

impl Rewrite for Freshen<'_> {
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
                let nx = self.next();
                let mut r2 = ren.clone();
                r2.insert(*x, nx);
                Comp::Bind(Box::new(rhs2), nx, Box::new(self.comp(body, &r2)))
            }
            Comp::Lam(ps, b) => {
                let mut r2 = ren.clone();
                let mut nps: Vec<Sym> = Vec::with_capacity(ps.len());
                for p in ps {
                    let n = self.next();
                    r2.insert(*p, n);
                    nps.push(n);
                }
                Comp::Lam(nps, Box::new(self.comp(b, &r2)))
            }
            Comp::Case(scrut, arms) => {
                let scrut2 = self.value(scrut, ren);
                let mut arms2 = Vec::with_capacity(arms.len());
                for (p, b) in arms {
                    let mut r2 = ren.clone();
                    let np = match p {
                        CorePat::Wild => CorePat::Wild,
                        CorePat::Var(s) => CorePat::Var(self.fresh_for(*s, &mut r2)),
                        CorePat::Ctor(c, bs) => {
                            let mut nbs = Vec::with_capacity(bs.len());
                            for b in bs {
                                nbs.push(b.map(|s| self.fresh_for(s, &mut r2)));
                            }
                            CorePat::Ctor(*c, nbs)
                        }
                        CorePat::Tuple(bs) => {
                            let mut nbs = Vec::with_capacity(bs.len());
                            for b in bs {
                                nbs.push(b.map(|s| self.fresh_for(s, &mut r2)));
                            }
                            CorePat::Tuple(nbs)
                        }
                    };
                    let nb = self.comp(b, &r2);
                    arms2.push((np, nb));
                }
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
                        let n = self.next();
                        let mut r2 = ren.clone();
                        r2.insert(*v, n);
                        (
                            Some(n),
                            return_body.as_ref().map(|b| Box::new(self.comp(b, &r2))),
                        )
                    }
                    None => (
                        None,
                        return_body.as_ref().map(|b| Box::new(self.comp(b, ren))),
                    ),
                };
                let mut ops2 = Vec::with_capacity(ops.len());
                for o in ops {
                    let mut r2 = ren.clone();
                    let mut nps: Vec<Sym> = Vec::with_capacity(o.params.len());
                    for p in &o.params {
                        let n = self.next();
                        r2.insert(*p, n);
                        nps.push(n);
                    }
                    let nres = self.next();
                    r2.insert(o.resume, nres);
                    let nbody = self.comp(&o.body, &r2);
                    ops2.push(HandleOp {
                        name: o.name,
                        params: nps,
                        resume: nres,
                        body: nbody,
                    });
                }
                Comp::Handle {
                    body: body2,
                    return_var: rv,
                    return_body: rb,
                    ops: ops2,
                }
            }
            Comp::WithReuse { token, freed, body } => {
                let freed2 = self.value(freed, ren);
                let nt = self.next();
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
