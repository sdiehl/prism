//! Dictionary specialization.
//!
//! A constrained function called with statically known (global, context-free)
//! instance dictionaries is cloned with those dictionaries materialized at the
//! top of its body. The clone is, by construction, the original applied to the
//! rebuilt dictionaries, so it is behavior-identical; on top of that, every
//! method projection on a materialized dictionary reduces to a direct call to
//! the instance method, and the now-dead dictionary build is eliminated. The net
//! effect is that typeclass dispatch on a known instance becomes a direct,
//! inlinable call. Parity-safe by construction and gated by the parity oracle.
//!
//! Scope (first slice): instances whose dictionary builder is nullary
//! (context-free, e.g. `Show Int`, `Eq Int`, a user instance with no
//! superclass). An instance with a superclass context (`Ord` needs `Eq`) takes
//! its context dictionaries as builder parameters and is left generic for now.

use std::collections::BTreeMap;

use super::super::cbpv::{Comp, Core, CoreFn, CorePat, HandleOp, Value};
use super::super::fv;
use super::super::traverse::Rewrite;
use crate::names::DICT_PREFIX;
use crate::sym::Sym;

/// Specialize every constrained call on a context-free global dictionary.
///
/// Adds the specialized clones and dead-code-eliminates the dictionaries they
/// make redundant. A program with no instances or no constrained calls is
/// returned unchanged in spirit.
#[must_use]
pub fn specialize(core: &Core) -> Core {
    specialize_counted(core).0
}

// As `specialize`, also returning a tick count (clones generated plus method
// projections reduced) for telemetry.
pub(crate) fn specialize_counted(core: &Core) -> (Core, u64) {
    let builders = builders(core);
    let constrained = constrained(core);
    if builders.is_empty() || constrained.is_empty() {
        return (core.clone(), 0);
    }
    let bodies = core.fns.iter().map(|f| (f.name, f.clone())).collect();
    let mut sp = Specializer {
        builders,
        constrained,
        bodies,
        memo: BTreeMap::new(),
        clones: Vec::new(),
        counter: 0,
        reductions: 0,
    };
    let empty = BTreeMap::new();
    let mut fns: Vec<CoreFn> = core
        .fns
        .iter()
        .map(|f| CoreFn {
            name: f.name,
            params: f.params.clone(),
            body: sp.comp(&f.body, &empty),
        })
        .collect();
    let ticks = sp.counter as u64 + sp.reductions;
    fns.extend(sp.clones);
    for f in &mut fns {
        f.body = dce(&f.body, &sp.builders);
    }
    (Core { fns }, ticks)
}

// A context-free instance dictionary builder: a nullary function whose body is a
// dict cell `_DClass(field0, ..)`. The fields are the cell's contents (method
// thunks, in builder order).
fn builders(core: &Core) -> BTreeMap<Sym, Vec<Value>> {
    core.fns
        .iter()
        .filter(|f| f.params.is_empty())
        .filter_map(|f| match &f.body {
            Comp::Return(Value::Ctor(c, _, fields)) if c.as_str().starts_with(DICT_PREFIX) => {
                Some((f.name, fields.clone()))
            }
            _ => None,
        })
        .collect()
}

// A constrained function carries leading `_c{i}` dictionary parameters; the count
// is how many.
fn constrained(core: &Core) -> BTreeMap<Sym, usize> {
    core.fns
        .iter()
        .filter_map(|f| {
            let k = f.params.iter().take_while(|p| is_dict_param(**p)).count();
            (k > 0).then_some((f.name, k))
        })
        .collect()
}

fn is_dict_param(p: Sym) -> bool {
    p.as_str()
        .strip_prefix("_c")
        .is_some_and(|n| n.parse::<usize>().is_ok())
}

struct Specializer {
    builders: BTreeMap<Sym, Vec<Value>>,
    constrained: BTreeMap<Sym, usize>,
    bodies: BTreeMap<Sym, CoreFn>,
    memo: BTreeMap<(Sym, Vec<Sym>), Sym>,
    clones: Vec<CoreFn>,
    counter: usize,
    reductions: u64,
}

impl Specializer {
    // Request the clone of `f` specialized to `insts` (one builder per dict
    // param), generating it on first request. Memoized, so a self-recursive call
    // resolves to the in-flight clone name rather than looping.
    fn request(&mut self, f: Sym, insts: &[Sym]) -> Sym {
        let key = (f, insts.to_vec());
        if let Some(name) = self.memo.get(&key) {
            return *name;
        }
        self.counter += 1;
        let clone_name = Sym::from(&format!("{}$sp{}", f.as_str(), self.counter));
        self.memo.insert(key, clone_name);
        let orig = self.bodies[&f].clone();
        let k = insts.len();
        // Materialize each dict param from its builder at the top, then rewrite:
        // the materialization makes `_ci` an ordinary global-dict var, so the
        // method projections inside reduce and the recursive calls specialize.
        let mut body = orig.body;
        for i in (0..k).rev() {
            body = Comp::Bind(
                Box::new(Comp::Call(insts[i], Vec::new())),
                orig.params[i],
                Box::new(body),
            );
        }
        let body = self.comp(&body, &BTreeMap::new());
        self.clones.push(CoreFn {
            name: clone_name,
            params: orig.params[k..].to_vec(),
            body,
        });
        clone_name
    }

    fn rewrite_call(&mut self, f: Sym, args: &[Value], env: &BTreeMap<Sym, Sym>) -> Comp {
        if let Some(&k) = self.constrained.get(&f) {
            if args.len() >= k {
                let insts: Option<Vec<Sym>> = args[..k]
                    .iter()
                    .map(|a| match a {
                        Value::Var(v) => env.get(v).copied(),
                        _ => None,
                    })
                    .collect();
                if let Some(insts) = insts {
                    let clone = self.request(f, &insts);
                    let rest = args[k..].iter().map(|a| self.value(a, env)).collect();
                    return Comp::Call(clone, rest);
                }
            }
        }
        Comp::Call(f, args.iter().map(|a| self.value(a, env)).collect())
    }

    // `case _ci of _DClass(.., m, ..) => (force m)(vals)` on a known global dict
    // `_ci = inst()` reduces to the instance method applied to `vals` directly.
    fn try_reduce_projection(
        &mut self,
        scrut: &Value,
        arms: &[(CorePat, Comp)],
        env: &BTreeMap<Sym, Sym>,
    ) -> Option<Comp> {
        let Value::Var(ci) = scrut else { return None };
        let inst = *env.get(ci)?;
        let [(CorePat::Ctor(_, binders), arm)] = arms else {
            return None;
        };
        let mut bound = binders
            .iter()
            .enumerate()
            .filter_map(|(j, b)| b.map(|s| (j, s)));
        let (j, m) = bound.next()?;
        if bound.next().is_some() {
            return None; // more than one projected field (a superclass slice)
        }
        let Comp::App(callee, vals) = arm else {
            return None;
        };
        let Comp::Force(Value::Var(mv)) = callee.as_ref() else {
            return None;
        };
        if *mv != m {
            return None;
        }
        let field = self.builders.get(&inst)?.get(j)?.clone();
        let Value::Thunk(mbody) = field else {
            return None;
        };
        let Comp::Lam(ps, lbody) = *mbody else {
            return None;
        };
        if ps.len() != vals.len() {
            return None;
        }
        let vals2: Vec<Value> = vals.iter().map(|v| self.value(v, env)).collect();
        let subst: BTreeMap<Sym, Value> = ps.into_iter().zip(vals2).collect();
        self.reductions += 1;
        Some(subst_comp(&lbody, &subst))
    }
}

impl Rewrite for Specializer {
    // The env maps a let-bound var to the global dictionary builder it names, so a
    // method projection on it can reduce. Only `Bind` extends it; nothing else
    // scopes a builder var, so the rest defer to the structural descent.
    type Ctx = BTreeMap<Sym, Sym>;

    fn comp(&mut self, c: &Comp, env: &Self::Ctx) -> Comp {
        match c {
            Comp::Bind(rhs, x, body) => {
                let rhs2 = self.comp(rhs, env);
                let mut env2 = env.clone();
                if let Comp::Call(b, a) = &rhs2 {
                    if a.is_empty() && self.builders.contains_key(b) {
                        env2.insert(*x, *b);
                    }
                }
                let body2 = self.comp(body, &env2);
                Comp::Bind(Box::new(rhs2), *x, Box::new(body2))
            }
            Comp::Call(f, args) => self.rewrite_call(*f, args, env),
            Comp::Case(scrut, arms) => {
                if let Some(reduced) = self.try_reduce_projection(scrut, arms, env) {
                    return reduced;
                }
                self.descend_comp(c, env)
            }
            _ => self.descend_comp(c, env),
        }
    }
}

// Drop a `Bind(inst(), x, body)` whose materialized dictionary is unused: the
// builder call is effect-free, so a dead one is pure waste. Bottom-up so freeing
// one use can expose another.
fn dce(c: &Comp, builders: &BTreeMap<Sym, Vec<Value>>) -> Comp {
    match c {
        Comp::Bind(rhs, x, body) => {
            let body = dce(body, builders);
            let dead = matches!(rhs.as_ref(), Comp::Call(b, a) if a.is_empty() && builders.contains_key(b))
                && !fv::comp(&body).contains(x);
            if dead {
                body
            } else {
                Comp::Bind(Box::new(dce(rhs, builders)), *x, Box::new(body))
            }
        }
        Comp::Lam(ps, b) => Comp::Lam(ps.clone(), Box::new(dce(b, builders))),
        Comp::App(f, args) => Comp::App(Box::new(dce(f, builders)), args.clone()),
        Comp::If(c0, t, e) => Comp::If(
            c0.clone(),
            Box::new(dce(t, builders)),
            Box::new(dce(e, builders)),
        ),
        Comp::Case(s, arms) => Comp::Case(
            s.clone(),
            arms.iter()
                .map(|(p, b)| (p.clone(), dce(b, builders)))
                .collect(),
        ),
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => Comp::Handle {
            body: Box::new(dce(body, builders)),
            return_var: *return_var,
            return_body: return_body.as_ref().map(|b| Box::new(dce(b, builders))),
            ops: ops
                .iter()
                .map(|o| HandleOp {
                    name: o.name,
                    params: o.params.clone(),
                    resume: o.resume,
                    body: dce(&o.body, builders),
                })
                .collect(),
        },
        Comp::Mask(es, b) => Comp::Mask(es.clone(), Box::new(dce(b, builders))),
        Comp::WithReuse { token, freed, body } => Comp::WithReuse {
            token: *token,
            freed: freed.clone(),
            body: Box::new(dce(body, builders)),
        },
        other => other.clone(),
    }
}

// Capture-respecting substitution of variables by values in a computation. The
// substitution map is the threaded context; a binder shadowing a substituted
// name removes it from the map under that binder.
fn subst_comp(c: &Comp, s: &BTreeMap<Sym, Value>) -> Comp {
    Subst.comp(c, s)
}

struct Subst;

impl Subst {
    fn under(&mut self, c: &Comp, s: &BTreeMap<Sym, Value>, bound: &[Sym]) -> Comp {
        if bound.iter().any(|b| s.contains_key(b)) {
            let mut s2 = s.clone();
            for b in bound {
                s2.remove(b);
            }
            self.comp(c, &s2)
        } else {
            self.comp(c, s)
        }
    }
}

impl Rewrite for Subst {
    type Ctx = BTreeMap<Sym, Value>;

    fn value(&mut self, v: &Value, s: &Self::Ctx) -> Value {
        match v {
            Value::Var(x) => s.get(x).cloned().unwrap_or_else(|| v.clone()),
            _ => self.descend_value(v, s),
        }
    }

    fn comp(&mut self, c: &Comp, s: &Self::Ctx) -> Comp {
        match c {
            Comp::Bind(a, x, b) => Comp::Bind(
                Box::new(self.comp(a, s)),
                *x,
                Box::new(self.under(b, s, &[*x])),
            ),
            Comp::Lam(ps, b) => Comp::Lam(ps.clone(), Box::new(self.under(b, s, ps))),
            Comp::Case(scrut, arms) => Comp::Case(
                self.value(scrut, s),
                arms.iter()
                    .map(|(p, b)| (p.clone(), self.under(b, s, &pat_binders(p))))
                    .collect(),
            ),
            Comp::Handle {
                body,
                return_var,
                return_body,
                ops,
            } => Comp::Handle {
                body: Box::new(self.comp(body, s)),
                return_var: *return_var,
                return_body: return_body
                    .as_ref()
                    .map(|b| Box::new(self.under(b, s, return_var.as_slice()))),
                ops: ops
                    .iter()
                    .map(|o| {
                        let mut bound = o.params.clone();
                        bound.push(o.resume);
                        HandleOp {
                            name: o.name,
                            params: o.params.clone(),
                            resume: o.resume,
                            body: self.under(&o.body, s, &bound),
                        }
                    })
                    .collect(),
            },
            Comp::WithReuse { token, freed, body } => Comp::WithReuse {
                token: *token,
                freed: self.value(freed, s),
                body: Box::new(self.under(body, s, &[*token])),
            },
            _ => self.descend_comp(c, s),
        }
    }
}

fn pat_binders(p: &CorePat) -> Vec<Sym> {
    match p {
        CorePat::Var(s) => vec![*s],
        CorePat::Ctor(_, bs) | CorePat::Tuple(bs) => bs.iter().flatten().copied().collect(),
        CorePat::Wild => Vec::new(),
    }
}
