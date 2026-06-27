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
use crate::names::DICT_PREFIX;
use crate::sym::Sym;

/// Specialize every constrained call on a context-free global dictionary.
///
/// Adds the specialized clones and dead-code-eliminates the dictionaries they
/// make redundant. A program with no instances or no constrained calls is
/// returned unchanged in spirit.
#[must_use]
pub fn specialize(core: &Core) -> Core {
    let builders = builders(core);
    let constrained = constrained(core);
    if builders.is_empty() || constrained.is_empty() {
        return core.clone();
    }
    let bodies = core.fns.iter().map(|f| (f.name, f.clone())).collect();
    let mut sp = Specializer {
        builders,
        constrained,
        bodies,
        memo: BTreeMap::new(),
        clones: Vec::new(),
        counter: 0,
    };
    let empty = BTreeMap::new();
    let mut fns: Vec<CoreFn> = core
        .fns
        .iter()
        .map(|f| CoreFn {
            name: f.name,
            params: f.params.clone(),
            body: sp.rewrite_comp(&f.body, &empty),
        })
        .collect();
    fns.extend(sp.clones);
    for f in &mut fns {
        f.body = dce(&f.body, &sp.builders);
    }
    Core { fns }
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
        let body = self.rewrite_comp(&body, &BTreeMap::new());
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
                    let rest = args[k..]
                        .iter()
                        .map(|a| self.rewrite_value(a, env))
                        .collect();
                    return Comp::Call(clone, rest);
                }
            }
        }
        Comp::Call(f, args.iter().map(|a| self.rewrite_value(a, env)).collect())
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
        let vals2 = self.rewrite_values(vals, env);
        let subst: BTreeMap<Sym, Value> = ps.into_iter().zip(vals2).collect();
        Some(subst_comp(&lbody, &subst))
    }

    fn rewrite_value(&mut self, v: &Value, env: &BTreeMap<Sym, Sym>) -> Value {
        match v {
            Value::Thunk(c) => Value::Thunk(Box::new(self.rewrite_comp(c, env))),
            Value::Ctor(n, t, fs) => Value::Ctor(
                *n,
                *t,
                fs.iter().map(|f| self.rewrite_value(f, env)).collect(),
            ),
            Value::Tuple(fs) => {
                Value::Tuple(fs.iter().map(|f| self.rewrite_value(f, env)).collect())
            }
            _ => v.clone(),
        }
    }

    fn rewrite_comp(&mut self, c: &Comp, env: &BTreeMap<Sym, Sym>) -> Comp {
        match c {
            Comp::Bind(rhs, x, body) => {
                let rhs2 = self.rewrite_comp(rhs, env);
                let mut env2 = env.clone();
                if let Comp::Call(b, a) = &rhs2 {
                    if a.is_empty() && self.builders.contains_key(b) {
                        env2.insert(*x, *b);
                    }
                }
                let body2 = self.rewrite_comp(body, &env2);
                Comp::Bind(Box::new(rhs2), *x, Box::new(body2))
            }
            Comp::Call(f, args) => self.rewrite_call(*f, args, env),
            Comp::Case(scrut, arms) => {
                if let Some(reduced) = self.try_reduce_projection(scrut, arms, env) {
                    return reduced;
                }
                let scrut2 = self.rewrite_value(scrut, env);
                let arms2 = arms
                    .iter()
                    .map(|(p, b)| (p.clone(), self.rewrite_comp(b, env)))
                    .collect();
                Comp::Case(scrut2, arms2)
            }
            Comp::Return(v) => Comp::Return(self.rewrite_value(v, env)),
            Comp::Force(v) => Comp::Force(self.rewrite_value(v, env)),
            Comp::Lam(ps, b) => Comp::Lam(ps.clone(), Box::new(self.rewrite_comp(b, env))),
            Comp::App(f, args) => {
                let f2 = self.rewrite_comp(f, env);
                let args2 = self.rewrite_values(args, env);
                Comp::App(Box::new(f2), args2)
            }
            Comp::If(c0, t, e) => {
                let c2 = self.rewrite_value(c0, env);
                let t2 = self.rewrite_comp(t, env);
                let e2 = self.rewrite_comp(e, env);
                Comp::If(c2, Box::new(t2), Box::new(e2))
            }
            Comp::Prim(op, a, b) => {
                let a2 = self.rewrite_value(a, env);
                let b2 = self.rewrite_value(b, env);
                Comp::Prim(*op, a2, b2)
            }
            Comp::Print(v) => Comp::Print(self.rewrite_value(v, env)),
            Comp::PrintF(v) => Comp::PrintF(self.rewrite_value(v, env)),
            Comp::PrintS(v) => Comp::PrintS(self.rewrite_value(v, env)),
            Comp::PrintNl => Comp::PrintNl,
            Comp::ReadInt => Comp::ReadInt,
            Comp::ReadLine => Comp::ReadLine,
            Comp::Rand => Comp::Rand,
            Comp::Srand(v) => Comp::Srand(self.rewrite_value(v, env)),
            Comp::Error(v) => Comp::Error(self.rewrite_value(v, env)),
            Comp::FloatBuiltin(op, v) => Comp::FloatBuiltin(*op, self.rewrite_value(v, env)),
            Comp::Do(n, args) => Comp::Do(*n, self.rewrite_values(args, env)),
            Comp::Handle {
                body,
                return_var,
                return_body,
                ops,
            } => {
                let body2 = self.rewrite_comp(body, env);
                let return_body2 = return_body
                    .as_ref()
                    .map(|b| Box::new(self.rewrite_comp(b, env)));
                let ops2 = ops
                    .iter()
                    .map(|o| HandleOp {
                        name: o.name,
                        params: o.params.clone(),
                        resume: o.resume,
                        body: self.rewrite_comp(&o.body, env),
                    })
                    .collect();
                Comp::Handle {
                    body: Box::new(body2),
                    return_var: *return_var,
                    return_body: return_body2,
                    ops: ops2,
                }
            }
            Comp::Mask(es, b) => Comp::Mask(es.clone(), Box::new(self.rewrite_comp(b, env))),
            Comp::StrBuiltin(b, args) => Comp::StrBuiltin(*b, self.rewrite_values(args, env)),
            Comp::Dup(v) => Comp::Dup(self.rewrite_value(v, env)),
            Comp::Drop(v) => Comp::Drop(self.rewrite_value(v, env)),
            Comp::WithReuse { token, freed, body } => {
                let freed2 = self.rewrite_value(freed, env);
                let body2 = self.rewrite_comp(body, env);
                Comp::WithReuse {
                    token: *token,
                    freed: freed2,
                    body: Box::new(body2),
                }
            }
            Comp::Reuse(t, v) => Comp::Reuse(*t, self.rewrite_value(v, env)),
            Comp::RefNew(v) => Comp::RefNew(self.rewrite_value(v, env)),
            Comp::RefGet(v) => Comp::RefGet(self.rewrite_value(v, env)),
            Comp::RefSet(a, b) => {
                let a2 = self.rewrite_value(a, env);
                let b2 = self.rewrite_value(b, env);
                Comp::RefSet(a2, b2)
            }
        }
    }

    fn rewrite_values(&mut self, vs: &[Value], env: &BTreeMap<Sym, Sym>) -> Vec<Value> {
        vs.iter().map(|v| self.rewrite_value(v, env)).collect()
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

// Capture-respecting substitution of variables by values in a computation. A
// binder shadowing a substituted name stops the substitution under it.
fn subst_comp(c: &Comp, s: &BTreeMap<Sym, Value>) -> Comp {
    let sc = |c: &Comp| subst_comp(c, s);
    let sv = |v: &Value| subst_value(v, s);
    let under = |c: &Comp, bound: &[Sym]| {
        if bound.iter().any(|b| s.contains_key(b)) {
            let mut s2 = s.clone();
            for b in bound {
                s2.remove(b);
            }
            subst_comp(c, &s2)
        } else {
            subst_comp(c, s)
        }
    };
    match c {
        Comp::Return(v) => Comp::Return(sv(v)),
        Comp::Bind(a, x, b) => Comp::Bind(Box::new(sc(a)), *x, Box::new(under(b, &[*x]))),
        Comp::Force(v) => Comp::Force(sv(v)),
        Comp::Lam(ps, b) => Comp::Lam(ps.clone(), Box::new(under(b, ps))),
        Comp::App(f, args) => Comp::App(Box::new(sc(f)), args.iter().map(sv).collect()),
        Comp::If(c0, t, e) => Comp::If(sv(c0), Box::new(sc(t)), Box::new(sc(e))),
        Comp::Prim(op, a, b) => Comp::Prim(*op, sv(a), sv(b)),
        Comp::Call(n, args) => Comp::Call(*n, args.iter().map(sv).collect()),
        Comp::Print(v) => Comp::Print(sv(v)),
        Comp::PrintF(v) => Comp::PrintF(sv(v)),
        Comp::PrintS(v) => Comp::PrintS(sv(v)),
        Comp::PrintNl => Comp::PrintNl,
        Comp::ReadInt => Comp::ReadInt,
        Comp::ReadLine => Comp::ReadLine,
        Comp::Rand => Comp::Rand,
        Comp::Srand(v) => Comp::Srand(sv(v)),
        Comp::Error(v) => Comp::Error(sv(v)),
        Comp::Case(scrut, arms) => Comp::Case(
            sv(scrut),
            arms.iter()
                .map(|(p, b)| (p.clone(), under(b, &pat_binders(p))))
                .collect(),
        ),
        Comp::FloatBuiltin(op, v) => Comp::FloatBuiltin(*op, sv(v)),
        Comp::Do(n, args) => Comp::Do(*n, args.iter().map(sv).collect()),
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => Comp::Handle {
            body: Box::new(sc(body)),
            return_var: *return_var,
            return_body: return_body
                .as_ref()
                .map(|b| Box::new(under(b, return_var.as_slice()))),
            ops: ops
                .iter()
                .map(|o| {
                    let mut bound = o.params.clone();
                    bound.push(o.resume);
                    HandleOp {
                        name: o.name,
                        params: o.params.clone(),
                        resume: o.resume,
                        body: under(&o.body, &bound),
                    }
                })
                .collect(),
        },
        Comp::Mask(es, b) => Comp::Mask(es.clone(), Box::new(sc(b))),
        Comp::StrBuiltin(b, args) => Comp::StrBuiltin(*b, args.iter().map(sv).collect()),
        Comp::Dup(v) => Comp::Dup(sv(v)),
        Comp::Drop(v) => Comp::Drop(sv(v)),
        Comp::WithReuse { token, freed, body } => Comp::WithReuse {
            token: *token,
            freed: sv(freed),
            body: Box::new(under(body, &[*token])),
        },
        Comp::Reuse(t, v) => Comp::Reuse(*t, sv(v)),
        Comp::RefNew(v) => Comp::RefNew(sv(v)),
        Comp::RefGet(v) => Comp::RefGet(sv(v)),
        Comp::RefSet(a, b) => Comp::RefSet(sv(a), sv(b)),
    }
}

fn subst_value(v: &Value, s: &BTreeMap<Sym, Value>) -> Value {
    match v {
        Value::Var(x) => s.get(x).cloned().unwrap_or_else(|| v.clone()),
        Value::Thunk(c) => Value::Thunk(Box::new(subst_comp(c, s))),
        Value::Ctor(n, t, fs) => {
            Value::Ctor(*n, *t, fs.iter().map(|f| subst_value(f, s)).collect())
        }
        Value::Tuple(fs) => Value::Tuple(fs.iter().map(|f| subst_value(f, s)).collect()),
        _ => v.clone(),
    }
}

fn pat_binders(p: &CorePat) -> Vec<Sym> {
    match p {
        CorePat::Var(s) => vec![*s],
        CorePat::Ctor(_, bs) | CorePat::Tuple(bs) => bs.iter().flatten().copied().collect(),
        CorePat::Wild => Vec::new(),
    }
}
