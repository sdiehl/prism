//! Evidence passing and its stream-fusion extensions.
//!
//! When every reachable handler is tail-resumptive, no continuation is ever
//! reified. Each op carries its active clause as evidence: a thunk `ev@<id>`
//! bound at the handle site (the clause body with its tail `resume(v)` replaced
//! by `return v`, free vars captured lexically). `do op(args)` becomes
//! `force(ev@<id>)(args)`, and every effectful function takes the evidence for
//! the ops latent in it as extra parameters so each perform site reaches the
//! clause active where its handler was installed.
//!
//! A stream combinator returns its body inside a thunk (`smap(s,f) = \u ->
//! smap_go(s,f)`), so the effect escapes first-class and the free-monad path
//! would force whole-program monadic mode. The fusion extension threads evidence
//! through these thunks instead: an escaping effectful thunk gains the same
//! `ev@<id>` parameters for the ops its body is latent in, and each force site
//! `force(s)(args)` appends the evidence for `s`'s signature (from the
//! interprocedural [`flow`] analysis). The free monad, its `EOp` cells, and
//! `ebind` all vanish.

use std::collections::BTreeSet;

use super::flow::{self, Loc};
use super::{contains_mask, each_subcomp, each_value, thunks_in_value, Env, Lowerer, MaskOp};
use crate::core::cbpv::{Comp, Core, CoreFn, HandleOp, Value};
use crate::core::fv;
use crate::names::{ev, ENTRY_POINT};
use crate::sym::Sym;

impl Lowerer {
    // Lower the whole program by evidence passing, or report ineligibility by
    // returning None (no state to undo: the caller falls back to the free
    // monad). Eligibility is decided up front by the static guards, then
    // confirmed structurally as the rewrite threads each escaping thunk to its
    // force sites; an untrackable thunk aborts the whole attempt.
    pub(super) fn try_lower_ev(&mut self, core: &Core) -> Option<Core> {
        if !self.ev_eligible(core) {
            return None;
        }
        let mut fns = Vec::with_capacity(core.fns.len());
        for f in &core.fns {
            // Each function receives the evidence for the ops latent in it
            // under the canonical `ev@<id>` param name; the body threads that
            // environment, rebinding it under fresh names at handles. Its
            // thunk-valued parameters seed the local signature environment so
            // their force sites know what evidence to append.
            let env: Env = self
                .ev_ids(f.name)?
                .into_iter()
                .map(|id| (id, ev(id).into()))
                .collect();
            let loc: Loc = f
                .params
                .iter()
                .copied()
                .zip(self.flow.param[&f.name].iter().cloned())
                .collect();
            let mut params = f.params.clone();
            params.extend(env.values().copied());
            fns.push(CoreFn {
                name: f.name,
                params,
                body: self.thread_ev(&f.body, &env, &loc)?,
            });
        }
        Some(Core { fns })
    }

    // The op ids a function needs evidence for: those latent in its body,
    // sorted so a call site and the definition agree on parameter order (a
    // BTreeMap keyed by id keeps both in ascending order).
    pub(super) fn ev_ids(&self, fname: Sym) -> Option<Vec<i64>> {
        self.sig_ids(self.latent.get(&fname).into_iter().flatten())
    }

    // Map a set of latent op names to their ids in ascending order. Force
    // sites, thunk parameter lists, and effectful-call argument lists all use
    // this single ordering so evidence lines up positionally everywhere. None
    // (an op that escaped `collect_ops`, an internal inconsistency) aborts the
    // evidence attempt so the caller falls back to the free-monad path, which
    // surfaces the same inconsistency as a structured error.
    pub(super) fn sig_ids<'a>(
        &self,
        ops: impl IntoIterator<Item = &'a MaskOp>,
    ) -> Option<Vec<i64>> {
        let mut v: Vec<i64> = ops
            .into_iter()
            .map(|op| self.op_id(op.id).ok())
            .collect::<Option<_>>()?;
        v.sort_unstable();
        v.dedup();
        Some(v)
    }

    // Build the evidence thunk for one clause: strip the tail `resume(v)` to
    // `return v`, thread the body under the outer environment (a clause runs
    // where its handler was installed, not under its own binding), and wrap it
    // in a lambda over the op params.
    fn clause_evidence(&mut self, op: &HandleOp, env: &Env, loc: &Loc) -> Option<Value> {
        let stripped = strip_resume(&op.body, &resume_set(op.resume))?;
        let body = self.thread_ev(&stripped, env, loc)?;
        let params = if op.params.is_empty() {
            vec![self.fresh("u")]
        } else {
            op.params.clone()
        };
        Some(Value::Thunk(Box::new(Comp::Lam(params, Box::new(body)))))
    }

    // Rewrite a body for the evidence path. `do op` forces the current evidence
    // for that op. Calls to effectful functions append their evidence. A handle
    // binds each clause under a fresh name (so an inner handler shadows an op
    // already in scope without a clash). A force of a thunk-valued variable
    // appends the evidence for that thunk's signature. Returns None when an
    // escaping effectful thunk cannot be tracked to its force sites.
    fn thread_ev(&mut self, c: &Comp, env: &Env, loc: &Loc) -> Option<Comp> {
        Some(match c {
            Comp::Do(op, args) => {
                let id = self.op_id(*op).ok()?;
                let ev = env.get(&id)?;
                let a = if args.is_empty() {
                    vec![Value::Unit]
                } else {
                    self.thread_values(args, env, loc)?
                };
                Comp::App(Box::new(Comp::Force(Value::Var(*ev))), a)
            }
            Comp::Call(g, args) => {
                let mut a = self.thread_values(args, env, loc)?;
                if self.eff.contains(g) {
                    for id in self.ev_ids(*g)? {
                        let ev = env.get(&id)?;
                        a.push(Value::Var(*ev));
                    }
                }
                Comp::Call(*g, a)
            }
            // Forcing a thunk-valued variable: append the evidence for the ops
            // its body performs, in ascending id order to match how the thunk's
            // parameters were laid out.
            Comp::App(f, args) => {
                let mut a = self.thread_values(args, env, loc)?;
                if let Comp::Force(Value::Var(v)) = f.as_ref() {
                    if let Some(sig) = loc.get(v) {
                        for id in self.sig_ids(sig)? {
                            a.push(Value::Var(*env.get(&id)?));
                        }
                    }
                }
                Comp::App(Box::new(self.thread_ev(f, env, loc)?), a)
            }
            Comp::Return(v) => Comp::Return(self.thread_value(v, env, loc)?),
            Comp::Handle {
                body,
                return_var,
                return_body,
                ops,
            } => {
                // Clauses thread under the outer env; the body and a fresh env
                // see this handler's ops rebound to fresh names.
                let mut binders = Vec::new();
                let mut body_env = env.clone();
                for op in ops {
                    let id = self.op_id(op.name).ok()?;
                    let clause = self.clause_evidence(op, env, loc)?;
                    let nm = self.fresh("ev");
                    body_env.insert(id, nm);
                    binders.push((nm, clause));
                }
                let rv = (*return_var).unwrap_or_else(|| self.fresh("hr"));
                // The return clause runs outside this handler's dynamic scope,
                // so it threads under the outer env, not body_env.
                let rb = match return_body {
                    Some(b) => self.thread_ev(b, env, loc)?,
                    None => Comp::Return(Value::Var(rv)),
                };
                let mut acc = Comp::Bind(
                    Box::new(self.thread_ev(body, &body_env, loc)?),
                    rv,
                    Box::new(rb),
                );
                for (nm, clause) in binders.into_iter().rev() {
                    acc = Comp::Bind(Box::new(Comp::Return(clause)), nm, Box::new(acc));
                }
                acc
            }
            Comp::Mask(_, b) => self.thread_ev(b, env, loc)?,
            Comp::Bind(m, x, n) => {
                let mut loc2 = loc.clone();
                loc2.insert(*x, flow::result_sig(m, loc, &self.latent, &self.flow));
                Comp::Bind(
                    Box::new(self.thread_ev(m, env, loc)?),
                    *x,
                    Box::new(self.thread_ev(n, env, &loc2)?),
                )
            }
            Comp::If(v, t, e) => Comp::If(
                v.clone(),
                Box::new(self.thread_ev(t, env, loc)?),
                Box::new(self.thread_ev(e, env, loc)?),
            ),
            Comp::Case(v, arms) => Comp::Case(
                v.clone(),
                arms.iter()
                    .map(|(p, b)| Some((p.clone(), self.thread_ev(b, env, loc)?)))
                    .collect::<Option<_>>()?,
            ),
            Comp::Lam(ps, b) => Comp::Lam(ps.clone(), Box::new(self.thread_ev(b, env, loc)?)),
            other => other.clone(),
        })
    }

    fn thread_values(&mut self, vs: &[Value], env: &Env, loc: &Loc) -> Option<Vec<Value>> {
        vs.iter().map(|v| self.thread_value(v, env, loc)).collect()
    }

    // Rewrite a value. An escaping effectful thunk (a `\..` whose body performs
    // latent ops) gains `ev@<id>` parameters for those ops and has its body
    // threaded with them in scope, so its force sites can supply the matching
    // evidence. A pure thunk still has its body threaded (it may contain a
    // self-contained handle). An effectful thunk we cannot rewrite this way (a
    // non-lambda thunk, or one buried in a constructor) makes the program
    // ineligible.
    fn thread_value(&mut self, v: &Value, env: &Env, loc: &Loc) -> Option<Value> {
        Some(match v {
            Value::Thunk(c) => match c.as_ref() {
                Comp::Lam(ps, b) => {
                    let ids = self.sig_ids(self.latent_ops(b).iter())?;
                    let mut env2 = env.clone();
                    let mut ps2 = ps.clone();
                    for id in ids {
                        let nm: Sym = ev(id).into();
                        env2.insert(id, nm);
                        ps2.push(nm);
                    }
                    Value::Thunk(Box::new(Comp::Lam(
                        ps2,
                        Box::new(self.thread_ev(b, &env2, loc)?),
                    )))
                }
                other => {
                    if !self.latent_ops(other).is_empty() {
                        return None;
                    }
                    Value::Thunk(Box::new(self.thread_ev(other, env, loc)?))
                }
            },
            Value::Ctor(n, t, fs) => {
                if fs.iter().any(|f| self.effectful_thunk(f)) {
                    return None;
                }
                Value::Ctor(*n, *t, self.thread_values(fs, env, loc)?)
            }
            Value::Tuple(fs) => {
                if fs.iter().any(|f| self.effectful_thunk(f)) {
                    return None;
                }
                Value::Tuple(self.thread_values(fs, env, loc)?)
            }
            _ => v.clone(),
        })
    }

    // The ops a computation is latent in (read against the whole-program map).
    pub(super) fn latent_ops(&self, c: &Comp) -> BTreeSet<MaskOp> {
        let mut s = BTreeSet::new();
        super::latent(c, &self.latent, &mut s);
        s
    }

    // A thunk whose body performs latent ops, in any position. Such a thunk is
    // only trackable as a top-level lambda value, not nested in data.
    fn effectful_thunk(&self, v: &Value) -> bool {
        match v {
            Value::Thunk(c) => {
                let body = if let Comp::Lam(_, b) = c.as_ref() {
                    b
                } else {
                    c
                };
                !self.latent_ops(body).is_empty()
            }
            Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.iter().any(|f| self.effectful_thunk(f)),
            _ => false,
        }
    }

    // The eligibility prologue both stream-fusion front-ends share. A program
    // can fuse only if it has no masks, lets nothing latent escape (neither a
    // first-class effectful thunk the flow cannot track nor an open latent at
    // `main`), and installs at least one handler. Returns the program's handles
    // for the caller's own per-handler shape check, or None when a guard fails
    // (the caller then falls back to the free monad). The two callers,
    // [`ev_eligible`](Self::ev_eligible) and [`fold_uniform`](Self::fold_uniform),
    // differ only in that per-handler check, not in this prologue.
    pub(super) fn fusion_handles<'a>(&self, core: &'a Core) -> Option<Vec<&'a Comp>> {
        if core.fns.iter().any(|f| contains_mask(&f.body)) {
            return None;
        }
        if flow::escapes(core, &self.latent, &self.flow) {
            return None;
        }
        if self
            .latent
            .get(&Sym::new(ENTRY_POINT))
            .is_some_and(|s| !s.is_empty())
        {
            return None;
        }
        let mut handles = Vec::new();
        for f in &core.fns {
            find_handles(&f.body, &mut handles);
        }
        if handles.is_empty() {
            return None;
        }
        Some(handles)
    }

    // Static eligibility for evidence passing: the shared fusion prologue plus
    // every reachable handler being tail-resumptive. Escaping effectful thunks
    // are fine here: the rewrite confirms it can track each one. An open handler
    // whose clause re-performs its own op (smap-style `emit(f(x))`) is fine: that
    // op is caught by an outer handler, whose evidence is in scope as a parameter.
    fn ev_eligible(&self, core: &Core) -> bool {
        let Some(handles) = self.fusion_handles(core) else {
            return false;
        };
        handles.iter().all(|h| {
            let Comp::Handle { ops, .. } = h else {
                return false;
            };
            ops.iter()
                .all(|op| strip_resume(&op.body, &resume_set(op.resume)).is_some())
        })
    }
}

pub(super) fn resume_set(resume: Sym) -> BTreeSet<Sym> {
    let mut s = BTreeSet::new();
    s.insert(resume);
    s
}

// Rewrite a tail-resumptive clause body into a plain function body: drop the
// `resume` binder (and any rebindings of it), and turn its single tail call
// `resume(v)` into `return v`. Returns None when the clause is not
// tail-resumptive (resume captured, used off the tail, or some path never
// resumes), which is exactly the eligibility test.
pub(super) fn strip_resume(c: &Comp, aliases: &BTreeSet<Sym>) -> Option<Comp> {
    match c {
        Comp::App(f, args) if matches!(f.as_ref(), Comp::Force(Value::Var(v)) if aliases.contains(v)) =>
        {
            let [arg] = args.as_slice() else {
                return None;
            };
            if !fv::value(arg).is_disjoint(aliases) {
                return None;
            }
            Some(Comp::Return(arg.clone()))
        }
        Comp::Bind(m, x, n) => {
            if let Comp::Return(Value::Var(v)) = m.as_ref() {
                if aliases.contains(v) {
                    let mut a2 = aliases.clone();
                    a2.insert(*x);
                    return strip_resume(n, &a2);
                }
            }
            if !fv::comp(m).is_disjoint(aliases) {
                return None;
            }
            Some(Comp::Bind(
                m.clone(),
                *x,
                Box::new(strip_resume(n, aliases)?),
            ))
        }
        Comp::If(v, t, e) => {
            if !fv::value(v).is_disjoint(aliases) {
                return None;
            }
            Some(Comp::If(
                v.clone(),
                Box::new(strip_resume(t, aliases)?),
                Box::new(strip_resume(e, aliases)?),
            ))
        }
        Comp::Case(v, arms) => {
            if !fv::value(v).is_disjoint(aliases) {
                return None;
            }
            let arms = arms
                .iter()
                .map(|(p, b)| Some((p.clone(), strip_resume(b, aliases)?)))
                .collect::<Option<Vec<_>>>()?;
            Some(Comp::Case(v.clone(), arms))
        }
        _ => None,
    }
}

pub(super) fn find_handles<'a>(c: &'a Comp, out: &mut Vec<&'a Comp>) {
    if matches!(c, Comp::Handle { .. }) {
        out.push(c);
    }
    each_value(c, &mut |v| {
        let mut ts = Vec::new();
        thunks_in_value(v, &mut ts);
        for t in ts {
            find_handles(t, out);
        }
    });
    each_subcomp(c, &mut |sc| find_handles(sc, out));
}
