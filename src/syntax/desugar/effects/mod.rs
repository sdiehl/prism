//! Scope-directed effect rewrite: var cells, named handlers, view patterns.
//!
//! `mod.rs` holds the shared scope types and the orchestrating tree-walker
//! (`rw`/`rw_sugar`); each cohesive transform lives in a sibling module:
//! [`vars`] (`var` cells), [`handlers`] (arm sugar + named instances),
//! [`views`] (view patterns), [`defaults`] (named-arg/default filling).

use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use super::sugar::expand_interp;
use super::{call, evar, lam1, sp, Cx};
use crate::error::TypeError;
use crate::names::{self, RET, UNIT_ARG};
use crate::syntax::ast::{
    Arm, Core, Expr, HandlerArm, Marker, Param, Pattern, Qualifier, Sugar, SugarArm, Surface, S,
};

mod defaults;
mod escape;
mod handlers;
mod vars;
mod views;

use defaults::fill_call;
use handlers::{rw_arms, rw_named, wrap_vals};
use vars::rw_var_decl;
use views::{check_views, pat_vars, rw_view_match};

// Lambda parameters carry no defaults in source (only top-level `fn`s do), so a
// surface lambda param maps to a core one unchanged but for the dropped slot.
fn core_param(p: &Param) -> Param<Core> {
    Param {
        name: p.name.clone(),
        ty: p.ty.clone(),
        borrow: p.borrow,
        default: None,
    }
}

// What a desugar-scoped name stands for: a `var`'s get/put ops, a named handler
// instance's map from user op names to its private mangled ops, or an ordinary
// local that shadows any top-level fn of the same name (so its calls bypass the
// named/default-argument rewrite).
#[derive(Clone)]
pub(super) enum Binding {
    Var(String, String),
    Inst(BTreeMap<String, String>),
    Local,
}

pub(super) type Vars = BTreeMap<String, Binding>;

// The scope-directed surface rewrite: walks an expression carrying `env` (the
// in-scope `var` cells and named handler instances) and rewrites their uses into
// ordinary effect operations (a `var` read becomes `get(())`, an assign becomes
// `put(v)`, an instance op becomes its private op call), so later passes see
// plain effects. Also home to the misuse diagnostics (a bare instance or pattern
// name as a value, a trailing `with`, assigning a non-var).
pub(super) fn rw(e: &S<Expr>, env: &Vars, cx: &mut Cx) -> Result<S<Expr<Core>>, TypeError> {
    let span = e.span;
    let node: Expr<Core> = match &e.node {
        Expr::Marker(Marker::With) => {
            return Err(TypeError::Other {
                span,
                msg: "`with` cannot be the last statement of a block: there is nothing for it to wrap".into(),
            });
        }
        // `Try`/`Interp` markers only ever appear as a call head, handled by the
        // `Call` arms below; a bare one is unreachable, but surface an error
        // rather than crash if a malformed marker reaches here.
        Expr::Marker(Marker::Try | Marker::Interp) => {
            return Err(TypeError::Other {
                span,
                msg: "internal: stray interpolation or `?` marker".into(),
            });
        }
        Expr::Var(x) => match env.get(x) {
            Some(Binding::Var(get, _)) => {
                return Ok(call(evar(get, span), vec![sp(Expr::Unit, span)], span));
            }
            Some(Binding::Inst(_)) => {
                return Err(TypeError::Other {
                    span,
                    msg: format!(
                        "handler instance `{x}` is not a value: call its operations as `{x}.op(...)`"
                    ),
                });
            }
            Some(Binding::Local) => Expr::Var(x.clone()),
            None => {
                if cx.patterns.contains_key(x) {
                    return Err(TypeError::Other {
                        span,
                        msg: format!("pattern `{x}` is not a value: apply it as `{x}(...)`"),
                    });
                }
                Expr::Var(x.clone())
            }
        },
        Expr::Let(x, v, b) => {
            let v2 = rw(v, env, cx)?;
            let mut env2 = env.clone();
            env2.insert(x.clone(), Binding::Local);
            Expr::Let(x.clone(), Box::new(v2), Box::new(rw(b, &env2, cx)?))
        }
        Expr::Lam(ps, b) => {
            let mut env2 = env.clone();
            for p in ps {
                env2.insert(p.name.clone(), Binding::Local);
            }
            let ps2 = ps.iter().map(core_param).collect();
            Expr::Lam(ps2, Box::new(rw(b, &env2, cx)?))
        }
        Expr::Match(s, arms) => {
            for a in arms {
                check_views(&a.pat, true, cx)?;
            }
            if let Some(idx) = arms.iter().position(
                |a| matches!(&a.pat.node, Pattern::Ctor(n, _) if cx.patterns.contains_key(n)),
            ) {
                return rw_view_match(s, arms, idx, span, env, cx);
            }
            let s2 = rw(s, env, cx)?;
            let mut arms2 = Vec::new();
            for a in arms {
                let mut env2 = env.clone();
                let mut bound = BTreeSet::new();
                pat_vars(&a.pat, &mut bound);
                for n in &bound {
                    env2.insert(n.clone(), Binding::Local);
                }
                let guard = match &a.guard {
                    Some(g) => Some(rw(g, &env2, cx)?),
                    None => None,
                };
                arms2.push(Arm {
                    pat: a.pat.clone(),
                    guard,
                    body: rw(&a.body, &env2, cx)?,
                });
            }
            Expr::Match(Box::new(s2), arms2)
        }
        Expr::Handle(b, arms) => {
            let b2 = rw(b, env, cx)?;
            let (arms2, vals) = rw_arms(arms, env, cx)?;
            let handled = sp(Expr::Handle(Box::new(b2), arms2), span);
            return Ok(wrap_vals(vals, handled, span));
        }
        Expr::Bin(op, a, b) => Expr::Bin(*op, Box::new(rw(a, env, cx)?), Box::new(rw(b, env, cx)?)),
        Expr::If(c, t, f) => Expr::If(
            Box::new(rw(c, env, cx)?),
            Box::new(rw(t, env, cx)?),
            Box::new(rw(f, env, cx)?),
        ),
        Expr::Call(f, args) if matches!(&f.node, Expr::Marker(Marker::Interp)) => {
            return expand_interp(args, span, env, cx);
        }
        Expr::Call(f, _) if matches!(&f.node, Expr::Marker(Marker::Try)) => {
            return Err(TypeError::Other {
                span,
                msg: "`?` is only allowed on a whole statement: write `let x = e?` or `e?`".into(),
            });
        }
        // `f.op(args)` parses as `op(f, args)`; when the receiver is a handler
        // instance in scope, the call dispatches to its private op instead.
        Expr::Call(f, args) => {
            // A pattern in expression position constructs through its `make`.
            if let Expr::Var(n) = &f.node {
                if let Some(&(arity, has_make)) = cx.patterns.get(n) {
                    if !has_make {
                        return Err(TypeError::Other {
                            span,
                            msg: format!("pattern `{n}` has no `make` clause and cannot be used as an expression"),
                        });
                    }
                    if args.len() != arity {
                        return Err(TypeError::Other {
                            span,
                            msg: format!(
                                "pattern `{n}` takes {arity} argument(s), {} given",
                                args.len()
                            ),
                        });
                    }
                    let args2: Result<Vec<_>, _> = args.iter().map(|a| rw(a, env, cx)).collect();
                    return Ok(call(evar(&names::pat_make(n), f.span), args2?, span));
                }
            }
            if let (Expr::Var(m), Some(Expr::Var(r))) = (&f.node, args.first().map(|a| &a.node)) {
                if let Some(Binding::Inst(ops)) = env.get(r) {
                    let Some(mangled) = ops.get(m).cloned() else {
                        return Err(TypeError::Other {
                            span,
                            msg: format!("handler instance `{r}` has no operation `{m}`"),
                        });
                    };
                    let rest: Result<Vec<_>, _> =
                        args[1..].iter().map(|a| rw(a, env, cx)).collect();
                    return Ok(call(evar(&mangled, f.span), rest?, span));
                }
            }
            // A call of a top-level fn (not locally shadowed) may carry named
            // arguments or omit trailing defaulted ones; fill it to a plain
            // positional call. Partial applications fall through unchanged.
            if let Expr::Var(name) = &f.node {
                if env.get(name).is_none() {
                    if let Some(sig) = cx.fn_sigs.get(name) {
                        let named = args
                            .iter()
                            .any(|a| matches!(&a.node, Expr::Sugar(Sugar::Assign(..))));
                        if named || args.len() < sig.len() {
                            let sig = sig.clone();
                            return fill_call(name, &sig, args, f.span, span, env, cx);
                        }
                    }
                }
            }
            let f2 = rw(f, env, cx)?;
            let args2: Result<Vec<_>, _> = args.iter().map(|a| rw(a, env, cx)).collect();
            Expr::Call(Box::new(f2), args2?)
        }
        Expr::Pipe(a, b) => Expr::Pipe(Box::new(rw(a, env, cx)?), Box::new(rw(b, env, cx)?)),
        Expr::List(es) => {
            let es2: Result<Vec<_>, _> = es.iter().map(|a| rw(a, env, cx)).collect();
            Expr::List(es2?)
        }
        Expr::Tuple(es) => {
            let es2: Result<Vec<_>, _> = es.iter().map(|a| rw(a, env, cx)).collect();
            Expr::Tuple(es2?)
        }
        Expr::FieldAccess(b, f) => Expr::FieldAccess(Box::new(rw(b, env, cx)?), f.clone()),
        Expr::RecordCreate(n, fs) => {
            let fs2: Result<Vec<_>, _> = fs
                .iter()
                .map(|(f, v)| rw(v, env, cx).map(|v2| (f.clone(), v2)))
                .collect();
            Expr::RecordCreate(n.clone(), fs2?)
        }
        Expr::RecordUpdate(b, n, fs) => {
            let b2 = rw(b, env, cx)?;
            let fs2: Result<Vec<_>, _> = fs
                .iter()
                .map(|(f, v)| rw(v, env, cx).map(|v2| (f.clone(), v2)))
                .collect();
            Expr::RecordUpdate(Box::new(b2), n.clone(), fs2?)
        }
        Expr::RecordUpdatePath(b, ups) => {
            let b2 = rw(b, env, cx)?;
            let ups2: Result<Vec<_>, _> = ups
                .iter()
                .map(|(p, v)| rw(v, env, cx).map(|v2| (p.clone(), v2)))
                .collect();
            Expr::RecordUpdatePath(Box::new(b2), ups2?)
        }
        Expr::Inst(f, ns) => Expr::Inst(Box::new(rw(f, env, cx)?), ns.clone()),
        Expr::Ann(a, t) => Expr::Ann(Box::new(rw(a, env, cx)?), t.clone()),
        Expr::Mask(eff, b) => Expr::Mask(eff.clone(), Box::new(rw(b, env, cx)?)),
        Expr::Sugar(s) => return rw_sugar(s, span, env, cx),
        Expr::Int(i) => Expr::Int(i.clone()),
        Expr::Float(x) => Expr::Float(*x),
        Expr::Char(c) => Expr::Char(*c),
        Expr::Bool(b) => Expr::Bool(*b),
        Expr::Unit => Expr::Unit,
        Expr::Str(s) => Expr::Str(s.clone()),
    };
    Ok(sp(node, span))
}

// Each surface-only form rebuilds a sugar-free surface tree (a handler, a
// stream, a field access) and re-runs `rw` on it, except `var`/named-handler
// which have their own driver; nothing here returns sugar.
fn rw_sugar(
    s: &Sugar<Surface>,
    span: Span,
    env: &Vars,
    cx: &mut Cx,
) -> Result<S<Expr<Core>>, TypeError> {
    match s {
        Sugar::NamedHandle(f, body, arms) => rw_named(f, body, arms, span, env, cx),
        Sugar::VarDecl(x, init, rest) => rw_var_decl(x, init, rest, span, env, cx),
        Sugar::Assign(x, v) => {
            let v2 = rw(v, env, cx)?;
            match env.get(x) {
                Some(Binding::Var(_, put)) => Ok(call(evar(put, span), vec![v2], span)),
                _ => Err(TypeError::Other {
                    span,
                    msg: format!("cannot assign to `{x}`: declare it with `var {x} := ...`"),
                }),
            }
        }
        Sugar::Throw(name, args) => {
            if !cx.errors.contains(name) {
                return Err(TypeError::Other {
                    span,
                    msg: format!("`{name}` is not a declared error"),
                });
            }
            let args2: Result<Vec<_>, _> = args.iter().map(|a| rw(a, env, cx)).collect();
            Ok(call(evar(&names::throw_op(name), span), args2?, span))
        }
        // One nested handle per catch arm, first arm innermost. Each level is
        // a `final ctl` clause for that error's throw op plus an identity
        // return; the rebuilt tree goes back through rw so the Final
        // machinery (resume rejection, CONT rewrite) applies.
        Sugar::TryCatch(body, arms) => {
            let mut acc = (**body).clone();
            for a in arms {
                if !cx.errors.contains(&a.name) {
                    return Err(TypeError::Other {
                        span: a.span,
                        msg: format!("`{}` is not a declared error", a.name),
                    });
                }
                let arity = cx.op_sigs[&names::throw_op(&a.name)].2.params.len();
                if a.binders.len() != arity {
                    return Err(TypeError::Other {
                        span: a.span,
                        msg: format!(
                            "`{}` carries {arity} value(s), this catch arm binds {}",
                            a.name,
                            a.binders.len()
                        ),
                    });
                }
                let harms = vec![
                    HandlerArm::Sugar(SugarArm::Final(
                        names::throw_op(&a.name),
                        a.binders.clone(),
                        a.body.clone(),
                    )),
                    HandlerArm::Return(RET.into(), evar(RET, a.span)),
                ];
                acc = sp(Expr::Handle(Box::new(acc), harms), a.span);
            }
            rw(&acc, env, cx)
        }
        // `for x in s, <quals> do body`: install a consumer handler over the
        // producer, run the qualifier-folded body per element via a tail-
        // resumptive emit clause, result Unit.
        Sugar::For(x, s, quals, body) => {
            let inner = fold_quals(quals, (**body).clone(), span);
            let run = call((**s).clone(), vec![sp(Expr::Unit, s.span)], s.span);
            let arms = vec![
                HandlerArm::Sugar(SugarArm::Fun("emit".into(), vec![x.clone()], inner)),
                HandlerArm::Return(RET.into(), sp(Expr::Unit, span)),
            ];
            rw(&sp(Expr::Handle(Box::new(run), arms), span), env, cx)
        }
        // `[ head for x in s, <quals> ]`: re-emit the head from a thunk-stream
        // and collect the emits into a list with `scollect`.
        Sugar::Comp(head, x, s, quals) => {
            let emit_head = call(evar("emit", head.span), vec![(**head).clone()], head.span);
            let body = sp(
                Expr::Sugar(Sugar::For(
                    x.clone(),
                    s.clone(),
                    quals.clone(),
                    Box::new(emit_head),
                )),
                span,
            );
            let thunk = lam1(UNIT_ARG, body, span);
            rw(&call(evar("scollect", span), vec![thunk], span), env, cx)
        }
        // `a ?? b`: a `Fail`-discarding handler over `a` that returns `b` on
        // failure; a `Fail` raised by `b` itself escapes to the outer context.
        Sugar::Default(a, b) => {
            let arms = vec![
                HandlerArm::Sugar(SugarArm::Final(
                    names::FAIL_OP.into(),
                    Vec::new(),
                    (**b).clone(),
                )),
                HandlerArm::Return(RET.into(), evar(RET, span)),
            ];
            rw(&sp(Expr::Handle(a.clone(), arms), span), env, cx)
        }
        // `transact body else fallback`: snapshot every live `var` with its get
        // op, run body in a `Fail`-discarding handler, and on failure restore
        // each var with its put op before yielding `fallback`. The restoring puts
        // and the snapshots hit the outer var handlers, so a failed body's
        // mutations drop with the continuation and pre-transaction values are
        // re-established. Vars declared inside body are not in `env` here, so they
        // are correctly left untouched.
        Sugar::Transact(body, fallback) => {
            let vars: Vec<(String, String)> = env
                .values()
                .filter_map(|b| match b {
                    Binding::Var(get, put) => Some((get.clone(), put.clone())),
                    _ => None,
                })
                .collect();
            let snaps: Vec<String> = vars
                .iter()
                .map(|_| names::snapshot(cx.next.bump()))
                .collect();
            let mut restore = (**fallback).clone();
            for ((_, put), snap) in vars.iter().zip(&snaps).rev() {
                let put_call = call(evar(put, span), vec![evar(snap, span)], span);
                restore = sp(
                    Expr::Let(UNIT_ARG.into(), Box::new(put_call), Box::new(restore)),
                    span,
                );
            }
            let arms = vec![
                HandlerArm::Sugar(SugarArm::Final(names::FAIL_OP.into(), Vec::new(), restore)),
                HandlerArm::Return(RET.into(), evar(RET, span)),
            ];
            let mut handled = sp(Expr::Handle(body.clone(), arms), span);
            for ((get, _), snap) in vars.iter().zip(&snaps).rev() {
                let get_call = call(evar(get, span), vec![sp(Expr::Unit, span)], span);
                handled = sp(
                    Expr::Let(snap.clone(), Box::new(get_call), Box::new(handled)),
                    span,
                );
            }
            rw(&handled, env, cx)
        }
        // `a?.b` is `force(a).b`: a `None` makes `force` raise `Fail`, so the
        // access is failable and chains short-circuit to the nearest handler.
        Sugar::OptChain(a, field) => {
            let forced = call(evar("force", span), vec![(**a).clone()], span);
            let access = sp(Expr::FieldAccess(Box::new(forced), field.clone()), span);
            rw(&access, env, cx)
        }
        // `[a..z]` / `[a, b..z]`: the prefix sets the start, and its first two
        // (when present) the step; the rest of the prefix is redundant.
        Sugar::Range(pre, hi) => {
            let (f, mut args) = if pre.len() >= 2 {
                ("enum_from_then_to", vec![pre[0].clone(), pre[1].clone()])
            } else {
                ("enum_from_to", vec![pre[0].clone()])
            };
            args.push((**hi).clone());
            rw(&call(evar(f, span), args, span), env, cx)
        }
    }
}

// Fold a comprehension's qualifiers inside-out around its body. A `Guard` keeps
// the element only when `g` both succeeds and holds: `guard(g)` fails on a false
// condition, and `succeeds` reifies that (plus any `Fail` raised computing `g`)
// back to a `Bool`, so the element is pruned rather than the failure escaping.
// Pure and failable guards share this rule, since `succeeds` discharges the
// `Fail` either way. A `Bind` becomes `let y = e in acc`.
fn fold_quals(quals: &[Qualifier], body: S<Expr>, span: Span) -> S<Expr> {
    // Builds a sugar-free surface tree that `rw` consumes; phase stays Surface.
    let mut acc = body;
    for q in quals.iter().rev() {
        acc = match q {
            Qualifier::Guard(g) => {
                let guarded = call(evar("guard", g.span), vec![g.clone()], g.span);
                let thunk = sp(Expr::Lam(Vec::new(), Box::new(guarded)), g.span);
                let test = call(evar("succeeds", g.span), vec![thunk], g.span);
                sp(
                    Expr::If(
                        Box::new(test),
                        Box::new(acc),
                        Box::new(sp(Expr::Unit, span)),
                    ),
                    g.span,
                )
            }
            Qualifier::Bind(y, e) => sp(
                Expr::Let(y.clone(), Box::new(e.clone()), Box::new(acc)),
                e.span,
            ),
        };
    }
    acc
}
