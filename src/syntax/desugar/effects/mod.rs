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
use crate::names::{self, COMPOSE, RET, UNIT_ARG};
use crate::syntax::ast::{
    Arm, BinOp, Core, Expr, HandlerArm, Marker, Param, PathOp, PathStep, Pattern, Qualifier, Sugar,
    SugarArm, Surface, S,
};

mod defaults;
mod escape;
mod handlers;
mod paths;
mod vars;
mod views;

use defaults::fill_call;
pub(in crate::syntax::desugar) use escape::referenced_names;
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
        // `a ^ b` is sugar for the `Pow` class method `pow(a, b)`. The head is a
        // synthesized node, so its dictionary keys on its own `NodeId` and never
        // aliases a real dispatch site (see `synth_span`). Lowering through the
        // class keeps int exponentiation bignum-correct (its `Int` instance
        // multiplies) and float exponentiation a `pow_float` call.
        Expr::Bin(BinOp::Pow, a, b) => {
            let head = evar(names::POW_METHOD, synth_span(cx));
            return rw(
                &call(head, vec![(**a).clone(), (**b).clone()], span),
                env,
                cx,
            );
        }
        Expr::Bin(op, a, b) => Expr::Bin(*op, Box::new(rw(a, env, cx)?), Box::new(rw(b, env, cx)?)),
        Expr::Neg(a) => Expr::Neg(Box::new(rw(a, env, cx)?)),
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
            // An `each`/`?Ctor` step lowers to `fmap`/`match` here, before tc;
            // what remains is a `Field`-only path the checker and elaborator
            // rebuild directly.
            if paths::has_optic(ups) {
                return paths::lower_optics(b, ups, env, cx, span);
            }
            let b2 = rw(b, env, cx)?;
            let ups2: Result<Vec<_>, _> = ups
                .iter()
                .map(|(p, op)| {
                    let op2 = match op {
                        PathOp::Set(v) => PathOp::Set(rw(v, env, cx)?),
                        PathOp::Modify(v) => PathOp::Modify(rw(v, env, cx)?),
                    };
                    // `has_optic` was false, so every step is a `Field`.
                    let p2 = p
                        .iter()
                        .map(|s| match s {
                            PathStep::Field(f) => PathStep::Field(f.clone()),
                            _ => unreachable!("optic step in a non-optic path"),
                        })
                        .collect();
                    Ok((p2, op2))
                })
                .collect();
            Expr::RecordUpdatePath(Box::new(b2), ups2?)
        }
        Expr::Inst(f, ns) => Expr::Inst(Box::new(rw(f, env, cx)?), ns.clone()),
        Expr::Index(recv, key) => {
            Expr::Index(Box::new(rw(recv, env, cx)?), Box::new(rw(key, env, cx)?))
        }
        Expr::IndexSet(recv, key, val) => Expr::IndexSet(
            Box::new(rw(recv, env, cx)?),
            Box::new(rw(key, env, cx)?),
            Box::new(rw(val, env, cx)?),
        ),
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
// `recv[key] := value` rebinds the root variable as `root := index_set(..)`,
// nesting one `IndexSet` per level for `grid[i][j] := v`. The base must be a
// variable; returns the equivalent `Sugar::Assign` surface expr to rewrite.
fn index_to_var_set(
    recv: &S<Expr>,
    key: &S<Expr>,
    value: S<Expr>,
    span: Span,
) -> Result<S<Expr>, TypeError> {
    let set = sp(
        Expr::IndexSet(
            Box::new(recv.clone()),
            Box::new(key.clone()),
            Box::new(value),
        ),
        span,
    );
    match &recv.node {
        Expr::Var(name) => Ok(sp(
            Expr::Sugar(Sugar::Assign(name.clone(), Box::new(set))),
            span,
        )),
        Expr::Index(inner_recv, inner_key) => index_to_var_set(inner_recv, inner_key, set, span),
        _ => Err(TypeError::Other {
            span: recv.span,
            msg: "the base of an indexed assignment must be a variable".into(),
        }),
    }
}

fn rw_sugar(
    s: &Sugar<Surface>,
    span: Span,
    env: &Vars,
    cx: &mut Cx,
) -> Result<S<Expr<Core>>, TypeError> {
    match s {
        Sugar::NamedHandle(f, body, arms) => rw_named(f, body, arms, span, env, cx),
        Sugar::ReadPath(base, steps) => paths::read_path(base, steps, env, cx, span),
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
        // `recv[key] := value` rebinds the root `var`; recover the equivalent
        // `root := index_set(..)` surface form and rewrite that, so var-read
        // rewriting and the `put` emission go through the `Assign` path above.
        Sugar::IndexAssign(recv, key, value) => {
            let assign = index_to_var_set(recv, key, (**value).clone(), span)?;
            rw(&assign, env, cx)
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
                let harms = final_handler(
                    names::throw_op(&a.name),
                    a.binders.clone(),
                    a.body.clone(),
                    a.span,
                );
                acc = sp(Expr::Handle(Box::new(acc), harms), a.span);
            }
            rw(&acc, env, cx)
        }
        // `for x in s, <quals> do body`: install a consumer handler over the
        // producer, run the qualifier-folded body per element via a tail-
        // resumptive emit clause, result Unit. `break`/`continue` retrofit the
        // same way as `while`: a `continue` handler wraps each element's body so
        // the emit clause resumes to the next element, and a `break` handler wraps
        // the whole consumer so it abandons the producer (its suspended
        // continuation drops the same way a `??`/`fail` escape does).
        Sugar::For(x, s, quals, body) => {
            // `break`/`continue` may appear in a qualifier guard/bind, not only the
            // body; those must be caught by this loop, so scan the qualifiers too.
            let (mut has_break, mut has_continue) = loop_ctl_used(body);
            for q in quals {
                let (b, c) = match q {
                    Qualifier::Guard(g) | Qualifier::Bind(_, g) => loop_ctl_used(g),
                };
                has_break = has_break || b;
                has_continue = has_continue || c;
            }
            let inner = fold_quals(quals, (**body).clone(), span, cx);
            let inner = wrap_if(has_continue, names::CONTINUE_OP, inner, span);
            let run = call((**s).clone(), vec![sp(Expr::Unit, s.span)], s.span);
            let arms = vec![
                HandlerArm::Sugar(SugarArm::Fun("emit".into(), vec![x.clone()], inner)),
                HandlerArm::Return(RET.into(), sp(Expr::Unit, span)),
            ];
            let consumer = sp(Expr::Handle(Box::new(run), arms), span);
            let full = wrap_if(has_break, names::BREAK_OP, consumer, span);
            rw(&full, env, cx)
        }
        Sugar::While(cond, body) => rw_while(cond.as_deref(), body, span, env, cx),
        // `break` / `continue`: non-resumable performs of the internal loop-control
        // effects, caught by the handlers `rw_while` installs around the loop.
        Sugar::Break => rw(
            &call(evar(names::BREAK_OP, span), Vec::new(), span),
            env,
            cx,
        ),
        Sugar::Continue => rw(
            &call(evar(names::CONTINUE_OP, span), Vec::new(), span),
            env,
            cx,
        ),
        // `return e`: perform the internal `Return` op carrying `e`, caught by the
        // handler `wrap_return` installs around the enclosing function body.
        Sugar::Return(e) => rw(
            &call(evar(names::RETURN_OP, span), vec![(**e).clone()], span),
            env,
            cx,
        ),
        // `[ head for x in s ]` with no qualifiers is exactly a mapped stream, so
        // lower it to `scollect(smap(s, \x -> head))`: the head map is a stream
        // combinator that fuses with the collecting fold. The general form below
        // hands `scollect` a first-class effectful thunk (the qualifier-folded
        // for-consumer), which cannot fuse and reifies into the free monad, one
        // eff-op cell per element. Both paths evaluate `s` once, in emission order,
        // and produce the identical list; this one just stays on the fused tier.
        Sugar::Comp(head, x, s, quals) if quals.is_empty() => {
            let f = lam1(x, (**head).clone(), head.span);
            let mapped = call(evar(names::SMAP_FN, span), vec![(**s).clone(), f], span);
            rw(
                &call(evar(names::SCOLLECT_FN, span), vec![mapped], span),
                env,
                cx,
            )
        }
        // `[ head for x in s, <quals> ]`: re-emit the head from a thunk-stream
        // and collect the emits into a list with `scollect`. The guards and binds
        // fold around the head inside the for-consumer, so this path keeps them.
        Sugar::Comp(head, x, s, quals) => {
            let emit_head = call(
                evar(names::EMIT_OP, head.span),
                vec![(**head).clone()],
                head.span,
            );
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
            rw(
                &call(evar(names::SCOLLECT_FN, span), vec![thunk], span),
                env,
                cx,
            )
        }
        // `a ?? b`: a `Fail`-discarding handler over `a` that returns `b` on
        // failure; a `Fail` raised by `b` itself escapes to the outer context.
        Sugar::Default(a, b) => {
            let arms = final_handler(names::FAIL_OP.into(), Vec::new(), (**b).clone(), span);
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
            let arms = final_handler(names::FAIL_OP.into(), Vec::new(), restore, span);
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
        Sugar::Probe(name, body) => {
            validate_probe_name(name, span)?;
            let gate = call(
                evar("probe_enabled", span),
                vec![sp(Expr::Str(name.clone()), span)],
                span,
            );
            let branch = sp(
                Expr::If(
                    Box::new(gate),
                    Box::new((**body).clone()),
                    Box::new(sp(Expr::Unit, span)),
                ),
                span,
            );
            rw(&branch, env, cx)
        }
        // `a?.b` is `force(a).b`: a `None` makes `force` raise `Fail`, so the
        // access is failable and chains short-circuit to the nearest handler.
        Sugar::OptChain(a, field) => {
            let forced = call(evar(names::FORCE_FN, span), vec![(**a).clone()], span);
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
        // `f >> g` lowers to `\x -> g(f(x))`, `f << g` to `\x -> f(g(x))`. The
        // bound name is unforgeable, so the synthesized lambda cannot capture.
        Sugar::Compose(forward, f, g) => {
            let (outer, inner) = if *forward { (g, f) } else { (f, g) };
            let xv = evar(COMPOSE, span);
            let inner_call = call((**inner).clone(), vec![xv], span);
            let body = call((**outer).clone(), vec![inner_call], span);
            let param = Param {
                name: COMPOSE.into(),
                ty: None,
                borrow: false,
                default: None,
            };
            rw(&sp(Expr::Lam(vec![param], Box::new(body)), span), env, cx)
        }
    }
}

fn validate_probe_name(name: &str, span: Span) -> Result<(), TypeError> {
    let valid = !name.is_empty()
        && name
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b':' | b'-'));
    if valid {
        return Ok(());
    }
    Err(TypeError::Other {
        span,
        msg: "probe name must match [A-Za-z0-9_.:-]+".into(),
    })
}

// `while cond do body` / `loop body` desugar to the tail-recursive prelude
// `while_loop(cond, body)`. The condition and body are each wrapped in a thunk so
// they re-run per iteration; the thunks close over the ambient `var` State effect,
// so mutations thread through the enclosing var handlers, and `loop` passes a
// constant-`true` condition. `while_loop`'s self-call is in tail position, so the
// loop runs in constant stack with no per-iteration allocation, and because
// `while_loop` is unconstrained and effect-polymorphic, a break/continue-free loop
// adds no effect of its own (pay-as-you-go). The call head is a synthesized node,
// keyed for dispatch by its own `NodeId`, so it never aliases a real dispatch site.
fn rw_while(
    cond: Option<&S<Expr>>,
    body: &S<Expr>,
    span: Span,
    env: &Vars,
    cx: &mut Cx,
) -> Result<S<Expr<Core>>, TypeError> {
    // Pay-as-you-go: a loop adds a control handler only for the keyword it uses.
    // `continue` ends the current iteration, so its handler wraps each body run;
    // `break` exits the loop, so its handler wraps the whole driver call. `break`
    // performed in the body forwards through the continue handler (a different
    // effect) out to the break handler. Both are `final ctl`, so neither label
    // surfaces. A nested loop captures its own break/continue, so the scan stops
    // at one.
    let (has_break, has_continue) = loop_ctl_used(body);
    let body = wrap_if(has_continue, names::CONTINUE_OP, body.clone(), span);
    let body_thunk = sp(Expr::Lam(Vec::new(), Box::new(body)), span);
    // An unconditional `loop` that cannot `break` never returns, so it lowers to
    // the bottom-typed `forever` and can stand as the body of a function of any
    // result type whose only exits are early `return`s. Every other loop can fall
    // through (a false `while` condition, or a `break`), so it lowers to the
    // Unit-typed `repeat_while`.
    let driver = if cond.is_none() && !has_break {
        let head = evar(names::FOREVER, synth_span(cx));
        call(head, vec![body_thunk], span)
    } else {
        let cond_expr = cond.cloned().unwrap_or_else(|| sp(Expr::Bool(true), span));
        let cond_thunk = sp(Expr::Lam(Vec::new(), Box::new(cond_expr)), span);
        let head = evar(names::REPEAT_WHILE, synth_span(cx));
        call(head, vec![cond_thunk, body_thunk], span)
    };
    let full = wrap_if(has_break, names::BREAK_OP, driver, span);
    rw(&full, env, cx)
}

// A `final ctl` handler that catches one loop-control op and yields `()`: as a
// final clause the continuation is dropped, so catching `break` abandons the loop
// and catching `continue` abandons the current iteration. The return arm also
// yields `()`, so the handled block has type Unit either way (the driver ignores
// the body's value and the loop itself yields Unit).
fn loop_ctl_handler(op: &str, body: S<Expr>, span: Span) -> S<Expr> {
    let arms = vec![
        HandlerArm::Sugar(SugarArm::Final(op.into(), Vec::new(), sp(Expr::Unit, span))),
        HandlerArm::Return(RET.into(), sp(Expr::Unit, span)),
    ];
    sp(Expr::Handle(Box::new(body), arms), span)
}

// Wrap `body` in `loop_ctl_handler` for `op` only when the loop actually uses
// that control keyword (pay-as-you-go); otherwise return `body` untouched.
fn wrap_if(used: bool, op: &str, body: S<Expr>, span: Span) -> S<Expr> {
    if used {
        loop_ctl_handler(op, body, span)
    } else {
        body
    }
}

// A `final ctl` handler that catches one op, binds its carried values and yields
// the clause body, with an identity return arm (the handled block keeps its
// normal result). The twin of `loop_ctl_handler`, which instead yields Unit.
fn final_handler(op: String, binders: Vec<String>, body: S<Expr>, span: Span) -> Vec<HandlerArm> {
    vec![
        HandlerArm::Sugar(SugarArm::Final(op, binders, body)),
        HandlerArm::Return(RET.into(), evar(RET, span)),
    ]
}

// Wrap a function body in a `final ctl` handler for the internal `Return` effect
// when it uses `return`, so `return e` exits the function with `e`. The op arm
// binds the carried value and yields it; the return arm passes the normal result
// through. Both have the function's result type, the effect is fully discharged,
// and a return-free body is returned untouched (pay-as-you-go).
pub(super) fn wrap_return(body: S<Expr>, cx: &mut Cx) -> S<Expr> {
    if !CtlScan::returns(&body) {
        return body;
    }
    let span = body.span;
    let v = format!("{}{}", names::VAL, cx.next.bump());
    let arms = final_handler(
        names::RETURN_OP.into(),
        vec![v.clone()],
        evar(&v, span),
        span,
    );
    sp(Expr::Handle(Box::new(body), arms), span)
}

// Loop-control keywords a body performs at this loop's level: `(break, continue)`.
fn loop_ctl_used(e: &S<Expr>) -> (bool, bool) {
    let f = CtlScan::scan(e, false, true);
    (f.0, f.1)
}

// Read-only scan for the control keywords a body performs at its own level.
// `descend_loops`/`descend_lambdas` set the boundaries: loop control
// (`break`/`continue`) stops at a nested loop but enters lambdas, while `return`
// stops at a nested lambda (a new function) but enters loops. Everything else (the
// other sugar, `if`, `match`, handler arms) is always entered, matching the
// dynamic scope of the handler the desugar installs.
struct CtlScan {
    descend_loops: bool,
    descend_lambdas: bool,
    found: (bool, bool, bool),
}

impl CtlScan {
    fn scan(e: &S<Expr>, descend_loops: bool, descend_lambdas: bool) -> (bool, bool, bool) {
        let mut s = Self {
            descend_loops,
            descend_lambdas,
            found: (false, false, false),
        };
        s.go(e);
        s.found
    }

    fn returns(e: &S<Expr>) -> bool {
        Self::scan(e, true, false).2
    }

    fn arm(&mut self, a: &HandlerArm) {
        match a {
            HandlerArm::Return(_, b)
            | HandlerArm::Op(_, _, _, b)
            | HandlerArm::Sugar(
                SugarArm::Fun(_, _, b) | SugarArm::Final(_, _, b) | SugarArm::Val(_, b),
            ) => self.go(b),
        }
    }

    fn quals(&mut self, quals: &[Qualifier]) {
        for q in quals {
            match q {
                Qualifier::Guard(g) => self.go(g),
                Qualifier::Bind(_, e) => self.go(e),
            }
        }
    }

    fn sugar(&mut self, s: &Sugar<Surface>) {
        match s {
            Sugar::Break => self.found.0 = true,
            Sugar::Continue => self.found.1 = true,
            Sugar::Return(e) => {
                self.found.2 = true;
                self.go(e);
            }
            // A probe body is transparent to control flow: a `break`/`continue`/
            // `return` inside it belongs to the enclosing loop or function, so
            // scan through it to install those handlers.
            Sugar::Probe(_, body) => self.go(body),
            Sugar::While(c, b) if self.descend_loops => {
                if let Some(c) = c {
                    self.go(c);
                }
                self.go(b);
            }
            Sugar::For(_, s, quals, b) if self.descend_loops => {
                self.go(s);
                self.quals(quals);
                self.go(b);
            }
            Sugar::Comp(h, _, s, quals) if self.descend_loops => {
                self.go(h);
                self.go(s);
                self.quals(quals);
            }
            // A nested loop/comprehension captures its own break/continue.
            Sugar::While(..) | Sugar::For(..) | Sugar::Comp(..) => {}
            Sugar::VarDecl(_, v, b) => {
                self.go(v);
                self.go(b);
            }
            Sugar::Assign(_, v) | Sugar::OptChain(v, _) => self.go(v),
            Sugar::IndexAssign(recv, key, v) => {
                self.go(recv);
                self.go(key);
                self.go(v);
            }
            Sugar::NamedHandle(_, b, arms) => {
                self.go(b);
                for a in arms {
                    self.arm(a);
                }
            }
            Sugar::Throw(_, args) => {
                for a in args {
                    self.go(a);
                }
            }
            Sugar::TryCatch(b, arms) => {
                self.go(b);
                for a in arms {
                    self.go(&a.body);
                }
            }
            Sugar::Default(a, b) | Sugar::Transact(a, b) | Sugar::Compose(_, a, b) => {
                self.go(a);
                self.go(b);
            }
            Sugar::Range(pre, hi) => {
                for x in pre {
                    self.go(x);
                }
                self.go(hi);
            }
            Sugar::ReadPath(b, steps) => {
                self.go(b);
                for s in steps {
                    if let Some(e) = s.sub_expr() {
                        self.go(e);
                    }
                }
            }
        }
    }

    fn go(&mut self, e: &S<Expr>) {
        match &e.node {
            Expr::Sugar(s) => self.sugar(s),
            Expr::Bin(_, a, b) | Expr::Pipe(a, b) => {
                self.go(a);
                self.go(b);
            }
            Expr::If(c, t, f) => {
                self.go(c);
                self.go(t);
                self.go(f);
            }
            Expr::Let(_, v, b) => {
                self.go(v);
                self.go(b);
            }
            Expr::Lam(_, b) if self.descend_lambdas => self.go(b),
            Expr::Call(f, args) => {
                self.go(f);
                for a in args {
                    self.go(a);
                }
            }
            Expr::Match(s, arms) => {
                self.go(s);
                for a in arms {
                    if let Some(g) = &a.guard {
                        self.go(g);
                    }
                    self.go(&a.body);
                }
            }
            Expr::List(es) | Expr::Tuple(es) => {
                for x in es {
                    self.go(x);
                }
            }
            Expr::FieldAccess(b, _)
            | Expr::Inst(b, _)
            | Expr::Ann(b, _)
            | Expr::Mask(_, b)
            | Expr::Neg(b) => {
                self.go(b);
            }
            Expr::Index(recv, key) => {
                self.go(recv);
                self.go(key);
            }
            Expr::IndexSet(recv, key, val) => {
                self.go(recv);
                self.go(key);
                self.go(val);
            }
            Expr::RecordCreate(_, fs) => {
                for (_, v) in fs {
                    self.go(v);
                }
            }
            Expr::RecordUpdate(b, _, fs) => {
                self.go(b);
                for (_, v) in fs {
                    self.go(v);
                }
            }
            Expr::RecordUpdatePath(b, ups) => {
                self.go(b);
                for (steps, op) in ups {
                    for s in steps {
                        if let Some(e) = s.sub_expr() {
                            self.go(e);
                        }
                    }
                    self.go(op.expr());
                }
            }
            Expr::Handle(b, arms) => {
                self.go(b);
                for a in arms {
                    self.arm(a);
                }
            }
            // A lambda whose body is not descended into (return stops at a nested
            // function), the leaves, and markers carry no control keyword.
            Expr::Lam(..)
            | Expr::Int(_)
            | Expr::Float(_)
            | Expr::Char(_)
            | Expr::Bool(_)
            | Expr::Unit
            | Expr::Str(_)
            | Expr::Var(_)
            | Expr::Marker(_) => {}
        }
    }
}

// A span for a synthesized node. Dispatch identity is the node's `NodeId`
// (assigned after desugar), not its span, so a synthesized call head can no
// longer alias a real dispatch site by reusing a source span -- the source of
// the old "or it crashes monadification" hazard. The span is now purely a
// diagnostic, and a synthesized node has no source location, so it collapses to
// the empty span. The fresh id is still consumed (it is shared with generated
// variable names) to keep that numbering stable.
const fn synth_span(cx: &mut Cx) -> Span {
    let _ = cx.next.bump();
    Span::empty(0)
}

// Fold a comprehension's qualifiers inside-out around its body. A `Guard` keeps
// the element only when `g` both succeeds and holds: `guard(g)` fails on a false
// condition, and `succeeds` reifies that (plus any `Fail` raised computing `g`)
// back to a `Bool`, so the element is pruned rather than the failure escaping.
// Pure and failable guards share this rule, since `succeeds` discharges the
// `Fail` either way. A `Bind` becomes `let y = e in acc`.
fn fold_quals(quals: &[Qualifier], body: S<Expr>, span: Span, cx: &mut Cx) -> S<Expr> {
    // Builds a sugar-free surface tree that `rw` consumes; phase stays Surface.
    let mut acc = body;
    for q in quals.iter().rev() {
        acc = match q {
            Qualifier::Guard(g) => {
                let guarded = call(
                    evar(names::GUARD_FN, synth_span(cx)),
                    vec![g.clone()],
                    g.span,
                );
                let thunk = sp(Expr::Lam(Vec::new(), Box::new(guarded)), g.span);
                let test = call(
                    evar(names::SUCCEEDS_FN, synth_span(cx)),
                    vec![thunk],
                    g.span,
                );
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
