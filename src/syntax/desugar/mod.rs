//! Surface desugaring driver and shared constructors.
//!
//! `var x := e` becomes a per-var algebraic effect: reads are `get@x@n(())`,
//! writes are `set@x@n(e)`, and the block runs under a parameter-passing handler
//! applied to the initial value, so the effect is discharged and the enclosing
//! function stays observably pure. (Built in `effects/vars.rs`.)

use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use super::ast::{
    BigInt, Constraint, Core, Decl, EffOp, EffectDecl, Expr, Fip, InstanceDecl, IntLit, Param,
    Pattern, Phase, Program, Spanned, Suffix, Ty, S,
};
use crate::error::TypeError;
use crate::fresh::Fresh;
use crate::names;

mod aliases;
mod derive;
mod effects;
mod sugar;
mod synonyms;

use aliases::expand_aliases;
use derive::derive_instances;
use effects::{rw, Binding, Vars};
use synonyms::expand_synonyms;

pub use sugar::{
    dot_call, interp_lit, let_pat, let_stmt, open_if, pattern_decl, seq_stmt, try_mark, with_rest,
    with_stmt, IfTail,
};

// Per-op record: owning effect name, that effect's type parameters, signature.
pub(super) type OpSig = (String, Vec<String>, EffOp);

// Per-pattern record: declared arity and whether a `make` clause exists.
pub(super) type PatMap = BTreeMap<String, (usize, bool)>;

// Per-fn record: each parameter's name and capture-free default, in order. The
// call rewrite consults it to resolve named arguments and fill omitted defaults.
pub(super) type FnSig = Vec<(String, Option<S<Expr>>)>;

pub(super) struct Cx {
    pub(super) next: Fresh,
    pub(super) ctors: BTreeSet<String>,
    pub(super) effects: Vec<EffectDecl>,
    pub(super) op_sigs: BTreeMap<String, OpSig>,
    pub(super) errors: BTreeSet<String>,
    pub(super) patterns: PatMap,
    pub(super) fn_sigs: BTreeMap<String, FnSig>,
}

// Hygienic return-type var for a throw op: never resumes, so the checker
// instantiates it fresh at each throw site.
const THROW_RET: &str = "a@throw";

// `fail()` is the anonymous twin of an `error`: a builtin one-op effect always
// in scope, so any expression can short-circuit and the row tracks it. Reusing
// THROW_RET makes the checker instantiate its return fresh per site and restrict
// it to `final ctl`, exactly the throw path.
fn inject_fail(prog: &mut Program) {
    prog.effects.push(EffectDecl {
        name: names::FAIL_EFFECT.into(),
        params: Vec::new(),
        ops: vec![EffOp {
            name: names::FAIL_OP.into(),
            params: Vec::new(),
            ret: Ty::Var(THROW_RET.into()),
        }],
        span: Span::empty(0),
    });
}

// `error Name(T, ..)` is a one-op effect whose op never resumes.
fn lower_errors(prog: &mut Program) -> BTreeSet<String> {
    let mut names_out = BTreeSet::new();
    for e in std::mem::take(&mut prog.errors) {
        names_out.insert(e.name.clone());
        prog.effects.push(EffectDecl {
            name: e.name.clone(),
            params: Vec::new(),
            ops: vec![EffOp {
                name: names::throw_op(&e.name),
                params: e.params,
                ret: Ty::Var(THROW_RET.into()),
            }],
            span: e.span,
        });
    }
    names_out
}

// A `pattern` declaration lowers to hidden top-level functions (`view@P`,
// `make@P`); the map drives the match and call rewrites below.
fn lower_patterns(prog: &mut Program, ctors: &BTreeSet<String>) -> Result<PatMap, TypeError> {
    let mut out = PatMap::new();
    for p in std::mem::take(&mut prog.patterns) {
        if ctors.contains(&p.name) {
            return Err(TypeError::Other {
                span: p.span,
                msg: format!(
                    "pattern `{}` clashes with a constructor of the same name",
                    p.name
                ),
            });
        }
        // `for` names a concrete type (a monomorphic view from a lambda) or a
        // single-param class (a view dispatched through a class method, so one
        // pattern deconstructs every instance type). In the class form the view
        // clause names the method, whose signature fully types the synthesized
        // view; a `make` would need a construction method, so it is rejected.
        let mut make_ret = None;
        let view = if let Some(cl) = prog.classes.iter().find(|c| c.name == p.for_ty) {
            if p.make.is_some() {
                return Err(TypeError::Other {
                    span: p.span,
                    msg: format!(
                        "class-dispatched pattern `{}` cannot have a `make` clause",
                        p.name
                    ),
                });
            }
            let Expr::Var(method) = &p.view.node else {
                return Err(TypeError::Other {
                    span: p.view.span,
                    msg: format!(
                        "class-dispatched pattern `{}` view must name a method of `{}`",
                        p.name, p.for_ty
                    ),
                });
            };
            let Some((_, mty)) = cl.methods.iter().find(|(n, _)| n == method) else {
                return Err(TypeError::Other {
                    span: p.view.span,
                    msg: format!("`{method}` is not a method of class `{}`", p.for_ty),
                });
            };
            let fun = match mty {
                Ty::Forall(_, b) => b.as_ref(),
                t => t,
            };
            let Ty::Fun(ps, _, ret) = fun else {
                return Err(TypeError::Other {
                    span: p.view.span,
                    msg: format!("view method `{method}` must be a one-argument function"),
                });
            };
            if ps.len() != 1 {
                return Err(TypeError::Other {
                    span: p.view.span,
                    msg: format!("view method `{method}` must take exactly one argument"),
                });
            }
            let tv = Ty::Var(cl.param.clone());
            let ret_ty = ret.as_ref().clone();
            let body = call(evar(method, p.span), vec![evar("_x", p.span)], p.span);
            let mut d = lift_lam(names::pat_view(&p.name), lam1("_x", body, p.span), p.span);
            d.params[0].ty = Some(tv.clone());
            d.ret = Some(ret_ty);
            d.constraints = vec![Constraint {
                class: p.for_ty.clone(),
                ty: tv,
                span: p.span,
            }];
            d
        } else if let Some(data) = prog.types.iter().find(|d| d.name == p.for_ty) {
            let fty = Ty::Con(
                p.for_ty.clone(),
                data.params.iter().cloned().map(Ty::Var).collect(),
            );
            make_ret = Some(fty.clone());
            let mut d = lift_lam(names::pat_view(&p.name), p.view.clone(), p.span);
            d.params[0].ty = Some(fty);
            d
        } else {
            return Err(TypeError::Other {
                span: p.span,
                msg: format!(
                    "pattern `{}` is for undeclared type or class `{}`",
                    p.name, p.for_ty
                ),
            });
        };
        if out
            .insert(p.name.clone(), (p.params.len(), p.make.is_some()))
            .is_some()
        {
            return Err(TypeError::Other {
                span: p.span,
                msg: format!("pattern `{}` is declared more than once", p.name),
            });
        }
        // Splice both fns at the first fn declared after this pattern, so source
        // order is preserved across several patterns (each inserted fn carries
        // the pattern's own span, so a later pattern lands after them). Inserting
        // make then view at the same index leaves [view, make]; the order between
        // a pattern's own two fns is irrelevant, since they resolve by name.
        let at = prog
            .fns
            .iter()
            .position(|d| d.span.start > p.span.start)
            .unwrap_or(prog.fns.len());
        if let Some(mk) = p.make {
            let mut d = lift_lam(names::pat_make(&p.name), mk, p.span);
            d.ret = make_ret;
            prog.fns.insert(at, d);
        }
        prog.fns.insert(at, view);
    }
    Ok(out)
}

// Fold a function's trailing `where` bindings into nested `let`s around its
// body. Bindings are let*-scoped: the first is outermost, so each sees those
// before it (non-recursive, matching the language's plain `let`).
fn fold_wheres(d: &mut Decl) {
    if d.wheres.is_empty() {
        return;
    }
    let span = d.body.span;
    let body = std::mem::replace(
        &mut d.body,
        Spanned {
            synth: false,
            node: Expr::Unit,
            span,
        },
    );
    d.body = std::mem::take(&mut d.wheres)
        .into_iter()
        .rev()
        .fold(body, |acc, (n, v)| Spanned {
            synth: false,
            node: Expr::Let(n, Box::new(v), Box::new(acc)),
            span,
        });
}

fn lift_lam(name: String, lam: S<Expr>, span: Span) -> Decl {
    let Expr::Lam(params, body) = lam.node else {
        unreachable!("ICE: pattern clause is not a lambda")
    };
    Decl {
        name,
        params,
        ret: None,
        eff: None,
        constraints: Vec::new(),
        body: *body,
        wheres: Vec::new(),
        konst: false,
        fip: Fip::No,
        span,
    }
}

// A later definition replaces an earlier one of the same name, so user
// functions shadow the prelude. Matches the interpreter's env semantics and
// keeps codegen from emitting the dead earlier copy.
fn shadow_fns(prog: &mut Program) {
    let mut seen = BTreeSet::new();
    let mut kept: Vec<Decl> = prog
        .fns
        .drain(..)
        .rev()
        .filter(|d| seen.insert(d.name.clone()))
        .collect();
    kept.reverse();
    prog.fns = kept;
}

// Ops dispatch globally by name, so a redeclared effect or op would silently
// shadow an earlier one (including the prelude's Emit). Reject it up front.
fn check_effect_dups(prog: &Program) -> Result<(), TypeError> {
    let mut effs = BTreeSet::new();
    let mut ops: BTreeMap<&str, &str> = BTreeMap::new();
    for e in &prog.effects {
        if !effs.insert(e.name.as_str()) {
            return Err(TypeError::Other {
                span: e.span,
                msg: format!("effect `{}` is declared more than once", e.name),
            });
        }
        for op in &e.ops {
            if let Some(prev) = ops.insert(&op.name, &e.name) {
                return Err(TypeError::Other {
                    span: e.span,
                    msg: format!(
                        "operation `{}` is declared in both `{prev}` and `{}`",
                        op.name, e.name
                    ),
                });
            }
        }
    }
    Ok(())
}

/// # Errors
/// Fails on malformed sugar, reported as a type error.
pub fn desugar(mut prog: Program) -> Result<Program<Core>, TypeError> {
    shadow_fns(&mut prog);
    inject_fail(&mut prog);
    check_effect_dups(&prog)?;
    let errors = lower_errors(&mut prog);
    expand_synonyms(&mut prog)?;
    expand_aliases(&mut prog)?;
    derive_instances(&mut prog)?;
    let ctors: BTreeSet<String> = prog
        .types
        .iter()
        .flat_map(|d| d.ctors.iter().map(|c| c.name.clone()))
        .collect();
    let patterns = lower_patterns(&mut prog, &ctors)?;
    let op_sigs = prog
        .effects
        .iter()
        .flat_map(|e| {
            e.ops.iter().map(|op| {
                (
                    op.name.clone(),
                    (e.name.clone(), e.params.clone(), op.clone()),
                )
            })
        })
        .collect();
    let fn_sigs = prog
        .fns
        .iter()
        .map(|d| {
            let ps = d
                .params
                .iter()
                .map(|p| (p.name.clone(), p.default.clone()))
                .collect();
            (d.name.clone(), ps)
        })
        .collect();
    let mut cx = Cx {
        next: Fresh::new(),
        ctors,
        effects: Vec::new(),
        op_sigs,
        errors,
        patterns,
        fn_sigs,
    };
    let mut fns = Vec::with_capacity(prog.fns.len());
    for mut d in std::mem::take(&mut prog.fns) {
        fold_wheres(&mut d);
        fns.push(core_decl(d, &mut cx)?);
    }
    let mut instances = Vec::with_capacity(prog.instances.len());
    for i in prog.instances {
        let mut methods = Vec::with_capacity(i.methods.len());
        for mut m in i.methods {
            fold_wheres(&mut m);
            methods.push(core_decl(m, &mut cx)?);
        }
        instances.push(InstanceDecl {
            name: i.name,
            class: i.class,
            head: i.head,
            context: i.context,
            methods,
            span: i.span,
        });
    }
    prog.effects.append(&mut cx.effects);
    Ok(Program {
        types: prog.types,
        effects: prog.effects,
        errors: prog.errors,
        aliases: prog.aliases,
        synonyms: prog.synonyms,
        classes: prog.classes,
        instances,
        patterns: Vec::new(),
        fns,
        imports: prog.imports,
        exports: prog.exports,
        opaques: prog.opaques,
    })
}

// Rewrite a surface `Decl` into a core one: its body loses all sugar via `rw`,
// `where`s are already folded, and parameter defaults (consumed by the call
// rewrite) drop, so no surface expression survives.
fn core_decl(d: Decl, cx: &mut Cx) -> Result<Decl<Core>, TypeError> {
    let body = rw(&d.body, &seed(&d.params), cx)?;
    let params = d
        .params
        .into_iter()
        .map(|p| Param {
            name: p.name,
            ty: p.ty,
            borrow: p.borrow,
            default: None,
        })
        .collect();
    Ok(Decl {
        name: d.name,
        params,
        ret: d.ret,
        eff: d.eff,
        constraints: d.constraints,
        body,
        wheres: Vec::new(),
        konst: d.konst,
        fip: d.fip,
        span: d.span,
    })
}

/// # Errors
/// Fails on malformed sugar, reported as a type error.
pub fn desugar_expr(e: &S<Expr>) -> Result<S<Expr<Core>>, TypeError> {
    let mut cx = Cx {
        next: Fresh::new(),
        ctors: BTreeSet::new(),
        effects: Vec::new(),
        op_sigs: BTreeMap::new(),
        errors: BTreeSet::new(),
        patterns: PatMap::new(),
        fn_sigs: BTreeMap::new(),
    };
    rw(e, &Vars::new(), &mut cx)
}

// A function body's initial scope: its parameters, so a call of a global fn
// they shadow bypasses the named/default-argument rewrite.
fn seed(params: &[Param]) -> Vars {
    params
        .iter()
        .map(|p| (p.name.clone(), Binding::Local))
        .collect()
}

pub(super) const fn spat(node: Pattern, span: Span) -> S<Pattern> {
    Spanned {
        synth: false,
        node,
        span,
    }
}

pub(super) fn eint<P: Phase>(i: usize, span: Span) -> S<Expr<P>> {
    sp(
        Expr::Int(IntLit {
            value: BigInt::from(i),
            suffix: Suffix::None,
        }),
        span,
    )
}

pub(super) const fn sp<P: Phase>(node: Expr<P>, span: Span) -> S<Expr<P>> {
    Spanned {
        synth: false,
        node,
        span,
    }
}

// Sugar nodes the formatter restores to surface syntax (pattern lets, `?`).
pub(super) const fn sp_sugar(node: Expr, span: Span) -> S<Expr> {
    Spanned {
        synth: true,
        node,
        span,
    }
}

pub(super) fn evar<P: Phase>(name: &str, span: Span) -> S<Expr<P>> {
    sp(Expr::Var(name.into()), span)
}

pub(super) fn call<P: Phase>(f: S<Expr<P>>, args: Vec<S<Expr<P>>>, span: Span) -> S<Expr<P>> {
    sp(Expr::Call(Box::new(f), args), span)
}

pub(super) fn lam1<P: Phase>(p: &str, body: S<Expr<P>>, span: Span) -> S<Expr<P>> {
    let param = Param {
        name: p.into(),
        ty: None,
        borrow: false,
        default: None,
    };
    sp(Expr::Lam(vec![param], Box::new(body)), span)
}
