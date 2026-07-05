//! Surface desugaring driver and shared constructors.
//!
//! `var x := e` becomes a per-var algebraic effect: reads are `get@x@n(())`,
//! writes are `set@x@n(e)`, and the block runs under a parameter-passing handler
//! applied to the initial value, so the effect is discharged and the enclosing
//! function stays observably pure. (Built in `effects/vars.rs`.)

use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use super::ast::{
    BigInt, Constraint, Core, Decl, EffOp, EffectDecl, Expr, Fip, Grade, InstanceDecl, IntLit,
    NodeId, Param, Pattern, Phase, Program, Spanned, Suffix, Ty, S,
};
use crate::error::TypeError;
use crate::fresh::Fresh;
use crate::names;

mod aliases;
mod derive;
mod effects;
mod ids;
mod stable;
mod sugar;
mod synonyms;

use aliases::expand_aliases;
use derive::derive_instances;
use effects::{rw, wrap_return, Binding, Vars};
use ids::assign_ids;
use stable::expand_stable;
pub(crate) use stable::stable_rung_digests;
use synonyms::expand_synonyms;

pub use sugar::{
    assign_stmt, build_stable, compound_assign, compound_stmt, dot_call, interp_lit, let_pat,
    let_stmt, open_if, pattern_decl, seq_stmt, try_mark, with_rest, with_stmt, IfTail, StableItem,
    DECLINE_DIM_ARITH, FLIP_CLASS, FLIP_EFFECT, FLIP_INSTANCE,
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
    // Per constructor: arity and field names (empty when positional). Drives the
    // `?Ctor` prism lowering, which rebuilds the constructor positionally.
    pub(super) ctor_shapes: BTreeMap<String, (usize, Vec<String>)>,
    // Per constructor: how many constructors its type has, so the prism `match`
    // drops its pass-through arm when the paths already cover every constructor.
    pub(super) ctor_total: BTreeMap<String, usize>,
    pub(super) effects: Vec<EffectDecl>,
    pub(super) op_sigs: BTreeMap<String, OpSig>,
    pub(super) errors: BTreeSet<String>,
    pub(super) patterns: PatMap,
    pub(super) fn_sigs: BTreeMap<String, FnSig>,
    // Synthetic top-level functions lifted out of `without alloc { .. }` blocks,
    // drained into the program's `fns` after every body is rewritten.
    pub(super) lifted: Vec<Decl<Core>>,
}

// Hygienic return-type var for a throw op: never resumes, so the checker
// instantiates it fresh at each throw site.
const THROW_RET: &str = "a@throw";

// A one-op effect whose op never resumes (its result is the freshened-per-site
// THROW_RET var pinned to `final ctl`). `fail`, `break`/`continue`, and every
// `error` are all this exact shape, differing only in name and op params.
fn throw_effect(name: String, op_name: String, op_params: Vec<Ty>, span: Span) -> EffectDecl {
    EffectDecl {
        name,
        params: Vec::new(),
        ops: vec![EffOp {
            name: op_name,
            params: op_params,
            ret: Ty::Var(THROW_RET.into()),
            // Never resumes: the poly-return restriction already forces every
            // handler to `final ctl`, so grade Zero states the same fact.
            grade: Grade::Zero,
        }],
        span,
    }
}

// `fail()` is the anonymous twin of an `error`: a builtin one-op effect always
// in scope, so any expression can short-circuit and the row tracks it.
fn inject_fail(prog: &mut Program) {
    prog.effects.push(throw_effect(
        names::FAIL_EFFECT.into(),
        names::FAIL_OP.into(),
        Vec::new(),
        Span::empty(0),
    ));
}

// `break` / `continue` desugar to non-resumable performs of these one-op effects,
// each discharged by a handler the loop desugar installs, so neither ever appears
// in a surfaced row. Always in scope (like `fail`), reusing THROW_RET so the
// checker instantiates the op's result fresh per site and pins it to `final ctl`.
fn inject_loop_effects(prog: &mut Program) {
    for (eff, op) in [
        (names::BREAK_EFFECT, names::BREAK_OP),
        (names::CONTINUE_EFFECT, names::CONTINUE_OP),
    ] {
        prog.effects.push(throw_effect(
            eff.into(),
            op.into(),
            Vec::new(),
            Span::empty(0),
        ));
    }
}

// `return e` desugars to a non-resumable perform of this one-op effect, caught by
// a handler the fn-body desugar wraps around a function that uses it. The op
// carries the value: a polymorphic param (instantiated to the function's result
// type at each `return`) and a never-resume result, so `return` type-checks in any
// position and the surfaced row stays clean.
fn inject_return_effect(prog: &mut Program) {
    // `Return(a)` is parametric in the carried value `a`: a handler picks one `a`
    // for its scope, so every `return` in the same function unifies its value with
    // that one type (the function's result type), exactly as `Emit(a)` ties a
    // stream's element type. The op result is the never-resume var, freshened and
    // restricted to `final ctl` per site.
    prog.effects.push(EffectDecl {
        name: names::RETURN_EFFECT.into(),
        params: vec![names::RETURN_VAL.into()],
        ops: vec![EffOp {
            name: names::RETURN_OP.into(),
            params: vec![Ty::Var(names::RETURN_VAL.into())],
            ret: Ty::Var(THROW_RET.into()),
            grade: Grade::Zero,
        }],
        span: Span::empty(0),
    });
}

// `error Name(T, ..)` is a one-op effect whose op never resumes.
fn lower_errors(prog: &mut Program) -> BTreeSet<String> {
    let mut names_out = BTreeSet::new();
    for e in std::mem::take(&mut prog.errors) {
        names_out.insert(e.name.clone());
        prog.effects.push(throw_effect(
            e.name.clone(),
            names::throw_op(&e.name),
            e.params,
            e.span,
        ));
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
    let body = std::mem::replace(&mut d.body, sp(Expr::Unit, span));
    d.body = std::mem::take(&mut d.wheres)
        .into_iter()
        .rev()
        .fold(body, |acc, (n, v)| {
            sp(Expr::Let(n, Box::new(v), Box::new(acc)), span)
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
        replayable: false,
        no_alloc: false,
        no_alloc_bs: false,
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
        if crate::names::RESERVED_SEAM_EFFECTS.contains(&e.name.as_str()) {
            return Err(TypeError::Other {
                span: e.span,
                msg: format!(
                    "effect `{}` is a reserved name (reserved for the concurrency preemption seam)",
                    e.name
                ),
            });
        }
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
    inject_loop_effects(&mut prog);
    inject_return_effect(&mut prog);
    // Lower errors first so their synthesized throw-effects and throw-ops take
    // part in the duplicate check: a repeated `error Foo`, an `error` colliding
    // with an `effect` of the same name, or a throw-op clashing with another
    // effect's op are all rejected here rather than silently overwriting.
    let errors = lower_errors(&mut prog);
    check_effect_dups(&prog)?;
    // Expand `stable` blocks into rung types, ladder functions, and synonyms
    // before deriving (the rungs derive their codecs) and synonym expansion (the
    // current-rung version tag is a synonym), and before the frozen goldens are
    // gated against the recomputed per-rung shape digests.
    expand_stable(&mut prog)?;
    expand_synonyms(&mut prog)?;
    expand_aliases(&mut prog)?;
    derive_instances(&mut prog)?;
    let ctors: BTreeSet<String> = prog
        .types
        .iter()
        .flat_map(|d| d.ctors.iter().map(|c| c.name.clone()))
        .collect();
    let ctor_shapes: BTreeMap<String, (usize, Vec<String>)> = prog
        .types
        .iter()
        .flat_map(|d| &d.ctors)
        .map(|c| {
            let fields = c
                .fields
                .as_ref()
                .map(|fs| fs.iter().map(|(n, _)| n.clone()).collect())
                .unwrap_or_default();
            (c.name.clone(), (c.args.len(), fields))
        })
        .collect();
    let ctor_total: BTreeMap<String, usize> = prog
        .types
        .iter()
        .flat_map(|d| d.ctors.iter().map(move |c| (c.name.clone(), d.ctors.len())))
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
        ctor_shapes,
        ctor_total,
        effects: Vec::new(),
        op_sigs,
        errors,
        patterns,
        fn_sigs,
        lifted: Vec::new(),
    };
    let mut fns = Vec::with_capacity(prog.fns.len());
    for mut d in std::mem::take(&mut prog.fns) {
        fold_wheres(&mut d);
        fns.push(core_decl(d, &mut cx)?);
    }
    wrap_main_world(&mut fns);
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
            module: i.module,
            span: i.span,
        });
    }
    prog.effects.append(&mut cx.effects);
    // Splice in the functions lifted from `without alloc { .. }` blocks (from both
    // top-level bodies and instance methods) as ordinary top-level definitions.
    fns.append(&mut cx.lifted);
    let mut out = Program {
        types: prog.types,
        effects: prog.effects,
        errors: prog.errors,
        aliases: prog.aliases,
        synonyms: prog.synonyms,
        classes: prog.classes,
        instances,
        // Consumed by `expand_stable` above into ordinary types/fns/instances.
        stable: Vec::new(),
        canonicals: prog.canonicals,
        patterns: Vec::new(),
        fns,
        imports: prog.imports,
        exports: prog.exports,
        opaques: prog.opaques,
        deprecated: prog.deprecated,
    };
    assign_ids(&mut out);
    Ok(out)
}

// Wrap `main` in the default world handler `run_io` so top-level capability IO
// works without the user installing a handler. Only applied when the program
// defines `run_io` (the prelude does) and `main` reaches a capability wrapper, so
// pure programs and the prelude-free corpus stay untouched and pay nothing.
// Wrapping only on demand also keeps the fused world handler clear of programs
// whose body reifies an inner handler, where a wrap-over-reified-handler would
// otherwise surface a backend divergence.
//
// The trigger is the surface wrappers (`names::CAP_WRAPPERS`), not the raw
// capability operations, so a program that performs a capability directly and
// installs its own handler (`run_io(\() -> rng_rand(()))`) is left unwrapped. The
// wrapper names and the Replay/output names are single-sourced in `names`/
// `builtins`, and a drift guard test pins each to its prelude definition.
fn wrap_main_world(fns: &mut [Decl<Core>]) {
    let names: BTreeSet<&str> = fns.iter().map(|d| d.name.as_str()).collect();
    if !names.contains(names::RUN_IO) || !names.contains(names::ENTRY_POINT) {
        return;
    }
    let mut edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for d in fns.iter() {
        edges.insert(d.name.clone(), effects::referenced_names(&d.body));
    }
    let mut reachable: BTreeSet<String> = BTreeSet::new();
    let mut queue = vec![names::ENTRY_POINT.to_string()];
    while let Some(n) = queue.pop() {
        if !reachable.insert(n.clone()) {
            continue;
        }
        if let Some(refs) = edges.get(&n) {
            queue.extend(refs.iter().filter(|r| names.contains(r.as_str())).cloned());
        }
    }
    let reaches_cap = names::CAP_WRAPPERS.iter().any(|w| reachable.contains(*w));
    // `print`/`println` route through `Output` only when the Replay machinery is
    // imported (see `elaborate`); only then does a printing `main` need the world
    // handler to discharge the output ops. Without it, output lowers directly and
    // wrapping a reified-handler body in `run_io` would diverge on the backend.
    let uses_replay = names::REPLAY_DRIVERS.iter().any(|f| names.contains(*f))
        || names::INCR_REPLAY_DRIVERS
            .iter()
            .any(|f| names.contains(*f));
    let reaches_output = uses_replay
        && reachable.iter().any(|n| {
            edges.get(n).is_some_and(|refs| {
                crate::core::builtins::OUTPUT_BUILTINS
                    .iter()
                    .any(|o| refs.contains(*o))
            })
        });
    if !reaches_cap && !reaches_output {
        return;
    }
    if let Some(d) = fns.iter_mut().find(|d| d.name == names::ENTRY_POINT) {
        let span = d.body.span;
        let body = std::mem::replace(&mut d.body, sp(Expr::Unit, span));
        let action = lam1(names::UNIT_ARG, body, span);
        d.body = call(evar(names::RUN_IO, span), vec![action], span);
    }
}

// Retarget the policy-neutral `run_cooperative` to a concrete scheduler chosen by
// the `--scheduler` flag. `run_cooperative(main) = run_async(main)` by definition;
// this rebuilds its body to forward to `target` instead, so a program calling
// `run_cooperative` follows the deployment's default without any source change.
// `run_async`/`run_lifo` callers are untouched: only this one entry is neutral. A
// no-op when the program does not import `Concurrent`.
pub fn retarget_cooperative(prog: &mut Program<Core>, target: &str) {
    if let Some(d) = prog
        .fns
        .iter_mut()
        .find(|d| d.name == names::RUN_COOPERATIVE)
    {
        let span = d.body.span;
        let args = d.params.iter().map(|p| evar(&p.name, span)).collect();
        d.body = call(evar(target, span), args, span);
    }
}

// Rewrite a surface `Decl` into a core one: its body loses all sugar via `rw`,
// `where`s are already folded, and parameter defaults (consumed by the call
// rewrite) drop, so no surface expression survives.
fn core_decl(d: Decl, cx: &mut Cx) -> Result<Decl<Core>, TypeError> {
    // A `return` in the body desugars to a perform discharged by a handler wrapped
    // here, at the function boundary, so the early exit cannot leak past the fn.
    let src = wrap_return(d.body, cx);
    let body = rw(&src, &seed(&d.params), cx)?;
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
        replayable: d.replayable,
        no_alloc: d.no_alloc,
        no_alloc_bs: d.no_alloc_bs,
        span: d.span,
    })
}

/// # Errors
/// Fails on malformed sugar, reported as a type error.
pub fn desugar_expr(e: &S<Expr>) -> Result<S<Expr<Core>>, TypeError> {
    let mut cx = Cx {
        next: Fresh::new(),
        ctors: BTreeSet::new(),
        ctor_shapes: BTreeMap::new(),
        ctor_total: BTreeMap::new(),
        effects: Vec::new(),
        op_sigs: BTreeMap::new(),
        errors: BTreeSet::new(),
        patterns: PatMap::new(),
        fn_sigs: BTreeMap::new(),
        lifted: Vec::new(),
    };
    let mut out = rw(e, &Vars::new(), &mut cx)?;
    ids::assign_expr_ids(&mut out);
    Ok(out)
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
        id: NodeId::DUMMY,
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
        id: NodeId::DUMMY,
        synth: false,
        node,
        span,
    }
}

// Sugar nodes the formatter restores to surface syntax (pattern lets, `?`).
pub(super) const fn sp_sugar(node: Expr, span: Span) -> S<Expr> {
    Spanned {
        id: NodeId::DUMMY,
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
