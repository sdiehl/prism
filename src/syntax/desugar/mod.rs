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
    NodeId, Param, Pattern, Phase, Program, Row, Spanned, Suffix, Total, Ty, S,
};
use crate::error::{ErrKind, TypeError};
use crate::kw;
use crate::names;
use crate::types::coeffect::CoeffectFact;
use crate::util::fresh::Fresh;

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
pub(crate) use stable::{family_lock, routes_to_current, stable_rung_digests};
use synonyms::expand_synonyms;

pub use sugar::{
    assign_stmt, build_stable, compound_assign, compound_stmt, decl_mods, dot_call, dot_op_removed,
    grade_word_msg, interp_lit, let_pat, let_stmt, lift_noalloc, mig_dir, open_if, pattern_decl,
    seq_stmt, try_mark, with_rest, with_stmt, IfTail, StableItem, DECLINE_DIM_ARITH, FLIP_CLASS,
    FLIP_EFFECT, FLIP_INSTANCE, GRADE_MANY_CLAUSE, MIGRATE_RESUME, MIGRATE_RET_ORDER,
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
}

// Hygienic return-type var for a throw op: never resumes, so the checker
// instantiates it fresh at each throw site.
const THROW_RET: &str = "a@throw";

// A one-op effect whose op never resumes (its result is the freshened-per-site
// THROW_RET var pinned to `never`). `fail`, `break`/`continue`, and every
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
            // handler to `never`, so grade Zero states the same fact.
            grade: Grade::Never,
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
// checker instantiates the op's result fresh per site and pins it to `never`.
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
    // restricted to `never` per site.
    prog.effects.push(EffectDecl {
        name: names::RETURN_EFFECT.into(),
        params: vec![names::RETURN_VAL.into()],
        ops: vec![EffOp {
            name: names::RETURN_OP.into(),
            params: vec![Ty::Var(names::RETURN_VAL.into())],
            ret: Ty::Var(THROW_RET.into()),
            grade: Grade::Never,
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
            return Err(ErrKind::PatternClashesCtor {
                name: p.name.clone(),
            }
            .at(p.span));
        }
        // `for` names a concrete type (a monomorphic view from a lambda) or a
        // single-param class (a view dispatched through a class method, so one
        // pattern deconstructs every instance type). In the class form the view
        // clause names the method, whose signature fully types the synthesized
        // view; a `make` would need a construction method, so it is rejected.
        let mut make_ret = None;
        let view = if let Some(cl) = prog.classes.iter().find(|c| c.name == p.for_ty) {
            if p.make.is_some() {
                return Err(ErrKind::ClassPatternHasMake {
                    name: p.name.clone(),
                }
                .at(p.span));
            }
            let Expr::Var(method) = &p.view.node else {
                return Err(ErrKind::ClassPatternViewNotMethod {
                    name: p.name.clone(),
                    class: p.for_ty.clone(),
                }
                .at(p.view.span));
            };
            let Some((_, mty)) = cl.methods.iter().find(|(n, _)| n == method) else {
                return Err(ErrKind::PatternViewUnknownMethod {
                    method: method.clone(),
                    class: p.for_ty.clone(),
                }
                .at(p.view.span));
            };
            let fun = match mty {
                Ty::Forall(_, b) => b.as_ref(),
                t => t,
            };
            let Ty::Fun(ps, _, ret) = fun else {
                return Err(ErrKind::ViewMethodNotFunction {
                    method: method.clone(),
                }
                .at(p.view.span));
            };
            if ps.len() != 1 {
                return Err(ErrKind::ViewMethodArity {
                    method: method.clone(),
                }
                .at(p.view.span));
            }
            let tv = Ty::Var(cl.param.clone());
            let ret_ty = ret.as_ref().clone();
            let body = call(evar(method, p.span), vec![evar("_x", p.span)], p.span);
            let mut d = lift_lam(
                names::pat_view(&p.name),
                lam1("_x", body, p.span),
                p.span,
                kw::VIEW,
                &p.name,
            )?;
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
            let mut d = lift_lam(
                names::pat_view(&p.name),
                p.view.clone(),
                p.span,
                kw::VIEW,
                &p.name,
            )?;
            d.params[0].ty = Some(fty);
            d
        } else {
            return Err(ErrKind::PatternForUnknownType {
                name: p.name.clone(),
                ty: p.for_ty.clone(),
            }
            .at(p.span));
        };
        if out
            .insert(p.name.clone(), (p.params.len(), p.make.is_some()))
            .is_some()
        {
            return Err(ErrKind::DuplicateDecl {
                kind: "pattern".into(),
                name: p.name.clone(),
            }
            .at(p.span));
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
            let mut d = lift_lam(names::pat_make(&p.name), mk, p.span, kw::MAKE, &p.name)?;
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
    // Zero-width `let` wrappers: the original body alone keeps its span (and
    // therefore its tooltip); each `where` binding's expression keeps its own
    // honest parsed span.
    let anchor = Span::empty(span.start);
    let body = std::mem::replace(&mut d.body, sp(Expr::Unit, span));
    d.body = std::mem::take(&mut d.wheres)
        .into_iter()
        .rev()
        .fold(body, |acc, (n, v)| {
            sp(Expr::Let(n, Box::new(v), Box::new(acc)), anchor)
        });
}

// Lower a pattern clause body into a hidden top-level function. A `view`/`make`
// clause must be written as a lambda (`view` takes the scrutinee, `make` one
// argument per pattern parameter); a bare expression (e.g. a plain function
// reference) has no parameters to bind and is rejected with a pointed error
// rather than reaching the constructor blindly.
fn lift_lam(
    name: String,
    lam: S<Expr>,
    span: Span,
    clause: &str,
    pat: &str,
) -> Result<Decl, TypeError> {
    let clause_span = lam.span;
    let Expr::Lam(params, body) = lam.node else {
        return Err(ErrKind::PatternClauseNotLambda {
            clause: clause.to_string(),
            pat: pat.to_string(),
        }
        .at(clause_span));
    };
    Ok(Decl {
        name,
        params,
        ret: None,
        eff: None,
        eff_tail: None,
        constraints: Vec::new(),
        body: *body,
        wheres: Vec::new(),
        requires: Vec::new(),
        ensures: Vec::new(),
        decreases: None,
        konst: false,
        test: false,
        total: Total::No,
        fip: Fip::No,
        replayable: false,
        no_alloc: false,
        span,
    })
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
        if let Some((_, reason)) = crate::names::RESERVED_SEAM_EFFECTS
            .iter()
            .find(|(n, _)| *n == e.name)
        {
            return Err(ErrKind::ReservedEffectName {
                name: e.name.clone(),
                reason: (*reason).to_string(),
            }
            .at(e.span));
        }
        if !effs.insert(e.name.as_str()) {
            return Err(ErrKind::DuplicateDecl {
                kind: "effect".into(),
                name: e.name.clone(),
            }
            .at(e.span));
        }
        for op in &e.ops {
            if let Some(prev) = ops.insert(&op.name, &e.name) {
                return Err(ErrKind::DuplicateEffectOp {
                    op: op.name.clone(),
                    first: prev.to_string(),
                    second: e.name.clone(),
                }
                .at(e.span));
            }
        }
    }
    Ok(())
}

// Reject any usage row that survives in a type. One walk over every surface
// position that carries a `Ty` (fn signatures, class methods, instance heads,
// contexts and methods, data constructors, effect operations, synonyms, and
// aliases), one diagnostic shape, so no reserved fact can acquire a meaning by
// slipping through a position this pass does not visit.
fn reject_coeffect_tys(prog: &Program) -> Result<(), TypeError> {
    fn check(t: &Ty, span: Span) -> Result<(), TypeError> {
        if let Ty::Coeffect(inner, row) = t {
            // An unwired fact is always the reserved-fact error.
            if let Some(f) = row.first_unwired() {
                return Err(ErrKind::CoeffectFactUnimplemented {
                    fact: f.to_string(),
                }
                .at(span));
            }
            // A wired closure-usage row (`@ once` / `@ portable`) on a function type
            // is a valid contract; it flows to the type checker. Anything else is
            // misplaced: `@ noalloc` was lifted at the fn root, `@ noescape` is
            // admitted only on a function domain (below), and a usage row on a
            // non-function type has no closure boundary to constrain.
            if row.is_closure_contract() && matches!(**inner, Ty::Fun(..)) {
                return check(inner, span);
            }
            return Err(ErrKind::CoeffectRowMisplaced.at(span));
        }
        // A function type's domain may carry the scoped-token contract
        // (`(Builder @ noescape) -> a`): the callback promises that argument does
        // not outlive the call. Admitted here, positionally, and nowhere else;
        // the manual walk mirrors `each_child` for `Fun` (domains, row label
        // arguments, return) so no position is skipped.
        if let Ty::Fun(doms, row, ret) = t {
            for d in doms {
                match d {
                    Ty::Coeffect(inner, drow)
                        if drow.first_unwired().is_none() && drow.is_noescape_only() =>
                    {
                        check(inner, span)?;
                    }
                    other => check(other, span)?,
                }
            }
            if let Row::Cons(labels, _) = row {
                for l in labels {
                    for a in &l.args {
                        check(a, span)?;
                    }
                }
            }
            return check(ret, span);
        }
        let mut out = Ok(());
        t.each_child(&mut |c| {
            if out.is_ok() {
                out = check(c, span);
            }
        });
        out
    }
    let check_decl = |d: &Decl| -> Result<(), TypeError> {
        for p in &d.params {
            if let Some(t) = &p.ty {
                check(t, d.span)?;
            }
        }
        if let Some(t) = &d.ret {
            check(t, d.span)?;
        }
        Ok(())
    };
    for d in &prog.fns {
        check_decl(d)?;
    }
    for c in &prog.classes {
        for (_, t) in &c.methods {
            check(t, c.span)?;
        }
    }
    for i in &prog.instances {
        check(&i.head, i.span)?;
        for c in &i.context {
            check(&c.ty, i.span)?;
        }
        for m in &i.methods {
            check_decl(m)?;
        }
    }
    for ty in &prog.types {
        for c in &ty.ctors {
            for a in &c.args {
                check(a, ty.span)?;
            }
            if let Some(fs) = &c.fields {
                for (_, ft) in fs {
                    check(ft, ty.span)?;
                }
            }
        }
    }
    for e in &prog.effects {
        for op in &e.ops {
            for p in &op.params {
                check(p, e.span)?;
            }
            check(&op.ret, e.span)?;
        }
    }
    for s in &prog.synonyms {
        check(&s.ty, s.span)?;
    }
    for a in &prog.aliases {
        for label in &a.labels {
            for arg in &label.args {
                check(arg, a.span)?;
            }
        }
    }
    Ok(())
}

// A parameter annotated `((..) -> ..) @ once`: a usage row carrying `once` on a
// function type.
fn is_once_param(p: &Param) -> bool {
    matches!(&p.ty, Some(Ty::Coeffect(inner, row))
        if matches!(**inner, Ty::Fun(..)) && row.multiplicity() == Some(CoeffectFact::Once))
}

// Enforce the `@ once` linearity contract on closure parameters: each is used at
// most once in the body, and only directly (as a call head `g(x)` or a direct
// argument `h(g)`). Aliasing (`let x = g`), capture under a lambda, or any other
// occurrence forces the `many` verdict, since the number of uses is then
// unbounded. Branches take the max (only one runs); sequenced positions sum. This
// complements the type checker's contravariant subsumption, which catches handing
// a `@ once` closure to a `@ many` context; here we catch the direct reuse the
// types alone would let through.
fn check_once_linearity(prog: &Program) -> Result<(), TypeError> {
    for d in &prog.fns {
        for p in &d.params {
            if is_once_param(p) && once_uses(&d.body, &p.name) > 1 {
                return Err(ErrKind::OnceUsedMoreThanOnce {
                    fn_name: d.name.clone(),
                    param: p.name.clone(),
                }
                .at(d.span));
            }
        }
    }
    Ok(())
}

// Uses of `name` in `e`, clamped to the once lattice (0, 1, or 2 meaning "more
// than once or unbounded"). A use is `name` appearing as a call head or a direct
// argument; any other occurrence returns 2 (an escape). Sequenced positions sum
// (clamped), branches take the max.
fn once_uses(e: &S<Expr>, name: &str) -> usize {
    let cap = |n: usize| n.min(2);
    match &e.node {
        // A bare occurrence not consumed as a call head or direct argument below:
        // aliased, captured, returned, or otherwise escaping.
        Expr::Var(n) if n == name => 2,
        Expr::Call(f, args) => {
            let mut total = match &f.node {
                Expr::Var(n) if n == name => 1,
                _ => once_uses(f, name),
            };
            for a in args {
                let u = match &a.node {
                    Expr::Var(n) if n == name => 1,
                    _ => once_uses(a, name),
                };
                total = cap(total + u);
            }
            total
        }
        // A lambda body may run any number of times, so capturing `name` escapes.
        // A parameter that shadows `name` rebinds it: the body's occurrences are a
        // different variable and do not count.
        Expr::Lam(params, b) => {
            if params.iter().any(|p| p.name == name) {
                0
            } else {
                usize::from(once_uses(b, name) > 0) * 2
            }
        }
        Expr::If(c, t, el) => cap(once_uses(c, name) + once_uses(t, name).max(once_uses(el, name))),
        // The bound value is in the outer scope; the body sees `name` only when the
        // let binder does not shadow it.
        Expr::Let(binder, v, b) => {
            let body = if binder.as_str() == name {
                0
            } else {
                once_uses(b, name)
            };
            cap(once_uses(v, name) + body)
        }
        Expr::Match(s, arms) => {
            let branch = arms
                .iter()
                .map(|a| {
                    let mut binds = Vec::new();
                    pat_binds(&a.pat, &mut binds);
                    if binds.iter().any(|b| b == name) {
                        // The arm pattern rebinds `name`; guard and body refer to
                        // the fresh binding.
                        0
                    } else {
                        cap(a.guard.as_ref().map_or(0, |g| once_uses(g, name))
                            + once_uses(&a.body, name))
                    }
                })
                .max()
                .unwrap_or(0);
            cap(once_uses(s, name) + branch)
        }
        _ => {
            let mut total = 0;
            e.node
                .each_child(&mut |c| total = cap(total + once_uses(c, name)));
            total
        }
    }
}

// A parameter annotated `((..) -> ..) @ portable`.
fn is_portable_param(p: &Param) -> bool {
    matches!(&p.ty, Some(Ty::Coeffect(inner, row)) if matches!(**inner, Ty::Fun(..)) && row.is_portable())
}

// A written type whose values are portable (encodable) by construction: the
// scalars and tuples/datatype spines over them. The AST dual of
// `kont::portable_value_type`; a captured value of such a type may cross a
// `@ portable` boundary.
fn is_portable_annotation(t: &Ty) -> bool {
    match t {
        Ty::Int | Ty::I64 | Ty::U64 | Ty::Bool | Ty::Unit | Ty::Float | Ty::Char | Ty::Str => true,
        Ty::Tuple(ts) | Ty::Con(_, ts) => ts.iter().all(is_portable_annotation),
        _ => false,
    }
}

// Collect every free variable of `e` (occurrences not bound by an enclosing
// lambda, `let`, or match arm). Conservative around surface sugar: a form this
// does not special-case recurses through `each_child` with the current binder
// scope, so a name it cannot prove bound is reported free (a false capture only
// costs a diagnostic).
fn free_names(e: &S<Expr>, bound: &mut Vec<String>, out: &mut BTreeSet<String>) {
    match &e.node {
        Expr::Var(n) => {
            if !bound.contains(n) {
                out.insert(n.clone());
            }
        }
        Expr::Lam(params, body) => {
            let base = bound.len();
            bound.extend(params.iter().map(|p| p.name.clone()));
            free_names(body, bound, out);
            bound.truncate(base);
        }
        Expr::Let(name, v, b) => {
            free_names(v, bound, out);
            bound.push(name.clone());
            free_names(b, bound, out);
            bound.pop();
        }
        Expr::Match(scrut, arms) => {
            free_names(scrut, bound, out);
            for a in arms {
                let base = bound.len();
                pat_binds(&a.pat, bound);
                if let Some(g) = &a.guard {
                    free_names(g, bound, out);
                }
                free_names(&a.body, bound, out);
                bound.truncate(base);
            }
        }
        _ => e.node.each_child(&mut |c| free_names(c, bound, out)),
    }
}

// The names a pattern binds, appended to `out`.
fn pat_binds(p: &S<Pattern>, out: &mut Vec<String>) {
    match &p.node {
        Pattern::Var(n) => out.push(n.clone()),
        Pattern::Ctor(_, subs) | Pattern::Tuple(subs) => {
            for s in subs {
                pat_binds(s, out);
            }
        }
        Pattern::Record(_, fields, _) => {
            for (_, s) in fields {
                pat_binds(s, out);
            }
        }
        _ => {}
    }
}

// Enforce the `@ portable` mobility contract: a closure passed to a `@ portable`
// parameter may capture only names that travel to a fresh runtime: a top-level
// function or constructor (a content-addressed code reference), another
// `@ portable` parameter of the enclosing function (a relay), or a
// portable-typed parameter (scalar data). Any other captured free variable (a
// local closure, a `var` cell, a handler op, a nonportable value) is rejected.
// A scalar bound by a local `let` is excluded because this check admits only
// facts available directly from the enclosing function's signature.
fn check_portable_captures(prog: &Program) -> Result<(), TypeError> {
    let portable_params: BTreeMap<&str, Vec<usize>> = prog
        .fns
        .iter()
        .filter_map(|d| {
            let idxs: Vec<usize> = d
                .params
                .iter()
                .enumerate()
                .filter(|(_, p)| is_portable_param(p))
                .map(|(i, _)| i)
                .collect();
            (!idxs.is_empty()).then_some((d.name.as_str(), idxs))
        })
        .collect();
    if portable_params.is_empty() {
        return Ok(());
    }
    let mut code_names: BTreeSet<&str> = prog.fns.iter().map(|d| d.name.as_str()).collect();
    for t in &prog.types {
        for c in &t.ctors {
            code_names.insert(c.name.as_str());
        }
    }
    for d in &prog.fns {
        let ok: BTreeSet<String> = d
            .params
            .iter()
            .filter(|p| is_portable_param(p) || p.ty.as_ref().is_some_and(is_portable_annotation))
            .map(|p| p.name.clone())
            .collect();
        check_portable_calls(&d.body, &portable_params, &code_names, &ok)?;
    }
    Ok(())
}

fn check_portable_calls(
    e: &S<Expr>,
    portable_params: &BTreeMap<&str, Vec<usize>>,
    code_names: &BTreeSet<&str>,
    ok: &BTreeSet<String>,
) -> Result<(), TypeError> {
    if let Expr::Call(f, args) = &e.node {
        if let Expr::Var(name) = &f.node {
            if let Some(idxs) = portable_params.get(name.as_str()) {
                for &i in idxs {
                    if let Some(arg) = args.get(i) {
                        check_arg_portable(arg, code_names, ok)?;
                    }
                }
            }
        }
    }
    let mut out = Ok(());
    e.node.each_child(&mut |c| {
        if out.is_ok() {
            out = check_portable_calls(c, portable_params, code_names, ok);
        }
    });
    out
}

// A single argument flowing into a `@ portable` parameter.
fn check_arg_portable(
    arg: &S<Expr>,
    code_names: &BTreeSet<&str>,
    ok: &BTreeSet<String>,
) -> Result<(), TypeError> {
    let bad = |subject: String| Err(ErrKind::PortableCapturesNonportable { subject }.at(arg.span));
    match &arg.node {
        Expr::Lam(params, body) => {
            let mut bound: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
            let mut free = BTreeSet::new();
            free_names(body, &mut bound, &mut free);
            for name in &free {
                if !code_names.contains(name.as_str()) && !ok.contains(name) {
                    return bad(name.clone());
                }
            }
            Ok(())
        }
        // A bare code reference or a relayed `@ portable` value is already portable.
        Expr::Var(g) if code_names.contains(g.as_str()) || ok.contains(g) => Ok(()),
        Expr::Var(g) => bad(g.clone()),
        _ => bad("a computed closure".into()),
    }
}

// The domain positions of a function-typed parameter that carry the scoped-token
// contract: `f : (Builder @ noescape) -> a` yields `[0]`. Phase-generic: the
// contract map is built from the desugared (Core-phase) declarations.
fn noescape_domains<P: Phase>(p: &Param<P>) -> Vec<usize> {
    let Some(Ty::Fun(doms, _, _)) = &p.ty else {
        return Vec::new();
    };
    doms.iter()
        .enumerate()
        .filter(|(_, d)| matches!(d, Ty::Coeffect(_, row) if row.is_noescape_only()))
        .map(|(j, _)| j)
        .collect()
}

// Enforce `@ noescape` on scoped-token callbacks: at every call handing a
// closure to a parameter typed `(T @ noescape) -> a`, the closure's token
// argument must not outlive the call. The value analysis (`token_escapes`)
// rejects the directly expressible escapes: the token returned as the result,
// embedded in returned data, aliased through a `let` that then flows out, or
// captured by another closure. Runs on the desugared (Core-phase) bodies, where
// statement sugar is gone, so value position is honest. The callback must be a
// closure literal, a top-level function, or a relayed parameter carrying the
// same contract; anything else cannot be checked and is rejected.
fn check_noescape_contracts(prog: &Program<Core>) -> Result<(), TypeError> {
    let mut contracts: BTreeMap<&str, Vec<(usize, usize)>> = BTreeMap::new();
    for d in &prog.fns {
        for (i, p) in d.params.iter().enumerate() {
            for j in noescape_domains(p) {
                contracts.entry(d.name.as_str()).or_default().push((i, j));
            }
        }
    }
    if contracts.is_empty() {
        return Ok(());
    }
    let ctors: BTreeSet<String> = prog
        .types
        .iter()
        .flat_map(|t| t.ctors.iter().map(|c| c.name.clone()))
        .collect();
    let fns: BTreeMap<&str, &Decl<Core>> = prog.fns.iter().map(|d| (d.name.as_str(), d)).collect();
    for d in &prog.fns {
        // Parameters of the enclosing function that carry the same contract at
        // the same position may be relayed onward unchecked here; their own call
        // sites are checked where a concrete closure is supplied.
        let relays: BTreeSet<(String, usize)> = d
            .params
            .iter()
            .flat_map(|p| noescape_domains(p).into_iter().map(|j| (p.name.clone(), j)))
            .collect();
        walk_noescape_calls(&d.body, &contracts, &ctors, &fns, &relays)?;
    }
    Ok(())
}

fn walk_noescape_calls(
    e: &S<Expr<Core>>,
    contracts: &BTreeMap<&str, Vec<(usize, usize)>>,
    ctors: &BTreeSet<String>,
    fns: &BTreeMap<&str, &Decl<Core>>,
    relays: &BTreeSet<(String, usize)>,
) -> Result<(), TypeError> {
    if let Expr::Call(h, args) = &e.node {
        if let Expr::Var(callee) = &h.node {
            if let Some(sites) = contracts.get(callee.as_str()) {
                for (i, j) in sites {
                    if let Some(arg) = args.get(*i) {
                        check_noescape_arg(arg, *j, callee, ctors, fns, relays)?;
                    }
                }
            }
        }
    }
    let mut out = Ok(());
    e.node.each_child(&mut |c| {
        if out.is_ok() {
            out = walk_noescape_calls(c, contracts, ctors, fns, relays);
        }
    });
    out
}

fn check_noescape_arg(
    arg: &S<Expr<Core>>,
    j: usize,
    callee: &str,
    ctors: &BTreeSet<String>,
    fns: &BTreeMap<&str, &Decl<Core>>,
    relays: &BTreeSet<(String, usize)>,
) -> Result<(), TypeError> {
    let escape = |token: &str, span: Span| {
        Err(ErrKind::NoescapeTokenEscapes {
            token: token.to_string(),
            callee: callee.to_string(),
        }
        .at(span))
    };
    match &arg.node {
        Expr::Lam(params, body) => {
            let Some(p) = params.get(j) else {
                return Ok(());
            };
            effects::token_escapes(body, &p.name, ctors, &mut BTreeSet::new())
                .map_or(Ok(()), |span| escape(&p.name, span))
        }
        // A top-level function as the callback: its own body is the closure body.
        Expr::Var(g) if fns.contains_key(g.as_str()) => {
            let d = fns[g.as_str()];
            let Some(p) = d.params.get(j) else {
                return Ok(());
            };
            effects::token_escapes(&d.body, &p.name, ctors, &mut BTreeSet::new())
                .map_or(Ok(()), |span| escape(&p.name, span))
        }
        // A relayed parameter carrying the same contract at the same position.
        Expr::Var(g) if relays.contains(&(g.clone(), j)) => Ok(()),
        _ => Err(ErrKind::NoescapeUncheckable {
            callee: callee.to_string(),
        }
        .at(arg.span)),
    }
}

/// # Errors
/// Fails on malformed sugar, reported as a type error.
pub fn desugar(prog: Program) -> Result<Program<Core>, TypeError> {
    desugar_with_scope(prog, &BTreeMap::new(), &BTreeMap::new())
}

/// Desugar with imported class and helper canonical names supplied by checked
/// dependency interfaces. This lets a module expand `deriving` without merging
/// dependency implementation ASTs into its body.
///
/// # Errors
/// Fails on malformed sugar, reported as a type error.
pub fn desugar_with_scope(
    mut prog: Program,
    external_classes: &BTreeMap<String, String>,
    external_values: &BTreeMap<String, String>,
) -> Result<Program<Core>, TypeError> {
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
    // Every usage row still inside a type is rejected here, before synonym and
    // alias expansion can copy one into other positions: the single wired fact
    // (`@ noalloc` at a `fn` return root) was lifted onto the decl flag at
    // parse, so anything left is a reserved fact or a misplaced certificate.
    reject_coeffect_tys(&prog)?;
    check_once_linearity(&prog)?;
    check_portable_captures(&prog)?;
    expand_synonyms(&mut prog)?;
    expand_aliases(&mut prog)?;
    derive_instances(&mut prog, external_classes, external_values)?;
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
        // Surface-only proof declarations: never lowered, dropped at `Core`.
        logic_fns: Vec::new(),
        imports: prog.imports,
        exports: prog.exports,
        opaques: prog.opaques,
        deprecated: prog.deprecated,
    };
    assign_ids(&mut out);
    check_noescape_contracts(&out)?;
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
// installs its own handler (`run_io(\() -> rng_rand())`) is left unwrapped. The
// wrapper names and the Replay/output names are single-sourced in `names`/
// `builtins`, and a drift guard test checks each to its prelude definition.
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
        eff_tail: d.eff_tail,
        constraints: d.constraints,
        body,
        wheres: Vec::new(),
        // Contracts and the `decreases` measure are surface-only proof data: they
        // carry no runtime meaning and are dropped here at the `Core` boundary, so
        // an edit touching only a `requires`/`ensures`/`decreases` clause leaves
        // executable Core byte-identical.
        requires: Vec::new(),
        ensures: Vec::new(),
        decreases: None,
        konst: d.konst,
        // Test membership survives to Core: the test lane's discovery reads it
        // off the checked program. Neutral because production mode strips test
        // declarations before desugar, and `test` never enters the Core hash.
        test: d.test,
        total: Total::No,
        fip: d.fip,
        replayable: d.replayable,
        no_alloc: d.no_alloc,
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
