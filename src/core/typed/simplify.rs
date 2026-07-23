//! The gentle simplifier for typed Core: fixed-point local rewrites that
//! preserve every result/effect witness through each reduction.
//!
//! Mirrors [`super::super::opt::simplify::simplify_counted`] rule-for-rule:
//! case-of-known-constructor, trivial copy-propagation, dead-let elimination,
//! constant folding, used-once-thunk inlining, and bounded case-of-case. The
//! typed-specific difference is representation transparency: unlike legacy
//! Core, a [`TypedValueKind::Reinterpret`], [`TypedValueKind::LoweredRepr`], or
//! [`TypedValueKind::NewtypeRepr`] wrapper still surrounds its inner value at
//! this phase (it erases away only at [`TypedCore::erase`]). Every
//! classification decision below therefore looks through such a wrapper via
//! [`peel`] before deciding whether a value is known, trivial, or
//! pattern-matchable, while every rewrite still carries forward the original
//! (possibly wrapped) value unchanged.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::CoreOp;
use crate::error::TypedCoreSimplifyFailure;
use crate::sym::Sym;
use crate::types::ty::EffRow;

use super::specialize_support::{free_comp_vars, free_value_vars, Rewrite};
use super::verify::instantiate_value_scheme;
use super::{
    CompSig, TypedBinder, TypedComp, TypedCompKind, TypedCore, TypedHandleOp, TypedHandler,
    TypedPattern, TypedValue, TypedValueKind,
};

// A runaway guard: a correct fixed point converges far below this, so exceeding
// it means a rewrite is fighting itself. Matches the legacy bound exactly.
const MAX_TICKS: u64 = 5_000_000;

/// Rewrite counts for typed simplification.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct SimplifyStats {
    ticks: u64,
}

impl SimplifyStats {
    /// Total rewrites fired across every fixed-point round.
    pub(crate) const fn ticks(self) -> u64 {
        self.ticks
    }
}

/// Simplify typed Core to a fixed point, preserving every witness.
pub(crate) fn simplify<P>(
    core: TypedCore<P>,
) -> Result<(TypedCore<P>, SimplifyStats), TypedCoreSimplifyFailure> {
    let mut current = core;
    let mut total = 0u64;
    loop {
        let mut pass = Simplifier { ticks: 0 };
        current = pass.core(&current, &Env::new());
        total += pass.ticks;
        if total > MAX_TICKS {
            return Err(TypedCoreSimplifyFailure::RunawayRewrite { ticks: total });
        }
        if pass.ticks == 0 {
            break;
        }
    }
    Ok((current, SimplifyStats { ticks: total }))
}

// Maps a let binder to the value it is known to hold, for the region where
// that is still true.
type Env = BTreeMap<Sym, TypedValue>;

struct Simplifier {
    ticks: u64,
}

// Look through representation-only wrappers to classify the value they carry.
// Every caller keeps the original (wrapped) `TypedValue` for reconstruction;
// only classification consults the peeled shape.
fn peel(value: &TypedValue) -> &TypedValue {
    match &value.kind {
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr {
            value: inner,
            proof: _,
        }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => peel(inner),
        _ => value,
    }
}

// A value worth remembering for a binder: a constructor or tuple (enables
// case-of-known-constructor) or a trivial value (enables copy-propagation). A
// thunk is not tracked, since inlining it could duplicate work.
fn known(v: &TypedValue) -> bool {
    matches!(
        peel(v).kind,
        TypedValueKind::Ctor { .. } | TypedValueKind::Tuple(_) | TypedValueKind::UnboxedTuple(_)
    ) || trivial(v)
}

// A value whose head PROVES what it can and cannot match: a constructor,
// tuple, or literal. A bare variable is deliberately not discriminable; its
// runtime shape is unknown, so pattern mismatch against it is never a proof.
fn discriminable(v: &TypedValue) -> bool {
    matches!(
        peel(v).kind,
        TypedValueKind::Ctor { .. }
            | TypedValueKind::Tuple(_)
            | TypedValueKind::UnboxedTuple(_)
            | TypedValueKind::Int(_)
            | TypedValueKind::I64(_)
            | TypedValueKind::U64(_)
            | TypedValueKind::Float(_)
            | TypedValueKind::Bool(_)
            | TypedValueKind::Unit
            | TypedValueKind::Str(_)
    )
}

fn trivial(v: &TypedValue) -> bool {
    matches!(
        peel(v).kind,
        TypedValueKind::Var { .. }
            | TypedValueKind::Int(_)
            | TypedValueKind::I64(_)
            | TypedValueKind::U64(_)
            | TypedValueKind::Float(_)
            | TypedValueKind::Bool(_)
            | TypedValueKind::Unit
            | TypedValueKind::Str(_)
    )
}

// Rebuild a remembered trivial alias at one local occurrence. A higher-rank
// binder is stored at its scheme, but each use carries both its monomorphic
// witness and explicit scheme arguments. Copying the scheme-valued alias over
// that use would retain the wrapper around the occurrence while replacing its
// inner witness with `forall`, producing an illegal representation coercion.
// Direct variable aliases can instead inherit the occurrence's instantiation;
// every other type mismatch simply declines copy propagation.
fn alias_at(alias: &TypedValue, occurrence: &TypedValue) -> Option<TypedValue> {
    if alias.ty() == occurrence.ty() {
        return Some(alias.clone());
    }
    let TypedValueKind::Var {
        instantiation: use_instantiation,
        ..
    } = occurrence.kind()
    else {
        return None;
    };
    let TypedValueKind::Var {
        name,
        instantiation: alias_instantiation,
    } = alias.kind()
    else {
        return None;
    };
    if !alias_instantiation.is_empty() {
        return None;
    }
    let ty = instantiate_value_scheme(alias.ty(), use_instantiation).ok()?;
    (ty == *occurrence.ty()).then(|| {
        TypedValue::new(
            ty,
            TypedValueKind::Var {
                name: *name,
                instantiation: use_instantiation.clone(),
            },
        )
    })
}

// Drop env entries a binder invalidates: those whose key it shadows, and those
// whose remembered value mentions a shadowed name (inlining which would capture).
fn narrow(env: &Env, bs: &[Sym]) -> Env {
    if bs.is_empty() {
        return env.clone();
    }
    let set: BTreeSet<Sym> = bs.iter().copied().collect();
    env.iter()
        .filter(|(k, v)| !set.contains(k) && free_value_vars(v).is_disjoint(&set))
        .map(|(k, v)| (*k, v.clone()))
        .collect()
}

fn pattern_binder_names(pattern: &TypedPattern) -> Vec<Sym> {
    match pattern {
        TypedPattern::Wild => Vec::new(),
        TypedPattern::Var(binder) => vec![binder.name],
        TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
            fields.iter().flatten().map(|binder| binder.name).collect()
        }
    }
}

// Bindings produced by matching `pat` against the known value `kv`, or `None`
// if the pattern cannot match it. Binders carry their declared typed shape so
// `build_arm` can construct a properly typed `Bind`.
fn pat_match(pat: &TypedPattern, kv: &TypedValue) -> Option<Vec<(TypedBinder, TypedValue)>> {
    let fields_binds = |binders: &[Option<TypedBinder>], fields: &[TypedValue]| {
        binders
            .iter()
            .zip(fields)
            .filter_map(|(b, f)| b.clone().map(|b| (b, f.clone())))
            .collect()
    };
    match (pat, &peel(kv).kind) {
        (TypedPattern::Wild, _) => Some(Vec::new()),
        (TypedPattern::Var(binder), _) => Some(vec![(binder.clone(), kv.clone())]),
        (
            TypedPattern::Ctor { name, fields, .. },
            TypedValueKind::Ctor {
                name: name2,
                fields: vfields,
                ..
            },
        ) if name == name2 && fields.len() == vfields.len() => Some(fields_binds(fields, vfields)),
        (
            TypedPattern::Tuple(fields),
            TypedValueKind::Tuple(vfields) | TypedValueKind::UnboxedTuple(vfields),
        ) if fields.len() == vfields.len() => Some(fields_binds(fields, vfields)),
        _ => None,
    }
}

// Resolve a scrutinee to a known constructor/tuple/literal, through one env
// hop. A variable bound to another variable is not chased here; copy-prop
// rewrites it first.
fn resolve(scrut: &TypedValue, env: &Env) -> Option<TypedValue> {
    match &peel(scrut).kind {
        TypedValueKind::Ctor { .. }
        | TypedValueKind::Tuple(_)
        | TypedValueKind::UnboxedTuple(_) => Some(scrut.clone()),
        TypedValueKind::Var { name, .. } => match env.get(name) {
            Some(v) if !matches!(&peel(v).kind, TypedValueKind::Var { .. }) => Some(v.clone()),
            _ => None,
        },
        _ if trivial(scrut) => Some(scrut.clone()),
        _ => None,
    }
}

// Fold a `Prim` over float literals, mirroring the evaluator's
// `dispatch_float_op` exactly. `Divf` by zero yields inf (not a trap), so
// unlike integer `Div` it folds.
#[allow(clippy::float_cmp)]
fn const_fold_float(op: CoreOp, x: f64, y: f64) -> Option<TypedValueKind> {
    Some(match op {
        CoreOp::Addf => TypedValueKind::Float(x + y),
        CoreOp::Subf => TypedValueKind::Float(x - y),
        CoreOp::Mulf => TypedValueKind::Float(x * y),
        CoreOp::Divf => TypedValueKind::Float(x / y),
        CoreOp::Eqf => TypedValueKind::Bool(x == y),
        CoreOp::Nef => TypedValueKind::Bool(x != y),
        CoreOp::Ltf => TypedValueKind::Bool(x < y),
        CoreOp::Lef => TypedValueKind::Bool(x <= y),
        CoreOp::Gtf => TypedValueKind::Bool(x > y),
        CoreOp::Gef => TypedValueKind::Bool(x >= y),
        _ => return None,
    })
}

// Fold a `Prim` over integer literals, mirroring the evaluator's i64 fast path
// (`dispatch_int_op`). Comparisons fold always; arithmetic folds only when the
// result is representable as a tagged immediate, i.e. it neither overflows i64
// nor leaves the tagged-immediate range the elaborator uses (`small_int`). A
// `Div`/`Rem` by zero never folds (the runtime error must still raise). Float
// operands fold via `const_fold_float`; machine-int (`I64`/`U64`) operands are
// left alone, so the fold is parity-exact.
fn const_fold(op: CoreOp, a: &TypedValue, b: &TypedValue) -> Option<TypedValueKind> {
    let (pa, pb) = (peel(a), peel(b));
    if let (TypedValueKind::Float(x), TypedValueKind::Float(y)) = (&pa.kind, &pb.kind) {
        return const_fold_float(op, *x, *y);
    }
    let (TypedValueKind::Int(x), TypedValueKind::Int(y)) = (&pa.kind, &pb.kind) else {
        return None;
    };
    let (x, y) = (*x, *y);
    // The immediate (untagged 63-bit) range a `TypedValueKind::Int` may hold,
    // matching `small_int` in elaboration.
    let imm = |r: i64| {
        ((-(1i64 << 62))..(1i64 << 62))
            .contains(&r)
            .then_some(TypedValueKind::Int(r))
    };
    match op {
        CoreOp::Eq => Some(TypedValueKind::Bool(x == y)),
        CoreOp::Ne => Some(TypedValueKind::Bool(x != y)),
        CoreOp::Lt => Some(TypedValueKind::Bool(x < y)),
        CoreOp::Le => Some(TypedValueKind::Bool(x <= y)),
        CoreOp::Gt => Some(TypedValueKind::Bool(x > y)),
        CoreOp::Ge => Some(TypedValueKind::Bool(x >= y)),
        CoreOp::Add => x.checked_add(y).and_then(imm),
        CoreOp::Sub => x.checked_sub(y).and_then(imm),
        CoreOp::Mul => x.checked_mul(y).and_then(imm),
        CoreOp::Div if y != 0 => x.checked_div(y).and_then(imm),
        CoreOp::Rem if y != 0 => imm(x.wrapping_rem(y)),
        _ => None,
    }
}

// The selected arm: bind each matched field with its declared type, then the
// original body. `Return(v)` is always effect-`Empty`, so the verified
// `Bind` sig-construction rule collapses to exactly `out`'s existing sig.
fn build_arm(binds: Vec<(TypedBinder, TypedValue)>, body: &TypedComp) -> TypedComp {
    let mut out = body.clone();
    for (binder, value) in binds.into_iter().rev() {
        let ty = value.ty.clone();
        out = TypedComp::new(
            out.sig.clone(),
            TypedCompKind::Bind(
                Box::new(TypedComp::new(
                    CompSig::new(ty, EffRow::Empty),
                    TypedCompKind::Return(value),
                )),
                binder,
                Box::new(out),
            ),
        );
    }
    out
}

// The node budget a case-of-case continuation may have. The bound is what
// keeps duplication (each scrutinee arm gets the continuation branch it
// selects) finite.
const COC_SIZE_LIMIT: usize = 48;

// A bounded node count of `c`, for the case-of-case size guard.
fn comp_nodes(c: &TypedComp) -> usize {
    1 + match &c.kind {
        TypedCompKind::Bind(a, _, b) => comp_nodes(a) + comp_nodes(b),
        TypedCompKind::Case(_, arms) => arms.iter().map(|(_, b)| comp_nodes(b)).sum(),
        TypedCompKind::If(_, t, e) => comp_nodes(t) + comp_nodes(e),
        TypedCompKind::Lam(_, b) | TypedCompKind::Mask(_, b) => comp_nodes(b),
        TypedCompKind::App { callee, .. } => comp_nodes(callee),
        TypedCompKind::WithReuse { body, .. } => comp_nodes(body),
        TypedCompKind::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            comp_nodes(body)
                + return_body.as_ref().map_or(0, |b| comp_nodes(b))
                + ops.arms.iter().map(|o| comp_nodes(&o.body)).sum::<usize>()
        }
        _ => 0,
    }
}

// A continuation `K` that immediately scrutinizes the let-bound `x` and
// nothing else: either `case x of <arms>` or `if x then .. else ..`. Used by
// case-of-case to compute, per scrutinee arm, the branch a known value
// selects.
enum Cont<'a> {
    Case(&'a [(TypedPattern, TypedComp)]),
    If(&'a TypedComp, &'a TypedComp),
}

// View `body` as a continuation on `x`: it must scrutinize `x` at its head and
// use `x` nowhere else (so dropping the `let x = ...` cannot leave `x`
// dangling).
fn cont_on(x: Sym, body: &TypedComp) -> Option<Cont<'_>> {
    match &body.kind {
        TypedCompKind::Case(scrut, arms) => {
            let is_x = matches!(&peel(scrut).kind, TypedValueKind::Var { name, .. } if *name == x);
            (is_x && !arms.iter().any(|(_, b)| free_comp_vars(b).contains(&x)))
                .then_some(Cont::Case(arms))
        }
        TypedCompKind::If(scrut, t, e) => {
            let is_x = matches!(&peel(scrut).kind, TypedValueKind::Var { name, .. } if *name == x);
            (is_x && !free_comp_vars(t).contains(&x) && !free_comp_vars(e).contains(&x))
                .then_some(Cont::If(t, e))
        }
        _ => None,
    }
}

impl Cont<'_> {
    // The branch this continuation takes when `x` is the known value `kv`,
    // fully collapsed (the inner scrutinee is gone). `None` if no branch is
    // selected, in which case case-of-case must not fire (collapse is not
    // guaranteed).
    fn select(&self, kv: &TypedValue) -> Option<TypedComp> {
        match self {
            Self::Case(arms) => {
                // Selecting an arm by scanning in order is sound only when every
                // earlier arm's failure to match is a PROOF of mismatch, which
                // needs a discriminable head (a constructor, tuple, or literal).
                // A bare variable is `known` for copy-propagation but its runtime
                // constructor is unknown: a preceding constructor arm returning
                // no match is ignorance, not proof, and skipping to a wildcard
                // arm would statically select the default for a value that may
                // match `Doing(..)` at run time (the filtered-optic miscompile).
                // For a non-discriminable value only an unconditionally matching
                // FIRST arm (wildcard or variable pattern) may be selected.
                if discriminable(kv) {
                    arms.iter().find_map(|(pat, body)| {
                        pat_match(pat, kv).map(|binds| build_arm(binds, body))
                    })
                } else {
                    arms.first().and_then(|(pat, body)| {
                        matches!(pat, TypedPattern::Wild | TypedPattern::Var(_))
                            .then(|| pat_match(pat, kv).map(|binds| build_arm(binds, body)))
                            .flatten()
                    })
                }
            }
            Self::If(t, e) => match &peel(kv).kind {
                TypedValueKind::Bool(true) => Some((*t).clone()),
                TypedValueKind::Bool(false) => Some((*e).clone()),
                _ => None,
            },
        }
    }
}

// `Return(v)` with `v` a known value, the shape every arm/branch of a
// case-of-case scrutinee must have.
fn ret_known(c: &TypedComp) -> Option<TypedValue> {
    if let TypedCompKind::Return(v) = &c.kind {
        known(v).then(|| v.clone())
    } else {
        None
    }
}

// Case-of-case, terminating-by-construction form. Floats `let x = E in K`
// into E's arms only when the float is guaranteed to immediately collapse and
// strictly remove a join: `E` is a `Case`/`If` whose every arm/branch is
// `Return(known)`, `K` immediately scrutinizes `x` (and uses it nowhere
// else), and `K` is within the size bound. Each arm becomes the K-branch that
// arm's known value selects, computed here, so the inner scrutinee vanishes
// with no later pass and no growth beyond K's bounded size. `None` when any
// precondition fails. Uses `body.sig`, not `rhs.sig`: the collapsed branches
// are `body`'s own continuation branches, not the scrutinee's result.
fn case_of_case(x: &TypedBinder, rhs: &TypedComp, body: &TypedComp) -> Option<TypedComp> {
    if !matches!(&rhs.kind, TypedCompKind::Case(..) | TypedCompKind::If(..)) {
        return None;
    }
    let cont = cont_on(x.name, body)?;
    if comp_nodes(body) > COC_SIZE_LIMIT {
        return None;
    }
    match &rhs.kind {
        TypedCompKind::Case(scrut, arms) => {
            // `K` is floated under each arm's pattern binders; a binder that
            // shadows a free var of `K` would capture it, so bail in that case.
            let kfv: BTreeSet<Sym> = free_comp_vars(body)
                .into_iter()
                .filter(|v| *v != x.name)
                .collect();
            let mut out = Vec::with_capacity(arms.len());
            for (pat, abody) in arms {
                if pattern_binder_names(pat).iter().any(|b| kfv.contains(b)) {
                    return None;
                }
                out.push((pat.clone(), cont.select(&ret_known(abody)?)?));
            }
            Some(TypedComp::new(
                body.sig.clone(),
                TypedCompKind::Case(scrut.clone(), out),
            ))
        }
        TypedCompKind::If(scrut, t, e) => {
            let tb = cont.select(&ret_known(t)?)?;
            let eb = cont.select(&ret_known(e)?)?;
            Some(TypedComp::new(
                body.sig.clone(),
                TypedCompKind::If(scrut.clone(), Box::new(tb), Box::new(eb)),
            ))
        }
        _ => None,
    }
}

impl Rewrite for Simplifier {
    type Ctx = Env;

    fn value(&mut self, v: &TypedValue, env: &Env) -> TypedValue {
        if let TypedValueKind::Var { name, .. } = &v.kind {
            if let Some(t) = env.get(name) {
                if trivial(t) {
                    if let Some(alias) = alias_at(t, v) {
                        self.ticks += 1;
                        return alias;
                    }
                }
            }
        }
        self.descend_value(v, env)
    }

    #[allow(clippy::too_many_lines)]
    fn comp(&mut self, comp: &TypedComp, env: &Env) -> TypedComp {
        match &comp.kind {
            TypedCompKind::Bind(rhs, x, body) => {
                let rhs2 = self.comp(rhs, env);
                let mut benv = narrow(env, &[x.name]);
                if let TypedCompKind::Return(v) = &rhs2.kind {
                    if known(v) {
                        benv.insert(x.name, v.clone());
                    }
                }
                let body2 = self.comp(body, &benv);
                // Case-of-case (terminating-by-construction): when `rhs` is a
                // case/if of known returns and `body` immediately scrutinizes
                // `x`, float into the arms, collapsing the inner scrutinee on
                // the spot.
                if let Some(coc) = case_of_case(x, &rhs2, &body2) {
                    self.ticks += 1;
                    return coc;
                }
                // Used-once-thunk inlining (canonical immediate-force shape):
                // a thunk bound and then immediately forced once collapses to
                // its computation, dropping the allocation. Sound because
                // Prism thunks are not memoized, so the inline runs it
                // exactly as often; `x` not free in `rest` confirms the force
                // was the only use.
                if let TypedCompKind::Return(v) = &rhs2.kind {
                    if let TypedValueKind::Thunk(c) = &peel(v).kind {
                        if let TypedCompKind::Bind(forced, y, rest) = &body2.kind {
                            let forces_x = matches!(
                                &forced.kind,
                                TypedCompKind::Force(fv)
                                    if matches!(&peel(fv).kind, TypedValueKind::Var { name, .. } if *name == x.name)
                            );
                            if forces_x && !free_comp_vars(rest).contains(&x.name) {
                                self.ticks += 1;
                                return TypedComp::new(
                                    body2.sig.clone(),
                                    TypedCompKind::Bind(c.clone(), y.clone(), rest.clone()),
                                );
                            }
                        }
                    }
                }
                if matches!(rhs2.kind, TypedCompKind::Return(_))
                    && !free_comp_vars(&body2).contains(&x.name)
                {
                    self.ticks += 1; // dead-let
                    body2
                } else {
                    TypedComp::new(
                        comp.sig.clone(),
                        TypedCompKind::Bind(Box::new(rhs2), x.clone(), Box::new(body2)),
                    )
                }
            }
            TypedCompKind::Case(scrut, arms) => {
                if let Some(kv) = resolve(scrut, env) {
                    for (pat, body) in arms {
                        if let Some(binds) = pat_match(pat, &kv) {
                            self.ticks += 1; // case-of-known-constructor
                            return build_arm(binds, body);
                        }
                    }
                }
                let scrut2 = self.value(scrut, env);
                let arms2 = arms
                    .iter()
                    .map(|(p, b)| {
                        let e = narrow(env, &pattern_binder_names(p));
                        (p.clone(), self.comp(b, &e))
                    })
                    .collect();
                TypedComp::new(comp.sig.clone(), TypedCompKind::Case(scrut2, arms2))
            }
            TypedCompKind::Lam(ps, b) => {
                let names: Vec<Sym> = ps.iter().map(|p| p.name).collect();
                let e = narrow(env, &names);
                TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::Lam(ps.clone(), Box::new(self.comp(b, &e))),
                )
            }
            TypedCompKind::Handle {
                body,
                return_binder,
                return_body,
                ops,
            } => {
                let body2 = Box::new(self.comp(body, env));
                let return_body2 = return_body.as_ref().map(|b| {
                    let names: Vec<Sym> = return_binder.iter().map(|rb| rb.name).collect();
                    let e = narrow(env, &names);
                    Box::new(self.comp(b, &e))
                });
                let ops2 = TypedHandler {
                    arms: ops
                        .arms
                        .iter()
                        .map(|o| {
                            let mut bs: Vec<Sym> = o.params.iter().map(|p| p.name).collect();
                            bs.push(o.resume.name);
                            let e = narrow(env, &bs);
                            TypedHandleOp {
                                name: o.name,
                                instantiation: o.instantiation.clone(),
                                params: o.params.clone(),
                                resume: o.resume.clone(),
                                body: self.comp(&o.body, &e),
                            }
                        })
                        .collect(),
                    forwarded: ops.forwarded.clone(),
                };
                TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::Handle {
                        body: body2,
                        return_binder: return_binder.clone(),
                        return_body: return_body2,
                        ops: ops2,
                    },
                )
            }
            TypedCompKind::WithReuse { token, freed, body } => {
                let freed2 = self.value(freed, env);
                let e = narrow(env, &[token.name]);
                TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::WithReuse {
                        token: token.clone(),
                        freed: freed2,
                        body: Box::new(self.comp(body, &e)),
                    },
                )
            }
            TypedCompKind::Prim(op, a, b) => {
                let a2 = self.value(a, env);
                let b2 = self.value(b, env);
                if let Some(folded) = const_fold(*op, &a2, &b2) {
                    self.ticks += 1;
                    TypedComp::new(
                        comp.sig.clone(),
                        TypedCompKind::Return(TypedValue::new(comp.sig.result.clone(), folded)),
                    )
                } else {
                    TypedComp::new(comp.sig.clone(), TypedCompKind::Prim(*op, a2, b2))
                }
            }
            _ => self.descend_comp(comp, env),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use crate::core::{EffectStrategy, OpGrades};
    use crate::flags::{DynFlags, EffectTier};
    use crate::types::ty::Label;
    use crate::types::Type;

    use super::super::effect_lower::lower_effects;
    use super::super::verify::{verify, OperationSig, VerifyEnv};
    use super::super::{
        CoreFnSig, CoreQuantifier, CoreType, EffectLowered, Elaborated, TypedCoreFn, TypedLowering,
    };
    use super::*;

    fn sym(name: &str) -> Sym {
        Sym::new(name)
    }

    fn source(ty: Type) -> CoreType {
        CoreType::Source(ty)
    }

    fn pure(result: CoreType) -> CompSig {
        CompSig::new(result, EffRow::Empty)
    }

    fn var(name: &str, ty: CoreType) -> TypedValue {
        TypedValue::new(
            ty,
            TypedValueKind::Var {
                name: sym(name),
                instantiation: Vec::new(),
            },
        )
    }

    fn int(n: i64) -> TypedValue {
        TypedValue::new(source(Type::Int), TypedValueKind::Int(n))
    }

    fn ret(v: TypedValue) -> TypedComp {
        TypedComp::new(pure(v.ty.clone()), TypedCompKind::Return(v))
    }

    fn one_fn(body: TypedComp) -> Vec<TypedCoreFn> {
        vec![TypedCoreFn::new(
            sym("f"),
            Vec::new(),
            body.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), body.sig),
            0,
        )]
    }

    fn run_simplify(functions: Vec<TypedCoreFn>, env: &VerifyEnv) -> (TypedCore<Elaborated>, u64) {
        let input = TypedCore::new(functions);
        if let Err(violations) = verify(&input, env) {
            panic!("input fixture is invalid: {violations:#?}");
        }
        let (actual, stats) = simplify(input).expect("typed simplification");
        if let Err(violations) = verify(&actual, env) {
            panic!("simplified typed Core is invalid: {violations:#?}");
        }
        (actual, stats.ticks())
    }

    fn lowered_simplify_fixture() -> (TypedCore<EffectLowered>, VerifyEnv) {
        let operation = sym("ask");
        let effect = sym("Ask");
        let mut env = VerifyEnv::new();
        env.insert_operation(
            operation,
            OperationSig::new(
                Vec::new(),
                Vec::new(),
                source(Type::Int),
                Label::bare(effect),
            ),
        );
        let effects = EffRow::singleton(effect);
        let main_body = TypedComp::new(
            CompSig::new(source(Type::Int), effects.clone()),
            TypedCompKind::Do {
                operation,
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let main = TypedCoreFn::new(
            sym("main"),
            Vec::new(),
            main_body,
            CoreFnSig::new(
                Vec::new(),
                Vec::new(),
                CompSig::new(source(Type::Int), effects),
            ),
            0,
        );
        let input = TypedCore::<Elaborated>::new(vec![main]);
        if let Err(violations) = verify(&input, &env) {
            panic!("elaborated late-pass fixture is invalid: {violations:#?}");
        }
        let flags = DynFlags {
            effect_tier: EffectTier::FreeMonad,
            quiet: true,
            ..DynFlags::default()
        };
        let TypedLowering {
            core: lowered,
            env,
            ctors,
            warning: _,
            strategy,
        } = lower_effects(input, &env, &BTreeMap::new(), &flags, &OpGrades::new())
            .expect("fixture lowers through the production effect ABI");
        assert_eq!(strategy, EffectStrategy::SelectiveFreeMonad);
        assert!(ctors.contains_key("EPure"));
        assert!(ctors.contains_key("EOp"));
        assert!(
            crate::core::pretty::pp_core(&lowered.clone().erase()).contains("EOp"),
            "the production-origin fixture must contain a reified operation"
        );

        let target_body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(ret(int(7))),
                TypedBinder::new(sym("copy"), source(Type::Int)),
                Box::new(ret(var("copy", source(Type::Int)))),
            ),
        );
        let target = TypedCoreFn::new(
            sym("late_simplify_target"),
            Vec::new(),
            target_body,
            CoreFnSig::new(Vec::new(), Vec::new(), pure(source(Type::Int))),
            0,
        );
        let mut functions = lowered.functions().to_vec();
        functions.push(target);
        let core = TypedCore::<EffectLowered>::new(functions);
        if let Err(violations) = verify(&core, &env) {
            panic!("effect-lowered late-pass fixture is invalid: {violations:#?}");
        }
        (core, env)
    }

    #[test]
    fn effect_lowered_simplify_collapses_the_copy_binding() {
        let (input, env) = lowered_simplify_fixture();
        let (actual, stats) = simplify(input).expect("effect-lowered fixture simplifies");
        if let Err(violations) = verify(&actual, &env) {
            panic!("effect-lowered Simplify output is invalid: {violations:#?}");
        }
        assert!(stats.ticks() >= 2, "the lowered fixture must simplify");
        let target = actual
            .functions()
            .iter()
            .find(|function| function.name() == sym("late_simplify_target"))
            .expect("the late-pass target survives");
        assert!(matches!(
            target.body().kind(),
            TypedCompKind::Return(TypedValue {
                kind: TypedValueKind::Int(7),
                ..
            })
        ));
    }

    #[test]
    fn copy_propagation_reinstantiates_a_row_polymorphic_alias() {
        let row = sym("e");
        let thunk = |quantifiers, effects| {
            CoreType::Thunk(Box::new(CompSig::new(
                CoreType::Function(Box::new(CoreFnSig::new(
                    quantifiers,
                    vec![source(Type::Int)],
                    CompSig::new(source(Type::Int), effects),
                ))),
                EffRow::Empty,
            )))
        };
        let scheme = thunk(vec![CoreQuantifier::Row(row)], EffRow::Var(row));
        let empty = thunk(Vec::new(), EffRow::Empty);
        let io = thunk(Vec::new(), EffRow::singleton("IO"));
        let parameter = TypedBinder::new(sym("h"), scheme.clone());
        let local = TypedBinder::new(sym("t"), scheme.clone());
        let local_at_empty = TypedValue::new(
            empty,
            TypedValueKind::Var {
                name: local.name(),
                instantiation: vec![super::super::CoreInstantiation::Row(EffRow::Empty)],
            },
        );
        let argument = TypedValue::new(
            io.clone(),
            TypedValueKind::Reinterpret(Box::new(local_at_empty)),
        );
        let consume = TypedCoreFn::new(
            sym("consume"),
            vec![TypedBinder::new(sym("g"), io.clone())],
            ret(int(0)),
            CoreFnSig::new(
                Vec::new(),
                vec![io],
                CompSig::new(source(Type::Int), EffRow::Empty),
            ),
            0,
        );
        let tail = TypedComp::new(
            CompSig::new(source(Type::Int), EffRow::Empty),
            TypedCompKind::Call {
                callee: consume.name(),
                instantiation: Vec::new(),
                args: vec![argument],
            },
        );
        let head = TypedComp::new(
            CompSig::new(scheme.clone(), EffRow::Empty),
            TypedCompKind::Return(TypedValue::new(
                scheme.clone(),
                TypedValueKind::Var {
                    name: parameter.name(),
                    instantiation: Vec::new(),
                },
            )),
        );
        let body = TypedComp::new(
            tail.sig().clone(),
            TypedCompKind::Bind(Box::new(head), local, Box::new(tail)),
        );
        let caller = TypedCoreFn::new(
            sym("caller"),
            vec![parameter],
            body,
            CoreFnSig::new(
                Vec::new(),
                vec![scheme],
                CompSig::new(source(Type::Int), EffRow::Empty),
            ),
            0,
        );
        let env = VerifyEnv::new();
        let input = TypedCore::<EffectLowered>::new(vec![caller, consume]);
        assert_eq!(verify(&input, &env), Ok(()));

        let (output, stats) = simplify(input).expect("simplification converges");
        assert!(stats.ticks() > 0);
        assert_eq!(verify(&output, &env), Ok(()));

        // Copy propagation rewrites the `t` occurrence to `h` reinstantiated at
        // the use site's empty row, so the `let t = h` binding is dead and the
        // reinstantiated `h` flows straight into the call under its wrapper.
        let caller = output
            .functions()
            .iter()
            .find(|function| function.name() == sym("caller"))
            .expect("caller survives");
        assert!(!free_comp_vars(caller.body()).contains(&sym("t")));
        let TypedCompKind::Call { args, .. } = caller.body().kind() else {
            panic!("the dead alias binding must be eliminated, leaving the call");
        };
        let [argument] = args.as_slice() else {
            panic!("consume takes exactly its one argument");
        };
        let TypedValueKind::Reinterpret(inner) = &argument.kind else {
            panic!("the argument keeps its representation wrapper");
        };
        assert!(matches!(
            &inner.kind,
            TypedValueKind::Var { name, instantiation }
                if *name == sym("h")
                    && instantiation.as_slice()
                        == [super::super::CoreInstantiation::Row(EffRow::Empty)]
        ));
    }

    // `let sc = Some(v) in match sc { Some(a) => a, None => () }` collapses to
    // `v` end to end via case-of-known-constructor, copy-propagation, and
    // dead-let, exactly like the legacy fixture.
    #[test]
    fn known_constructor_match_collapses_to_the_field() {
        let mut env = VerifyEnv::new();
        env.insert_constructor(
            sym("Some"),
            super::super::verify::ConstructorSig::new(
                Vec::new(),
                0,
                vec![source(Type::Int)],
                source(Type::Int),
            ),
        );
        env.insert_constructor(
            sym("None"),
            super::super::verify::ConstructorSig::new(Vec::new(), 1, Vec::new(), source(Type::Int)),
        );
        let some_v = TypedValue::new(
            source(Type::Int),
            TypedValueKind::Ctor {
                name: sym("Some"),
                tag: 0,
                instantiation: Vec::new(),
                fields: vec![var("v", source(Type::Int))],
            },
        );
        let case = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Case(
                var("sc", source(Type::Int)),
                vec![
                    (
                        TypedPattern::Ctor {
                            name: sym("Some"),
                            instantiation: Vec::new(),
                            fields: vec![Some(TypedBinder::new(sym("a"), source(Type::Int)))],
                        },
                        ret(var("a", source(Type::Int))),
                    ),
                    (
                        TypedPattern::Ctor {
                            name: sym("None"),
                            instantiation: Vec::new(),
                            fields: Vec::new(),
                        },
                        ret(int(0)),
                    ),
                ],
            ),
        );
        let body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(ret(some_v)),
                TypedBinder::new(sym("sc"), source(Type::Int)),
                Box::new(case),
            ),
        );
        let functions = vec![TypedCoreFn::new(
            sym("f"),
            vec![TypedBinder::new(sym("v"), source(Type::Int))],
            body.clone(),
            CoreFnSig::new(Vec::new(), vec![source(Type::Int)], body.sig),
            0,
        )];
        let (actual, _) = run_simplify(functions, &env);
        assert_eq!(
            actual.functions()[0].body().kind(),
            &TypedCompKind::Return(var("v", source(Type::Int)))
        );
    }

    // `let x = 2 in let y = 3 in x + y` const-folds through copy-propagation
    // to `Return(Int(5))`, the parity-safe integer boundary.
    #[test]
    fn const_folds_integer_arithmetic_through_copy_propagation() {
        let env = VerifyEnv::new();
        let inner = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Prim(
                CoreOp::Add,
                var("x", source(Type::Int)),
                var("y", source(Type::Int)),
            ),
        );
        let body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(ret(int(2))),
                TypedBinder::new(sym("x"), source(Type::Int)),
                Box::new(TypedComp::new(
                    pure(source(Type::Int)),
                    TypedCompKind::Bind(
                        Box::new(ret(int(3))),
                        TypedBinder::new(sym("y"), source(Type::Int)),
                        Box::new(inner),
                    ),
                )),
            ),
        );
        let (actual, _) = run_simplify(one_fn(body), &env);
        assert_eq!(
            actual.functions()[0].body().kind(),
            &TypedCompKind::Return(int(5))
        );
    }

    // An overflowing add is left as a residual `Prim`, matching the legacy
    // non-folding boundary exactly.
    #[test]
    fn overflowing_add_does_not_fold() {
        let env = VerifyEnv::new();
        let big = i64::MAX;
        let body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Prim(CoreOp::Add, int(big), int(big)),
        );
        let (actual, ticks) = run_simplify(one_fn(body), &env);
        assert_eq!(ticks, 0);
        assert!(matches!(
            actual.functions()[0].body().kind(),
            TypedCompKind::Prim(CoreOp::Add, _, _)
        ));
    }

    // Float arithmetic and comparison fold bit-for-bit, matching the
    // evaluator's `dispatch_float_op`.
    #[test]
    fn const_folds_float_arithmetic_and_comparison() {
        let env = VerifyEnv::new();
        let lhs = TypedValue::new(source(Type::Float), TypedValueKind::Float(1.5));
        let rhs = TypedValue::new(source(Type::Float), TypedValueKind::Float(2.5));
        let body = TypedComp::new(
            pure(source(Type::Float)),
            TypedCompKind::Prim(CoreOp::Addf, lhs, rhs),
        );
        let (actual, _) = run_simplify(one_fn(body), &env);
        assert_eq!(
            actual.functions()[0].body().kind(),
            &TypedCompKind::Return(TypedValue::new(
                source(Type::Float),
                TypedValueKind::Float(4.0)
            ))
        );
    }

    // `let t = thunk(...) in let r = force t in r` inlines the thunk body
    // directly at its sole force, dropping the allocation.
    #[test]
    fn used_once_thunk_inlines_at_its_force() {
        let env = VerifyEnv::new();
        let thunked = ret(int(9));
        let thunk_value = TypedValue::new(
            CoreType::Thunk(Box::new(thunked.sig.clone())),
            TypedValueKind::Thunk(Box::new(thunked)),
        );
        let force = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Force(var("t", CoreType::Thunk(Box::new(pure(source(Type::Int)))))),
        );
        let body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(ret(thunk_value)),
                TypedBinder::new(sym("t"), CoreType::Thunk(Box::new(pure(source(Type::Int))))),
                Box::new(TypedComp::new(
                    pure(source(Type::Int)),
                    TypedCompKind::Bind(
                        Box::new(force),
                        TypedBinder::new(sym("r"), source(Type::Int)),
                        Box::new(ret(var("r", source(Type::Int)))),
                    ),
                )),
            ),
        );
        let (actual, _) = run_simplify(one_fn(body), &env);
        assert_eq!(
            actual.functions()[0].body().kind(),
            &TypedCompKind::Return(int(9))
        );
    }

    // `let x = (if c then Return(1) else Return(2)) in if x then A else B`
    // floats into the branches, collapsing the inner `if` on the spot.
    #[test]
    fn case_of_case_floats_and_collapses_the_inner_scrutinee() {
        let env = VerifyEnv::new();
        let cond = var("c", source(Type::Bool));
        let inner_if = TypedComp::new(
            pure(source(Type::Bool)),
            TypedCompKind::If(
                cond,
                Box::new(ret(TypedValue::new(
                    source(Type::Bool),
                    TypedValueKind::Bool(true),
                ))),
                Box::new(ret(TypedValue::new(
                    source(Type::Bool),
                    TypedValueKind::Bool(false),
                ))),
            ),
        );
        let outer_if = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::If(
                var("x", source(Type::Bool)),
                Box::new(ret(int(1))),
                Box::new(ret(int(2))),
            ),
        );
        let body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(inner_if),
                TypedBinder::new(sym("x"), source(Type::Bool)),
                Box::new(outer_if),
            ),
        );
        let functions = vec![TypedCoreFn::new(
            sym("f"),
            vec![TypedBinder::new(sym("c"), source(Type::Bool))],
            body.clone(),
            CoreFnSig::new(Vec::new(), vec![source(Type::Bool)], body.sig),
            0,
        )];
        let (actual, _) = run_simplify(functions, &env);
        assert!(!free_comp_vars(actual.functions()[0].body()).contains(&sym("x")));
    }

    // A shadowing inner binder of the same name invalidates the outer env
    // entry rather than being satisfied by it.
    #[test]
    fn shadowing_binder_narrows_the_outer_env_entry() {
        let env = VerifyEnv::new();
        let inner = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(ret(int(2))),
                TypedBinder::new(sym("x"), source(Type::Int)),
                Box::new(ret(var("x", source(Type::Int)))),
            ),
        );
        let body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(ret(int(1))),
                TypedBinder::new(sym("x"), source(Type::Int)),
                Box::new(inner),
            ),
        );
        let (actual, _) = run_simplify(one_fn(body), &env);
        assert_eq!(
            actual.functions()[0].body().kind(),
            &TypedCompKind::Return(int(2))
        );
    }

    // A nested thunk (thunk-of-thunk, forced once at each layer) inlines both
    // layers, matching the legacy pass applied twice at fixed point.
    #[test]
    fn nested_thunk_inlines_at_each_force() {
        let env = VerifyEnv::new();
        let innermost = ret(int(11));
        let inner_thunk = TypedValue::new(
            CoreType::Thunk(Box::new(innermost.sig.clone())),
            TypedValueKind::Thunk(Box::new(innermost)),
        );
        let inner_force = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Force(var("u", CoreType::Thunk(Box::new(pure(source(Type::Int)))))),
        );
        let outer_body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(ret(inner_thunk)),
                TypedBinder::new(sym("u"), CoreType::Thunk(Box::new(pure(source(Type::Int))))),
                Box::new(TypedComp::new(
                    pure(source(Type::Int)),
                    TypedCompKind::Bind(
                        Box::new(inner_force),
                        TypedBinder::new(sym("v"), source(Type::Int)),
                        Box::new(ret(var("v", source(Type::Int)))),
                    ),
                )),
            ),
        );
        let outer_thunk = TypedValue::new(
            CoreType::Thunk(Box::new(outer_body.sig.clone())),
            TypedValueKind::Thunk(Box::new(outer_body)),
        );
        let outer_force = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Force(var("t", CoreType::Thunk(Box::new(pure(source(Type::Int)))))),
        );
        let body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(ret(outer_thunk)),
                TypedBinder::new(sym("t"), CoreType::Thunk(Box::new(pure(source(Type::Int))))),
                Box::new(TypedComp::new(
                    pure(source(Type::Int)),
                    TypedCompKind::Bind(
                        Box::new(outer_force),
                        TypedBinder::new(sym("r"), source(Type::Int)),
                        Box::new(ret(var("r", source(Type::Int)))),
                    ),
                )),
            ),
        );
        let (actual, _) = run_simplify(one_fn(body), &env);
        assert_eq!(
            actual.functions()[0].body().kind(),
            &TypedCompKind::Return(int(11))
        );
    }

    // A handled computation whose body simplifies (dead-let elimination
    // inside the handled body, ahead of an unhandled `Do`) descends through
    // `Handle` and its forwarding evidence unchanged.
    #[test]
    fn handler_body_simplifies_and_forwarding_survives() {
        let operation_name = sym("get");
        let effect_name = sym("State");
        let mut env = VerifyEnv::new();
        env.insert_operation(
            operation_name,
            super::super::OperationSig::new(
                Vec::new(),
                Vec::new(),
                source(Type::Int),
                Label::bare(effect_name),
            ),
        );
        env.insert_operation(
            sym("put"),
            super::super::OperationSig::new(
                Vec::new(),
                vec![source(Type::Int)],
                source(Type::Unit),
                Label::bare(effect_name),
            ),
        );
        let do_get = TypedComp::new(
            CompSig::new(source(Type::Int), EffRow::singleton(effect_name)),
            TypedCompKind::Do {
                operation: operation_name,
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let dead_let = TypedComp::new(
            CompSig::new(source(Type::Int), EffRow::singleton(effect_name)),
            TypedCompKind::Bind(
                Box::new(ret(int(1))),
                TypedBinder::new(sym("_dead"), source(Type::Int)),
                Box::new(do_get),
            ),
        );
        let residual = CompSig::new(source(Type::Int), EffRow::singleton(effect_name));
        let resume = TypedBinder::new(
            sym("resume_partial"),
            CoreType::Thunk(Box::new(pure(CoreType::Function(Box::new(
                CoreFnSig::new(Vec::new(), vec![source(Type::Int)], residual.clone()),
            ))))),
        );
        let arm = TypedHandleOp::new(operation_name, Vec::new(), Vec::new(), resume, ret(int(0)));
        let body = TypedComp::new(
            residual,
            TypedCompKind::Handle {
                body: Box::new(dead_let),
                return_binder: None,
                return_body: None,
                ops: TypedHandler::new(vec![arm]).unwrap().with_forwarded(vec![
                    super::super::TypedForward::new(sym("put"), Label::bare(effect_name)),
                ]),
            },
        );
        let (actual, _) = run_simplify(one_fn(body), &env);
        let TypedCompKind::Handle { body, ops, .. } = actual.functions()[0].body().kind() else {
            panic!("expected a surviving Handle node");
        };
        assert_eq!(
            body.kind(),
            &TypedCompKind::Do {
                operation: operation_name,
                instantiation: Vec::new(),
                args: Vec::new(),
            }
        );
        assert_eq!(ops.forwarded().len(), 1);
    }

    // A type-polymorphic identity call with an explicit instantiation
    // descends unchanged (no rewrite rule touches `App`/`instantiation`);
    // simplification is a no-op fixed point immediately.
    #[test]
    fn type_polymorphic_call_is_left_unchanged() {
        let env = VerifyEnv::new();
        let quantified = sym("a");
        let scheme = CoreFnSig::new(
            vec![CoreQuantifier::Type(quantified)],
            vec![CoreType::Source(Type::Var(quantified))],
            pure(CoreType::Source(Type::Var(quantified))),
        );
        let callee_ty = CoreType::Function(Box::new(scheme));
        let id_ty = CoreType::Thunk(Box::new(pure(callee_ty.clone())));
        let callee = TypedComp::new(
            pure(callee_ty),
            TypedCompKind::Force(var("id", id_ty.clone())),
        );
        let body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::App {
                callee: Box::new(callee),
                instantiation: vec![super::super::CoreInstantiation::Type(Type::Int)],
                args: vec![int(1)],
            },
        );
        let functions = vec![TypedCoreFn::new(
            sym("f"),
            vec![TypedBinder::new(sym("id"), id_ty.clone())],
            body.clone(),
            CoreFnSig::new(Vec::new(), vec![id_ty], body.sig),
            0,
        )];
        let (_, ticks) = run_simplify(functions, &env);
        assert_eq!(ticks, 0);
    }

    // A row-polymorphic effect (`Force` of a thunk carrying a residual
    // `EffRow::Var`) cannot be dropped even though its result is unused: the
    // dead-let rule only ever discards a pure `Return` rhs. Simplification
    // therefore leaves the `Bind` and its row-polymorphic sig untouched.
    #[test]
    fn row_polymorphic_sig_survives_simplification() {
        let env = VerifyEnv::new();
        let quantified = sym("e");
        let eff_sig = CompSig::new(source(Type::Int), EffRow::Var(quantified));
        let thunk_ty = CoreType::Thunk(Box::new(eff_sig.clone()));
        let forced = TypedComp::new(
            eff_sig.clone(),
            TypedCompKind::Force(var("k", thunk_ty.clone())),
        );
        let body = TypedComp::new(
            eff_sig,
            TypedCompKind::Bind(
                Box::new(forced),
                TypedBinder::new(sym("_dead"), source(Type::Int)),
                Box::new(ret(int(3))),
            ),
        );
        let functions = vec![TypedCoreFn::new(
            sym("f"),
            vec![TypedBinder::new(sym("k"), thunk_ty.clone())],
            body.clone(),
            CoreFnSig::new(
                vec![CoreQuantifier::Row(quantified)],
                vec![thunk_ty],
                body.sig,
            ),
            0,
        )];
        let (actual, _) = run_simplify(functions, &env);
        assert_eq!(
            actual.functions()[0].body().sig().effects(),
            &EffRow::Var(quantified)
        );
    }

    // A fixture requiring two fixed-point rounds: the first pass folds `1+1`
    // to `2`, only after which the second pass can resolve the case scrutinee
    // that depends on the folded value being remembered.
    #[test]
    fn multi_round_fixed_point_folds_then_resolves_the_case() {
        let mut env = VerifyEnv::new();
        env.insert_constructor(
            sym("Some"),
            super::super::verify::ConstructorSig::new(
                Vec::new(),
                0,
                vec![source(Type::Int)],
                source(Type::Int),
            ),
        );
        let folded_prim = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Prim(CoreOp::Add, int(1), int(1)),
        );
        let wrapped = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(folded_prim),
                TypedBinder::new(sym("n"), source(Type::Int)),
                Box::new(ret(TypedValue::new(
                    source(Type::Int),
                    TypedValueKind::Ctor {
                        name: sym("Some"),
                        tag: 0,
                        instantiation: Vec::new(),
                        fields: vec![var("n", source(Type::Int))],
                    },
                ))),
            ),
        );
        let case = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Case(
                var("wrapped", source(Type::Int)),
                vec![(
                    TypedPattern::Ctor {
                        name: sym("Some"),
                        instantiation: Vec::new(),
                        fields: vec![Some(TypedBinder::new(sym("field"), source(Type::Int)))],
                    },
                    ret(var("field", source(Type::Int))),
                )],
            ),
        );
        let body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(wrapped),
                TypedBinder::new(sym("wrapped"), source(Type::Int)),
                Box::new(case),
            ),
        );
        let (actual, ticks) = run_simplify(one_fn(body), &env);
        assert!(ticks >= 4);
        assert_eq!(
            actual.functions()[0].body().kind(),
            &TypedCompKind::Return(int(2))
        );
    }
}
