//! Typed erasure of loop-control effects (`break`/`continue`/`return`) to
//! direct control flow.
//!
//! The three internal one-op control effects are discharged by fixed `never`
//! handler templates the desugar wraps around the loop body (`continue`), the
//! loop driver call (`break`), or the whole function body (`return`), so the
//! control flow is recovered directly instead of reifying a continuation.
//! `break`/`continue` thread an immediate `ctl : Int` (0 ran to the end, 1
//! continue, 2 break); `return` threads `Step` (`SMore` no return yet,
//! `SDone v` a return propagating) since it crosses loops to the function
//! boundary. Unmatched shapes are left for the general lowering, exactly the
//! recognize-or-leave discipline [`super::erase_var`] uses.
//!
//! The typed-specific steps are the same two the var erasure needed: the
//! private control label is discharged from every sig in the rewritten region
//! ([`super::subtract`]), and every node the pass builds carries the witness
//! its verified construction rule demands. The `Step` witnesses are explicit:
//! body threading yields `Step(Int, R)`, a driver yields `Step(Unit, R)`, and
//! function-level threading yields `Step(R, R)` which `seed_unwrap` collapses
//! back to `R`.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::effect_abi::{DONE_TAG, MORE_TAG, SDONE, SMORE, STEP};
use crate::names::{self, FOREVER, REPEAT_WHILE};
use crate::sym::Sym;
use crate::types::ty::EffRow;
use crate::types::Type;
use crate::util::fresh::Fresh;

use super::super::specialize_support::free_comp_vars;
use super::super::verify::{instantiate_value_scheme, ConstructorSig, VerifyEnv};
use super::super::{
    CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, LoweredType, TypedBinder,
    TypedComp, TypedCompKind, TypedCoreFn, TypedHandleOp, TypedHandler, TypedPattern, TypedValue,
    TypedValueKind,
};
use super::as_var;

// Canonical control dispositions threaded through a loop body.
const CTL_NORMAL: i64 = 0;
const CTL_CONTINUE: i64 = 1;
const CTL_BREAK: i64 = 2;

// The two `Step` type parameters, in scheme order: the `SMore` payload and the
// `SDone` payload. Combined threading genuinely mixes them (`SMore(Int)` rides
// beside `SDone(R)`), so the constructor family is two-parameter.
const STEP_MORE_PARAM: &str = "m";
const STEP_DONE_PARAM: &str = "d";

/// The `Step` witness at one threading site.
pub(super) fn step_type(more: &Type, done: &Type) -> Type {
    Type::Con(Sym::new(STEP), vec![more.clone(), done.clone()])
}

/// Register the `SMore`/`SDone` constructor schemes the control and state
/// paths share, so a threaded loop verifies before erasure. Idempotent: the
/// state path's early-termination protocol declares the same family.
pub(super) fn insert_step_constructors(env: &mut VerifyEnv) {
    let more = Sym::new(STEP_MORE_PARAM);
    let done = Sym::new(STEP_DONE_PARAM);
    let quantifiers = vec![CoreQuantifier::Type(more), CoreQuantifier::Type(done)];
    let result = step_type(&Type::Var(more), &Type::Var(done));
    env.insert_constructor(
        Sym::new(SMORE),
        ConstructorSig::new(
            quantifiers.clone(),
            MORE_TAG,
            vec![CoreType::Source(Type::Var(more))],
            CoreType::Source(result.clone()),
        ),
    );
    env.insert_constructor(
        Sym::new(SDONE),
        ConstructorSig::new(
            quantifiers,
            DONE_TAG,
            vec![CoreType::Source(Type::Var(done))],
            CoreType::Source(result),
        ),
    );
}

/// One `Step` instantiation: the witnesses a construction or match site
/// carries, so the verifier substitutes rather than infers.
#[derive(Clone, Debug)]
pub(super) struct StepAt {
    pub(super) more: Type,
    pub(super) done: Type,
}

impl StepAt {
    pub(super) const fn new(more: Type, done: Type) -> Self {
        Self { more, done }
    }

    fn instantiation(&self) -> Vec<CoreInstantiation> {
        vec![
            CoreInstantiation::Type(self.more.clone()),
            CoreInstantiation::Type(self.done.clone()),
        ]
    }

    pub(super) fn ty(&self) -> CoreType {
        CoreType::Source(step_type(&self.more, &self.done))
    }

    /// `SMore(v)` at this instantiation.
    pub(super) fn smore(&self, v: TypedValue) -> TypedValue {
        TypedValue::new(
            self.ty(),
            TypedValueKind::Ctor {
                name: Sym::new(SMORE),
                tag: MORE_TAG,
                instantiation: self.instantiation(),
                fields: vec![v],
            },
        )
    }

    /// `SDone(v)` at this instantiation.
    pub(super) fn sdone(&self, v: TypedValue) -> TypedValue {
        TypedValue::new(
            self.ty(),
            TypedValueKind::Ctor {
                name: Sym::new(SDONE),
                tag: DONE_TAG,
                instantiation: self.instantiation(),
                fields: vec![v],
            },
        )
    }

    /// The `SMore(binder)` pattern at this instantiation.
    pub(super) fn more_pattern(&self, binder: TypedBinder) -> TypedPattern {
        TypedPattern::Ctor {
            name: Sym::new(SMORE),
            instantiation: self.instantiation(),
            fields: vec![Some(binder)],
        }
    }

    /// The `SDone(binder)` pattern at this instantiation.
    pub(super) fn done_pattern(&self, binder: TypedBinder) -> TypedPattern {
        TypedPattern::Ctor {
            name: Sym::new(SDONE),
            instantiation: self.instantiation(),
            fields: vec![Some(binder)],
        }
    }
}

/// Whether `op` is one of the three loop-control ops this pass erases.
pub(super) fn is_control_op(op: Sym) -> bool {
    let s = op.as_str();
    names::is_break_op(s) || names::is_continue_op(s) || names::is_return_op(s)
}

/// The disposition a `do` carries, or `None` if it is not a `break`/`continue`.
pub(super) fn ctl_signal(op: Sym) -> Option<i64> {
    if names::is_break_op(op.as_str()) {
        Some(CTL_BREAK)
    } else if names::is_continue_op(op.as_str()) {
        Some(CTL_CONTINUE)
    } else {
        None
    }
}

/// Recognize the `continue` handler template the desugar wraps around a loop
/// body. Matching is on the op name alone: binders are alpha-renamed, but the
/// op name is unforgeable in source.
pub(super) fn match_continue(c: &TypedComp) -> Option<&TypedComp> {
    let TypedCompKind::Handle { body, ops, .. } = c.kind() else {
        return None;
    };
    let [op] = ops.arms() else {
        return None;
    };
    names::is_continue_op(op.name().as_str()).then_some(body.as_ref())
}

/// Recognize the `return` handler template the desugar wraps around a function
/// body.
pub(super) fn match_return(c: &TypedComp) -> Option<&TypedComp> {
    let TypedCompKind::Handle { body, ops, .. } = c.kind() else {
        return None;
    };
    let [op] = ops.arms() else {
        return None;
    };
    names::is_return_op(op.name().as_str()).then_some(body.as_ref())
}

/// Whether a computation performs a `do fn@return`. Unlike `break`/`continue`,
/// `return` crosses every loop to the function boundary, so this descends
/// through loop handlers too.
pub(super) fn signals_return(c: &TypedComp) -> bool {
    if matches!(c.kind(), TypedCompKind::Do { operation, .. } if names::is_return_op(operation.as_str()))
    {
        return true;
    }
    let mut found = false;
    super::walk::each_subterm(c, &mut |sc| found |= signals_return(sc));
    found
}

/// Whether a computation performs a `do break`/`do continue` this loop catches.
/// A nested loop absorbs its body's control ops (they target the innermost
/// loop), so a control-catching handle is opaque here.
pub(super) fn signals_ctl(c: &TypedComp) -> bool {
    match c.kind() {
        TypedCompKind::Do { operation, .. } => ctl_signal(*operation).is_some(),
        TypedCompKind::Handle { ops, .. }
            if ops.arms().iter().any(|o| ctl_signal(o.name()).is_some()) =>
        {
            false
        }
        _ => {
            let mut found = false;
            super::walk::each_subterm(c, &mut |sc| found |= signals_ctl(sc));
            found
        }
    }
}

/// Whether a computation performs a control op a `return`-crossing loop must
/// drive return-aware: a `break`/`continue` this loop catches, or a `return`
/// propagating through it.
pub(super) fn signals_loop(c: &TypedComp) -> bool {
    signals_ctl(c) || signals_return(c)
}

// A generated driver inlines its condition outside the source loop-handler
// spine. Be stricter here than `signals_ctl`: even control caught by a nested
// handler is declined, so erasing the condition cannot silently change its
// Bool witness while the enclosing driver is being constructed.
fn contains_control_signal(c: &TypedComp) -> bool {
    if matches!(c.kind(), TypedCompKind::Do { operation, .. } if is_control_op(*operation)) {
        return true;
    }
    let mut found = false;
    super::walk::each_subterm(c, &mut |sc| found |= contains_control_signal(sc));
    found
}

/// Whether `name` is one of the prelude loop drivers a recognized spine calls.
pub(super) fn is_loop_driver(name: Sym) -> bool {
    name.as_str() == REPEAT_WHILE || name.as_str() == FOREVER
}

/// The int-valued control disposition, as the immediate the threaded body
/// yields.
pub(super) const fn ctl_value(disposition: i64) -> TypedValue {
    TypedValue::new(
        CoreType::Source(Type::Int),
        TypedValueKind::Int(disposition),
    )
}

/// `return <int>` for a threaded body's disposition.
pub(super) fn ctl_return(disposition: i64) -> TypedComp {
    let v = ctl_value(disposition);
    TypedComp::new(
        CompSig::new(v.ty().clone(), EffRow::Empty),
        TypedCompKind::Return(v),
    )
}

/// The pass's deterministic fresh-name source (`{n}@hint`, one shared counter
/// per erasure run).
pub(super) struct ControlFresh(Fresh);

impl ControlFresh {
    pub(super) const fn new() -> Self {
        Self(Fresh::new())
    }

    pub(super) fn binder(&mut self, hint: &str, ty: CoreType) -> TypedBinder {
        TypedBinder::new(Sym::from(names::lowered(hint, self.0.bump())), ty)
    }
}

/// The normal disposition every non-signalling tail yields.
pub(super) const fn normal() -> i64 {
    CTL_NORMAL
}

/// The break disposition a driver dispatches on.
pub(super) const fn breaks() -> i64 {
    CTL_BREAK
}

/// The continue disposition a body short-circuits with.
#[cfg(test)]
pub(super) const fn continues() -> i64 {
    CTL_CONTINUE
}

/// The types of the variables in scope, threaded through the erasure so a
/// generated driver can give each captured free variable its declared type.
pub(super) type TypeEnv = BTreeMap<Sym, CoreType>;

/// The result of one erasure run: the rewritten functions (with any generated
/// loop drivers appended) and whether a `return` erasure threaded `Step`, so
/// the caller knows to add the `SMore`/`SDone` constructors to its tables.
pub(super) struct Erased {
    pub(super) fns: Vec<TypedCoreFn>,
    pub(super) used_step: bool,
}

/// Rewrite recognized `break`/`continue`/`return` control handlers to direct
/// control flow, leaving unmatched handlers for the general lowering.
pub(super) fn erase_control(fns: &[TypedCoreFn]) -> Erased {
    // Functions that can perform an effect other than loop control: erasing a
    // control handler whose region reaches such an effect could change how it
    // interacts with an outer (possibly multishot) handler, so those loops are
    // left alone. An un-erased `var` surfaces here as a foreign latent effect,
    // so the multishot protection composes.
    let foreign: BTreeSet<Sym> = super::latent::latent_ops(fns)
        .into_iter()
        .filter(|(_, ops)| ops.iter().any(|op| !is_control_op(*op)))
        .map(|(n, _)| n)
        .collect();
    let mut eraser = Eraser {
        fresh: ControlFresh::new(),
        generated: Vec::new(),
        used_step: false,
        foreign,
        globals: fns.iter().map(TypedCoreFn::name).collect(),
    };
    let mut out: Vec<TypedCoreFn> = fns
        .iter()
        .map(|f| {
            let mut env: TypeEnv = f
                .params()
                .iter()
                .map(|p| (p.name(), p.ty().clone()))
                .collect();
            let body = eraser.erase(f.body(), &mut env);
            TypedCoreFn::new(
                f.name(),
                f.params().to_vec(),
                body,
                f.sig().clone(),
                f.dict_arity(),
            )
        })
        .collect();
    out.append(&mut eraser.generated);
    Erased {
        fns: out,
        used_step: eraser.used_step,
    }
}

struct Eraser {
    fresh: ControlFresh,
    generated: Vec<TypedCoreFn>,
    used_step: bool,
    foreign: BTreeSet<Sym>,
    /// The program's top-level names: a free variable naming one is a callee,
    /// not a captured local, so it never becomes a driver parameter.
    globals: BTreeSet<Sym>,
}

impl Eraser {
    // Whether `c` can perform an effect other than loop control: a `do` of a
    // non-control op, or a call to a function with such a latent effect.
    // Descends into thunks and sub-handlers (conservative).
    fn has_foreign_effect(&self, c: &TypedComp) -> bool {
        match c.kind() {
            TypedCompKind::Do { operation, .. } => !is_control_op(*operation),
            TypedCompKind::Call { callee, .. } if self.foreign.contains(callee) => true,
            _ => {
                let mut found = false;
                super::walk::each_subterm(c, &mut |sc| found |= self.has_foreign_effect(sc));
                found
            }
        }
    }

    // Conditions are inlined into fresh monomorphic recursive drivers. Until
    // condition effects themselves are threaded, accept only an exact pure
    // Bool computation with no control signal anywhere below it. Checking
    // both before and after structural erasure makes the recursive Call row
    // self-defending against a future child rewrite that changes the witness.
    fn prepare_driver_condition(&mut self, c: &TypedComp, env: &mut TypeEnv) -> Option<TypedComp> {
        let bool_ty = CoreType::Source(Type::Bool);
        if c.sig().result() != &bool_ty
            || c.sig().effects() != &EffRow::Empty
            || contains_control_signal(c)
            || self.has_foreign_effect(c)
        {
            return None;
        }
        let erased = self.erase(c, env);
        (erased.sig().result() == &bool_ty && erased.sig().effects() == &EffRow::Empty)
            .then_some(erased)
    }

    // Structural descent, threading the typing context. The control-handler
    // templates are matched here and rewritten; an unmatched node is rebuilt
    // unchanged. The `return` handler is outermost (it wraps the whole body,
    // loops included), so it is matched first; a `break` handler (wrapping the
    // driver call) before `continue` (whose handler nests inside the body).
    fn erase(&mut self, c: &TypedComp, env: &mut TypeEnv) -> TypedComp {
        if let Some(body) = match_return(c) {
            if !self.has_foreign_effect(body) {
                let mark = self.generated.len();
                let result = comp_result_type(c);
                if let Some(done) = result.clone() {
                    if let Some(threaded) = self.thread_fn_return(body, env, &done) {
                        self.used_step = true;
                        return self.seed_unwrap(threaded, result.as_ref());
                    }
                }
                // Bail: drop any nested drivers the partial threading emitted.
                self.generated.truncate(mark);
            }
        }
        if let Some((cond, body)) = match_break(c) {
            if !self.has_foreign_effect(&body) {
                if let Some(call) = self.build_driver(Some(&cond), &body, env, None) {
                    return call;
                }
            }
        }
        if let Some(body) = match_continue(c) {
            if !self.has_foreign_effect(body) {
                let body = body.clone();
                if let Some(threaded) = self.thread_ctl(&body, env) {
                    return threaded;
                }
            }
        }
        self.descend(c, env)
    }

    // Rebuild `c`'s children under the extended context, exhaustively: every
    // value position is erased through
    // `erase_value` so a control template nested inside a thunk (a loop body
    // in particular) stays reachable. Retyping is diff-gated, not
    // unconditional: several verified construction rules (`Lam`'s body,
    // `Bind`'s row and result, `Return`'s witness) are checked by subtyping,
    // not equality, so a node's *declared* sig may legitimately be wider than
    // the exact sig recomputed bottom-up from its current children (a
    // polymorphic closure passed to a combinator like `fold` keeps its
    // quantified effect row even though its concrete body is effect-free).
    // Recomputing unconditionally collapses that declared generality and
    // desyncs it from what callers still expect. So: erase every child first,
    // and only when a child's own sig actually changed do we recompute this
    // node's sig (matching the node's verified construction rule exactly);
    // otherwise the original stale sig is reused verbatim, exactly as an
    // untouched node would report it.
    #[allow(clippy::too_many_lines)]
    fn descend(&mut self, c: &TypedComp, env: &mut TypeEnv) -> TypedComp {
        match c.kind() {
            TypedCompKind::Return(v) => {
                let v2 = self.erase_value(v, env);
                let sig = if v2.ty() == v.ty() {
                    c.sig().clone()
                } else {
                    CompSig::new(v2.ty().clone(), EffRow::Empty)
                };
                TypedComp::new(sig, TypedCompKind::Return(v2))
            }
            TypedCompKind::Bind(m, x, n) => {
                let m2 = self.erase(m, env);
                let m_changed = m2.sig() != m.sig();
                let x2 = if m_changed {
                    TypedBinder::new(x.name(), m2.sig().result().clone())
                } else {
                    x.clone()
                };
                let shadowed = env.insert(x2.name(), x2.ty().clone());
                let n2 = self.erase(n, env);
                restore(env, x2.name(), shadowed);
                if m_changed || n2.sig() != n.sig() {
                    bind(m2, x2, n2)
                } else {
                    TypedComp::new(
                        c.sig().clone(),
                        TypedCompKind::Bind(Box::new(m2), x2, Box::new(n2)),
                    )
                }
            }
            TypedCompKind::Force(v) => {
                let v2 = self.erase_value(v, env);
                let sig = if v2.ty() == v.ty() {
                    c.sig().clone()
                } else {
                    match v2.ty() {
                        CoreType::Thunk(sig) => sig.as_ref().clone(),
                        _ => c.sig().clone(),
                    }
                };
                TypedComp::new(sig, TypedCompKind::Force(v2))
            }
            TypedCompKind::Lam(ps, b) => {
                let saved: Vec<_> = ps
                    .iter()
                    .map(|p| (p.name(), env.insert(p.name(), p.ty().clone())))
                    .collect();
                let b2 = self.erase(b, env);
                for (name, prev) in saved {
                    restore(env, name, prev);
                }
                if b2.sig() == b.sig() {
                    TypedComp::new(
                        c.sig().clone(),
                        TypedCompKind::Lam(ps.clone(), Box::new(b2)),
                    )
                } else {
                    let ty = match c.sig().result() {
                        CoreType::Function(orig) => CoreType::Function(Box::new(CoreFnSig::new(
                            orig.quantifiers().to_vec(),
                            orig.params().to_vec(),
                            b2.sig().clone(),
                        ))),
                        other => other.clone(),
                    };
                    TypedComp::new(
                        CompSig::new(ty, EffRow::Empty),
                        TypedCompKind::Lam(ps.clone(), Box::new(b2)),
                    )
                }
            }
            TypedCompKind::If(v, t, e) => {
                let v2 = self.erase_value(v, env);
                let t2 = self.erase(t, env);
                let e2 = self.erase(e, env);
                if v2.ty() == v.ty() && t2.sig() == t.sig() && e2.sig() == e.sig() {
                    TypedComp::new(
                        c.sig().clone(),
                        TypedCompKind::If(v2, Box::new(t2), Box::new(e2)),
                    )
                } else {
                    if_then(v2, t2, e2)
                }
            }
            TypedCompKind::Prim(op, a, b) => TypedComp::new(
                c.sig().clone(),
                TypedCompKind::Prim(*op, self.erase_value(a, env), self.erase_value(b, env)),
            ),
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => {
                let args2: Vec<_> = args.iter().map(|a| self.erase_value(a, env)).collect();
                let instantiation2 = retype_loop_instantiation(*callee, instantiation, &args2);
                TypedComp::new(
                    c.sig().clone(),
                    TypedCompKind::Call {
                        callee: *callee,
                        instantiation: instantiation2,
                        args: args2,
                    },
                )
            }
            TypedCompKind::Io(op, args) => TypedComp::new(
                c.sig().clone(),
                TypedCompKind::Io(*op, args.iter().map(|a| self.erase_value(a, env)).collect()),
            ),
            TypedCompKind::Error(v) => TypedComp::new(
                c.sig().clone(),
                TypedCompKind::Error(self.erase_value(v, env)),
            ),
            TypedCompKind::Case(v, arms) => {
                let v2 = self.erase_value(v, env);
                let arms2: Vec<_> = arms
                    .iter()
                    .map(|(p, b)| {
                        let saved = bind_pattern(env, p);
                        let b2 = self.erase(b, env);
                        unbind_pattern(env, saved);
                        (p.clone(), b2)
                    })
                    .collect();
                let unchanged = v2.ty() == v.ty()
                    && arms2
                        .iter()
                        .zip(arms.iter())
                        .all(|((_, b2), (_, b))| b2.sig() == b.sig());
                if unchanged {
                    TypedComp::new(c.sig().clone(), TypedCompKind::Case(v2, arms2))
                } else {
                    case_of(v2, arms2, c.sig().result())
                }
            }
            TypedCompKind::FloatBuiltin(op, v) => TypedComp::new(
                c.sig().clone(),
                TypedCompKind::FloatBuiltin(*op, self.erase_value(v, env)),
            ),
            TypedCompKind::Neg(lane, v) => TypedComp::new(
                c.sig().clone(),
                TypedCompKind::Neg(*lane, self.erase_value(v, env)),
            ),
            TypedCompKind::UnboxedProject(v, field) => TypedComp::new(
                c.sig().clone(),
                TypedCompKind::UnboxedProject(self.erase_value(v, env), *field),
            ),
            TypedCompKind::Do {
                operation,
                instantiation,
                args,
            } => TypedComp::new(
                c.sig().clone(),
                TypedCompKind::Do {
                    operation: *operation,
                    instantiation: instantiation.clone(),
                    args: args.iter().map(|a| self.erase_value(a, env)).collect(),
                },
            ),
            TypedCompKind::Handle {
                body,
                return_binder,
                return_body,
                ops,
            } => {
                let body2 = self.erase(body, env);
                let return_body2 = match (return_binder, return_body) {
                    (Some(rb), Some(rbody)) => {
                        let shadowed = env.insert(rb.name(), rb.ty().clone());
                        let r2 = self.erase(rbody, env);
                        restore(env, rb.name(), shadowed);
                        Some(Box::new(r2))
                    }
                    _ => None,
                };
                let arms2: Vec<TypedHandleOp> = ops
                    .arms()
                    .iter()
                    .map(|op| {
                        let saved: Vec<_> = op
                            .params()
                            .iter()
                            .chain(std::iter::once(op.resume()))
                            .map(|p| (p.name(), env.insert(p.name(), p.ty().clone())))
                            .collect();
                        let op_body2 = self.erase(op.body(), env);
                        for (name, prev) in saved {
                            restore(env, name, prev);
                        }
                        TypedHandleOp::new(
                            op.name(),
                            op.instantiation().to_vec(),
                            op.params().to_vec(),
                            op.resume().clone(),
                            op_body2,
                        )
                    })
                    .collect();
                let ops2 = TypedHandler::new(arms2)
                    .expect("erasure preserves handler-arm name uniqueness")
                    .with_forwarded(ops.forwarded().to_vec());
                TypedComp::new(
                    c.sig().clone(),
                    TypedCompKind::Handle {
                        body: Box::new(body2),
                        return_binder: return_binder.clone(),
                        return_body: return_body2,
                        ops: ops2,
                    },
                )
            }
            TypedCompKind::Mask(ops, b) => TypedComp::new(
                c.sig().clone(),
                TypedCompKind::Mask(ops.clone(), Box::new(self.erase(b, env))),
            ),
            TypedCompKind::StrBuiltin {
                op,
                instantiation,
                args,
            } => TypedComp::new(
                c.sig().clone(),
                TypedCompKind::StrBuiltin {
                    op: *op,
                    instantiation: instantiation.clone(),
                    args: args.iter().map(|a| self.erase_value(a, env)).collect(),
                },
            ),
            TypedCompKind::Dup(v) => TypedComp::new(
                c.sig().clone(),
                TypedCompKind::Dup(self.erase_value(v, env)),
            ),
            TypedCompKind::Drop(v) => TypedComp::new(
                c.sig().clone(),
                TypedCompKind::Drop(self.erase_value(v, env)),
            ),
            TypedCompKind::WithReuse { token, freed, body } => {
                let freed2 = self.erase_value(freed, env);
                let shadowed = env.insert(token.name(), token.ty().clone());
                let body2 = self.erase(body, env);
                restore(env, token.name(), shadowed);
                TypedComp::new(
                    c.sig().clone(),
                    TypedCompKind::WithReuse {
                        token: token.clone(),
                        freed: freed2,
                        body: Box::new(body2),
                    },
                )
            }
            TypedCompKind::Reuse(token, v) => TypedComp::new(
                c.sig().clone(),
                TypedCompKind::Reuse(token.clone(), self.erase_value(v, env)),
            ),
            TypedCompKind::InitAt(cell, v) => TypedComp::new(
                c.sig().clone(),
                TypedCompKind::InitAt(self.erase_value(cell, env), self.erase_value(v, env)),
            ),
            TypedCompKind::RefNew(v) => TypedComp::new(
                c.sig().clone(),
                TypedCompKind::RefNew(self.erase_value(v, env)),
            ),
            TypedCompKind::RefGet(v) => TypedComp::new(
                c.sig().clone(),
                TypedCompKind::RefGet(self.erase_value(v, env)),
            ),
            TypedCompKind::RefSet(cell, v) => TypedComp::new(
                c.sig().clone(),
                TypedCompKind::RefSet(self.erase_value(cell, env), self.erase_value(v, env)),
            ),
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => {
                let callee2 = self.erase(callee, env);
                let args2: Vec<_> = args.iter().map(|a| self.erase_value(a, env)).collect();
                TypedComp::new(
                    c.sig().clone(),
                    TypedCompKind::App {
                        callee: Box::new(callee2),
                        instantiation: instantiation.clone(),
                        args: args2,
                    },
                )
            }
        }
    }

    // Erase control templates nested inside a value's thunk-valued children,
    // mirroring `specialize_support::descend_value`'s completeness. Only
    // `Var` (refreshed from the current binder type in `env`) and `Thunk`
    // (re-witnessed from its rewritten body's actual sig, the same idiom
    // `arena.rs`'s widening uses) can change type here; every other form's
    // declared type is fixed by its own constructor scheme and is left as-is.
    fn erase_value(&mut self, v: &TypedValue, env: &mut TypeEnv) -> TypedValue {
        match v.kind() {
            TypedValueKind::Var {
                name,
                instantiation,
            } => {
                // `env` stores the binder's scheme, while a local reference
                // stores the scheme instantiated at this use. Refreshing the
                // reference directly from `env` would therefore turn
                // `forall e. A ! e` back into a polymorphic witness while
                // retaining its explicit `[e := R]` arguments. Rebuild the use
                // from the refreshed scheme by the same rule the independent
                // verifier applies to local references.
                let ty = env.get(name).map_or_else(
                    || v.ty().clone(),
                    |stored| {
                        if instantiation.is_empty() {
                            stored.clone()
                        } else {
                            instantiate_value_scheme(stored, instantiation)
                                .unwrap_or_else(|error| {
                                    panic!(
                                        "control erasure invalidated local `{name}` instantiation: {error}"
                                    )
                                })
                        }
                    },
                );
                TypedValue::new(
                    ty,
                    TypedValueKind::Var {
                        name: *name,
                        instantiation: instantiation.clone(),
                    },
                )
            }
            TypedValueKind::Thunk(body) => {
                let body2 = self.erase(body, env);
                let ty = if body2.sig() == body.sig() {
                    v.ty().clone()
                } else {
                    CoreType::Thunk(Box::new(body2.sig().clone()))
                };
                TypedValue::new(ty, TypedValueKind::Thunk(Box::new(body2)))
            }
            TypedValueKind::Reinterpret(inner) => {
                let inner2 = self.erase_value(inner, env);
                // A thunk-to-thunk reinterpret is only ever legal when both
                // sides are exact witnesses of each other (verify's
                // `representation_preserving` requires identical params,
                // effects, and body result, modulo quantifier spelling); when
                // thunk descent retyped the inner witness, the declared outer
                // coercion must track it exactly rather than keep the stale
                // pre-erasure target, completing the retype chain for a
                // reinterpreted loop-body thunk.
                let ty = match (inner2.ty(), v.ty()) {
                    (CoreType::Thunk(_), CoreType::Thunk(_)) if inner2.ty() != inner.ty() => {
                        inner2.ty().clone()
                    }
                    _ => v.ty().clone(),
                };
                TypedValue::new(ty, TypedValueKind::Reinterpret(Box::new(inner2)))
            }
            TypedValueKind::LoweredRepr { value, proof } => TypedValue::new(
                v.ty().clone(),
                TypedValueKind::LoweredRepr {
                    value: Box::new(self.erase_value(value, env)),
                    proof: proof.clone(),
                },
            ),
            TypedValueKind::NewtypeRepr {
                constructor,
                instantiation,
                value,
            } => TypedValue::new(
                v.ty().clone(),
                TypedValueKind::NewtypeRepr {
                    constructor: *constructor,
                    instantiation: instantiation.clone(),
                    value: Box::new(self.erase_value(value, env)),
                },
            ),
            TypedValueKind::Ctor {
                name,
                tag,
                instantiation,
                fields,
            } => TypedValue::new(
                v.ty().clone(),
                TypedValueKind::Ctor {
                    name: *name,
                    tag: *tag,
                    instantiation: instantiation.clone(),
                    fields: fields.iter().map(|f| self.erase_value(f, env)).collect(),
                },
            ),
            TypedValueKind::Tuple(fields) => TypedValue::new(
                v.ty().clone(),
                TypedValueKind::Tuple(fields.iter().map(|f| self.erase_value(f, env)).collect()),
            ),
            TypedValueKind::UnboxedTuple(fields) => TypedValue::new(
                v.ty().clone(),
                TypedValueKind::UnboxedTuple(
                    fields.iter().map(|f| self.erase_value(f, env)).collect(),
                ),
            ),
            TypedValueKind::UnboxedRecord(fields) => TypedValue::new(
                v.ty().clone(),
                TypedValueKind::UnboxedRecord(
                    fields
                        .iter()
                        .map(|(n, f)| (*n, self.erase_value(f, env)))
                        .collect(),
                ),
            ),
            TypedValueKind::Int(_)
            | TypedValueKind::I64(_)
            | TypedValueKind::U64(_)
            | TypedValueKind::Float(_)
            | TypedValueKind::Bool(_)
            | TypedValueKind::Unit
            | TypedValueKind::Str(_) => v.clone(),
        }
    }
}

// The loop-driver `Call`'s instantiation carries the trailing body-thunk's
// polymorphic result type explicitly (`repeat_while`'s and `forever`'s shared
// scheme quantifies the ambient effect row first and the discarded body
// result last), so once ctl-threading changes that thunk's actual result
// type (`Unit` erases to `Int`), the last instantiation slot must follow it;
// a stale slot would substitute the callee's declared scheme to a type the
// retyped argument no longer matches. A break-having loop's driver `Call` is
// never reached here: `build_driver` replaces the whole spine with a fresh,
// monomorphic call instead.
//
// The body argument is a thunk of a *nullary lambda* (the desugared spine
// wraps the loop body as `Return(Thunk(Lam([], body)))`, matching
// `nullary_thunk`), not a thunk of the body directly: `body_arg.ty()` is
// `Thunk(CompSig{result: Function(CoreFnSig{params: [], body: <the real
// disposition sig>}), ..})`. The polymorphic slot tracks that inner
// disposition type one layer past the thunk, so unwrap the nullary function
// before reading the source type.
// Whether an effect row still mentions an unbound row quantifier. A generated
// top-level driver has no quantifiers of its own (`build_driver` mints
// `CoreFnSig::new(Vec::new(), ...)`), so any row it captures must already be
// closed; a live `Var`/`Exist` would be orphaned by lifting the row into that
// driver's signature.
fn row_has_active_var(row: &EffRow) -> bool {
    match row {
        EffRow::Empty => false,
        EffRow::Extend(label, tail) => {
            label.args.iter().any(type_has_active_var) || row_has_active_var(tail)
        }
        EffRow::Var(_) | EffRow::Exist(_) => true,
    }
}

// Whether a type still mentions an unbound type quantifier, for the same
// reason `row_has_active_var` checks rows: a generated driver's witnesses
// (its return-aware `Step` payload, its captured parameter types) must be
// closed, since the driver carries no quantifiers to bind one. Conservative
// on any head this pass has no reason to see closed at a loop-driver site
// (`App`, `Forall`, `RowForall`): treating it as active only costs a decline,
// never a soundness gap.
fn type_has_active_var(t: &Type) -> bool {
    match t {
        Type::Unit
        | Type::Int
        | Type::I64
        | Type::U64
        | Type::Bool
        | Type::Float
        | Type::Char
        | Type::Str
        | Type::Nat(_) => false,
        Type::Var(_)
        | Type::Exist(_)
        | Type::App(_, _)
        | Type::Forall(_, _)
        | Type::RowForall(_, _) => true,
        Type::Fun(params, row, ret) => {
            params.iter().any(type_has_active_var)
                || row_has_active_var(row)
                || type_has_active_var(ret)
        }
        Type::Con(_, args) => args.iter().any(type_has_active_var),
        Type::Tuple(xs) | Type::UnboxedTuple(xs) => xs.iter().any(type_has_active_var),
        Type::UnboxedRecord(fields) => fields.iter().any(|(_, t)| type_has_active_var(t)),
        Type::OrNull(inner) | Type::Coeffect(inner, _) => type_has_active_var(inner),
        Type::Row(row) => row_has_active_var(row),
    }
}

// The `CoreType`-level counterpart of `type_has_active_var`, for captured
// driver parameters: their type has already passed through effect-lowering's
// own representation choices (`Thunk`/`Function`/`Ref`/`ReuseToken`), not
// just the checked source language. Recurse to every embedded source `Type`
// or `EffRow` and defer to the two leaf checks above; a phase-private
// `Lowered` representation carries no source quantifier to orphan.
fn core_type_has_active_var(t: &CoreType) -> bool {
    match t {
        CoreType::Source(t) => type_has_active_var(t),
        CoreType::Thunk(sig) => {
            core_type_has_active_var(sig.result()) || row_has_active_var(sig.effects())
        }
        CoreType::Function(fn_sig) => {
            fn_sig.params().iter().any(core_type_has_active_var)
                || core_type_has_active_var(fn_sig.body().result())
                || row_has_active_var(fn_sig.body().effects())
        }
        CoreType::Ref(inner) | CoreType::ReuseToken(inner) => core_type_has_active_var(inner),
        CoreType::Lowered(LoweredType::Word) => false,
        CoreType::Lowered(
            LoweredType::Eff(row) | LoweredType::Queue(row) | LoweredType::QueueView(row),
        ) => row_has_active_var(row),
    }
}

fn retype_loop_instantiation(
    callee: Sym,
    instantiation: &[CoreInstantiation],
    args: &[TypedValue],
) -> Vec<CoreInstantiation> {
    if !is_loop_driver(callee) {
        return instantiation.to_vec();
    }
    let Some(body_arg) = args.last() else {
        return instantiation.to_vec();
    };
    let CoreType::Thunk(sig) = body_arg.ty() else {
        return instantiation.to_vec();
    };
    let CoreType::Function(fn_sig) = sig.result() else {
        return instantiation.to_vec();
    };
    if !fn_sig.params().is_empty() {
        return instantiation.to_vec();
    }
    let CoreType::Source(result_ty) = fn_sig.body().result() else {
        return instantiation.to_vec();
    };
    let mut out = instantiation.to_vec();
    if let Some(last) = out.last_mut() {
        *last = CoreInstantiation::Type(result_ty.clone());
    }
    out
}

// Re-insert or remove a shadowed binding, so a nested scope cannot leak its
// binder's type outward.
fn restore(env: &mut TypeEnv, name: Sym, previous: Option<CoreType>) {
    match previous {
        Some(ty) => {
            env.insert(name, ty);
        }
        None => {
            env.remove(&name);
        }
    }
}

// A W6a rewrite in a non-signalling Bind head may change its result witness
// (most notably a nested loop body thunk from Unit to Int). W6b must carry
// that witness through both the binder and every Var occurrence refreshed
// from TypeEnv; retaining the original binder would make the continuation
// internally inconsistent even though it does not itself signal control.
fn retype_bind_binder(head: &TypedComp, binder: &TypedBinder) -> TypedBinder {
    if head.sig().result() == binder.ty() {
        binder.clone()
    } else {
        TypedBinder::new(binder.name(), head.sig().result().clone())
    }
}

fn bind_pattern(env: &mut TypeEnv, p: &TypedPattern) -> Vec<(Sym, Option<CoreType>)> {
    pattern_binders(p)
        .into_iter()
        .map(|b| (b.name(), env.insert(b.name(), b.ty().clone())))
        .collect()
}

fn unbind_pattern(env: &mut TypeEnv, saved: Vec<(Sym, Option<CoreType>)>) {
    for (name, prev) in saved {
        restore(env, name, prev);
    }
}

fn pattern_binders(p: &TypedPattern) -> Vec<TypedBinder> {
    match p {
        TypedPattern::Wild => Vec::new(),
        TypedPattern::Var(b) => vec![b.clone()],
        TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
            fields.iter().flatten().cloned().collect()
        }
    }
}

// The source result type of a computation, needed to instantiate `Step` at a
// threading site. Only a source-typed result can ride a `Step` payload; a
// representation-only result (a thunk, a closure, a cell) would need the
// general lowering's uniform representation instead.
fn comp_result_type(c: &TypedComp) -> Option<Type> {
    match c.sig().result() {
        CoreType::Source(t) => Some(t.clone()),
        _ => None,
    }
}

impl Eraser {
    // Thread `Step` through a computation `c : T` so it yields `SMore(v : T)`
    // (no return fired) or `SDone(v : R)` (a `return v` is propagating), where
    // `R` is the enclosing FUNCTION's result type. The two payloads are
    // genuinely different types: a `return` inside a Unit-typed statement
    // still carries the function's result, which is why `Step` is a
    // two-parameter family. A representation-only result cannot ride a
    // payload, so it is left for the general lowering.
    fn thread_fn_return(
        &mut self,
        c: &TypedComp,
        env: &mut TypeEnv,
        done: &Type,
    ) -> Option<TypedComp> {
        // A loop (a bare `repeat_while`/`forever` spine, or a `break` loop)
        // the return crosses: drive it return-aware so an inner `SDone`
        // propagates out. The source loop's own result type is not this
        // call's `Step` result, so this must run before `comp_result_type(c)`
        // is read below.
        if let Some((call, rest)) = self.return_loop_call(c, env, done) {
            return Some(match rest {
                // The loop is the function tail: its `Step` is the result.
                None => call,
                // Code follows the loop: on normal/`break` exit (`SMore`) run
                // it; an inner `SDone` propagates.
                Some(r) => {
                    let cont = self.thread_fn_return(&r, env, done)?;
                    // The call's own Step instantiation, not a hardcoded
                    // `Step(Unit, done)`: a condition-less driver witnesses
                    // `done` itself (see `build_driver`), so the "more"
                    // payload type here tracks whichever `build_driver` chose.
                    let driver_at = step_at_of(&call)?;
                    let s = self.fresh.binder("s", driver_at.ty());
                    let w = self
                        .fresh
                        .binder("w", CoreType::Source(driver_at.more.clone()));
                    let guarded = self.guard_fn_return(&driver_at, &s, w, cont)?;
                    bind(call, s, guarded)
                }
            });
        }
        let more = comp_result_type(c)?;
        let at = StepAt::new(more, done.clone());
        match c.kind() {
            TypedCompKind::Do {
                operation, args, ..
            } if names::is_return_op(operation.as_str()) => {
                Some(value_return(at.sdone(ret_arg(args, done))))
            }
            TypedCompKind::Bind(m, x, n) => {
                if let TypedCompKind::Do {
                    operation, args, ..
                } = m.kind()
                {
                    if names::is_return_op(operation.as_str()) {
                        return Some(value_return(at.sdone(ret_arg(args, done))));
                    }
                }
                if signals_return(m) {
                    // A compound head (an `if`/`match`) that may return: bind
                    // its normal value, propagate an `SDone`.
                    let m_at = StepAt::new(comp_result_type(m)?, done.clone());
                    let mt = self.thread_fn_return(m, env, done)?;
                    let shadowed = env.insert(x.name(), x.ty().clone());
                    let cont = self.thread_fn_return(n, env, done);
                    restore(env, x.name(), shadowed);
                    let cont = cont?;
                    let s = self.fresh.binder("s", m_at.ty());
                    let guarded = self.guard_fn_return(&m_at, &s, x.clone(), cont)?;
                    Some(bind(mt, s, guarded))
                } else {
                    let m2 = self.erase(m, env);
                    let x2 = retype_bind_binder(&m2, x);
                    let shadowed = env.insert(x2.name(), x2.ty().clone());
                    let n2 = self.thread_fn_return(n, env, done);
                    restore(env, x2.name(), shadowed);
                    Some(bind(m2, x2, n2?))
                }
            }
            TypedCompKind::If(v, t, e) => {
                let t2 = self.thread_fn_return(t, env, done)?;
                let e2 = self.thread_fn_return(e, env, done)?;
                Some(if_then(v.clone(), t2, e2))
            }
            TypedCompKind::Case(v, arms) => {
                let mut out = Vec::with_capacity(arms.len());
                for (p, b) in arms {
                    let saved = bind_pattern(env, p);
                    let b2 = self.thread_fn_return(b, env, done);
                    unbind_pattern(env, saved);
                    out.push((p.clone(), b2?));
                }
                Some(case(v.clone(), out, &at))
            }
            // A tail that cannot return: its value is the normal result.
            _ if !signals_return(c) => {
                let c2 = self.erase(c, env);
                let r = self.fresh.binder("r", c2.sig().result().clone());
                let more = at.smore(binder_value(&r));
                Some(bind(c2, r, value_return(more)))
            }
            _ => None,
        }
    }

    // `case s of SMore(x) => cont | SDone(v) => SDone(v)`: bind the normal
    // result to `x` and continue, or propagate a `return`. The scrutinee and
    // the continuation sit at different `Step` instantiations (their `SMore`
    // payloads differ), so the propagating arm rebuilds at the continuation's.
    fn guard_fn_return(
        &mut self,
        scrutinee_at: &StepAt,
        s: &TypedBinder,
        x: TypedBinder,
        cont: TypedComp,
    ) -> Option<TypedComp> {
        let out_at = step_at_of(&cont)?;
        let v = self
            .fresh
            .binder("v", CoreType::Source(scrutinee_at.done.clone()));
        let done_arm = value_return(out_at.sdone(binder_value(&v)));
        Some(TypedComp::new(
            cont.sig().clone(),
            TypedCompKind::Case(
                binder_value(s),
                vec![
                    (scrutinee_at.more_pattern(x), cont),
                    (scrutinee_at.done_pattern(v), done_arm),
                ],
            ),
        ))
    }

    // Unwrap the `Step` at the function tail back to the bare result.
    fn seed_unwrap(&mut self, threaded: TypedComp, result: Option<&Type>) -> TypedComp {
        let Some(result) = result.cloned() else {
            return threaded;
        };
        let at = StepAt::new(result.clone(), result.clone());
        let ty = CoreType::Source(result);
        let fin = self.fresh.binder("fin", at.ty());
        let a = self.fresh.binder("a", ty.clone());
        let b = self.fresh.binder("b", ty.clone());
        let out_sig = CompSig::new(ty, threaded.sig().effects().clone());
        let body = TypedComp::new(
            out_sig,
            TypedCompKind::Case(
                binder_value(&fin),
                vec![
                    (at.more_pattern(a.clone()), value_return(binder_value(&a))),
                    (at.done_pattern(b.clone()), value_return(binder_value(&b))),
                ],
            ),
        );
        bind(threaded, fin, body)
    }

    // Thread the combined `Step(SMore(ctl), SDone(v))` disposition through a
    // loop body that a `return` crosses: `break`/`continue` ride
    // `SMore(2)`/`SMore(1)`, a `return` becomes `SDone(v)`, a normal end is
    // `SMore(0)`. Every successful result has type `Step(Int, done)`.
    fn thread_loop_combined(
        &mut self,
        c: &TypedComp,
        env: &mut TypeEnv,
        done: &Type,
    ) -> Option<TypedComp> {
        if let Some(inner) = match_continue(c) {
            return self.thread_loop_combined(inner, env, done);
        }
        let body_at = StepAt::new(Type::Int, done.clone());
        // A nested loop the return crosses: its own `break`/`continue` are
        // absorbed by its own driver, so to the enclosing loop it is just a
        // head yielding `Step` (`SMore` = it finished, `SDone` = a `return`
        // is propagating out through it).
        if let Some((call, rest)) = self.return_loop_call(c, env, done) {
            // The call's own Step instantiation, not a hardcoded
            // `Step(Unit, done)`: a condition-less nested driver witnesses
            // `done` itself (see `build_driver`), so the "more" payload type
            // here tracks whichever `build_driver` chose.
            let driver_at = step_at_of(&call)?;
            let s = self.fresh.binder("s", driver_at.ty());
            let w = self
                .fresh
                .binder("w", CoreType::Source(driver_at.more.clone()));
            return Some(match rest {
                // The nested loop is the enclosing body's tail: its normal
                // exit means this iteration completed (`ctl 0`); a `return`
                // propagates.
                None => {
                    let v = self.fresh.binder("v", CoreType::Source(done.clone()));
                    bind(
                        call,
                        s.clone(),
                        case(
                            binder_value(&s),
                            vec![
                                (
                                    driver_at.more_pattern(w),
                                    value_return(body_at.smore(ctl_value(normal()))),
                                ),
                                (
                                    driver_at.done_pattern(v.clone()),
                                    value_return(body_at.sdone(binder_value(&v))),
                                ),
                            ],
                            &body_at,
                        ),
                    )
                }
                Some(r) => {
                    let cont = self.thread_loop_combined(&r, env, done)?;
                    let guarded = self.guard_fn_return(&driver_at, &s, w, cont)?;
                    bind(call, s, guarded)
                }
            });
        }
        match c.kind() {
            TypedCompKind::Do {
                operation, args, ..
            } if names::is_return_op(operation.as_str()) => {
                Some(value_return(body_at.sdone(ret_arg(args, done))))
            }
            TypedCompKind::Do { operation, .. } => {
                ctl_signal(*operation).map(|v| value_return(body_at.smore(ctl_value(v))))
            }
            TypedCompKind::Bind(m, x, n) => {
                if let TypedCompKind::Do {
                    operation, args, ..
                } = m.kind()
                {
                    if names::is_return_op(operation.as_str()) {
                        return Some(value_return(body_at.sdone(ret_arg(args, done))));
                    }
                    if let Some(v) = ctl_signal(*operation) {
                        return Some(value_return(body_at.smore(ctl_value(v))));
                    }
                }
                if signals_loop(m) {
                    // The short-circuited tail drops `x`, so a use of it
                    // would observe a value the discarded continuation never
                    // bound.
                    if free_comp_vars(n).contains(&x.name()) {
                        return None;
                    }
                    let mt = self.thread_loop_combined(m, env, done)?;
                    let shadowed = env.insert(x.name(), x.ty().clone());
                    let rest = self.thread_loop_combined(n, env, done);
                    restore(env, x.name(), shadowed);
                    let rest = rest?;
                    let s = self.fresh.binder("s", body_at.ty());
                    let guarded = self.step_guard_combined(&body_at, &s, rest);
                    Some(bind(mt, s, guarded))
                } else {
                    let m2 = self.erase(m, env);
                    let x2 = retype_bind_binder(&m2, x);
                    let shadowed = env.insert(x2.name(), x2.ty().clone());
                    let n2 = self.thread_loop_combined(n, env, done);
                    restore(env, x2.name(), shadowed);
                    Some(bind(m2, x2, n2?))
                }
            }
            TypedCompKind::If(v, t, e) => {
                let t2 = self.thread_loop_combined(t, env, done)?;
                let e2 = self.thread_loop_combined(e, env, done)?;
                Some(if_then(v.clone(), t2, e2))
            }
            TypedCompKind::Case(v, arms) => {
                let mut out = Vec::with_capacity(arms.len());
                for (p, b) in arms {
                    let saved = bind_pattern(env, p);
                    let b2 = self.thread_loop_combined(b, env, done);
                    unbind_pattern(env, saved);
                    out.push((p.clone(), b2?));
                }
                Some(case(v.clone(), out, &body_at))
            }
            _ if !signals_loop(c) => {
                let c2 = self.erase(c, env);
                let u = self.fresh.binder("u", c2.sig().result().clone());
                Some(bind(
                    c2,
                    u,
                    value_return(body_at.smore(ctl_value(normal()))),
                ))
            }
            _ => None,
        }
    }

    // `case s of SMore(ctl) => if ctl == 0 then cont else SMore(ctl) | SDone(v)
    // => SDone(v)`: a `continue`/`break` short-circuits the body carrying its
    // disposition; a `return` propagates. `s` and `cont` share `at`; only
    // `cont`'s side of the disjunction actually needs it (the propagating arm
    // rebuilds from `s`'s own `done` witness, which is the same `at.done`).
    fn step_guard_combined(&mut self, at: &StepAt, s: &TypedBinder, cont: TypedComp) -> TypedComp {
        let ctl = self.fresh.binder("ctl", CoreType::Source(Type::Int));
        let t = self.fresh.binder("t", CoreType::Source(Type::Bool));
        let v = self.fresh.binder("v", CoreType::Source(at.done.clone()));
        let eq = prim_eq(binder_value(&ctl), ctl_value(normal()));
        let smore_arm = bind(
            eq,
            t.clone(),
            if_then(
                binder_value(&t),
                cont,
                value_return(at.smore(binder_value(&ctl))),
            ),
        );
        case(
            binder_value(s),
            vec![
                (at.more_pattern(ctl), smore_arm),
                (
                    at.done_pattern(v.clone()),
                    value_return(at.sdone(binder_value(&v))),
                ),
            ],
            at,
        )
    }

    // Recognize a loop that a `return` crosses (its body performs
    // `do fn@return`), build a return-aware driver for it, and return the
    // driver call (yielding `Step(Unit, done)`) together with the
    // continuation after the loop (`None` when the loop is the tail). Covers
    // a bare `repeat_while`/`forever` spine and a `break` loop (its handler
    // wrapping the driver call), as a tail or a statement head. Mints
    // nothing itself; every mint comes from the called `build_driver`.
    fn return_loop_call(
        &mut self,
        c: &TypedComp,
        env: &mut TypeEnv,
        done: &Type,
    ) -> Option<(TypedComp, Option<TypedComp>)> {
        // A bare `repeat_while`/`forever` spine.
        if let Some((cond, body, rest)) = peel_loop_spine(c) {
            if signals_return(&body) {
                let call = self.build_driver(cond.as_ref(), &body, env, Some(done))?;
                return Some((call, rest));
            }
        }
        // A `break` loop as a statement head, with code following it.
        if let TypedCompKind::Bind(m, w, rest) = c.kind() {
            if let Some((cond, body)) = match_break(m) {
                if signals_return(&body) {
                    // The loop's Unit result must be discarded (bound to an
                    // unused binder).
                    if free_comp_vars(rest).contains(&w.name()) {
                        return None;
                    }
                    let call = self.build_driver(Some(&cond), &body, env, Some(done))?;
                    return Some((call, Some(rest.as_ref().clone())));
                }
            }
        }
        // A `break` loop as the tail.
        if let Some((cond, body)) = match_break(c) {
            if signals_return(&body) {
                let call = self.build_driver(Some(&cond), &body, env, Some(done))?;
                return Some((call, None));
            }
        }
        None
    }
}

// The value `do fn@return(v)` carries (its single argument), or unit when the
// return is valueless.
fn ret_arg(args: &[TypedValue], result: &Type) -> TypedValue {
    args.first()
        .cloned()
        .unwrap_or_else(|| TypedValue::new(CoreType::Source(result.clone()), TypedValueKind::Unit))
}

fn value_return(v: TypedValue) -> TypedComp {
    TypedComp::new(
        CompSig::new(v.ty().clone(), EffRow::Empty),
        TypedCompKind::Return(v),
    )
}

fn binder_value(b: &TypedBinder) -> TypedValue {
    TypedValue::new(
        b.ty().clone(),
        TypedValueKind::Var {
            name: b.name(),
            instantiation: Vec::new(),
        },
    )
}

// `Bind` with the verified sig-construction rule: the continuation's result
// over the children's row union.
fn bind(first: TypedComp, binder: TypedBinder, rest: TypedComp) -> TypedComp {
    let sig = CompSig::new(
        rest.sig().result().clone(),
        super::union_effects(first.sig().effects(), rest.sig().effects()),
    );
    TypedComp::new(
        sig,
        TypedCompKind::Bind(Box::new(first), binder, Box::new(rest)),
    )
}

fn if_then(cond: TypedValue, t: TypedComp, e: TypedComp) -> TypedComp {
    let sig = CompSig::new(
        t.sig().result().clone(),
        super::union_effects(t.sig().effects(), e.sig().effects()),
    );
    TypedComp::new(sig, TypedCompKind::If(cond, Box::new(t), Box::new(e)))
}

fn case(scrutinee: TypedValue, arms: Vec<(TypedPattern, TypedComp)>, at: &StepAt) -> TypedComp {
    case_of(scrutinee, arms, &at.ty())
}

// `case`'s general form: the empty-arms fallback result type is supplied
// directly rather than derived from a `Step` instantiation, so `descend`'s
// generic `Case` arm (whose scrutinee is not necessarily `Step`-typed) can
// reuse the same sig-recomputation rule.
fn case_of(
    scrutinee: TypedValue,
    arms: Vec<(TypedPattern, TypedComp)>,
    fallback: &CoreType,
) -> TypedComp {
    let result = arms
        .first()
        .map_or_else(|| fallback.clone(), |(_, b)| b.sig().result().clone());
    let effects = arms.iter().fold(EffRow::Empty, |acc, (_, b)| {
        super::union_effects(&acc, b.sig().effects())
    });
    TypedComp::new(
        CompSig::new(result, effects),
        TypedCompKind::Case(scrutinee, arms),
    )
}

// The `Step` instantiation a threaded computation's result witnesses, when it
// is one.
fn step_at_of(c: &TypedComp) -> Option<StepAt> {
    match c.sig().result() {
        CoreType::Source(Type::Con(name, args)) if name.as_str() == STEP && args.len() == 2 => {
            Some(StepAt::new(args[0].clone(), args[1].clone()))
        }
        _ => None,
    }
}

impl Eraser {
    // Thread `ctl : Int` through a Unit-valued loop body so it yields `0` (ran
    // to the end), `1` (`continue`), or `2` (`break`). Each is an immediate,
    // so no per-iteration heap. `None` for a shape it cannot thread (control
    // captured in a closure, or whose discarded value is used).
    fn thread_ctl(&mut self, c: &TypedComp, env: &mut TypeEnv) -> Option<TypedComp> {
        if let Some(inner) = match_continue(c) {
            return self.thread_ctl(inner, env);
        }
        match c.kind() {
            TypedCompKind::Do { operation, .. } => ctl_signal(*operation).map(ctl_return),
            TypedCompKind::Bind(m, x, n) => {
                if let TypedCompKind::Do { operation, .. } = m.kind() {
                    if let Some(v) = ctl_signal(*operation) {
                        return Some(ctl_return(v));
                    }
                }
                if signals_ctl(m) {
                    // The short-circuited tail drops `x`, so a use of it would
                    // observe a value the discarded continuation never bound.
                    if free_comp_vars(n).contains(&x.name()) {
                        return None;
                    }
                    let mt = self.thread_ctl(m, env)?;
                    let shadowed = env.insert(x.name(), x.ty().clone());
                    let rest = self.thread_ctl(n, env);
                    restore(env, x.name(), shadowed);
                    let rest = rest?;
                    let ctl = self.fresh.binder("ctl", CoreType::Source(Type::Int));
                    let guarded = self.step_guard_int(&ctl, rest);
                    Some(bind(mt, ctl, guarded))
                } else {
                    let m2 = self.erase(m, env);
                    let x2 = retype_bind_binder(&m2, x);
                    let shadowed = env.insert(x2.name(), x2.ty().clone());
                    let n2 = self.thread_ctl(n, env);
                    restore(env, x2.name(), shadowed);
                    Some(bind(m2, x2, n2?))
                }
            }
            TypedCompKind::If(v, t, e) => {
                let t2 = self.thread_ctl(t, env)?;
                let e2 = self.thread_ctl(e, env)?;
                Some(if_then(v.clone(), t2, e2))
            }
            TypedCompKind::Case(v, arms) => {
                let mut out = Vec::with_capacity(arms.len());
                for (p, b) in arms {
                    let saved = bind_pattern(env, p);
                    let b2 = self.thread_ctl(b, env);
                    unbind_pattern(env, saved);
                    out.push((p.clone(), b2?));
                }
                Some(int_case(v.clone(), out))
            }
            _ if !signals_ctl(c) => {
                let c2 = self.erase(c, env);
                let u = self.fresh.binder("u", c2.sig().result().clone());
                Some(bind(c2, u, ctl_return(normal())))
            }
            _ => None,
        }
    }

    // A non-zero `ctl` (a `continue`/`break`) short-circuits, returning `ctl`;
    // a normal result (`ctl == 0`) runs `cont`.
    fn step_guard_int(&mut self, ctl: &TypedBinder, cont: TypedComp) -> TypedComp {
        let t = self.fresh.binder("t", CoreType::Source(Type::Bool));
        let eq = prim_eq(binder_value(ctl), ctl_value(normal()));
        let branch = if_then(binder_value(&t), cont, value_return(binder_value(ctl)));
        bind(eq, t, branch)
    }

    // `ctl == 2` (break) exits; `0`/`1` (normal/continue) tail-loop.
    fn int_dispatch(&mut self, threaded: TypedComp, self_call: TypedComp) -> TypedComp {
        let ctl = self.fresh.binder("ctl", CoreType::Source(Type::Int));
        let z = self.fresh.binder("z", CoreType::Source(Type::Bool));
        let eq = prim_eq(binder_value(&ctl), ctl_value(breaks()));
        let exit = value_return(unit_value_typed());
        let dispatch = bind(eq, z.clone(), if_then(binder_value(&z), exit, self_call));
        bind(threaded, ctl, dispatch)
    }

    // `case s of SMore(ctl) => if ctl == 2 then SMore(unit) else self-call |
    // SDone(v) => SDone(v)`: a `break` exits the loop normally (`SMore`), a
    // `return` propagates outward (`SDone`). `threaded : body_at.ty()`
    // (`Step(Int, done)`), result `driver_at.ty()` (`Step(Unit, done)`).
    fn combined_dispatch(
        &mut self,
        body_at: &StepAt,
        driver_at: &StepAt,
        threaded: TypedComp,
        self_call: TypedComp,
    ) -> TypedComp {
        let s = self.fresh.binder("s", body_at.ty());
        let ctl = self.fresh.binder("ctl", CoreType::Source(Type::Int));
        let z = self.fresh.binder("z", CoreType::Source(Type::Bool));
        let v = self
            .fresh
            .binder("v", CoreType::Source(driver_at.done.clone()));
        let eq = prim_eq(binder_value(&ctl), ctl_value(breaks()));
        let smore_arm = bind(
            eq,
            z.clone(),
            if_then(
                binder_value(&z),
                value_return(driver_at.smore(unit_value_typed())),
                self_call,
            ),
        );
        let done_arm = value_return(driver_at.sdone(binder_value(&v)));
        bind(
            threaded,
            s.clone(),
            case(
                binder_value(&s),
                vec![
                    (body_at.more_pattern(ctl), smore_arm),
                    (body_at.done_pattern(v), done_arm),
                ],
                driver_at,
            ),
        )
    }

    // `case s of SMore(ctl) => self-call | SDone(v) => SDone(v)`: the
    // return-aware driver for a bare `forever` spine with no `break` and no
    // `while` condition in source (`build_driver` only calls this when
    // `cond.is_none()` reached it through the unwrapped loop spine, never
    // through `match_break`, so the break tag `combined_dispatch` guards
    // against cannot occur here; every `SMore` is a `continue` and always
    // tail-loops, so this dispatch never actually constructs an `SMore`
    // value). The typed verifier distinguishes that unreachable case, so
    // `driver_at` here is `StepAt::new(done, done)`, not
    // `StepAt::new(Unit, done)`: since `SMore` is never actually witnessed
    // by a value, the driver is free to instantiate it at `done` instead of
    // `Unit`, which costs nothing and matches the `Step(R, R)` convention
    // `seed_unwrap` already assumes. `threaded : body_at.ty()` (`Step(Int,
    // done)`), result `driver_at.ty()` (`Step(done, done)`).
    fn never_breaks_dispatch(
        &mut self,
        body_at: &StepAt,
        driver_at: &StepAt,
        threaded: TypedComp,
        self_call: TypedComp,
    ) -> TypedComp {
        let s = self.fresh.binder("s", body_at.ty());
        let ctl = self.fresh.binder("ctl", CoreType::Source(Type::Int));
        let v = self
            .fresh
            .binder("v", CoreType::Source(driver_at.done.clone()));
        let done_arm = value_return(driver_at.sdone(binder_value(&v)));
        bind(
            threaded,
            s.clone(),
            case(
                binder_value(&s),
                vec![
                    (body_at.more_pattern(ctl), self_call),
                    (body_at.done_pattern(v), done_arm),
                ],
                driver_at,
            ),
        )
    }
}

// `a == b` over immediates, with the pure sig the verified `Prim` rule gives.
const fn prim_eq(a: TypedValue, b: TypedValue) -> TypedComp {
    TypedComp::new(
        CompSig::new(CoreType::Source(Type::Bool), EffRow::Empty),
        TypedCompKind::Prim(crate::core::CoreOp::Eq, a, b),
    )
}

const fn unit_value_typed() -> TypedValue {
    TypedValue::new(CoreType::Source(Type::Unit), TypedValueKind::Unit)
}

// A `case` whose arms all yield the threaded `ctl : Int`.
fn int_case(scrutinee: TypedValue, arms: Vec<(TypedPattern, TypedComp)>) -> TypedComp {
    let effects = arms.iter().fold(EffRow::Empty, |acc, (_, b)| {
        super::union_effects(&acc, b.sig().effects())
    });
    TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), effects),
        TypedCompKind::Case(scrutinee, arms),
    )
}

impl Eraser {
    // Emit a fresh tail-recursive driver for a recognized loop and return the
    // call that replaces it. The driver inlines the condition and the threaded
    // body, closing over the loop's free variables (the erased `var` cells and
    // captured params) as parameters, so its self-call is a plain tail `Call`
    // (codegen `musttail`, constant native stack). Each captured variable's
    // parameter type comes from the threaded typing context; a variable missing
    // from it means the region was not fully typed, so the loop is left for the
    // general lowering.
    // `return_done`: `None` for an ordinary `break`/`continue`-only driver
    // (result `Unit`, `int_dispatch`, exit `Unit`); `Some(done)` for a
    // return-aware driver a `return` crosses. Among return-aware drivers,
    // `cond.is_some()` (a `repeat_while` spine, reachable break) uses
    // `combined_dispatch` (result `Step(Unit, done)`, exit `SMore(Unit)`);
    // `cond.is_none()` (a bare `forever` spine, which only reaches here
    // unwrapped, so it provably has no `break`) uses `never_breaks_dispatch`
    // (result `Step(done, done)`, `exit` unused).
    fn build_driver(
        &mut self,
        cond: Option<&TypedComp>,
        body: &TypedComp,
        env: &mut TypeEnv,
        return_done: Option<&Type>,
    ) -> Option<TypedComp> {
        // Threading may emit nested drivers; on a bail, drop them so no orphan
        // function is left in the program.
        let mark = self.generated.len();
        let condition = match cond {
            Some(c) => {
                if let Some(c) = self.prepare_driver_condition(c, env) {
                    Some(c)
                } else {
                    self.generated.truncate(mark);
                    return None;
                }
            }
            None => None,
        };
        let threaded = match return_done {
            Some(done) => self.thread_loop_combined(body, env, done),
            None => self.thread_ctl(body, env),
        };
        let Some(threaded) = threaded else {
            self.generated.truncate(mark);
            return None;
        };

        let mut set = free_comp_vars(&threaded);
        if let Some(c) = &condition {
            set.extend(free_comp_vars(c));
        }
        // Deterministic parameter order by name keeps the generated signature
        // byte-stable.
        let mut names: Vec<Sym> = set.into_iter().collect();
        names.sort_by(|a, b| a.as_str().cmp(b.as_str()));
        // A name with no type here is a top-level function reference, not a
        // captured local; those are called, never passed.
        let params: Vec<TypedBinder> = names
            .iter()
            .filter_map(|n| env.get(n).map(|t| TypedBinder::new(*n, t.clone())))
            .collect();
        if params.len() != names.len() {
            let bound: BTreeSet<Sym> = params.iter().map(TypedBinder::name).collect();
            // Only a global (a name this program defines at the top level) may
            // be free without a local type; anything else is unaccounted for.
            if names
                .iter()
                .any(|n| !bound.contains(n) && !self.globals.contains(n))
            {
                self.generated.truncate(mark);
                return None;
            }
        }
        // The generated driver mints no quantifiers of its own
        // (`CoreFnSig::new(Vec::new(), ...)` below), so every captured type and
        // effect row must already be closed. Return-aware drivers additionally
        // carry `done` as a Step witness. Decline rather than orphan an active
        // variable in either the row tail or an effect-label argument.
        let driver_effects = condition.as_ref().map_or_else(
            || threaded.sig().effects().clone(),
            |c| super::union_effects(threaded.sig().effects(), c.sig().effects()),
        );
        let active = return_done.is_some_and(type_has_active_var)
            || params.iter().any(|p| core_type_has_active_var(p.ty()))
            || row_has_active_var(&driver_effects);
        if active {
            self.generated.truncate(mark);
            return None;
        }
        let args: Vec<TypedValue> = params.iter().map(binder_value).collect();

        let drv = self.fresh.binder("loopdrv", CoreType::Source(Type::Unit));
        // A `repeat_while` spine's normal exit (the condition goes false) is
        // a genuine `Unit`-carrying `SMore`, so its driver witnesses
        // `Step(Unit, done)`. A bare `forever` spine (`cond.is_none()`) never
        // constructs an `SMore` value at all (see `never_breaks_dispatch`:
        // its `SMore` arm is a tail self-call, not a value), so it is free
        // to witness `SMore` at `done` itself instead of `Unit`, giving it
        // the same `Step(R, R)` instantiation every non-loop return-aware
        // tail already uses. That lets `seed_unwrap`/`guard_fn_return`
        // (which unwrap by the function's own result type) treat it with no
        // separate case.
        let (result, exit, self_call_ty, driver_at) = match return_done {
            Some(done) if condition.is_none() => {
                let at = StepAt::new(done.clone(), done.clone());
                (at.ty(), value_return(unit_value_typed()), at.ty(), Some(at))
            }
            Some(done) => {
                let at = StepAt::new(Type::Unit, done.clone());
                (
                    at.ty(),
                    value_return(at.smore(unit_value_typed())),
                    at.ty(),
                    Some(at),
                )
            }
            None => (
                CoreType::Source(Type::Unit),
                value_return(unit_value_typed()),
                CoreType::Source(Type::Unit),
                None,
            ),
        };
        // The recursive call witnesses the complete generated-driver row.
        // Conditions are currently required to be exactly pure, but retaining
        // the explicit union here prevents the call and callee signatures from
        // diverging if that conservative restriction is relaxed later.
        let body_sig = CompSig::new(self_call_ty, driver_effects);
        let self_call = TypedComp::new(
            body_sig,
            TypedCompKind::Call {
                callee: drv.name(),
                instantiation: Vec::new(),
                args: args.clone(),
            },
        );
        let dispatch = match (return_done, &driver_at) {
            (Some(done), Some(driver_at)) => {
                let body_at = StepAt::new(Type::Int, done.clone());
                if condition.is_none() {
                    self.never_breaks_dispatch(&body_at, driver_at, threaded, self_call)
                } else {
                    self.combined_dispatch(&body_at, driver_at, threaded, self_call)
                }
            }
            _ => self.int_dispatch(threaded, self_call),
        };
        let drv_body = match condition {
            Some(c) => {
                let b = self.fresh.binder("b", CoreType::Source(Type::Bool));
                bind(c, b.clone(), if_then(binder_value(&b), dispatch, exit))
            }
            None => dispatch,
        };
        let sig = CoreFnSig::new(
            Vec::new(),
            params.iter().map(|p| p.ty().clone()).collect(),
            CompSig::new(result, drv_body.sig().effects().clone()),
        );
        self.generated.push(TypedCoreFn::new(
            drv.name(),
            params,
            drv_body,
            sig.clone(),
            0,
        ));
        Some(TypedComp::new(
            sig.body().clone(),
            TypedCompKind::Call {
                callee: drv.name(),
                instantiation: Vec::new(),
                args,
            },
        ))
    }
}

/// Recognize the `break` handler template the desugar wraps around the loop
/// driver, returning the inlined condition and body (the body with its own
/// `continue` wrapper peeled, since this loop's `continue` threads into the
/// same `ctl`).
pub(super) fn match_break(c: &TypedComp) -> Option<(TypedComp, TypedComp)> {
    let TypedCompKind::Handle { body, ops, .. } = c.kind() else {
        return None;
    };
    let [op] = ops.arms() else {
        return None;
    };
    if !names::is_break_op(op.name().as_str()) {
        return None;
    }
    let (cond, body, _) = peel_loop_spine(body)?;
    cond.map(|cond| (cond, body))
}

/// Recognize a bare `repeat_while`/`forever` loop spine (the thunk binds plus
/// the trailing driver call), returning the inlined condition (`None` for
/// `forever`), the body, and the continuation after the loop (`None` when the
/// loop is the tail).
fn peel_loop_spine(c: &TypedComp) -> Option<(Option<TypedComp>, TypedComp, Option<TypedComp>)> {
    let mut thunks: BTreeMap<Sym, TypedComp> = BTreeMap::new();
    let mut cur = c;
    loop {
        match cur.kind() {
            TypedCompKind::Bind(m, t, rest) if nullary_thunk(m).is_some() => {
                thunks.insert(t.name(), nullary_thunk(m)?.clone());
                cur = rest;
            }
            // The loop call followed by more code.
            TypedCompKind::Bind(call, w, rest) if is_loop_call(call) => {
                let (cond, body) = resolve_loop_call(call, &thunks)?;
                // The loop's Unit result is bound to `w`; it must be discarded.
                if free_comp_vars(rest).contains(&w.name()) {
                    return None;
                }
                return Some((cond, body, Some(rest.as_ref().clone())));
            }
            // The loop call as the tail.
            _ if is_loop_call(cur) => {
                let (cond, body) = resolve_loop_call(cur, &thunks)?;
                return Some((cond, body, None));
            }
            _ => return None,
        }
    }
}

fn is_loop_call(c: &TypedComp) -> bool {
    matches!(c.kind(), TypedCompKind::Call { callee, .. } if is_loop_driver(*callee))
}

// Resolve a `repeat_while(tc, tb)`/`forever(tb)` call against the peeled
// thunks to the inlined condition (`None` for `forever`) and body (continue
// wrapper peeled).
fn resolve_loop_call(
    c: &TypedComp,
    thunks: &BTreeMap<Sym, TypedComp>,
) -> Option<(Option<TypedComp>, TypedComp)> {
    let TypedCompKind::Call { callee, args, .. } = c.kind() else {
        return None;
    };
    if callee.as_str() == REPEAT_WHILE {
        let [tc, tb] = args.as_slice() else {
            return None;
        };
        let cond = thunks.get(&as_var(tc)?)?.clone();
        let body = peel_continue(thunks.get(&as_var(tb)?)?.clone());
        Some((Some(cond), body))
    } else {
        let [tb] = args.as_slice() else {
            return None;
        };
        let body = peel_continue(thunks.get(&as_var(tb)?)?.clone());
        Some((None, body))
    }
}

fn peel_continue(body: TypedComp) -> TypedComp {
    match_continue(&body).cloned().unwrap_or(body)
}

// The body of `return thunk { \. body }` (a nullary-lambda thunk), or `None`.
// Declines a quantified Lam: inlining its body into a generated driver would
// drop the Lam's own `CoreFnSig` quantifiers, orphaning any rigid variable
// the body still mentions (a driver mints no quantifiers of its own).
fn nullary_thunk(m: &TypedComp) -> Option<&TypedComp> {
    let TypedCompKind::Return(v) = m.kind() else {
        return None;
    };
    let TypedValueKind::Thunk(t) = &super::peel(v).kind else {
        return None;
    };
    if let CoreType::Function(fn_sig) = t.sig().result() {
        if !fn_sig.quantifiers().is_empty() {
            return None;
        }
    }
    match t.kind() {
        TypedCompKind::Lam(ps, b) if ps.is_empty() => Some(b),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::verify::verify;
    use super::super::super::Elaborated;
    use super::super::super::{CoreFnSig, TypedCore, TypedCoreFn};
    use super::*;

    fn test_eraser() -> Eraser {
        Eraser {
            fresh: ControlFresh::new(),
            generated: Vec::new(),
            used_step: false,
            foreign: BTreeSet::new(),
            globals: BTreeSet::new(),
        }
    }

    // The `Step` family the control and state paths share must verify as a
    // two-parameter scheme: combined threading mixes `SMore(Int)` with
    // `SDone(R)` in one match, so a single-parameter `Step` could not witness
    // both arms of the same scrutinee.
    #[test]
    fn step_constructors_verify_at_mixed_payloads() {
        let mut env = VerifyEnv::new();
        insert_step_constructors(&mut env);
        let at = StepAt::new(Type::Int, Type::Str);
        let more = at.smore(ctl_value(normal()));
        let done = at.sdone(TypedValue::new(
            CoreType::Source(Type::Str),
            TypedValueKind::Str("done".into()),
        ));
        assert_eq!(more.ty(), done.ty(), "both arms witness one Step type");

        // `case s of SMore(c) => 0 | SDone(v) => 1`: the scrutinee's witness is
        // the shared `Step(Int, Str)` and each arm binds its own payload type.
        let scrutinee = TypedBinder::new(Sym::new("s"), at.ty());
        let body = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Case(
                TypedValue::new(
                    at.ty(),
                    TypedValueKind::Var {
                        name: scrutinee.name(),
                        instantiation: Vec::new(),
                    },
                ),
                vec![
                    (
                        at.more_pattern(TypedBinder::new(
                            Sym::new("c"),
                            CoreType::Source(Type::Int),
                        )),
                        ctl_return(normal()),
                    ),
                    (
                        at.done_pattern(TypedBinder::new(
                            Sym::new("v"),
                            CoreType::Source(Type::Str),
                        )),
                        ctl_return(breaks()),
                    ),
                ],
            ),
        );
        let f = TypedCoreFn::new(
            Sym::new("main"),
            vec![scrutinee],
            body,
            CoreFnSig::new(
                Vec::new(),
                vec![at.ty()],
                CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            ),
            0,
        );
        if let Err(violations) = verify(&TypedCore::<Elaborated>::new(vec![f]), &env) {
            panic!("mixed-payload Step must verify: {violations:#?}");
        }
    }

    // A drift in the runtime encoding would silently change which branch a
    // driver takes.
    #[test]
    fn control_dispositions_pin_the_runtime_encoding() {
        assert_eq!((normal(), continues(), breaks()), (0, 1, 2));
    }

    #[test]
    fn active_variables_in_effect_label_arguments_are_not_closed() {
        let a = Sym::new("a");
        let open_arg = EffRow::Extend(
            crate::types::ty::Label {
                name: Sym::new("E"),
                args: vec![Type::Var(a)],
            },
            Box::new(EffRow::Empty),
        );
        let closed_arg = EffRow::Extend(
            crate::types::ty::Label {
                name: Sym::new("E"),
                args: vec![Type::Int],
            },
            Box::new(EffRow::Empty),
        );

        assert!(row_has_active_var(&open_arg));
        assert!(!row_has_active_var(&closed_arg));
    }

    #[test]
    fn guard_fn_return_declines_a_non_step_continuation() {
        let mut eraser = test_eraser();
        let at = StepAt::new(Type::Int, Type::Str);
        let s = TypedBinder::new(Sym::new("s"), at.ty());
        let x = TypedBinder::new(Sym::new("x"), CoreType::Source(Type::Int));
        let non_step = ctl_return(normal());

        assert!(eraser.guard_fn_return(&at, &s, x, non_step).is_none());
    }

    #[test]
    fn non_signalling_bind_retypes_its_binder_and_occurrences() {
        let stale = TypedBinder::new(Sym::new("x"), CoreType::Source(Type::Unit));
        let rewritten_head = ctl_return(normal());
        let refreshed = retype_bind_binder(&rewritten_head, &stale);
        assert_eq!(refreshed.name(), stale.name());
        assert_eq!(refreshed.ty(), &CoreType::Source(Type::Int));

        let mut eraser = test_eraser();
        let mut env = TypeEnv::new();
        env.insert(refreshed.name(), refreshed.ty().clone());
        let occurrence = eraser.erase_value(&binder_value(&stale), &mut env);
        assert_eq!(occurrence.ty(), refreshed.ty());
    }

    #[test]
    fn row_polymorphic_local_keeps_its_instantiated_use_witness() {
        let row = Sym::new("e");
        let thunk = |quantifiers, effects| {
            CoreType::Thunk(Box::new(CompSig::new(
                CoreType::Function(Box::new(CoreFnSig::new(
                    quantifiers,
                    vec![CoreType::Source(Type::Int)],
                    CompSig::new(CoreType::Source(Type::Int), effects),
                ))),
                EffRow::Empty,
            )))
        };
        let scheme = thunk(vec![CoreQuantifier::Row(row)], EffRow::Var(row));
        let instance = thunk(Vec::new(), EffRow::Empty);
        let parameter = TypedBinder::new(Sym::new("h"), scheme.clone());
        let local = TypedBinder::new(Sym::new("t"), scheme.clone());
        let instantiated_local = TypedValue::new(
            instance.clone(),
            TypedValueKind::Var {
                name: local.name(),
                instantiation: vec![CoreInstantiation::Row(EffRow::Empty)],
            },
        );
        let result = TypedValue::new(
            instance.clone(),
            TypedValueKind::Reinterpret(Box::new(instantiated_local)),
        );
        let tail = TypedComp::new(
            CompSig::new(instance.clone(), EffRow::Empty),
            TypedCompKind::Return(result),
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
        let function = TypedCoreFn::new(
            Sym::new("row_poly"),
            vec![parameter],
            body,
            CoreFnSig::new(
                Vec::new(),
                vec![scheme],
                CompSig::new(instance, EffRow::Empty),
            ),
            0,
        );
        let env = VerifyEnv::new();
        let input = TypedCore::<Elaborated>::new(vec![function]);
        assert_eq!(verify(&input, &env), Ok(()));

        let erased = erase_control(input.functions());
        let output = TypedCore::<Elaborated>::new(erased.fns);
        assert_eq!(verify(&output, &env), Ok(()));
        assert_eq!(output.erase(), input.erase());
    }

    #[test]
    fn generated_driver_conditions_decline_control_and_effects() {
        let pure = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Bool), EffRow::Empty),
            TypedCompKind::Return(TypedValue::new(
                CoreType::Source(Type::Bool),
                TypedValueKind::Bool(true),
            )),
        );
        let returning = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Bool), EffRow::Empty),
            TypedCompKind::Do {
                operation: Sym::new(names::RETURN_OP),
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let effectful = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Bool), EffRow::singleton("E")),
            TypedCompKind::Do {
                operation: Sym::new("E.ask"),
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let mut eraser = test_eraser();
        let mut env = TypeEnv::new();

        assert!(eraser.prepare_driver_condition(&pure, &mut env).is_some());
        assert!(eraser
            .prepare_driver_condition(&returning, &mut env)
            .is_none());
        assert!(eraser
            .prepare_driver_condition(&effectful, &mut env)
            .is_none());
    }
}
