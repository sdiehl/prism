use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use marginalia::Span;
use num_bigint::Sign;

use super::builtins::{builtin, Builtin, BuiltinKind, FloatOp, BUILTINS};
use super::cbpv::{
    CheckedHandler, Comp, Core, CoreFn, CoreOp, CorePat, ElaboratedCore, HandleOp, IoOp, NegLane,
    Value,
};
use super::typed::{
    build_typed, build_verify_env, core_fn_sig, dict_type, Elaborated as TypedElaborated,
    TypedCore, VerifyEnv,
};
use super::{verify_typed_core, CoreFnSig};
use crate::hir::{self, CheckedHir, NodeFacts, NodeRes};
use crate::types::ty::EffRow;
use crate::types::{
    infer_expr_env, Checked, CtorInfo, Dict, Env, FieldRef, NominalRepr, Type, CONS, DIV_CLASS,
    EQ_CLASS, LIST, NIL, NUM_CLASS, ORD_CLASS, SHOW_CLASS,
};
use crate::wired::Indexable;
use prism_common::fresh::Fresh;
use prism_common::sym::Sym;
use prism_syntax::ast::{
    Arm, BigInt, BinOp, Core as CorePhase, Expr, HandlerArm, IntLit, NodeId, PathOp, PathStep,
    Pattern, Program, Spanned, Suffix, S,
};
use prism_syntax::error::{
    Error, TypeError, TypedCoreConstructionFailure, TypedCoreErasureFailure,
    TypedCoreVerificationFailure, TypedCoreViolation,
};
use prism_syntax::names::{
    self, dict_ctor, instance_method, DIV_MOD_METHOD, DIV_QUOT_METHOD, EQ_METHOD, NUM_ADD_METHOD,
    NUM_FROMINT_METHOD, NUM_MUL_METHOD, NUM_NEG_METHOD, NUM_SUB_METHOD, ORD_METHOD,
};

mod dict;
mod expr;
mod match_compile;
mod show;

struct Elab<'a> {
    fresh: Fresh,
    ctors: &'a BTreeMap<String, CtorInfo>,
    arity: BTreeMap<String, usize>,
    // Top-level constants, keyed by name. A reference inlines the RHS rather
    // than calling, so a constant pushes no frame.
    consts: BTreeMap<String, &'a S<Expr<CorePhase>>>,
    // The local analogue of `consts`: type-polymorphic `let` values in scope,
    // keyed by name. A use of one of these expands the value rather than reading
    // a binding; see `Expansion`.
    expansion: ExpansionMap,
    checked: &'a Checked,
    // The checked HIR: the only view of per-node semantic facts. Whole programs
    // use `checked`'s facts; re-inferred REPL expressions supply a complete,
    // independent fact artifact so colliding numeric ids cannot fall through.
    hir: CheckedHir<'a>,
    effect_ops: BTreeSet<String>,
    // True when the `Output` capability is in scope (the prelude declares it), so
    // `print`/`println` route through the interceptable `out_print`/`out_println`
    // ops. A prelude-free program has no `Output` handler, so it prints directly.
    route_output: bool,
    show_fns: Vec<CoreFn>,
    show_sigs: BTreeMap<Sym, CoreFnSig>,
    show_seen: BTreeSet<String>,
    // True when the expression and every HIR fact came from the same check pass.
    strict: bool,
}

// Persistent, so the per-binder scope extension at every `let`, lambda, and
// match arm clones in O(1) by structural sharing instead of deep-copying the
// whole visible scope (which made elaborating an n-binder body O(n^2)).
// Iteration stays name-ordered exactly like the `BTreeMap` it replaced, so the
// positional shadow sentinels in `local_env` are unchanged.
type Locals = im::OrdMap<String, Option<Type>>;

// A local `let` whose value the checker generalized over at least one type.
// Core's `Bind` binds one monotype, so no bind is emitted for such a binding:
// each use re-elaborates the value instead, in the scope the value was written
// in, which is what is captured here. Only a locally-closed syntactic value is
// ever recorded (the checker's admission rule), so the copies duplicate no
// effect and no identity, differ in nothing but the types checking gave each
// use, and carry no free reference to an enclosing local that a binder between
// the `let` and a use could capture: every free variable resolves top-level.
struct Expansion {
    value: S<Expr<CorePhase>>,
    locals: Locals,
    // The expansion map as it stood at the binding, which excludes this binder:
    // a same-named outer binding inside the value resolves outward, so
    // re-elaboration cannot reenter itself.
    snapshot: ExpansionMap,
}

// Persistent and reference-counted for the reason `Locals` is persistent: every
// binder scopes its shadowing by cloning the map.
type ExpansionMap = im::OrdMap<String, Rc<Expansion>>;

// Red zone / segment size for the elaboration recursion, matching the typed-Core
// builder's constants (`core/typed/build.rs`).
const MEBIBYTE: usize = 1024 * 1024;
const ELAB_MIN_STACK: usize = 4 * MEBIBYTE;
const ELAB_GROW_STACK: usize = 8 * MEBIBYTE;

// The pointed error for the not-yet-lowered unboxed-values surface, shared by the
// elaborator's exhaustive-match backstop. The typechecker rejects these first
// (E1018); this only fires if that ordering ever changes.
fn unboxed_unsupported(span: Span) -> Error {
    prism_syntax::error::ErrKind::UnboxedUnsupported {
        what: "values".into(),
    }
    .at(span)
    .into()
}

fn row_mentions_effect(row: &EffRow, effect: &str) -> bool {
    match row {
        EffRow::Extend(label, rest) => {
            label.name.as_str() == effect || row_mentions_effect(rest, effect)
        }
        _ => false,
    }
}

fn checked_routes_output(checked: &Checked) -> bool {
    let Some(mut ty) = checked.interface.env.get(&Sym::from("print")).cloned() else {
        return false;
    };
    loop {
        match ty {
            Type::Forall(_, body) | Type::RowForall(_, body) => ty = *body,
            Type::Fun(_, row, _) => return row_mentions_effect(&row, names::OUTPUT_EFFECT),
            _ => return false,
        }
    }
}

fn checked_decl_scheme<'a>(checked: &'a Checked, name: &str) -> Result<&'a Type, Error> {
    checked
        .dispatch
        .constrained
        .get(&Sym::from(name))
        .map(|constrained| &constrained.scheme)
        .or_else(|| {
            checked
                .defs
                .decls
                .iter()
                .find(|decl| decl.name == name)
                .map(|decl| &decl.ty)
        })
        .ok_or_else(|| Error::InternalInvariant(format!("no checked scheme for `{name}`")))
}

fn source_dict_type(class: Sym, argument: Type) -> Type {
    Type::Con(Sym::from(&names::dict_ctor(class.as_str())), vec![argument])
}

fn prepend_source_params(ty: Type, prefix: &[Type]) -> Result<Type, Error> {
    match ty {
        Type::Forall(name, body) => Ok(Type::Forall(
            name,
            Box::new(prepend_source_params(*body, prefix)?),
        )),
        Type::RowForall(name, body) => Ok(Type::RowForall(
            name,
            Box::new(prepend_source_params(*body, prefix)?),
        )),
        Type::Fun(mut params, effects, result) => {
            let mut all = prefix.to_vec();
            all.append(&mut params);
            Ok(Type::Fun(all, effects, result))
        }
        other => Err(Error::InternalInvariant(format!(
            "expected checked function scheme, got {other:?}"
        ))),
    }
}

fn generalize_free(mut ty: Type) -> Type {
    let mut type_vars = BTreeSet::new();
    let mut row_vars = BTreeSet::new();
    ty.free_ty_vars(&mut type_vars);
    ty.free_row_vars(&mut row_vars);
    for name in row_vars.into_iter().rev() {
        ty = Type::RowForall(name, Box::new(ty));
    }
    for name in type_vars.into_iter().rev() {
        ty = Type::Forall(name, Box::new(ty));
    }
    ty
}

fn typed_builder_error(context: &str, error: impl std::fmt::Display) -> Error {
    TypedCoreConstructionFailure::InvalidDeclaration {
        declaration: context.into(),
        detail: error.to_string(),
    }
    .into()
}

// A resolved update path: (ctor name, field index, arity) per segment.
type Chain = Vec<FieldRef>;

// The terminal action a path applies to the focus it reaches. `Set` replaces
// the focus with the value; `Modify` forces the value (a function) and applies
// it to the old focus, so the old field is read before the rebuild.
enum PathTerm {
    Set(Value),
    Modify(Value),
}

// An integer literal fits the immediate (tagged) form below this many bits.
// The low bit is the tag, so the payload is 63 bits.
const SMALL_INT_BITS: u64 = 63;

fn subst_ty(ty: &Type, subst: &BTreeMap<String, Type>) -> Type {
    match ty {
        Type::Var(s) => subst.get(s.as_str()).cloned().unwrap_or_else(|| ty.clone()),
        Type::Con(n, args) => Type::Con(*n, args.iter().map(|a| subst_ty(a, subst)).collect()),
        Type::Tuple(tys) => Type::Tuple(tys.iter().map(|t| subst_ty(t, subst)).collect()),
        _ => ty.clone(),
    }
}

fn rebind(map: &[(String, String)], body: Comp) -> Comp {
    map.iter().rev().fold(body, |acc, (orig, fresh)| {
        Comp::Bind(
            Box::new(Comp::Return(Value::Var(fresh.clone().into()))),
            orig.clone().into(),
            Box::new(acc),
        )
    })
}

fn wrap_binds(binds: Vec<(Comp, String)>, body: Comp) -> Comp {
    let mut acc = body;
    for (c, v) in binds.into_iter().rev() {
        acc = Comp::Bind(Box::new(c), v.into(), Box::new(acc));
    }
    acc
}

fn param_locals(checked: &Checked, name: &str, params: &[String]) -> Locals {
    let arrow = checked.defs.decls.iter().find(|d| d.name == name).map(|d| {
        let mut t = &d.ty;
        while let Type::Forall(_, inner) | Type::RowForall(_, inner) = t {
            t = inner;
        }
        t
    });
    let ptys = match arrow {
        Some(Type::Fun(ps, _, _)) => Some(ps),
        _ => None,
    };
    params
        .iter()
        .enumerate()
        .map(|(i, p)| (p.clone(), ptys.and_then(|ps| ps.get(i)).cloned()))
        .collect()
}

fn pat_vars(p: &S<Pattern>, acc: &mut Locals) {
    match &p.node {
        Pattern::Wild
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Char(_)
        | Pattern::Bool(_) => {}
        Pattern::Var(x) => {
            acc.insert(x.clone(), None);
        }
        Pattern::Ctor(_, subs) | Pattern::Tuple(subs) => {
            for s in subs {
                pat_vars(s, acc);
            }
        }
        Pattern::Record(_, fields, _) => {
            for (_, p2) in fields {
                pat_vars(p2, acc);
            }
        }
        // Alternatives bind the same names, so the first one names them all.
        Pattern::Or(alts) => {
            if let Some(first) = alts.first() {
                pat_vars(first, acc);
            }
        }
    }
}

const fn spanned(p: Pattern) -> S<Pattern> {
    Spanned {
        id: NodeId::DUMMY,
        synth: false,
        node: p,
        span: Span::new(0, 0),
    }
}

/// Immediate payload when the value fits the small form (a tagged 63-bit int);
/// larger magnitudes spill to a heap bignum.
fn small_int(n: &BigInt) -> Option<i64> {
    if n.bits() > SMALL_INT_BITS {
        return None;
    }
    let mag = n.iter_u64_digits().next().unwrap_or(0);
    #[allow(clippy::cast_possible_wrap)]
    let v = if n.sign() == Sign::Minus {
        (mag as i64).wrapping_neg()
    } else {
        mag as i64
    };
    ((-(1i64 << 62))..(1i64 << 62)).contains(&v).then_some(v)
}

fn to_wrapped_u64(n: &BigInt) -> u64 {
    let low = n.iter_u64_digits().next().unwrap_or(0);
    if n.sign() == Sign::Minus {
        low.wrapping_neg()
    } else {
        low
    }
}

#[allow(clippy::cast_possible_wrap)]
fn to_wrapped_i64(n: &BigInt) -> i64 {
    to_wrapped_u64(n) as i64
}

// The `f64` an integer literal denotes when it adopts a `Float` lane from context
// (`let x : Float = 1`). The decimal parse is correctly rounded and identical on
// every platform, so the resolved lane constant is deterministic; nothing is
// converted at runtime.
fn to_float_lit(n: &BigInt) -> f64 {
    n.to_string().parse::<f64>().unwrap_or(f64::NAN)
}

pub fn builtin_arities(arity: &mut BTreeMap<String, usize>) {
    for (name, n, _) in BUILTINS {
        arity.insert((*name).into(), *n);
    }
}

/// # Errors
/// Fails when a checked program cannot be elaborated to core.
pub fn elaborate(prog: &Program<CorePhase>, checked: &Checked) -> Result<Core, Error> {
    elaborate_typed(prog, checked).map(TypedElaboration::into_compatibility)
}

/// Both representations consumed on either side of the typed boundary.
///
/// The elaborated program in both of its boundary forms.
///
/// `compatibility` is the exact pre-optimizer identity surface. `typed` carries
/// the same tree plus witnesses through the typed prefix before its sole semantic
/// erasure. Keeping both avoids rebuilding witnesses or changing the
/// content-addressed identity at the boundary.
#[derive(Debug)]
pub struct TypedElaboration {
    compatibility: ElaboratedCore,
    typed: TypedCore<TypedElaborated>,
    verify_env: VerifyEnv,
}

impl TypedElaboration {
    #[must_use]
    pub const fn compatibility(&self) -> &ElaboratedCore {
        &self.compatibility
    }

    #[must_use]
    pub fn into_compatibility(self) -> Core {
        self.compatibility.into_core()
    }

    /// Consume the product without discarding the validated elaboration stage.
    #[must_use]
    pub fn into_parts(self) -> (ElaboratedCore, TypedCore<TypedElaborated>, VerifyEnv) {
        (self.compatibility, self.typed, self.verify_env)
    }
}

/// Elaborate once, retaining both the verified typed spine and the exact
/// compatibility tree consumed by passes outside the typed prefix.
///
/// # Errors
/// Fails when source elaboration, witness construction, or independent typed
/// verification fails.
pub fn elaborate_typed(
    prog: &Program<CorePhase>,
    checked: &Checked,
) -> Result<TypedElaboration, Error> {
    let mut arity: BTreeMap<String, usize> = prog
        .fns
        .iter()
        .filter(|d| !d.konst)
        .map(|d| (d.name.clone(), d.params.len()))
        .collect();
    builtin_arities(&mut arity);
    let effect_ops: BTreeSet<String> = checked.defs.eff_ops.keys().cloned().collect();
    // Keep print routing in lockstep with the checker, which rewrites
    // `print`/`println` from `IO` to `Output` only for programs that include the
    // replay driver surface. Key on the checked scheme, not the arity table after
    // builtins and constants have been merged in.
    let route_output =
        effect_ops.contains(names::OUTPUT_PRINT_OP) && checked_routes_output(checked);
    let consts: BTreeMap<String, &S<Expr<CorePhase>>> = prog
        .fns
        .iter()
        .filter(|d| d.konst)
        .map(|d| (d.name.clone(), &d.body))
        .collect();

    let mut elab = Elab {
        fresh: Fresh::new(),
        ctors: &checked.defs.ctors,
        arity,
        consts,
        expansion: ExpansionMap::new(),
        checked,
        hir: hir::build(checked),
        route_output,
        effect_ops,
        show_fns: Vec::new(),
        show_sigs: BTreeMap::new(),
        show_seen: BTreeSet::new(),
        strict: true,
    };

    let mut fns = Vec::with_capacity(prog.fns.len());
    let mut signatures = BTreeMap::new();
    for d in &prog.fns {
        if d.konst {
            continue;
        }
        let names: Vec<String> = d.params.iter().map(|p| p.name.clone()).collect();
        let mut locals = param_locals(checked, &d.name, &names);
        let mut params = names;
        if !d.constraints.is_empty() {
            let dps: Vec<String> = (0..d.constraints.len()).map(names::dict_param).collect();
            for dp in &dps {
                locals.insert(dp.clone(), None);
            }
            let mut all = dps;
            all.extend(params);
            params = all;
        }
        let body = elab.elab(&d.body, &locals).map_err(|e| match e {
            Error::InternalInvariant(m) => {
                Error::InternalInvariant(format!("in `{}`: {m}", d.name))
            }
            other => other,
        })?;
        let name = Sym::from(&d.name);
        let scheme = checked_decl_scheme(checked, &d.name)?;
        let prefix = checked
            .dispatch
            .constrained
            .get(&name)
            .map(|constrained| {
                constrained
                    .constraints
                    .iter()
                    .map(|c| dict_type(c.class, c.head.clone()))
                    .collect()
            })
            .unwrap_or_default();
        let signature = core_fn_sig(scheme, prefix)
            .map_err(|error| typed_builder_error("function signature", error))?;
        signatures.insert(name, signature);
        fns.push(CoreFn {
            name,
            body,
            params: params.into_iter().map(Sym::from).collect(),
            // The leading `_c{i}` dictionary params prepended just above, one per
            // class constraint (zero when the context is empty).
            dict_arity: d.constraints.len(),
        });
    }

    for inst in &prog.instances {
        let info = checked
            .dispatch
            .instances
            .get(&Sym::from(&inst.name))
            .ok_or_else(|| {
                Error::InternalInvariant(format!("no instance info for `{}`", inst.name))
            })?;
        let class = checked.dispatch.classes.get(&info.class).ok_or_else(|| {
            Error::InternalInvariant(format!("no class info for `{}`", info.class))
        })?;
        // Dict params: the declared context first (so method bodies' `_c{i}`
        // indices are unchanged), then one per superclass obligation.
        let nctx = info.context.len();
        // The dictionary arity every function in this instance carries: one param
        // per declared context obligation plus one per superclass.
        let ndict = nctx + info.supers.len();
        let dps: Vec<String> = (0..ndict).map(names::dict_param).collect();
        for m in &inst.methods {
            let sig = &class
                .methods
                .iter()
                .find(|(n, _)| n.as_str() == m.name)
                .ok_or_else(|| {
                    Error::InternalInvariant(format!("no class signature for `{}`", m.name))
                })?
                .1;
            let expected = sig.subst_var(class.param, &info.head);
            let doms = match &expected {
                Type::Fun(d, _, _) => d.clone(),
                _ => vec![],
            };
            let mut locals: Locals = m
                .params
                .iter()
                .zip(&doms)
                .map(|(p, t)| (p.name.clone(), Some(t.clone())))
                .collect();
            for dp in &dps {
                locals.insert(dp.clone(), None);
            }
            let mut params = dps.clone();
            params.extend(m.params.iter().map(|p| p.name.clone()));
            let method_name = Sym::from(&instance_method(&inst.name, &m.name));
            let dict_params: Vec<Type> = info
                .context
                .iter()
                .chain(&info.supers)
                .map(|(class, argument)| source_dict_type(*class, argument.clone()))
                .collect();
            let method_scheme =
                generalize_free(prepend_source_params(expected.clone(), &dict_params)?);
            signatures.insert(
                method_name,
                core_fn_sig(&method_scheme, Vec::new())
                    .map_err(|error| typed_builder_error("instance method signature", error))?,
            );
            fns.push(CoreFn {
                name: method_name,
                body: elab.elab(&m.body, &locals)?,
                params: params.into_iter().map(Sym::from).collect(),
                dict_arity: ndict,
            });
        }
        let mut fields = Vec::new();
        // Leading superclass-dictionary fields (the trailing dict params), then
        // one thunk per method. `Dict::Super` and method projection index past
        // these leading fields.
        for j in 0..info.supers.len() {
            fields.push(Value::Var(names::dict_param(nctx + j).into()));
        }
        for (mname, sig) in &class.methods {
            let arity = match sig {
                Type::Fun(d, _, _) => d.len(),
                _ => 0,
            };
            let ps: Vec<String> = (0..arity).map(names::generated_param).collect();
            let mut args: Vec<Value> = dps.iter().map(|d| Value::Var(d.clone().into())).collect();
            args.extend(ps.iter().map(|p| Value::Var(p.clone().into())));
            let call = Comp::Call(instance_method(&inst.name, mname.as_str()).into(), args);
            fields.push(Value::Thunk(Box::new(Comp::Lam(
                ps.into_iter().map(Sym::from).collect(),
                Box::new(call),
            ))));
        }
        let instance_name = Sym::from(&inst.name);
        let dictionary_params: Vec<Type> = info
            .context
            .iter()
            .chain(&info.supers)
            .map(|(class, argument)| source_dict_type(*class, argument.clone()))
            .collect();
        let dictionary_scheme = generalize_free(Type::fun(
            dictionary_params,
            source_dict_type(info.class, info.head.clone()),
        ));
        signatures.insert(
            instance_name,
            core_fn_sig(&dictionary_scheme, Vec::new())
                .map_err(|error| typed_builder_error("instance dictionary signature", error))?,
        );
        fns.push(CoreFn {
            name: instance_name,
            params: dps.into_iter().map(Sym::from).collect(),
            dict_arity: ndict,
            body: Comp::Return(Value::Ctor(
                dict_ctor(info.class.as_str()).into(),
                0,
                fields,
            )),
        });
    }

    fns.append(&mut elab.show_fns);
    signatures.append(&mut elab.show_sigs);
    let raw = Core { fns };
    let compatibility = raw.clone();
    let mut verify_env = build_verify_env(&checked.defs.ctors, &checked.defs.eff_ops)?;
    for constructor in super::opt::newtype_ctors(prog) {
        verify_env.mark_newtype_constructor(constructor);
    }
    for (name, info) in &checked.defs.data {
        if info.repr == NominalRepr::BoxedCell {
            verify_env.mark_boxed_nominal(Sym::from(name.as_str()));
        }
    }
    let typed = verify_typed_core(build_typed(raw, &signatures, &verify_env)?, &verify_env)
        .map_err(typed_verification_error)?;
    let erased = typed.clone().erase();
    if erased != compatibility {
        return Err(TypedCoreErasureFailure.into());
    }
    let compatibility = ElaboratedCore::validate(compatibility).map_err(|violations| {
        Error::InternalInvariant(format!(
            "elaborated Core failed structural validation:\n{}",
            violations.join("\n")
        ))
    })?;
    Ok(TypedElaboration {
        compatibility,
        typed,
        verify_env,
    })
}

#[must_use]
pub fn typed_verification_error(violations: Vec<super::typed::CoreViolation>) -> Error {
    TypedCoreVerificationFailure {
        violations: violations
            .into_iter()
            .map(|violation| TypedCoreViolation {
                function: violation.function().to_string(),
                path: violation.path().into(),
                detail: violation.message(),
            })
            .collect(),
    }
    .into()
}

/// # Errors
/// Fails when the expression cannot be elaborated to core.
/// Elaborate every `konst` (top-level `let`) as a zero-parameter [`CoreFn`], for
/// content hashing only. The real compile inlines konsts at their use sites, so
/// they are absent from the compiled Core and would otherwise get no behavior
/// hash. A konst is a genuine value definition (unlike a transparent alias), so
/// giving it its own hash makes it addressable and displayable. konst-to-konst
/// references inline, so two constants with the same value share a hash.
///
/// # Errors
/// Fails when a konst body cannot be elaborated (a compiler bug).
pub fn konst_fns(prog: &Program<CorePhase>, checked: &Checked) -> Result<Vec<CoreFn>, Error> {
    let mut arity: BTreeMap<String, usize> = prog
        .fns
        .iter()
        .filter(|d| !d.konst)
        .map(|d| (d.name.clone(), d.params.len()))
        .collect();
    builtin_arities(&mut arity);
    let consts: BTreeMap<String, S<Expr<CorePhase>>> = prog
        .fns
        .iter()
        .filter(|d| d.konst)
        .map(|d| (d.name.clone(), d.body.clone()))
        .collect();
    prog.fns
        .iter()
        .filter(|d| d.konst)
        .map(|d| {
            let body = elaborate_expr(checked, &d.body, &arity, None, &consts)?;
            Ok(CoreFn {
                name: d.name.clone().into(),
                params: Vec::new(),
                dict_arity: 0,
                body,
            })
        })
        .collect()
}

/// Elaborate a single surface expression to Core against an already-checked
/// program (used to hash konst bodies as zero-parameter definitions).
///
/// # Errors
/// Fails if the expression references a name or dictionary the elaborator cannot
/// resolve against `checked`.
pub(crate) fn elaborate_expr(
    checked: &Checked,
    e: &S<Expr<CorePhase>>,
    arity: &BTreeMap<String, usize>,
    facts: Option<&NodeFacts>,
    consts: &BTreeMap<String, S<Expr<CorePhase>>>,
) -> Result<Comp, Error> {
    elaborate_expr_defs(checked, e, arity, facts, consts).map(|(comp, _)| comp)
}

/// Like [`elaborate_expr`], but also returns the definitions the elaborator
/// synthesized on demand while lowering `e` (the structural `show` helpers).
///
/// The whole-program [`elaborate`] folds these into its `Core`, so a batch run
/// finds them in its global environment. A caller that evaluates a bare
/// expression against a pre-built environment (the REPL) must add them itself,
/// or a call to one faults as an unknown function.
///
/// # Errors
/// Fails if the expression references a name or dictionary the elaborator cannot
/// resolve against `checked`.
pub(crate) fn elaborate_expr_defs(
    checked: &Checked,
    e: &S<Expr<CorePhase>>,
    arity: &BTreeMap<String, usize>,
    facts: Option<&NodeFacts>,
    consts: &BTreeMap<String, S<Expr<CorePhase>>>,
) -> Result<(Comp, Vec<CoreFn>), Error> {
    let effect_ops: BTreeSet<String> = checked.defs.eff_ops.keys().cloned().collect();
    let mut elab = Elab {
        fresh: Fresh::new(),
        ctors: &checked.defs.ctors,
        arity: arity.clone(),
        consts: consts.iter().map(|(k, v)| (k.clone(), v)).collect(),
        expansion: ExpansionMap::new(),
        checked,
        // A re-inferred expression carries its own complete fact artifact under
        // fresh ids; a konst body shares the checked program's facts.
        hir: facts.map_or_else(|| hir::build(checked), |f| hir::build_for_expr(checked, f)),
        route_output: effect_ops.contains(names::OUTPUT_PRINT_OP) && checked_routes_output(checked),
        effect_ops,
        show_fns: Vec::new(),
        show_sigs: BTreeMap::new(),
        show_seen: BTreeSet::new(),
        strict: true,
    };
    let comp = elab.elab(e, &Locals::new())?;
    Ok((comp, elab.show_fns))
}
