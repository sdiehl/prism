use std::collections::{BTreeMap, BTreeSet};
use std::slice;

use marginalia::Span;
use num_bigint::Sign;

use super::builtins::{builtin, Builtin, BuiltinKind, FloatOp, BUILTINS};
use super::cbpv::{Comp, Core, CoreFn, CoreOp, CorePat, HandleOp, IoOp, NegLane, Value};
use crate::error::{Error, TypeError};
use crate::fresh::Fresh;
use crate::names::{
    self, dict_ctor, instance_method, DIV_MOD_METHOD, DIV_QUOT_METHOD, EQ_METHOD, NUM_ADD_METHOD,
    NUM_FROMINT_METHOD, NUM_MUL_METHOD, NUM_NEG_METHOD, NUM_SUB_METHOD, ORD_METHOD,
};
use crate::sym::Sym;
use crate::syntax::ast::{
    Arm, BigInt, BinOp, Core as CorePhase, Expr, HandlerArm, IntLit, NodeId, PathOp, PathStep,
    Pattern, Program, Spanned, Suffix, S,
};
use crate::types::{
    infer_expr_env, Checked, CtorInfo, Dict, Env, Type, CONS, DIV_CLASS, EQ_CLASS, LIST, NIL,
    NUM_CLASS, ORD_CLASS, SHOW_CLASS,
};

mod dict;
mod match_compile;
mod show;

struct Elab<'a> {
    fresh: Fresh,
    ctors: &'a BTreeMap<String, CtorInfo>,
    arity: BTreeMap<String, usize>,
    // Top-level constants, keyed by name. A reference inlines the RHS rather
    // than calling, so a constant pushes no frame.
    consts: BTreeMap<String, &'a S<Expr<CorePhase>>>,
    checked: &'a Checked,
    dicts: &'a BTreeMap<NodeId, Vec<Dict>>,
    effect_ops: BTreeSet<String>,
    // True when the `Output` capability is in scope (the prelude declares it), so
    // `print`/`println` route through the interceptable `out_print`/`out_println`
    // ops. A prelude-free program has no `Output` handler, so it prints directly.
    route_output: bool,
    show_fns: Vec<CoreFn>,
    show_seen: BTreeSet<String>,
    // True when `dicts` and the node tables come from the same check() pass.
    // REPL re-inference assigns fresh ids, so id-keyed integrity checks are off.
    strict: bool,
}

type Locals = BTreeMap<String, Option<Type>>;

// A resolved update path: (ctor name, field index, arity) per segment.
type Chain = Vec<(String, usize, usize)>;

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

impl Elab<'_> {
    fn fresh(&mut self) -> String {
        names::elab_tmp(self.fresh.bump())
    }

    fn ctor(&self, name: &str) -> Option<&CtorInfo> {
        self.ctors.get(name)
    }

    // Name-based field resolution for REPL re-elaboration, used only when the
    // checker's `field_res` is absent. Returns the unique (ctor, index, arity)
    // that declares `field`. A field that no record declares, or that several
    // distinct records declare, cannot be resolved by name alone: pick neither
    // and surface a diagnostic rather than silently extracting the wrong field.
    fn field_res_fallback(&self, field: &str) -> Result<(&str, usize, usize), Error> {
        let mut hit: Option<(&str, usize, usize)> = None;
        for (ctor_name, info) in self.ctors {
            if let Some(fi) = info.fields.iter().position(|f| f == field) {
                if hit.is_some() {
                    return Err(Error::Resolve(format!(
                        "field `{field}` is declared by more than one record; \
                         it cannot be resolved by name alone"
                    )));
                }
                hit = Some((ctor_name, fi, info.args.len()));
            }
        }
        hit.ok_or_else(|| Error::Resolve(format!("no record has field `{field}`")))
    }

    fn extract_field_of(scrut: Value, ctor: &str, fi: usize, n: usize, out: String) -> Comp {
        let binders = (0..n).map(|j| (j == fi).then(|| Sym::from(&out))).collect();
        let pat = CorePat::Ctor(Sym::from(ctor), binders);
        Comp::Case(scrut, vec![(pat, Comp::Return(Value::Var(out.into())))])
    }

    // Name-based chain resolution for REPL re-elaboration, mirroring
    // `field_index_for`. Checked programs carry exact chains in `path_res`.
    fn path_chain_fallback(&self, path: &[PathStep<CorePhase>]) -> Result<Chain, Error> {
        path.iter()
            .map(|seg| {
                let PathStep::Field(seg) = seg else {
                    return Err(Error::Ice("optic path step survived desugaring".into()));
                };
                self.ctors
                    .iter()
                    .find_map(|(cn, info)| {
                        let fi = info.fields.iter().position(|f| f == seg)?;
                        Some((cn.clone(), fi, info.args.len()))
                    })
                    .ok_or_else(|| Error::Ice(format!("no constructor has field `{seg}`")))
            })
            .collect()
    }

    // Nested rebuild along each path: one single-arm Case per level, each arm
    // ending in Return(Ctor), the exact shape the reuse analysis rewrites to
    // in-place mutation when the spine is uniquely owned.
    fn elab_update_path(
        &mut self,
        id: NodeId,
        base_expr: &S<Expr<CorePhase>>,
        ups: &[(Vec<PathStep<CorePhase>>, PathOp<CorePhase>)],
        locals: &Locals,
    ) -> Result<Comp, Error> {
        let chains: Vec<Chain> = match self.checked.path_res.get(&id) {
            Some(c) => c.clone(),
            None => ups
                .iter()
                .map(|(p, _)| self.path_chain_fallback(p))
                .collect::<Result<_, _>>()?,
        };
        let base_comp = self.elab(base_expr, locals)?;
        let bv = self.fresh();
        let mut binds = Vec::new();
        let mut items = Vec::new();
        for ((_, op), chain) in ups.iter().zip(chains) {
            let c = self.elab(op.expr(), locals)?;
            let v = self.fresh();
            binds.push((c, v.clone()));
            let val = Value::Var(v.into());
            let term = match op {
                PathOp::Set(_) => PathTerm::Set(val),
                PathOp::Modify(_) => PathTerm::Modify(val),
            };
            items.push((chain, term));
        }
        let rebuilt = wrap_binds(binds, self.rebuild_path(&bv, items)?);
        Ok(Comp::Bind(
            Box::new(base_comp),
            bv.into(),
            Box::new(rebuilt),
        ))
    }

    // One Case per level: bind every field, rebuild the constructor with the
    // updated slots, recurse for paths that go deeper. Items at one level
    // share the level's single constructor.
    fn rebuild_path(&mut self, scrut: &str, items: Vec<(Chain, PathTerm)>) -> Result<Comp, Error> {
        let (cname, _, n) = items
            .first()
            .and_then(|(chain, _)| chain.first())
            .ok_or_else(|| Error::Ice("empty record-update path".into()))?
            .clone();
        let tag = self.ctors.get(&cname).map_or(0, |i| i.tag);
        let fields: Vec<String> = (0..n).map(|_| self.fresh()).collect();
        let mut vals: Vec<Value> = fields
            .iter()
            .map(|f| Value::Var(f.clone().into()))
            .collect();
        let mut groups: BTreeMap<usize, Vec<(Chain, PathTerm)>> = BTreeMap::new();
        for (chain, v) in items {
            groups.entry(chain[0].1).or_default().push((chain, v));
        }
        let mut binds = Vec::new();
        for (fi, group) in groups {
            if group[0].0.len() == 1 {
                let term = group
                    .into_iter()
                    .next()
                    .ok_or_else(|| Error::Ice("empty record-update path group".into()))?
                    .1;
                vals[fi] = match term {
                    PathTerm::Set(v) => v,
                    // `~ f`: force the function value and apply it to the old
                    // field, binding the result as the new field.
                    PathTerm::Modify(f) => {
                        let nv = self.fresh();
                        let app = Comp::App(
                            Box::new(Comp::Force(f)),
                            vec![Value::Var(fields[fi].clone().into())],
                        );
                        binds.push((app, nv.clone()));
                        Value::Var(nv.into())
                    }
                };
            } else {
                let sub = group
                    .into_iter()
                    .map(|(mut ch, v)| {
                        ch.remove(0);
                        (ch, v)
                    })
                    .collect();
                let inner = self.rebuild_path(&fields[fi], sub)?;
                let nv = self.fresh();
                binds.push((inner, nv.clone()));
                vals[fi] = Value::Var(nv.into());
            }
        }
        let pat = CorePat::Ctor(
            Sym::from(&cname),
            fields.iter().map(|f| Some(Sym::from(f))).collect(),
        );
        let body = wrap_binds(binds, Comp::Return(Value::Ctor(cname.into(), tag, vals)));
        Ok(Comp::Case(Value::Var(scrut.into()), vec![(pat, body)]))
    }

    fn local_env(locals: &Locals) -> Env {
        // A local with a known type contributes it; an untyped one (a pattern
        // binder) still shadows a same-named global so re-inference cannot pick
        // up the global's type. Without this a binder shadowing a top-level
        // constant would resolve to the constant's type, misdirecting print
        // dispatch. The sentinel var is unguarded, so printing falls back to Int.
        locals
            .iter()
            .enumerate()
            .map(|(i, (k, v))| {
                let ty = v.clone().unwrap_or_else(|| {
                    Type::Var(Sym::new(&names::local_shadow(
                        u32::try_from(i).unwrap_or(u32::MAX),
                    )))
                });
                (Sym::from(k), ty)
            })
            .collect()
    }

    fn infer_local(&self, e: &S<Expr<CorePhase>>, locals: &Locals) -> Option<Type> {
        infer_expr_env(self.checked, &Self::local_env(locals), e)
            .ok()
            .map(|(t, _)| t)
    }

    fn local_ty(&self, e: &S<Expr<CorePhase>>, locals: &Locals) -> Option<Type> {
        self.checked
            .span_types
            .get(&e.id)
            .filter(|t| {
                let mut ex = BTreeSet::new();
                t.free_exist(&mut ex);
                ex.is_empty()
            })
            .cloned()
            .or_else(|| self.infer_local(e, locals))
    }

    // Canonical form: an Int literal is an immediate when it fits the 63-bit
    // payload, otherwise it is built at runtime through big_lit (a big cell).
    fn int_value(&self, lit: &IntLit, id: NodeId) -> Comp {
        let fixed = match lit.suffix {
            Suffix::I64 => Some(Type::I64),
            Suffix::U64 => Some(Type::U64),
            Suffix::None => self.checked.fixed.get(&id).cloned(),
        };
        match fixed {
            Some(Type::I64) => Comp::Return(Value::I64(to_wrapped_i64(&lit.value))),
            Some(Type::U64) => Comp::Return(Value::U64(to_wrapped_u64(&lit.value))),
            Some(Type::Float) => Comp::Return(Value::Float(to_float_lit(&lit.value))),
            _ => small_int(&lit.value).map_or_else(
                || Comp::StrBuiltin(Builtin::BigLit, vec![Value::Str(lit.value.to_string())]),
                |n| Comp::Return(Value::Int(n)),
            ),
        }
    }

    fn fixed_bin(&mut self, op: BinOp, ty: &Type, args: Vec<Value>) -> Result<Comp, Error> {
        let u = *ty == Type::U64;
        let b = match op {
            BinOp::Add => Builtin::I64Add,
            BinOp::Sub => Builtin::I64Sub,
            BinOp::Mul => Builtin::I64Mul,
            BinOp::Div if u => Builtin::U64Div,
            BinOp::Div => Builtin::I64Div,
            BinOp::Rem if u => Builtin::U64Rem,
            BinOp::Rem => Builtin::I64Rem,
            _ => {
                let cmp = if u { Builtin::U64Cmp } else { Builtin::I64Cmp };
                let c = self.fresh();
                let core_op = CoreOp::from_binop(op)
                    .ok_or_else(|| Error::Ice(format!("`{op:?}` is not a primitive op")))?;
                return Ok(Comp::Bind(
                    Box::new(Comp::StrBuiltin(cmp, args)),
                    c.clone().into(),
                    Box::new(Comp::Prim(core_op, Value::Var(c.into()), Value::Int(0))),
                ));
            }
        };
        Ok(Comp::StrBuiltin(b, args))
    }

    // The `Float` lane of the arithmetic and comparison operators, the exact
    // target the dotted spellings already lower to, so a plain operator on
    // `Float` and the dot spelling produce byte-identical Core. `%` is `fmod` (a
    // two-argument builtin, not a `CoreOp`); the rest are float `CoreOp`s.
    fn float_bin(op: BinOp, va: &Value, vb: &Value) -> Result<Comp, Error> {
        if op == BinOp::Rem {
            return Ok(Comp::StrBuiltin(
                Builtin::Fmod,
                vec![va.clone(), vb.clone()],
            ));
        }
        let core_op = match op {
            BinOp::Add => CoreOp::Addf,
            BinOp::Sub => CoreOp::Subf,
            BinOp::Mul => CoreOp::Mulf,
            BinOp::Div => CoreOp::Divf,
            BinOp::Eq => CoreOp::Eqf,
            BinOp::Ne => CoreOp::Nef,
            BinOp::Lt => CoreOp::Ltf,
            BinOp::Le => CoreOp::Lef,
            BinOp::Gt => CoreOp::Gtf,
            BinOp::Ge => CoreOp::Gef,
            _ => return Err(Error::Ice(format!("`{op:?}` is not a float numeric op"))),
        };
        Ok(Comp::Prim(core_op, va.clone(), vb.clone()))
    }

    // Unary minus, lowered per the lane the checker recorded on the node. A
    // literal operand is const-folded: exact, and the only way the I64 minimum is
    // built without overflowing the positive magnitude. Otherwise the operand is
    // bound and negated by a genuine `Comp::Neg` node in the lane the typechecker
    // resolved: `Int`, `I64` (wrapping two's-complement, so negating the minimum
    // wraps to itself), or `Float` (a real sign-bit flip that preserves signed
    // zero). The node is deliberately not a `0 - x` subtract: it lowers to a true
    // `fneg` on the float lane, and it is the byte-identical target the `Num`
    // negate method re-elaborates to.
    fn elab_neg(
        &mut self,
        inner: &S<Expr<CorePhase>>,
        id: NodeId,
        locals: &Locals,
    ) -> Result<Comp, Error> {
        match &inner.node {
            Expr::Int(lit) => {
                let negated = IntLit {
                    value: -lit.value.clone(),
                    suffix: lit.suffix,
                };
                if self.dicts.contains_key(&id) {
                    return self.elab_from_int_lit(&negated, id);
                }
                return Ok(self.int_value(&negated, id));
            }
            Expr::Float(f) => return Ok(Comp::Return(Value::Float(-f))),
            _ => {}
        }
        let c = self.elab(inner, locals)?;
        let v = self.fresh();
        let operand = Value::Var(v.clone().into());
        // A `Num`-polymorphic operand dispatches through the `negated` method; a
        // monomorphic lane keeps the direct `Comp::Neg` node (byte-identical to
        // the surface negation, the target the `Num` negate method re-elaborates to).
        if let Some(ds) = self.dicts.get(&id).cloned() {
            let d0 = ds
                .first()
                .ok_or_else(|| Error::Ice("empty dictionary set for unary minus".into()))?;
            let idx = self
                .checked
                .classes
                .get(&Sym::from(NUM_CLASS))
                .and_then(|c| c.methods.iter().position(|(n, _)| n == NUM_NEG_METHOD))
                .ok_or_else(|| Error::Ice(format!("no `{NUM_NEG_METHOD}` method on class Num")))?;
            let call = self.method_invoke(Sym::from(NUM_CLASS), idx, d0, vec![operand])?;
            return Ok(Comp::Bind(Box::new(c), v.into(), Box::new(call)));
        }
        let lane = match self.checked.fixed.get(&id).cloned() {
            Some(Type::I64) => NegLane::I64,
            Some(Type::Float) => NegLane::Float,
            _ => NegLane::Int,
        };
        let neg = Comp::Neg(lane, operand);
        Ok(Comp::Bind(Box::new(c), v.into(), Box::new(neg)))
    }

    fn negate(&mut self, c: Comp) -> Comp {
        let v = self.fresh();
        Comp::Bind(
            Box::new(c),
            v.clone().into(),
            Box::new(Comp::If(
                Value::Var(v.into()),
                Box::new(Comp::Return(Value::Bool(false))),
                Box::new(Comp::Return(Value::Bool(true))),
            )),
        )
    }

    fn elab_eq(
        &mut self,
        op: BinOp,
        a: &S<Expr<CorePhase>>,
        b: &S<Expr<CorePhase>>,
        id: NodeId,
        span: marginalia::Span,
        locals: &Locals,
    ) -> Result<Comp, Error> {
        let ca = self.elab(a, locals)?;
        let cb = self.elab(b, locals)?;
        let va = self.fresh();
        let vb = self.fresh();
        let args = vec![Value::Var(va.clone().into()), Value::Var(vb.clone().into())];
        let ne = op == BinOp::Ne;
        let (cmp, neg) = if let Some(ds) = self.dicts.get(&id).cloned() {
            let idx = self
                .checked
                .classes
                .get(&Sym::from(EQ_CLASS))
                .and_then(|c| c.methods.iter().position(|(n, _)| n == EQ_METHOD))
                .ok_or_else(|| Error::Ice("no `eq` method on class Eq".into()))?;
            let d0 = ds
                .first()
                .ok_or_else(|| Error::Ice("no dictionary for `==`".into()))?;
            (self.method_invoke(Sym::from(EQ_CLASS), idx, d0, args)?, ne)
        } else {
            match self.checked.fixed.get(&id).cloned() {
                Some(ty @ (Type::I64 | Type::U64)) => (self.fixed_bin(op, &ty, args)?, false),
                Some(Type::Float) => (
                    Comp::Prim(
                        if ne { CoreOp::Nef } else { CoreOp::Eqf },
                        Value::Var(va.clone().into()),
                        Value::Var(vb.clone().into()),
                    ),
                    false,
                ),
                Some(Type::Str) => (Comp::StrBuiltin(Builtin::StrEq, args), ne),
                Some(Type::Bool) => (
                    Comp::If(
                        Value::Var(va.clone().into()),
                        Box::new(Comp::Return(Value::Var(vb.clone().into()))),
                        Box::new(Comp::If(
                            Value::Var(vb.clone().into()),
                            Box::new(Comp::Return(Value::Bool(false))),
                            Box::new(Comp::Return(Value::Bool(true))),
                        )),
                    ),
                    ne,
                ),
                _ => {
                    if self.strict {
                        if let Some(t) = self.checked.span_types.get(&a.id) {
                            if !matches!(t, Type::Int | Type::Exist(_)) {
                                return Err(Error::Ice(format!(
                                    "missing Eq dispatch record at {:?} for type {}",
                                    span,
                                    t.show()
                                )));
                            }
                        }
                    }
                    let core_op = CoreOp::from_binop(op)
                        .ok_or_else(|| Error::Ice(format!("`{op:?}` is not a primitive op")))?;
                    (
                        Comp::Prim(
                            core_op,
                            Value::Var(va.clone().into()),
                            Value::Var(vb.clone().into()),
                        ),
                        false,
                    )
                }
            }
        };
        let body = if neg { self.negate(cmp) } else { cmp };
        Ok(Comp::Bind(
            Box::new(ca),
            va.into(),
            Box::new(Comp::Bind(Box::new(cb), vb.into(), Box::new(body))),
        ))
    }

    // `a < b` on an Ord-class type elaborates to `cmp(a, b) < 0`: the class
    // method yields the canonical -1/0/1 ordering Int, so the surface operator
    // itself becomes the primitive comparison of that Int against zero. Only
    // reached when the typechecker recorded a dictionary for this node; the
    // primitive numeric lanes stay on the generic `Expr::Bin` arm.
    fn elab_ord(
        &mut self,
        op: BinOp,
        a: &S<Expr<CorePhase>>,
        b: &S<Expr<CorePhase>>,
        id: NodeId,
        locals: &Locals,
    ) -> Result<Comp, Error> {
        let ca = self.elab(a, locals)?;
        let cb = self.elab(b, locals)?;
        let va = self.fresh();
        let vb = self.fresh();
        let args = vec![Value::Var(va.clone().into()), Value::Var(vb.clone().into())];
        let ds = self
            .dicts
            .get(&id)
            .cloned()
            .ok_or_else(|| Error::Ice("no dictionary for comparison operator".into()))?;
        let d0 = ds
            .first()
            .ok_or_else(|| Error::Ice("empty dictionary set for comparison operator".into()))?;
        let idx = self
            .checked
            .classes
            .get(&Sym::from(ORD_CLASS))
            .and_then(|c| c.methods.iter().position(|(n, _)| n == ORD_METHOD))
            .ok_or_else(|| Error::Ice("no `cmp` method on class Ord".into()))?;
        let cmp = self.method_invoke(Sym::from(ORD_CLASS), idx, d0, args)?;
        let r = self.fresh();
        let core_op = CoreOp::from_binop(op)
            .ok_or_else(|| Error::Ice(format!("`{op:?}` is not a primitive op")))?;
        let test = Comp::Bind(
            Box::new(cmp),
            r.clone().into(),
            Box::new(Comp::Prim(core_op, Value::Var(r.into()), Value::Int(0))),
        );
        Ok(Comp::Bind(
            Box::new(ca),
            va.into(),
            Box::new(Comp::Bind(Box::new(cb), vb.into(), Box::new(test))),
        ))
    }

    // The class and method a tower arithmetic operator dispatches through:
    // `+`/`-`/`*` are `Num.plus`/`minus`/`times`, `/`/`%` are
    // `Div.quotient`/`modulo`. Kept beside the `Num`/`Div` names so the operator
    // -> method mapping has one home.
    const fn arith_method(op: BinOp) -> Option<(&'static str, &'static str)> {
        Some(match op {
            BinOp::Add => (NUM_CLASS, NUM_ADD_METHOD),
            BinOp::Sub => (NUM_CLASS, NUM_SUB_METHOD),
            BinOp::Mul => (NUM_CLASS, NUM_MUL_METHOD),
            BinOp::Div => (DIV_CLASS, DIV_QUOT_METHOD),
            BinOp::Rem => (DIV_CLASS, DIV_MOD_METHOD),
            _ => return None,
        })
    }

    // `a + b` (and the other arithmetic operators) on a `Num`/`Div`-polymorphic
    // operand: dispatch through the class method, exactly as `elab_ord` does for
    // `<`. Only reached when the typechecker recorded a dictionary for this node;
    // a monomorphic lane stays on the direct-primitive arm below. The method
    // returns the result value directly (no comparison-to-zero step).
    fn elab_arith(
        &mut self,
        op: BinOp,
        a: &S<Expr<CorePhase>>,
        b: &S<Expr<CorePhase>>,
        id: NodeId,
        locals: &Locals,
    ) -> Result<Comp, Error> {
        let (class, method) = Self::arith_method(op)
            .ok_or_else(|| Error::Ice(format!("`{op:?}` is not a tower arithmetic op")))?;
        let ca = self.elab(a, locals)?;
        let cb = self.elab(b, locals)?;
        let va = self.fresh();
        let vb = self.fresh();
        let args = vec![Value::Var(va.clone().into()), Value::Var(vb.clone().into())];
        let ds = self
            .dicts
            .get(&id)
            .cloned()
            .ok_or_else(|| Error::Ice("no dictionary for arithmetic operator".into()))?;
        let d0 = ds
            .first()
            .ok_or_else(|| Error::Ice("empty dictionary set for arithmetic operator".into()))?;
        let idx = self
            .checked
            .classes
            .get(&Sym::from(class))
            .and_then(|c| c.methods.iter().position(|(n, _)| n == method))
            .ok_or_else(|| Error::Ice(format!("no `{method}` method on class {class}")))?;
        let call = self.method_invoke(Sym::from(class), idx, d0, args)?;
        Ok(Comp::Bind(
            Box::new(ca),
            va.into(),
            Box::new(Comp::Bind(Box::new(cb), vb.into(), Box::new(call))),
        ))
    }

    // A `Num`-polymorphic integer literal: build the value in the `Int` lane (no
    // `fixed` entry means `int_value` yields the `Int` form) and inject it into
    // the resolved lane through `from_int`. Where the enclosing function is
    // specialized to a concrete lane, the dictionary and the call collapse to that
    // lane's constant conversion; monomorphic literals never reach here.
    fn elab_from_int_lit(&mut self, lit: &IntLit, id: NodeId) -> Result<Comp, Error> {
        let int_comp = self.int_value(lit, id);
        let ds = self
            .dicts
            .get(&id)
            .cloned()
            .ok_or_else(|| Error::Ice("no dictionary for numeric literal".into()))?;
        let d0 = ds
            .first()
            .ok_or_else(|| Error::Ice("empty dictionary set for numeric literal".into()))?;
        let idx = self
            .checked
            .classes
            .get(&Sym::from(NUM_CLASS))
            .and_then(|c| c.methods.iter().position(|(n, _)| n == NUM_FROMINT_METHOD))
            .ok_or_else(|| Error::Ice(format!("no `{NUM_FROMINT_METHOD}` method on class Num")))?;
        let v = self.fresh();
        let call = self.method_invoke(
            Sym::from(NUM_CLASS),
            idx,
            d0,
            vec![Value::Var(v.clone().into())],
        )?;
        Ok(Comp::Bind(Box::new(int_comp), v.into(), Box::new(call)))
    }

    fn elab(&mut self, e: &S<Expr<CorePhase>>, locals: &Locals) -> Result<Comp, Error> {
        Ok(match &e.node {
            Expr::Int(lit) if self.dicts.contains_key(&e.id) => {
                self.elab_from_int_lit(lit, e.id)?
            }
            Expr::Int(lit) => self.int_value(lit, e.id),
            Expr::Float(f) => Comp::Return(Value::Float(*f)),
            Expr::Char(c) => Comp::Return(Value::Int(i64::from(u32::from(*c)))),
            Expr::Bool(b) => Comp::Return(Value::Bool(*b)),
            Expr::Unit => Comp::Return(Value::Unit),
            Expr::Str(s) => Comp::Return(Value::Str(s.clone())),
            Expr::Var(x) => {
                if locals.contains_key(x) {
                    Comp::Return(Value::Var(x.clone().into()))
                } else if let Some(body) = self.consts.get(x).copied() {
                    self.elab(body, &Locals::new())?
                } else if self.dicts.contains_key(&e.id) {
                    self.constrained_value(x, e.id)?
                } else if self.needs_dict(x) {
                    return Err(Error::Ice(format!(
                        "no dict record for `{x}` at {:?}",
                        e.span
                    )));
                } else {
                    self.value_global(x)?
                }
            }
            Expr::Inst(inner, _) => {
                let Expr::Var(x) = &inner.node else {
                    return Err(Error::Ice("instance application on a non-variable".into()));
                };
                self.constrained_value(x, e.id)?
            }
            Expr::Index(recv, key) => self.elab_index(recv, key, locals)?,
            Expr::IndexSet(recv, key, val) => self.elab_index_set(recv, key, val, locals)?,
            Expr::Ann(inner, _) => self.elab(inner, locals)?,
            Expr::Bin(BinOp::And, a, b) => {
                let ca = self.elab(a, locals)?;
                let cb = self.elab(b, locals)?;
                let va = self.fresh();
                Comp::Bind(
                    Box::new(ca),
                    va.clone().into(),
                    Box::new(Comp::If(
                        Value::Var(va.into()),
                        Box::new(cb),
                        Box::new(Comp::Return(Value::Bool(false))),
                    )),
                )
            }
            Expr::Bin(BinOp::Or, a, b) => {
                let ca = self.elab(a, locals)?;
                let cb = self.elab(b, locals)?;
                let va = self.fresh();
                Comp::Bind(
                    Box::new(ca),
                    va.clone().into(),
                    Box::new(Comp::If(
                        Value::Var(va.into()),
                        Box::new(Comp::Return(Value::Bool(true))),
                        Box::new(cb),
                    )),
                )
            }
            Expr::Bin(op @ (BinOp::Eq | BinOp::Ne), a, b) => {
                self.elab_eq(*op, a, b, e.id, e.span, locals)?
            }
            Expr::Bin(op @ (BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge), a, b)
                if self.dicts.contains_key(&e.id) =>
            {
                self.elab_ord(*op, a, b, e.id, locals)?
            }
            Expr::Bin(
                op @ (BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem),
                a,
                b,
            ) if self.dicts.contains_key(&e.id) => self.elab_arith(*op, a, b, e.id, locals)?,
            Expr::Bin(op, a, b) => {
                let ca = self.elab(a, locals)?;
                let cb = self.elab(b, locals)?;
                let va = self.fresh();
                let vb = self.fresh();
                let lhs_val = Value::Var(va.clone().into());
                let rhs_val = Value::Var(vb.clone().into());
                let args = vec![lhs_val.clone(), rhs_val.clone()];
                let prim = match self.checked.fixed.get(&e.id).cloned() {
                    Some(ty @ (Type::I64 | Type::U64)) => self.fixed_bin(*op, &ty, args)?,
                    // The tower brought `Float` onto the plain operators; lower to
                    // the same float primitive the dotted spelling emits.
                    Some(Type::Float) => Self::float_bin(*op, &lhs_val, &rhs_val)?,
                    _ => {
                        let core_op = CoreOp::from_binop(*op)
                            .ok_or_else(|| Error::Ice(format!("`{op:?}` is not a primitive op")))?;
                        Comp::Prim(core_op, lhs_val, rhs_val)
                    }
                };
                Comp::Bind(
                    Box::new(ca),
                    va.into(),
                    Box::new(Comp::Bind(Box::new(cb), vb.into(), Box::new(prim))),
                )
            }
            Expr::Neg(inner) => self.elab_neg(inner, e.id, locals)?,
            Expr::If(c, t, e2) => {
                let cc = self.elab(c, locals)?;
                let ct = self.elab(t, locals)?;
                let ce = self.elab(e2, locals)?;
                let vc = self.fresh();
                Comp::Bind(
                    Box::new(cc),
                    vc.clone().into(),
                    Box::new(Comp::If(Value::Var(vc.into()), Box::new(ct), Box::new(ce))),
                )
            }
            Expr::Let(x, v, b) => {
                let cv = self.elab(v, locals)?;
                let ty = self.infer_local(v, locals);
                let mut l2 = locals.clone();
                l2.insert(x.clone(), ty);
                let cb = self.elab(b, &l2)?;
                Comp::Bind(Box::new(cv), x.clone().into(), Box::new(cb))
            }
            Expr::Lam(ps, body) => {
                let names: Vec<String> = ps.iter().map(|p| p.name.clone()).collect();
                let mut l2 = locals.clone();
                l2.extend(names.iter().map(|n| (n.clone(), None)));
                let cb = self.elab(body, &l2)?;
                Comp::Return(Value::Thunk(Box::new(Comp::Lam(
                    names.into_iter().map(Sym::from).collect(),
                    Box::new(cb),
                ))))
            }
            Expr::Call(f, args) => self.elab_call(f, args, locals)?,
            Expr::Pipe(x, f) => self.elab_call(f, slice::from_ref(x), locals)?,
            Expr::Match(s, arms) => {
                let cs = self.elab(s, locals)?;
                let vs = self.fresh();
                let compiled = self.elab_arms(&vs, arms, locals, false)?;
                Comp::Bind(Box::new(cs), vs.into(), Box::new(compiled))
            }
            Expr::Tuple(elems) => {
                let mut binds = Vec::new();
                let mut vals = Vec::new();
                for elem in elems {
                    let c = self.elab(elem, locals)?;
                    let v = self.fresh();
                    binds.push((c, v.clone()));
                    vals.push(Value::Var(v.into()));
                }
                wrap_binds(binds, Comp::Return(Value::Tuple(vals)))
            }
            Expr::List(elems) => {
                let nil = Comp::Return(Value::Ctor(NIL.into(), 0, vec![]));
                let mut acc = nil;
                for elem in elems.iter().rev() {
                    let ce = self.elab(elem, locals)?;
                    let ve = self.fresh();
                    let vrest = self.fresh();
                    let cons = Comp::Return(Value::Ctor(
                        CONS.into(),
                        1,
                        vec![
                            Value::Var(ve.clone().into()),
                            Value::Var(vrest.clone().into()),
                        ],
                    ));
                    acc = Comp::Bind(
                        Box::new(ce),
                        ve.into(),
                        Box::new(Comp::Bind(Box::new(acc), vrest.into(), Box::new(cons))),
                    );
                }
                acc
            }
            Expr::FieldAccess(recv, field) => {
                let ce = self.elab(recv, locals)?;
                let ve = self.fresh();
                let vf = self.fresh();
                let extract = if let Some((ctor, fi, n)) = self.checked.field_res.get(&e.id) {
                    Self::extract_field_of(Value::Var(ve.clone().into()), ctor, *fi, *n, vf)
                } else {
                    let (ctor, fi, n) = self.field_res_fallback(field)?;
                    Self::extract_field_of(Value::Var(ve.clone().into()), ctor, fi, n, vf)
                };
                Comp::Bind(Box::new(ce), ve.into(), Box::new(extract))
            }
            Expr::RecordCreate(ctor_name, field_exprs) => {
                if let Some(info) = self.ctors.get(ctor_name).cloned() {
                    let n_fields = info.args.len();
                    let mut ordered: Vec<Option<(Comp, String)>> = vec![None; n_fields];
                    for (fname, fexpr) in field_exprs {
                        if let Some(fi) = info.fields.iter().position(|f| f == fname) {
                            let c = self.elab(fexpr, locals)?;
                            let v = self.fresh();
                            ordered[fi] = Some((c, v));
                        }
                    }
                    let mut binds = Vec::new();
                    let mut vals = Vec::new();
                    for opt in ordered {
                        let (c, v) = opt.ok_or_else(|| {
                            Error::Ice(format!("missing field in record {ctor_name}"))
                        })?;
                        binds.push((c, v.clone()));
                        vals.push(Value::Var(v.into()));
                    }
                    wrap_binds(
                        binds,
                        Comp::Return(Value::Ctor(ctor_name.clone().into(), info.tag, vals)),
                    )
                } else {
                    Comp::Error(Value::Str(format!("unknown record {ctor_name}")))
                }
            }
            Expr::Handle(body, arms) => {
                let body_comp = self.elab(body, locals)?;
                let mut ops = Vec::new();
                let mut return_var = None;
                let mut return_body = None;
                for arm in arms {
                    match arm {
                        HandlerArm::Return(x, arm_body) => {
                            let mut l2 = locals.clone();
                            l2.insert(x.clone(), None);
                            return_var = Some(x.clone().into());
                            return_body = Some(Box::new(self.elab(arm_body, &l2)?));
                        }
                        HandlerArm::Op(name, params, resume_var, arm_body) => {
                            let mut l2 = locals.clone();
                            l2.extend(params.iter().map(|p| (p.clone(), None)));
                            l2.insert(resume_var.clone(), None);
                            let compiled = self.elab(arm_body, &l2)?;
                            ops.push(HandleOp {
                                name: name.clone().into(),
                                params: params.iter().map(Sym::from).collect(),
                                resume: resume_var.clone().into(),
                                body: compiled,
                            });
                        }
                        #[expect(
                            clippy::uninhabited_references,
                            reason = "Never is uninhabited in Core; arm is unreachable"
                        )]
                        HandlerArm::Sugar(never) => match *never {},
                    }
                }
                Comp::Handle {
                    body: Box::new(body_comp),
                    return_var,
                    return_body,
                    ops,
                }
            }
            Expr::RecordUpdate(base_expr, ctor_name, field_exprs) => {
                if let Some(info) = self.ctors.get(ctor_name).cloned() {
                    let n_fields = info.args.len();
                    let base_comp = self.elab(base_expr, locals)?;
                    let base_var = self.fresh();
                    let mut field_vars: Vec<String> = (0..n_fields).map(|_| self.fresh()).collect();
                    let mut extract_binds: Vec<(Comp, String)> = Vec::new();
                    for (fi, fv) in field_vars.iter().enumerate() {
                        let extract = Comp::Case(
                            Value::Var(base_var.clone().into()),
                            vec![(
                                CorePat::Ctor(
                                    Sym::from(ctor_name),
                                    (0..n_fields)
                                        .map(|j| (j == fi).then(|| Sym::from(fv)))
                                        .collect(),
                                ),
                                Comp::Return(Value::Var(fv.clone().into())),
                            )],
                        );
                        extract_binds.push((extract, fv.clone()));
                    }
                    for (fname, fexpr) in field_exprs {
                        if let Some(fi) = info.fields.iter().position(|f| f == fname) {
                            let c = self.elab(fexpr, locals)?;
                            let v = self.fresh();
                            field_vars[fi].clone_from(&v);
                            extract_binds.push((c, v));
                        }
                    }
                    let vals: Vec<Value> = field_vars
                        .iter()
                        .map(|v| Value::Var(v.clone().into()))
                        .collect();
                    let body = Comp::Return(Value::Ctor(ctor_name.clone().into(), info.tag, vals));
                    let inner = wrap_binds(extract_binds, body);
                    Comp::Bind(Box::new(base_comp), base_var.into(), Box::new(inner))
                } else {
                    Comp::Error(Value::Str(format!("unknown record {ctor_name}")))
                }
            }
            Expr::RecordUpdatePath(base_expr, ups) => {
                self.elab_update_path(e.id, base_expr, ups, locals)?
            }
            Expr::Mask(eff, body) => {
                let ops = self
                    .checked
                    .eff_ops
                    .iter()
                    .filter(|(_, i)| i.effect_name == *eff)
                    .map(|(n, _)| Sym::from(n))
                    .collect();
                Comp::Mask(ops, Box::new(self.elab(body, locals)?))
            }
            // Sugar is unrepresentable in `Expr<Core>`, so the match is
            // exhaustive without it and no ICE arm is needed.
            #[expect(
                clippy::uninhabited_references,
                reason = "Never is uninhabited in Core; arm is unreachable"
            )]
            Expr::Sugar(never) | Expr::Marker(never) => match *never {},
        })
    }

    // Eta-expand a partial application (fewer args than arity) into an explicit
    // closure that calls the function at full arity. Without this, effect
    // lowering sees a partial `Call` and wrongly lowers it as a full effectful
    // call, miscompiling partial applications of effectful functions.
    // Returns None for builtins and saturated/over-saturated calls.
    fn eta_partial(&self, name: &str, given: &[Value]) -> Result<Option<Comp>, Error> {
        if builtin(name).is_some() {
            return Ok(None);
        }
        let Some(&arity) = self.arity.get(name) else {
            return Ok(None);
        };
        if given.len() >= arity {
            return Ok(None);
        }
        let ps: Vec<String> = (given.len()..arity).map(|i| format!("_p{i}")).collect();
        let mut all = given.to_vec();
        all.extend(ps.iter().map(|p| Value::Var(p.clone().into())));
        let body = Self::head_call(name, all)?;
        Ok(Some(Comp::Return(Value::Thunk(Box::new(Comp::Lam(
            ps.into_iter().map(Sym::from).collect(),
            Box::new(body),
        ))))))
    }

    // Missing-argument count if the function-typed expression at `span` is
    // applied to `given` arguments, or None if it is saturated or its checked
    // type is not a known arrow (then the application is left as-is).
    fn under_arity(&self, id: NodeId, given: usize) -> Option<usize> {
        let mut ty = self.checked.span_types.get(&id)?;
        while let Type::Forall(_, b) | Type::RowForall(_, b) = ty {
            ty = b;
        }
        match ty {
            Type::Fun(params, _, _) if params.len() > given => Some(params.len() - given),
            _ => None,
        }
    }

    fn elab_call(
        &mut self,
        f: &S<Expr<CorePhase>>,
        args: &[S<Expr<CorePhase>>],
        locals: &Locals,
    ) -> Result<Comp, Error> {
        let mut binds = Vec::new();
        let mut vals = Vec::new();
        for a in args {
            let c = self.elab(a, locals)?;
            let v = self.fresh();
            binds.push((c, v.clone()));
            vals.push(Value::Var(v.into()));
        }
        let body = match &f.node {
            // `print`/`println` resolve a `Show` dictionary for a polymorphic
            // argument, but are lowered by the print branch below (which also owns
            // the raw/structural fast path for a concrete argument), not by the
            // generic dictionary call.
            Expr::Var(name)
                if !locals.contains_key(name)
                    && self.dicts.contains_key(&f.id)
                    && !matches!(name.as_str(), "print" | "println") =>
            {
                self.dict_call(name, f.id, vals, &mut binds)?
            }
            Expr::Inst(inner, _) => {
                let Expr::Var(name) = &inner.node else {
                    return Err(Error::Ice("instance application on a non-variable".into()));
                };
                self.dict_call(name, f.id, vals, &mut binds)?
            }
            Expr::Var(name) if !locals.contains_key(name) => {
                if let Some(info) = self.ctor(name) {
                    Comp::Return(Value::Ctor(name.clone().into(), info.tag, vals))
                } else if self.effect_ops.contains(name) {
                    Comp::Do(name.clone().into(), vals)
                } else if (name == "print" || name == "println")
                    && !vals.is_empty()
                    && !args.is_empty()
                {
                    let newline = name == "println";
                    let v = vals
                        .into_iter()
                        .next()
                        .ok_or_else(|| Error::Ice("empty print args".into()))?;
                    match self.printable_ty(&args[0], locals) {
                        // A concrete or defaultable argument keeps the
                        // type-directed structural printer: byte-identical output,
                        // no dictionary, raw top-level strings.
                        Some(_) => {
                            if self.route_output {
                                self.out_perform(v, &args[0], locals, newline)
                            } else {
                                let p = self.print_dispatch(v, &args[0], locals)?;
                                if newline {
                                    Comp::Bind(
                                        Box::new(p),
                                        self.fresh().into(),
                                        Box::new(Comp::Io(IoOp::PrintNl, vec![])),
                                    )
                                } else {
                                    p
                                }
                            }
                        }
                        // A polymorphic argument (a rigid type var) has no static
                        // show. The typechecker resolved a `Show` dictionary for it
                        // (from an enclosing `given Show(a)`); render through that
                        // dictionary so `a = Bool` prints `true`/`false`, never the
                        // raw tag integer. A prelude-free program has no `Show`
                        // class and so no dictionary here: it is rejected, with the
                        // raw-printer runtime trap remaining behind that.
                        None => match self.dicts.get(&f.id).and_then(|ds| ds.first()).cloned() {
                            Some(d) => {
                                let shown =
                                    self.method_invoke(Sym::from(SHOW_CLASS), 0, &d, vec![v])?;
                                self.print_string(shown, newline)
                            }
                            None => return Err(show::polymorphic_print(args[0].span)),
                        },
                    }
                } else if name == names::DISPLAY_FN && !vals.is_empty() && !args.is_empty() {
                    // A string-interpolation hole: rendered by the type-directed
                    // display printer (raw for a top-level string), not the
                    // quoting `Show` method.
                    let v = vals
                        .into_iter()
                        .next()
                        .ok_or_else(|| Error::Ice("empty display args".into()))?;
                    self.display_comp(v, &args[0], locals)
                } else if self.needs_dict(name) {
                    return Err(Error::Ice(format!(
                        "no dict record for `{name}` at {:?}",
                        f.span
                    )));
                } else if let Some(closure) = self.eta_partial(name, &vals)? {
                    closure
                } else {
                    Self::head_call(name, vals)?
                }
            }
            _ => {
                let cf = self.elab(f, locals)?;
                let fv = self.fresh();
                binds.push((cf, fv.clone()));
                let force = Comp::Force(Value::Var(fv.into()));
                // A closure value applied to fewer arguments than its type's
                // arity is a partial application; eta-expand it like a known
                // function so an effectful closure lowers correctly.
                match self.under_arity(f.id, vals.len()) {
                    Some(extra) => {
                        let ps: Vec<String> = (0..extra).map(|i| format!("_p{i}")).collect();
                        let mut all = vals;
                        all.extend(ps.iter().map(|p| Value::Var(p.clone().into())));
                        let app = Comp::App(Box::new(force), all);
                        Comp::Return(Value::Thunk(Box::new(Comp::Lam(
                            ps.into_iter().map(Sym::from).collect(),
                            Box::new(app),
                        ))))
                    }
                    None => Comp::App(Box::new(force), vals),
                }
            }
        };
        Ok(wrap_binds(binds, body))
    }

    // `recv[key]`: dispatch on the receiver's checked head type to the failable
    // accessor for that container. tc already proved the receiver indexable, so
    // an unresolved or unexpected type here is a compiler bug.
    fn elab_index(
        &mut self,
        recv: &S<Expr<CorePhase>>,
        key: &S<Expr<CorePhase>>,
        locals: &Locals,
    ) -> Result<Comp, Error> {
        let accessor = match self.checked.span_types.get(&recv.id) {
            Some(Type::Con(n, args)) if n.as_str() == "Array" && args.len() == 1 => "at_array",
            Some(Type::Con(n, args)) if n.as_str() == "HashMap" && args.len() == 1 => "at_hashmap",
            Some(Type::Con(n, args)) if n.as_str() == LIST && args.len() == 1 => "at_list",
            Some(Type::Str) => "at_byte",
            other => {
                return Err(Error::Ice(format!(
                    "indexing receiver is not a known container at {:?}: {other:?}",
                    recv.span
                )))
            }
        };
        let cr = self.elab(recv, locals)?;
        let vr = self.fresh();
        let ck = self.elab(key, locals)?;
        let vk = self.fresh();
        let body = Comp::Call(
            accessor.into(),
            vec![Value::Var(vr.clone().into()), Value::Var(vk.clone().into())],
        );
        Ok(wrap_binds(vec![(cr, vr), (ck, vk)], body))
    }

    // `recv[key] := val`: dispatch on the receiver's head type to the in-place
    // (FBIP) setter builtin. tc restricts writes to `Array`/`HashMap`.
    fn elab_index_set(
        &mut self,
        recv: &S<Expr<CorePhase>>,
        key: &S<Expr<CorePhase>>,
        val: &S<Expr<CorePhase>>,
        locals: &Locals,
    ) -> Result<Comp, Error> {
        let setter = match self.checked.span_types.get(&recv.id) {
            Some(Type::Con(n, args)) if n.as_str() == "Array" && args.len() == 1 => "array_set",
            Some(Type::Con(n, args)) if n.as_str() == "HashMap" && args.len() == 1 => "hm_insert",
            Some(Type::Con(n, args)) if n.as_str() == LIST && args.len() == 1 => "list_set",
            other => {
                return Err(Error::Ice(format!(
                    "indexed assignment target is not a writable container at {:?}: {other:?}",
                    recv.span
                )))
            }
        };
        let cr = self.elab(recv, locals)?;
        let vr = self.fresh();
        let ck = self.elab(key, locals)?;
        let vk = self.fresh();
        let cv = self.elab(val, locals)?;
        let vv = self.fresh();
        // `array_set` is a builtin, `hm_insert` a prelude function; `head_call`
        // emits the right form (StrBuiltin vs Call) for each.
        let body = Self::head_call(
            setter,
            vec![
                Value::Var(vr.clone().into()),
                Value::Var(vk.clone().into()),
                Value::Var(vv.clone().into()),
            ],
        )?;
        Ok(wrap_binds(vec![(cr, vr), (ck, vk), (cv, vv)], body))
    }
}

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
    let arrow = checked.decls.iter().find(|d| d.name == name).map(|d| {
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
    let mut arity: BTreeMap<String, usize> = prog
        .fns
        .iter()
        .filter(|d| !d.konst)
        .map(|d| (d.name.clone(), d.params.len()))
        .collect();
    builtin_arities(&mut arity);
    let effect_ops: BTreeSet<String> = checked.eff_ops.keys().cloned().collect();
    // Route `print`/`println` through the interceptable `Output` ops only when the
    // record/replay/durable machinery is present (the `Replay` module is
    // imported). Otherwise `print` lowers directly to the runtime printer, so the
    // whole non-replay corpus keeps its fused, handler-free output and a program
    // with its own reified handlers is never wrapped in a world handler it cannot
    // fuse through. `Output` interception only changes behaviour where it matters.
    let route_output = effect_ops.contains("out_print")
        && (crate::names::REPLAY_DRIVERS
            .iter()
            .any(|f| arity.contains_key(*f))
            || crate::names::INCR_REPLAY_DRIVERS
                .iter()
                .any(|f| arity.contains_key(*f)));
    let consts: BTreeMap<String, &S<Expr<CorePhase>>> = prog
        .fns
        .iter()
        .filter(|d| d.konst)
        .map(|d| (d.name.clone(), &d.body))
        .collect();

    let mut elab = Elab {
        fresh: Fresh::new(),
        ctors: &checked.ctors,
        arity,
        consts,
        checked,
        dicts: &checked.dicts,
        route_output,
        effect_ops,
        show_fns: Vec::new(),
        show_seen: BTreeSet::new(),
        strict: true,
    };

    let mut fns = Vec::with_capacity(prog.fns.len());
    for d in &prog.fns {
        if d.konst {
            continue;
        }
        let names: Vec<String> = d.params.iter().map(|p| p.name.clone()).collect();
        let mut locals = param_locals(checked, &d.name, &names);
        let mut params = names;
        if !d.constraints.is_empty() {
            let dps: Vec<String> = (0..d.constraints.len()).map(|i| format!("_c{i}")).collect();
            for dp in &dps {
                locals.insert(dp.clone(), None);
            }
            let mut all = dps;
            all.extend(params);
            params = all;
        }
        let body = elab.elab(&d.body, &locals).map_err(|e| match e {
            Error::Ice(m) => Error::Ice(format!("in `{}`: {m}", d.name)),
            other => other,
        })?;
        fns.push(CoreFn {
            name: d.name.clone().into(),
            body,
            params: params.into_iter().map(Sym::from).collect(),
            // The leading `_c{i}` dictionary params prepended just above, one per
            // class constraint (zero when the context is empty).
            dict_arity: d.constraints.len(),
        });
    }

    for inst in &prog.instances {
        let info = checked
            .instances
            .get(&Sym::from(&inst.name))
            .ok_or_else(|| Error::Ice(format!("no instance info for `{}`", inst.name)))?;
        let class = checked
            .classes
            .get(&info.class)
            .ok_or_else(|| Error::Ice(format!("no class info for `{}`", info.class)))?;
        // Dict params: the declared context first (so method bodies' `_c{i}`
        // indices are unchanged), then one per superclass obligation.
        let nctx = info.context.len();
        // The dictionary arity every function in this instance carries: one param
        // per declared context obligation plus one per superclass.
        let ndict = nctx + info.supers.len();
        let dps: Vec<String> = (0..ndict).map(|i| format!("_c{i}")).collect();
        for m in &inst.methods {
            let sig = &class
                .methods
                .iter()
                .find(|(n, _)| n == &m.name)
                .ok_or_else(|| Error::Ice(format!("no class signature for `{}`", m.name)))?
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
            fns.push(CoreFn {
                name: instance_method(&inst.name, &m.name).into(),
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
            fields.push(Value::Var(format!("_c{}", nctx + j).into()));
        }
        for (mname, sig) in &class.methods {
            let arity = match sig {
                Type::Fun(d, _, _) => d.len(),
                _ => 0,
            };
            let ps: Vec<String> = (0..arity).map(|i| format!("_p{i}")).collect();
            let mut args: Vec<Value> = dps.iter().map(|d| Value::Var(d.clone().into())).collect();
            args.extend(ps.iter().map(|p| Value::Var(p.clone().into())));
            let call = Comp::Call(instance_method(&inst.name, mname.as_str()).into(), args);
            fields.push(Value::Thunk(Box::new(Comp::Lam(
                ps.into_iter().map(Sym::from).collect(),
                Box::new(call),
            ))));
        }
        fns.push(CoreFn {
            name: inst.name.clone().into(),
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
    Ok(Core { fns })
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
            let body = elaborate_expr(checked, &d.body, &arity, &checked.dicts, &consts)?;
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
pub fn elaborate_expr(
    checked: &Checked,
    e: &S<Expr<CorePhase>>,
    arity: &BTreeMap<String, usize>,
    dicts: &BTreeMap<NodeId, Vec<Dict>>,
    consts: &BTreeMap<String, S<Expr<CorePhase>>>,
) -> Result<Comp, Error> {
    let effect_ops: BTreeSet<String> = checked.eff_ops.keys().cloned().collect();
    let mut elab = Elab {
        fresh: Fresh::new(),
        ctors: &checked.ctors,
        arity: arity.clone(),
        consts: consts.iter().map(|(k, v)| (k.clone(), v)).collect(),
        checked,
        dicts,
        route_output: effect_ops.contains("out_print")
            && (crate::names::REPLAY_DRIVERS
                .iter()
                .any(|f| arity.contains_key(*f))
                || crate::names::INCR_REPLAY_DRIVERS
                    .iter()
                    .any(|f| arity.contains_key(*f))),
        effect_ops,
        show_fns: Vec::new(),
        show_seen: BTreeSet::new(),
        strict: false,
    };
    elab.elab(e, &Locals::new())
}
