use std::collections::{BTreeMap, BTreeSet};
use std::slice;

use marginalia::Span;
use num_bigint::Sign;

use super::builtins::{builtin, Builtin, BuiltinKind, FloatOp, BUILTINS};
use super::cbpv::{Comp, Core, CoreFn, CoreOp, CorePat, HandleOp, Value};
use crate::error::{Error, TypeError};
use crate::fresh::Fresh;
use crate::names::{self, dict_ctor, instance_method};
use crate::sym::Sym;
use crate::syntax::ast::{
    Arm, BigInt, BinOp, Core as CorePhase, Expr, HandlerArm, IntLit, Pattern, Program, Spanned,
    Suffix, S,
};
use crate::types::{infer_expr_env, Checked, CtorInfo, Dict, Env, Type, CONS, EQ_CLASS, LIST, NIL};

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
    dicts: &'a BTreeMap<Span, Vec<Dict>>,
    effect_ops: BTreeSet<String>,
    show_fns: Vec<CoreFn>,
    show_seen: BTreeSet<String>,
    // True when `dicts` and the span tables come from the same check() pass.
    // REPL re-inference uses fresh spans, so span-keyed integrity checks are off.
    strict: bool,
}

type Locals = BTreeMap<String, Option<Type>>;

// A resolved update path: (ctor name, field index, arity) per segment.
type Chain = Vec<(String, usize, usize)>;

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
    fn path_chain_fallback(&self, path: &[String]) -> Result<Chain, Error> {
        path.iter()
            .map(|seg| {
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
    // ending in Return(Ctor), the exact shape Perceus turns into in-place
    // reuse when the spine is uniquely owned.
    fn elab_update_path(
        &mut self,
        span: Span,
        base_expr: &S<Expr<CorePhase>>,
        ups: &[(Vec<String>, S<Expr<CorePhase>>)],
        locals: &Locals,
    ) -> Result<Comp, Error> {
        let chains: Vec<Chain> = match self.checked.path_res.get(&span) {
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
        for ((_, val), chain) in ups.iter().zip(chains) {
            let c = self.elab(val, locals)?;
            let v = self.fresh();
            binds.push((c, v.clone()));
            items.push((chain, Value::Var(v.into())));
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
    fn rebuild_path(&mut self, scrut: &str, items: Vec<(Chain, Value)>) -> Result<Comp, Error> {
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
        let mut groups: BTreeMap<usize, Vec<(Chain, Value)>> = BTreeMap::new();
        for (chain, v) in items {
            groups.entry(chain[0].1).or_default().push((chain, v));
        }
        let mut binds = Vec::new();
        for (fi, group) in groups {
            if group[0].0.len() == 1 {
                vals[fi] = group
                    .into_iter()
                    .next()
                    .ok_or_else(|| Error::Ice("empty record-update path group".into()))?
                    .1;
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
            .get(&e.span)
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
    fn int_value(&self, lit: &IntLit, span: Span) -> Comp {
        let fixed = match lit.suffix {
            Suffix::I64 => Some(Type::I64),
            Suffix::U64 => Some(Type::U64),
            Suffix::None => self.checked.fixed.get(&span).cloned(),
        };
        match fixed {
            Some(Type::I64) => Comp::Return(Value::I64(to_wrapped_i64(&lit.value))),
            Some(Type::U64) => Comp::Return(Value::U64(to_wrapped_u64(&lit.value))),
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
        span: marginalia::Span,
        locals: &Locals,
    ) -> Result<Comp, Error> {
        let ca = self.elab(a, locals)?;
        let cb = self.elab(b, locals)?;
        let va = self.fresh();
        let vb = self.fresh();
        let args = vec![Value::Var(va.clone().into()), Value::Var(vb.clone().into())];
        let ne = op == BinOp::Ne;
        let (cmp, neg) = if let Some(ds) = self.dicts.get(&span).cloned() {
            let idx = self
                .checked
                .classes
                .get(EQ_CLASS)
                .and_then(|c| c.methods.iter().position(|(n, _)| n == "eq"))
                .ok_or_else(|| Error::Ice("no `eq` method on class Eq".into()))?;
            (self.method_invoke(EQ_CLASS, idx, &ds[0], args), ne)
        } else {
            match self.checked.fixed.get(&span).cloned() {
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
                        if let Some(t) = self.checked.span_types.get(&a.span) {
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

    fn elab(&mut self, e: &S<Expr<CorePhase>>, locals: &Locals) -> Result<Comp, Error> {
        Ok(match &e.node {
            Expr::Int(lit) => self.int_value(lit, e.span),
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
                } else if self.dicts.contains_key(&e.span) {
                    self.constrained_value(x, e.span)?
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
                self.constrained_value(x, e.span)?
            }
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
                self.elab_eq(*op, a, b, e.span, locals)?
            }
            Expr::Bin(op, a, b) => {
                let ca = self.elab(a, locals)?;
                let cb = self.elab(b, locals)?;
                let va = self.fresh();
                let vb = self.fresh();
                let args = vec![Value::Var(va.clone().into()), Value::Var(vb.clone().into())];
                let prim = if let Some(ty @ (Type::I64 | Type::U64)) =
                    self.checked.fixed.get(&e.span).cloned()
                {
                    self.fixed_bin(*op, &ty, args)?
                } else {
                    let core_op = CoreOp::from_binop(*op)
                        .ok_or_else(|| Error::Ice(format!("`{op:?}` is not a primitive op")))?;
                    Comp::Prim(
                        core_op,
                        Value::Var(va.clone().into()),
                        Value::Var(vb.clone().into()),
                    )
                };
                Comp::Bind(
                    Box::new(ca),
                    va.into(),
                    Box::new(Comp::Bind(Box::new(cb), vb.into(), Box::new(prim))),
                )
            }
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
                let extract = if let Some((ctor, fi, n)) = self.checked.field_res.get(&e.span) {
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
                self.elab_update_path(e.span, base_expr, ups, locals)?
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

    // A user function applied to fewer arguments than its arity is a partial
    // application. Elaborate it to an explicit closure that captures the given
    // arguments, takes the rest, and calls the function at full arity inside.
    // Effect lowering then sees a real lambda whose body is a full call rather
    // than a partial `Call` it would wrongly lower as a full effectful call
    // (which silently miscompiled partial applications of effectful functions).
    // Returns None for builtins and for saturated or over-saturated calls.
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
    fn under_arity(&self, span: Span, given: usize) -> Option<usize> {
        let mut ty = self.checked.span_types.get(&span)?;
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
            Expr::Var(name) if !locals.contains_key(name) && self.dicts.contains_key(&f.span) => {
                self.dict_call(name, f.span, vals, &mut binds)?
            }
            Expr::Inst(inner, _) => {
                let Expr::Var(name) = &inner.node else {
                    return Err(Error::Ice("instance application on a non-variable".into()));
                };
                self.dict_call(name, f.span, vals, &mut binds)?
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
                    let v = vals
                        .into_iter()
                        .next()
                        .ok_or_else(|| Error::Ice("empty print args".into()))?;
                    let p = self.print_dispatch(v, &args[0], locals);
                    if name == "println" {
                        Comp::Bind(Box::new(p), self.fresh().into(), Box::new(Comp::PrintNl))
                    } else {
                        p
                    }
                } else if name == "show" && !vals.is_empty() && !args.is_empty() {
                    let v = vals
                        .into_iter()
                        .next()
                        .ok_or_else(|| Error::Ice("empty show args".into()))?;
                    self.show_dispatch(v, &args[0], locals)?
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
                match self.under_arity(f.span, vals.len()) {
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
        fns.push(CoreFn {
            name: d.name.clone().into(),
            body: elab.elab(&d.body, &locals)?,
            params: params.into_iter().map(Sym::from).collect(),
        });
    }

    for inst in &prog.instances {
        let info = &checked.instances[&inst.name];
        let class = &checked.classes[&info.class];
        // Dict params: the declared context first (so method bodies' `_c{i}`
        // indices are unchanged), then one per superclass obligation.
        let nctx = info.context.len();
        let dps: Vec<String> = (0..(nctx + info.supers.len()))
            .map(|i| format!("_c{i}"))
            .collect();
        for m in &inst.methods {
            let sig = &class
                .methods
                .iter()
                .find(|(n, _)| n == &m.name)
                .ok_or_else(|| Error::Ice(format!("no class signature for `{}`", m.name)))?
                .1;
            let expected = sig.subst_var(Sym::from(&class.param), &info.head);
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
            let call = Comp::Call(instance_method(&inst.name, mname).into(), args);
            fields.push(Value::Thunk(Box::new(Comp::Lam(
                ps.into_iter().map(Sym::from).collect(),
                Box::new(call),
            ))));
        }
        fns.push(CoreFn {
            name: inst.name.clone().into(),
            params: dps.into_iter().map(Sym::from).collect(),
            body: Comp::Return(Value::Ctor(dict_ctor(&info.class).into(), 0, fields)),
        });
    }

    fns.append(&mut elab.show_fns);
    Ok(Core { fns })
}

/// # Errors
/// Fails when the expression cannot be elaborated to core.
pub fn elaborate_expr(
    checked: &Checked,
    e: &S<Expr<CorePhase>>,
    arity: &BTreeMap<String, usize>,
    dicts: &BTreeMap<Span, Vec<Dict>>,
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
        effect_ops,
        show_fns: Vec::new(),
        show_seen: BTreeSet::new(),
        strict: false,
    };
    elab.elab(e, &Locals::new())
}
