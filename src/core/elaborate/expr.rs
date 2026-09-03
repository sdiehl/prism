//! Expression lowering: the `Elab` walk from checked surface expressions to
//! anonymous Core computations. Declaration and program orchestration stay in
//! the parent module; dictionary, match, and show support live in siblings.

use std::{mem, slice};

use prism_syntax::{kw, names};

use super::{
    builtin, infer_expr_env, show, small_int, to_float_lit, to_wrapped_i64, to_wrapped_u64,
    unboxed_unsupported, wrap_binds, BTreeMap, BTreeSet, BinOp, Builtin, Chain, CheckedHandler,
    Comp, CoreOp, CorePat, CorePhase, CtorInfo, Dict, Elab, Env, Error, Expansion, ExpansionMap,
    Expr, FieldRef, HandleOp, HandlerArm, Indexable, IntLit, IoOp, Locals, NegLane, NodeId,
    NodeRes, PathOp, PathStep, PathTerm, Rc, Span, Suffix, Sym, Type, Value, CONS, DIV_CLASS,
    DIV_MOD_METHOD, DIV_QUOT_METHOD, ELAB_GROW_STACK, ELAB_MIN_STACK, EQ_CLASS, EQ_METHOD, NIL,
    NUM_ADD_METHOD, NUM_CLASS, NUM_FROMINT_METHOD, NUM_MUL_METHOD, NUM_NEG_METHOD, NUM_SUB_METHOD,
    ORD_CLASS, ORD_METHOD, S, SHOW_CLASS,
};

impl Elab<'_> {
    pub(super) fn fresh(&mut self) -> String {
        names::elab_tmp(self.fresh.bump())
    }

    // Lower a product literal: elaborate each element to a fresh bound variable in
    // order, then return the product value `mk` builds from those variables.
    // Shared by boxed tuples and unboxed tuples, which differ only in `mk`.
    pub(super) fn elab_product(
        &mut self,
        elems: &[S<Expr<CorePhase>>],
        locals: &Locals,
        mk: impl FnOnce(Vec<Value>) -> Value,
    ) -> Result<Comp, Error> {
        let mut binds = Vec::new();
        let mut vals = Vec::new();
        for elem in elems {
            let c = self.elab(elem, locals)?;
            let v = self.fresh();
            binds.push((c, v.clone()));
            vals.push(Value::Var(v.into()));
        }
        Ok(wrap_binds(binds, Comp::Return(mk(vals))))
    }

    pub(super) fn ctor(&self, name: &str) -> Option<&CtorInfo> {
        self.ctors.get(name)
    }

    pub(super) fn extract_field_of(
        scrut: Value,
        ctor: &str,
        fi: usize,
        n: usize,
        out: String,
    ) -> Comp {
        let binders = (0..n).map(|j| (j == fi).then(|| Sym::from(&out))).collect();
        let pat = CorePat::Ctor(Sym::from(ctor), binders);
        Comp::Case(scrut, vec![(pat, Comp::Return(Value::Var(out.into())))])
    }

    pub(super) fn field_access(
        &mut self,
        id: NodeId,
        recv: &S<Expr<CorePhase>>,
        field: &str,
        locals: &Locals,
    ) -> Result<Comp, Error> {
        let ce = self.elab(recv, locals)?;
        let ve = self.fresh();
        let vf = self.fresh();
        let Some(NodeRes::Field(field_ref)) = self.hir.res(id) else {
            return Err(Error::InternalInvariant(format!(
                "missing checked resolution for field `{field}` at node {}",
                id.0
            )));
        };
        let extract = Self::extract_field_of(
            Value::Var(ve.clone().into()),
            &field_ref.ctor,
            field_ref.index,
            field_ref.arity,
            vf,
        );
        Ok(Comp::Bind(Box::new(ce), ve.into(), Box::new(extract)))
    }

    // Project the `fi`-th component out of a positional product (an unboxed record
    // lowered to a tuple). A `Case` binding only that field and returning it
    // reuses the product-destructuring RC and pattern machinery, so the projection
    // is refcount-balanced by construction (the unbound fields drop, the bound one
    // transfers out) exactly as a `let (_, x, _) = t` would be.
    pub(super) fn extract_tuple_field_of(scrut: Value, fi: usize, n: usize, out: String) -> Comp {
        let binders = (0..n).map(|j| (j == fi).then(|| Sym::from(&out))).collect();
        let pat = CorePat::Tuple(binders);
        Comp::Case(scrut, vec![(pat, Comp::Return(Value::Var(out.into())))])
    }

    // An unboxed record lowers to a positional unboxed tuple in its type's field
    // order (which its value always matches, since record types unify only at the
    // same field order). Field names are erased into positions; projection
    // recovers them by index.
    pub(super) fn elab_unboxed_record(
        &mut self,
        fields: &[(String, S<Expr<CorePhase>>)],
        locals: &Locals,
    ) -> Result<Comp, Error> {
        let mut binds = Vec::new();
        let mut vals = Vec::new();
        for (_, elem) in fields {
            let c = self.elab(elem, locals)?;
            let v = self.fresh();
            binds.push((c, v.clone()));
            vals.push(Value::Var(v.into()));
        }
        Ok(wrap_binds(binds, Comp::Return(Value::UnboxedTuple(vals))))
    }

    // Field projection is a positional tuple `Case`: the type checker resolved the
    // field to its index (the HIR's recorded resolution), so this reuses product
    // destructuring and its refcount handling.
    pub(super) fn elab_unboxed_field(
        &mut self,
        id: NodeId,
        recv: &S<Expr<CorePhase>>,
        span: Span,
        locals: &Locals,
    ) -> Result<Comp, Error> {
        let Some(&NodeRes::UnboxedField(fi, n)) = self.hir.res(id) else {
            return Err(unboxed_unsupported(span));
        };
        let ce = self.elab(recv, locals)?;
        let ve = self.fresh();
        let vf = self.fresh();
        let extract = Self::extract_tuple_field_of(Value::Var(ve.clone().into()), fi, n, vf);
        Ok(Comp::Bind(Box::new(ce), ve.into(), Box::new(extract)))
    }

    // Nested rebuild along each path: one single-arm Case per level, each arm
    // ending in Return(Ctor), the exact shape the reuse analysis rewrites to
    // in-place mutation when the spine is uniquely owned.
    pub(super) fn elab_update_path(
        &mut self,
        id: NodeId,
        base_expr: &S<Expr<CorePhase>>,
        ups: &[(Vec<PathStep<CorePhase>>, PathOp<CorePhase>)],
        locals: &Locals,
    ) -> Result<Comp, Error> {
        let Some(NodeRes::Paths(chains)) = self.hir.res(id) else {
            return Err(Error::InternalInvariant(format!(
                "missing checked update-path resolution for node {}",
                id.0
            )));
        };
        let chains = chains.clone();
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
    pub(super) fn rebuild_path(
        &mut self,
        scrut: &str,
        items: Vec<(Chain, PathTerm)>,
    ) -> Result<Comp, Error> {
        let FieldRef {
            ctor: cname,
            arity: n,
            ..
        } = items
            .first()
            .and_then(|(chain, _)| chain.first())
            .ok_or_else(|| Error::InternalInvariant("empty record-update path".into()))?
            .clone();
        let tag = self.ctors.get(&cname).map_or(0, |i| i.tag);
        let fields: Vec<String> = (0..n).map(|_| self.fresh()).collect();
        let mut vals: Vec<Value> = fields
            .iter()
            .map(|f| Value::Var(f.clone().into()))
            .collect();
        let mut groups: BTreeMap<usize, Vec<(Chain, PathTerm)>> = BTreeMap::new();
        for (chain, v) in items {
            groups.entry(chain[0].index).or_default().push((chain, v));
        }
        let mut binds = Vec::new();
        for (fi, group) in groups {
            if group[0].0.len() == 1 {
                let term = group
                    .into_iter()
                    .next()
                    .ok_or_else(|| {
                        Error::InternalInvariant("empty record-update path group".into())
                    })?
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

    pub(super) fn local_env(locals: &Locals) -> Env {
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

    pub(super) fn infer_local(&self, e: &S<Expr<CorePhase>>, locals: &Locals) -> Option<Type> {
        infer_expr_env(self.checked, &Self::local_env(locals), e)
            .ok()
            .map(|(t, _)| t)
    }

    pub(super) fn local_ty(&self, e: &S<Expr<CorePhase>>, locals: &Locals) -> Option<Type> {
        self.hir
            .node_type(e.id)
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
    pub(super) fn int_value(&self, lit: &IntLit, id: NodeId) -> Comp {
        let fixed = match lit.suffix {
            Suffix::I64 => Some(Type::I64),
            Suffix::U64 => Some(Type::U64),
            Suffix::None => self.hir.lane(id).cloned(),
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

    pub(super) fn fixed_bin(
        &mut self,
        op: BinOp,
        ty: &Type,
        args: Vec<Value>,
    ) -> Result<Comp, Error> {
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
                let core_op = CoreOp::from_binop(op).ok_or_else(|| {
                    Error::InternalInvariant(format!("`{op:?}` is not a primitive op"))
                })?;
                return Ok(Comp::Bind(
                    Box::new(Comp::StrBuiltin(cmp, args)),
                    c.clone().into(),
                    Box::new(Comp::Prim(core_op, Value::Var(c.into()), Value::Int(0))),
                ));
            }
        };
        Ok(Comp::StrBuiltin(b, args))
    }

    // The `Float` lane of the arithmetic and comparison operators. `%` is `fmod`
    // (a two-argument builtin, not a `CoreOp`); the rest are float `CoreOp`s.
    pub(super) fn float_bin(op: BinOp, va: &Value, vb: &Value) -> Result<Comp, Error> {
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
            _ => {
                return Err(Error::InternalInvariant(format!(
                    "`{op:?}` is not a float numeric op"
                )))
            }
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
    pub(super) fn elab_neg(
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
                if self.hir.evidence(id).is_some() {
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
        if let Some(ds) = self.hir.evidence(id).map(<[Dict]>::to_vec) {
            let d0 = ds.first().ok_or_else(|| {
                Error::InternalInvariant("empty dictionary set for unary minus".into())
            })?;
            let idx = self
                .checked
                .dispatch
                .classes
                .get(&Sym::from(NUM_CLASS))
                .and_then(|c| {
                    c.methods
                        .iter()
                        .position(|(n, _)| n.as_str() == NUM_NEG_METHOD)
                })
                .ok_or_else(|| {
                    Error::InternalInvariant(format!("no `{NUM_NEG_METHOD}` method on class Num"))
                })?;
            let call = self.method_invoke(Sym::from(NUM_CLASS), idx, d0, vec![operand])?;
            return Ok(Comp::Bind(Box::new(c), v.into(), Box::new(call)));
        }
        let lane = match self.hir.lane(id).cloned() {
            Some(Type::I64) => NegLane::I64,
            Some(Type::Float) => NegLane::Float,
            _ => NegLane::Int,
        };
        let neg = Comp::Neg(lane, operand);
        Ok(Comp::Bind(Box::new(c), v.into(), Box::new(neg)))
    }

    pub(super) fn negate(&mut self, c: Comp) -> Comp {
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

    pub(super) fn elab_eq(
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
        let (cmp, neg) = if let Some(ds) = self.hir.evidence(id).map(<[Dict]>::to_vec) {
            let idx = self
                .checked
                .dispatch
                .classes
                .get(&Sym::from(EQ_CLASS))
                .and_then(|c| c.methods.iter().position(|(n, _)| n.as_str() == EQ_METHOD))
                .ok_or_else(|| Error::InternalInvariant("no `eq` method on class Eq".into()))?;
            let d0 = ds
                .first()
                .ok_or_else(|| Error::InternalInvariant("no dictionary for `==`".into()))?;
            (self.method_invoke(Sym::from(EQ_CLASS), idx, d0, args)?, ne)
        } else {
            match self.hir.lane(id).cloned() {
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
                        if let Some(t) = self.hir.node_type(a.id) {
                            if !matches!(t, Type::Int | Type::Exist(_)) {
                                return Err(Error::InternalInvariant(format!(
                                    "missing Eq dispatch record at {:?} for type {}",
                                    span,
                                    t.show()
                                )));
                            }
                        }
                    }
                    let core_op = CoreOp::from_binop(op).ok_or_else(|| {
                        Error::InternalInvariant(format!("`{op:?}` is not a primitive op"))
                    })?;
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
    pub(super) fn elab_ord(
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
        let ds = self.hir.evidence(id).map(<[Dict]>::to_vec).ok_or_else(|| {
            Error::InternalInvariant("no dictionary for comparison operator".into())
        })?;
        let d0 = ds.first().ok_or_else(|| {
            Error::InternalInvariant("empty dictionary set for comparison operator".into())
        })?;
        let idx = self
            .checked
            .dispatch
            .classes
            .get(&Sym::from(ORD_CLASS))
            .and_then(|c| c.methods.iter().position(|(n, _)| n.as_str() == ORD_METHOD))
            .ok_or_else(|| Error::InternalInvariant("no `cmp` method on class Ord".into()))?;
        let cmp = self.method_invoke(Sym::from(ORD_CLASS), idx, d0, args)?;
        let r = self.fresh();
        let core_op = CoreOp::from_binop(op)
            .ok_or_else(|| Error::InternalInvariant(format!("`{op:?}` is not a primitive op")))?;
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
    pub(super) fn elab_arith(
        &mut self,
        op: BinOp,
        a: &S<Expr<CorePhase>>,
        b: &S<Expr<CorePhase>>,
        id: NodeId,
        locals: &Locals,
    ) -> Result<Comp, Error> {
        let (class, method) = Self::arith_method(op).ok_or_else(|| {
            Error::InternalInvariant(format!("`{op:?}` is not a tower arithmetic op"))
        })?;
        let ca = self.elab(a, locals)?;
        let cb = self.elab(b, locals)?;
        let va = self.fresh();
        let vb = self.fresh();
        let args = vec![Value::Var(va.clone().into()), Value::Var(vb.clone().into())];
        let ds = self.hir.evidence(id).map(<[Dict]>::to_vec).ok_or_else(|| {
            Error::InternalInvariant("no dictionary for arithmetic operator".into())
        })?;
        let d0 = ds.first().ok_or_else(|| {
            Error::InternalInvariant("empty dictionary set for arithmetic operator".into())
        })?;
        let idx = self
            .checked
            .dispatch
            .classes
            .get(&Sym::from(class))
            .and_then(|c| c.methods.iter().position(|(n, _)| n.as_str() == method))
            .ok_or_else(|| {
                Error::InternalInvariant(format!("no `{method}` method on class {class}"))
            })?;
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
    pub(super) fn elab_from_int_lit(&mut self, lit: &IntLit, id: NodeId) -> Result<Comp, Error> {
        let int_comp = self.int_value(lit, id);
        let ds =
            self.hir.evidence(id).map(<[Dict]>::to_vec).ok_or_else(|| {
                Error::InternalInvariant("no dictionary for numeric literal".into())
            })?;
        let d0 = ds.first().ok_or_else(|| {
            Error::InternalInvariant("empty dictionary set for numeric literal".into())
        })?;
        let idx = self
            .checked
            .dispatch
            .classes
            .get(&Sym::from(NUM_CLASS))
            .and_then(|c| {
                c.methods
                    .iter()
                    .position(|(n, _)| n.as_str() == NUM_FROMINT_METHOD)
            })
            .ok_or_else(|| {
                Error::InternalInvariant(format!("no `{NUM_FROMINT_METHOD}` method on class Num"))
            })?;
        let v = self.fresh();
        let call = self.method_invoke(
            Sym::from(NUM_CLASS),
            idx,
            d0,
            vec![Value::Var(v.clone().into())],
        )?;
        Ok(Comp::Bind(Box::new(int_comp), v.into(), Box::new(call)))
    }

    // Run one sub-elaboration under a different set of expandable bindings,
    // restoring the caller's on the way out.
    pub(super) fn with_expansion<R>(
        &mut self,
        map: ExpansionMap,
        under: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let saved = mem::replace(&mut self.expansion, map);
        let out = under(self);
        self.expansion = saved;
        out
    }

    // Run one sub-elaboration with `names` hidden from the expansion map. Every
    // binder must go through this: an inner binding of a name a polymorphic
    // `let` also binds shadows that `let`, and expanding the outer value under
    // the inner binding would read the wrong variable.
    pub(super) fn shadowing<'n, R>(
        &mut self,
        names: impl IntoIterator<Item = &'n str>,
        under: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let mut scoped = self.expansion.clone();
        for name in names {
            scoped.remove(name);
        }
        self.with_expansion(scoped, under)
    }

    pub(super) fn elab(&mut self, e: &S<Expr<CorePhase>>, locals: &Locals) -> Result<Comp, Error> {
        // Elaboration recurses per surface node, so a long statement block (a
        // right-nested `Let` chain) is deep recursion; grow stack segments on
        // demand, same discipline as the desugar rewrite and typed-Core builder.
        stacker::maybe_grow(ELAB_MIN_STACK, ELAB_GROW_STACK, || {
            self.elab_inner(e, locals)
        })
    }

    #[allow(clippy::too_many_lines)] // One arm per expression form; splitting hides the total.
    pub(super) fn elab_inner(
        &mut self,
        e: &S<Expr<CorePhase>>,
        locals: &Locals,
    ) -> Result<Comp, Error> {
        Ok(match &e.node {
            Expr::Int(lit) if self.hir.evidence(e.id).is_some() => {
                self.elab_from_int_lit(lit, e.id)?
            }
            Expr::Int(lit) => self.int_value(lit, e.id),
            Expr::Float(f) => Comp::Return(Value::Float(*f)),
            Expr::Char(c) => Comp::Return(Value::Int(i64::from(u32::from(*c)))),
            Expr::Bool(b) => Comp::Return(Value::Bool(*b)),
            Expr::Unit => Comp::Return(Value::Unit),
            Expr::Str(s) => Comp::Return(Value::Str(s.clone())),
            Expr::Hole(name) => Comp::Error(Value::Str(prism_syntax::error::typed_hole_fault(
                name, e.span,
            ))),
            // Bare `Null` is the nullary nullable constructor (tag 0, no payload).
            Expr::Var(x) if x == kw::CTOR_NULL && !locals.contains_key(x) => {
                Comp::Return(Value::Ctor(x.clone().into(), kw::OR_NULL_TAG, vec![]))
            }
            Expr::Var(x) => {
                if let Some(bound) = self.expansion.get(x).cloned() {
                    // A type-polymorphic local `let`: elaborate its value here,
                    // in the scope and expansion map it was written in, so this
                    // use gets the type checking chose for this use.
                    let outer = bound.snapshot.clone();
                    self.with_expansion(outer, |s| s.elab(&bound.value, &bound.locals))?
                } else if locals.contains_key(x) {
                    Comp::Return(Value::Var(x.clone().into()))
                } else if let Some(body) = self.consts.get(x).copied() {
                    // A constant's body sees globals only, so it elaborates in
                    // an empty scope; the expandable bindings empty with it, or
                    // a polymorphic `let` at the use site would capture the
                    // constant's reference to a same-named global.
                    self.with_expansion(ExpansionMap::new(), |s| s.elab(body, &Locals::new()))?
                } else if self.hir.evidence(e.id).is_some() {
                    self.constrained_value(x, e.id)?
                } else if self.needs_dict(x) {
                    return Err(Error::InternalInvariant(format!(
                        "no dict record for `{x}` at {:?}",
                        e.span
                    )));
                } else {
                    self.value_global(x)?
                }
            }
            Expr::Inst(inner, _) => {
                let Expr::Var(x) = &inner.node else {
                    return Err(Error::InternalInvariant(
                        "instance application on a non-variable".into(),
                    ));
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
                if self.hir.evidence(e.id).is_some() =>
            {
                self.elab_ord(*op, a, b, e.id, locals)?
            }
            Expr::Bin(
                op @ (BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem),
                a,
                b,
            ) if self.hir.evidence(e.id).is_some() => self.elab_arith(*op, a, b, e.id, locals)?,
            Expr::Bin(op, a, b) => {
                let ca = self.elab(a, locals)?;
                let cb = self.elab(b, locals)?;
                let va = self.fresh();
                let vb = self.fresh();
                let lhs_val = Value::Var(va.clone().into());
                let rhs_val = Value::Var(vb.clone().into());
                let args = vec![lhs_val.clone(), rhs_val.clone()];
                let prim = match self.hir.lane(e.id).cloned() {
                    Some(ty @ (Type::I64 | Type::U64)) => self.fixed_bin(*op, &ty, args)?,
                    // The tower brought `Float` onto the plain operators; lower to the
                    // float primitive `CoreOp`.
                    Some(Type::Float) => Self::float_bin(*op, &lhs_val, &rhs_val)?,
                    _ => {
                        let core_op = CoreOp::from_binop(*op).ok_or_else(|| {
                            Error::InternalInvariant(format!("`{op:?}` is not a primitive op"))
                        })?;
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
            Expr::Let(x, v, b) if self.hir.poly_let(v.id) => {
                // The value generalized over types, and a `Bind` would fix one
                // of them. Emit no bind: record the value with the scope it was
                // written in, and let each use elaborate it at that use's own
                // type. The name still enters `locals`, where it shadows a
                // same-named global and routes call sites through the generic
                // force-and-apply path; the type slot is empty because the
                // binding has no one type for it to hold.
                let bound = Rc::new(Expansion {
                    value: (**v).clone(),
                    locals: locals.clone(),
                    snapshot: self.expansion.clone(),
                });
                let mut l2 = locals.clone();
                l2.insert(x.clone(), None);
                let mut scoped = self.expansion.clone();
                scoped.insert(x.clone(), bound);
                self.with_expansion(scoped, |s| s.elab(b, &l2))?
            }
            Expr::Let(x, v, b) => {
                let cv = self.elab(v, locals)?;
                // HIR-first (`local_ty`): the checker already recorded the
                // bound expression's zonked type, so re-inference (which
                // rebuilds a full checker Env from every visible local, an
                // O(scope) cost per `let` that made long statement blocks
                // quadratic) is only the fallback for nodes whose recorded
                // type still carries free existentials.
                let ty = self.local_ty(v, locals);
                let mut l2 = locals.clone();
                l2.insert(x.clone(), ty);
                let cb = self.shadowing([x.as_str()], |s| s.elab(b, &l2))?;
                Comp::Bind(Box::new(cv), x.clone().into(), Box::new(cb))
            }
            Expr::Lam(ps, body) => {
                let names: Vec<String> = ps.iter().map(|p| p.name.clone()).collect();
                let mut l2 = locals.clone();
                l2.extend(names.iter().map(|n| (n.clone(), None)));
                let cb = self.shadowing(names.iter().map(String::as_str), |s| s.elab(body, &l2))?;
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
            Expr::UnboxedRecord(fields) => self.elab_unboxed_record(fields, locals)?,
            Expr::UnboxedField(recv, _) => self.elab_unboxed_field(e.id, recv, e.span, locals)?,
            Expr::Tuple(elems) => self.elab_product(elems, locals, Value::Tuple)?,
            // An unboxed tuple lowers exactly like a boxed one; only its Core value
            // node (and later its ABI) differs, so its observable behavior is
            // identical.
            Expr::UnboxedTuple(elems) => self.elab_product(elems, locals, Value::UnboxedTuple)?,
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
            Expr::FieldAccess(recv, field) => self.field_access(e.id, recv, field, locals)?,
            Expr::RecordCreate(ctor_name, field_exprs) => {
                if let Some(info) = self.ctors.get(ctor_name).cloned() {
                    let n_fields = info.args.len();
                    let mut ordered: Vec<Option<(Comp, String)>> = vec![None; n_fields];
                    for (fname, fexpr) in field_exprs {
                        if let Some(fi) = info.fields.iter().position(|f| f.as_str() == fname) {
                            let c = self.elab(fexpr, locals)?;
                            let v = self.fresh();
                            ordered[fi] = Some((c, v));
                        }
                    }
                    let mut binds = Vec::new();
                    let mut vals = Vec::new();
                    for opt in ordered {
                        let (c, v) = opt.ok_or_else(|| {
                            Error::InternalInvariant(format!("missing field in record {ctor_name}"))
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
            Expr::Handle(body, arms, _) => {
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
                            let compiled =
                                self.shadowing([x.as_str()], |s| s.elab(arm_body, &l2))?;
                            return_body = Some(Box::new(compiled));
                        }
                        HandlerArm::Op(name, params, resume_var, arm_body) => {
                            let mut l2 = locals.clone();
                            l2.extend(params.iter().map(|p| (p.clone(), None)));
                            l2.insert(resume_var.clone(), None);
                            let bound = params
                                .iter()
                                .chain(slice::from_ref(resume_var))
                                .map(String::as_str);
                            let compiled = self.shadowing(bound, |s| s.elab(arm_body, &l2))?;
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
                    // Sole validating build; the checker already rejects dups (E5008).
                    ops: CheckedHandler::new(ops).expect("checker rejects duplicate ops"),
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
                        if let Some(fi) = info.fields.iter().position(|f| f.as_str() == fname) {
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
                    .defs
                    .eff_ops
                    .iter()
                    .filter(|(_, i)| i.effect_name.as_str() == eff)
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
    pub(super) fn eta_partial(&self, name: &str, given: &[Value]) -> Result<Option<Comp>, Error> {
        if builtin(name).is_some() {
            return Ok(None);
        }
        let Some(&arity) = self.arity.get(name) else {
            return Ok(None);
        };
        if given.len() >= arity {
            return Ok(None);
        }
        let ps: Vec<String> = (given.len()..arity).map(names::generated_param).collect();
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
    pub(super) fn under_arity(&self, id: NodeId, given: usize) -> Option<usize> {
        let mut ty = self.hir.node_type(id)?;
        while let Type::Forall(_, b) | Type::RowForall(_, b) = ty {
            ty = b;
        }
        match ty {
            Type::Fun(params, _, _) if params.len() > given => Some(params.len() - given),
            _ => None,
        }
    }

    pub(super) fn elab_call(
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
                    && self.hir.evidence(f.id).is_some()
                    && !matches!(name.as_str(), "print" | "println") =>
            {
                self.dict_call(name, f.id, vals, &mut binds)?
            }
            Expr::Inst(inner, _) => {
                let Expr::Var(name) = &inner.node else {
                    return Err(Error::InternalInvariant(
                        "instance application on a non-variable".into(),
                    ));
                };
                self.dict_call(name, f.id, vals, &mut binds)?
            }
            // `This(v)` is the unary nullable constructor (tag 1, one payload).
            Expr::Var(name) if !locals.contains_key(name) && name == kw::CTOR_THIS => {
                Comp::Return(Value::Ctor(name.clone().into(), kw::OR_THIS_TAG, vals))
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
                        .ok_or_else(|| Error::InternalInvariant("empty print args".into()))?;
                    match self.printable_ty(&args[0], locals) {
                        // A concrete or defaultable argument keeps the
                        // type-directed structural printer: byte-identical output,
                        // no dictionary, raw top-level strings.
                        Some(_) => {
                            if self.route_output {
                                self.out_perform(v, &args[0], locals, newline)?
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
                        None => match self.hir.evidence(f.id).and_then(<[Dict]>::first).cloned() {
                            Some(d) => {
                                let shown =
                                    self.method_invoke(Sym::from(SHOW_CLASS), 0, &d, vec![v])?;
                                self.print_string(shown, newline)
                            }
                            None => return Err(show::polymorphic_print(args[0].span)),
                        },
                    }
                } else if name == names::DISPLAY_FN && !vals.is_empty() && !args.is_empty() {
                    // A string-interpolation hole. A concrete or defaultable type
                    // renders through the type-directed display printer (raw for a
                    // top-level string), byte-identical across tiers. A polymorphic
                    // hole (a rigid type var) has no static printer, so it is
                    // rejected with the same diagnostic as a polymorphic `print`
                    // (which points at `show(x)`); never fall back to the integer
                    // printer, which would misread a non-Int value and diverge
                    // native output from the interpreter. `display_comp` enforces
                    // the same rule for its other caller.
                    let v = vals
                        .into_iter()
                        .next()
                        .ok_or_else(|| Error::InternalInvariant("empty display args".into()))?;
                    self.display_comp(v, &args[0], locals)?
                } else if self.needs_dict(name) {
                    return Err(Error::InternalInvariant(format!(
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
                        let ps: Vec<String> = (0..extra).map(names::generated_param).collect();
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
    pub(super) fn elab_index(
        &mut self,
        recv: &S<Expr<CorePhase>>,
        key: &S<Expr<CorePhase>>,
        locals: &Locals,
    ) -> Result<Comp, Error> {
        let accessor = self
            .hir
            .node_type(recv.id)
            .and_then(Indexable::classify)
            .map(Indexable::getter)
            .ok_or_else(|| {
                Error::InternalInvariant(format!(
                    "indexing receiver is not a known container at {:?}",
                    recv.span
                ))
            })?;
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
    pub(super) fn elab_index_set(
        &mut self,
        recv: &S<Expr<CorePhase>>,
        key: &S<Expr<CorePhase>>,
        val: &S<Expr<CorePhase>>,
        locals: &Locals,
    ) -> Result<Comp, Error> {
        let setter = self
            .hir
            .node_type(recv.id)
            .and_then(Indexable::classify)
            .and_then(Indexable::setter)
            .ok_or_else(|| {
                Error::InternalInvariant(format!(
                    "indexed assignment target is not a writable container at {:?}",
                    recv.span
                ))
            })?;
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
