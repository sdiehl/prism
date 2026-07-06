use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use super::env::{collect_type_vars, Annot};
use super::{
    ClassInfo, Entry, Env, HandlerFrame, IndexOp, InstInfo, RowScope, SelfRef, Tc, Wanted,
};
use crate::error::TypeError;
use crate::sym::Sym;
use crate::syntax::ast::{self, BinOp, Core, Decl, Expr, HandlerArm, NodeId, PathOp, PathStep, S};
use crate::types::ty::{
    EffRow, Effects, Label, Type, DIV_CLASS, EQ_CLASS, LIST, NUM_CLASS, ORD_CLASS, SHOW_CLASS,
};

mod defaulting;
mod diagnostics;
mod paths;

use defaulting::{default_open_rows, NumClass};
use diagnostics::{forall_ty_binders, poly_recursion_hint};
use paths::{field_prefix, show_path};

// The existentials and scaffolding a declaration's body is inferred against: its
// parameter domains, return type, class constraints, parametric-effect scope,
// open row tail (`mu`) with its fixed-label prefix, and the assembled
// monomorphic self-type. Produced by `seed_decl`, consumed by `infer_body` and
// `finish_decl`, so a recursion group can seed every member before inferring any.
struct DeclSeed {
    doms: Vec<Type>,
    ret: Type,
    cur: Vec<(String, Type)>,
    scope: Vec<(Sym, Vec<Type>)>,
    mu: u32,
    self_ty: Type,
}

impl Tc<'_> {
    fn lit_range(lit: &ast::IntLit, ty: &Type, span: Span) -> Result<(), TypeError> {
        let max = match ty {
            Type::I64 => ast::BigInt::from(i64::MAX),
            _ => ast::BigInt::from(u64::MAX),
        };
        if lit.value > max {
            return Err(TypeError::Other {
                span,
                msg: format!("integer literal out of range for {}", ty.show()),
            });
        }
        Ok(())
    }

    fn check(&mut self, env: &Env, e: &S<Expr<Core>>, ty: &Type) -> Result<(), TypeError> {
        let span = e.span;
        let id = e.id;
        match (&e.node, ty) {
            (_, Type::Forall(n, b)) => {
                self.ctx.push(Entry::Uni(*n));
                self.check(env, e, b)?;
                self.drop_uni(*n);
                Ok(())
            }
            (_, Type::RowForall(n, b)) => {
                self.ctx.push(Entry::RowUni(*n));
                self.check(env, e, b)?;
                self.drop_row_uni(*n);
                Ok(())
            }
            (Expr::Lam(ps, body), Type::Fun(doms, eff, ret)) if ps.len() == doms.len() => {
                let mut env2 = env.clone();
                for (p, d) in ps.iter().zip(doms.iter()) {
                    env2.insert(Sym::from(&p.name), d.clone());
                }
                // Scope the body's effects into the expected arrow row: its fixed
                // labels become the prefix (so a body that performs them adds
                // nothing) and its tail absorbs anything extra. A flexible tail
                // means a pure body checks fine against an effectful type (the
                // closure introduction form admits row subsumption); a closed or
                // rigid tail is pinned afterward so the body may not exceed it.
                let eff = self.apply_row(eff);
                let mut prefix = BTreeSet::new();
                let mut cursor = &eff;
                while let EffRow::Extend(l, more) = cursor {
                    prefix.insert(l.name);
                    cursor = more;
                }
                let (tail, closed) = match cursor {
                    EffRow::Exist(r) => (*r, None),
                    other => (self.push_ex_row(), Some(other.clone())),
                };
                let checked =
                    self.with_row_scope(RowScope { tail, prefix }, |tc| tc.check(&env2, body, ret));
                checked?;
                if let Some(closed) = closed {
                    self.unify_row(&EffRow::Exist(tail), &closed)
                        .map_err(|e| e.at(span))?;
                }
                Ok(())
            }
            (Expr::If(c, t, e2), _) => {
                self.check(env, c, &Type::Bool)?;
                self.check(env, t, ty)?;
                self.check(env, e2, ty)
            }
            (Expr::Let(x, v, b), _) => {
                let tv = self.synth(env, v)?;
                // Unconditional generalization; no value restriction (see `generalize`).
                let g = self.generalize(env, &tv);
                let mut env2 = env.clone();
                env2.insert(Sym::from(x), g);
                self.check(&env2, b, ty)
            }
            (Expr::Match(s, arms), _) => {
                let ts = self.synth(env, s)?;
                let ts = self.apply(&ts);
                for arm in arms {
                    let env2 = self.check_pat(env, &arm.pat, &ts)?;
                    if let Some(g) = &arm.guard {
                        self.check(&env2, g, &Type::Bool)?;
                    }
                    self.check(&env2, &arm.body, ty)?;
                }
                self.check_coverage(arms, span)
            }
            (Expr::Tuple(elems), Type::Tuple(tys)) if elems.len() == tys.len() => {
                for (elem, t) in elems.iter().zip(tys) {
                    let t = self.apply(t);
                    self.check(env, elem, &t)?;
                }
                Ok(())
            }
            // A list literal against a known `List(T)` pushes `T` into each
            // element, so the tower's polymorphic literals reach through the
            // aggregate: `[1, 2, 3] : List(I64)` needs no per-element suffix, the
            // elements adopting `I64` exactly as a bare `1` in `I64` position does.
            (Expr::List(elems), Type::Con(head, args))
                if head.as_str() == LIST && args.len() == 1 =>
            {
                let elem_ty = self.apply(&args[0]);
                for elem in elems {
                    self.check(env, elem, &elem_ty)?;
                }
                Ok(())
            }
            (Expr::Int(lit), Type::I64 | Type::U64) if lit.suffix == ast::Suffix::None => {
                Self::lit_range(lit, ty, span)?;
                self.fixed.insert(id, ty.clone());
                Ok(())
            }
            // A bare integer literal adopts a `Float` expected type (the tower's
            // polymorphic literals: `let x : Float = 1` needs no `.0`). The
            // elaborator reads the recorded lane and emits a float constant, so no
            // runtime conversion survives. A suffixed literal stays its own lane
            // and falls through to the mismatch below.
            (Expr::Int(lit), Type::Float) if lit.suffix == ast::Suffix::None => {
                self.fixed.insert(id, ty.clone());
                Ok(())
            }
            // A bare integer literal at a `Num`-polymorphic type (a rigid variable
            // carrying a `Num` constraint in scope): raise the obligation on the
            // literal node so it elaborates through `from_int` at the resolved
            // lane. This is what lets generic `given Num(a)` code write `x + 1`.
            // Restricted to a variable that is actually `Num`-constrained, so a
            // literal against an unconstrained rigid variable stays the mismatch it
            // was (the signature promised nothing numeric about it).
            (Expr::Int(lit), Type::Var(v))
                if lit.suffix == ast::Suffix::None && self.num_var_in_scope(*v) =>
            {
                self.wanted.push(Wanted {
                    id,
                    span,
                    items: vec![(NUM_CLASS.into(), ty.clone(), None)],
                });
                Ok(())
            }
            // The same adoption applies through unary minus: `x + -1` in
            // `given Num(a)` code injects the exact negative `Int` literal through
            // `from_int` at the resolved lane, rather than defaulting the literal
            // to `Int` and failing against rigid `a`.
            (Expr::Neg(inner), Type::Var(v))
                if Self::bare_int_lit(inner).is_some() && self.num_var_in_scope(*v) =>
            {
                self.wanted.push(Wanted {
                    id,
                    span,
                    items: vec![(NUM_CLASS.into(), ty.clone(), None)],
                });
                Ok(())
            }
            // `-5` takes a fixed-width lane from context like `5`, but only the
            // signed one: `U64` is unsigned, and the magnitude checked is the
            // negated value so the I64 minimum is admissible.
            (Expr::Neg(inner), Type::I64 | Type::U64) if Self::bare_int_lit(inner).is_some() => {
                if *ty == Type::U64 {
                    return Err(Self::neg_unsigned(span));
                }
                let lit = Self::bare_int_lit(inner).expect("guarded by is_some");
                let negated = ast::IntLit {
                    value: -lit.value.clone(),
                    suffix: ast::Suffix::None,
                };
                Self::lit_range(&negated, ty, span)?;
                self.fixed.insert(id, ty.clone());
                Ok(())
            }
            // `-1` adopts a `Float` context like `1` does; the elaborator folds the
            // minus into the float constant it emits for the recorded lane.
            (Expr::Neg(inner), Type::Float) if Self::bare_int_lit(inner).is_some() => {
                self.fixed.insert(id, ty.clone());
                Ok(())
            }
            _ => {
                let a = self.synth(env, e)?;
                let a = self.apply(&a);
                let b = self.apply(ty);
                self.subtype(&a, &b).map_err(|e| {
                    e.or(TypeError::Mismatch {
                        span,
                        expected: b.show(),
                        found: a.show(),
                    })
                })
            }
        }
    }

    pub(super) fn synth(&mut self, env: &Env, e: &S<Expr<Core>>) -> Result<Type, TypeError> {
        let t = self.synth_node(env, e)?;
        self.pending.push((e.id, t.clone()));
        Ok(t)
    }

    // Scope the ambient self-reference state (name, type, constraints) so a
    // recursive call cannot leak one declaration's state into the next.
    fn with_self<R>(
        &mut self,
        name: String,
        ty: Type,
        cs: Vec<(String, Type)>,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let prev = self.cur_self.replace(SelfRef {
            name,
            self_ty: ty,
            constraints: cs,
        });
        let r = f(self);
        self.cur_self = prev;
        r
    }

    // Run `f` under a delimited ambient effect row, restoring the previous row
    // afterwards (mirrors `with_self`). Any reading of the scoped row (e.g. to
    // collect inferred effects) must happen inside `f`, before the restore.
    fn with_row_scope<R>(&mut self, scope: RowScope, f: impl FnOnce(&mut Self) -> R) -> R {
        let saved = self.cur_row.replace(scope);
        let r = f(self);
        self.cur_row = saved;
        r
    }

    // Zonk after resolve_all, while this declaration's solutions are still in ctx.
    fn flush_spans(&mut self) {
        for (id, t) in std::mem::take(&mut self.pending) {
            let t = self.apply(&t);
            self.span_types.insert(id, t);
        }
    }

    fn synth_record_create(
        &mut self,
        env: &Env,
        ctor_name: &str,
        field_exprs: &[(String, S<Expr<Core>>)],
        span: Span,
    ) -> Result<Type, TypeError> {
        let info = self
            .ctors
            .get(ctor_name)
            .cloned()
            .ok_or_else(|| TypeError::Other {
                span,
                msg: format!("unknown record constructor {ctor_name}"),
            })?;
        if info.fields.is_empty() {
            return Err(TypeError::Other {
                span,
                msg: format!("{ctor_name} is not a record constructor"),
            });
        }
        let (result, tsubs, rsubs) = self.open_ctor(&info);
        for (field_name, field_expr) in field_exprs {
            let fi = info
                .fields
                .iter()
                .position(|f| *f == field_name)
                .ok_or_else(|| TypeError::Other {
                    span,
                    msg: format!("unknown field {field_name} on {ctor_name}"),
                })?;
            let mut ft = info.args[fi].clone();
            for (pn, t) in &tsubs {
                ft = ft.subst_var(*pn, t);
            }
            for (pn, r) in &rsubs {
                ft = ft.subst_row_var(*pn, r);
            }
            let ft = self.apply(&ft);
            self.check(env, field_expr, &ft)?;
        }
        let missing: Vec<&str> = info
            .fields
            .iter()
            .map(|f| f.as_str())
            .filter(|f| !field_exprs.iter().any(|(n, _)| n == f))
            .collect();
        if !missing.is_empty() {
            return Err(TypeError::Other {
                span,
                msg: format!("missing field(s) {} in {ctor_name}", missing.join(", ")),
            });
        }
        Ok(self.apply(&result))
    }

    fn synth_node(&mut self, env: &Env, e: &S<Expr<Core>>) -> Result<Type, TypeError> {
        let span = e.span;
        let id = e.id;
        match &e.node {
            Expr::Int(lit) => {
                let ty = match lit.suffix {
                    ast::Suffix::None => return Ok(Type::Int),
                    ast::Suffix::I64 => Type::I64,
                    ast::Suffix::U64 => Type::U64,
                };
                Self::lit_range(lit, &ty, span)?;
                self.fixed.insert(id, ty.clone());
                Ok(ty)
            }
            Expr::Float(_) => Ok(Type::Float),
            Expr::Char(_) => Ok(Type::Char),
            Expr::Str(_) => Ok(Type::Str),
            Expr::Bool(_) => Ok(Type::Bool),
            Expr::Unit => Ok(Type::Unit),
            Expr::Var(x) => {
                let t = env
                    .get(&Sym::from(x))
                    .cloned()
                    .ok_or_else(|| TypeError::Unbound {
                        span,
                        name: x.clone(),
                    })?;
                if let Some((scheme, cs)) = self.constrained.get(&Sym::from(x)).cloned() {
                    if t == scheme && !cs.is_empty() {
                        return Ok(self.instantiate_constrained(&scheme, &cs, id, span, None));
                    }
                }
                if let Some(s) = &self.cur_self {
                    if *x == s.name && t == s.self_ty && !s.constraints.is_empty() {
                        let items = s
                            .constraints
                            .clone()
                            .into_iter()
                            .map(|(class, cty)| (class, cty, None))
                            .collect();
                        self.wanted.push(Wanted { id, span, items });
                    }
                }
                Ok(t)
            }
            Expr::Inst(f, names) => self.synth_inst(env, f, names, id, span),
            Expr::Index(recv, key) => self.synth_index(env, recv, key, span),
            Expr::IndexSet(recv, key, val) => self.synth_index_set(env, recv, key, val, span),
            Expr::Bin(op, a, b) => self.synth_bin(env, *op, a, b, id, span),
            Expr::Neg(e2) => self.synth_neg(env, e2, id, span),
            Expr::If(c, t, e2) => {
                self.check(env, c, &Type::Bool)?;
                let tt = self.synth(env, t)?;
                let tt = self.apply(&tt);
                self.check(env, e2, &tt)?;
                Ok(self.apply(&tt))
            }
            Expr::Let(x, v, b) => {
                let tv = self.synth(env, v)?;
                // Unconditional generalization; no value restriction (see `generalize`).
                let g = self.generalize(env, &tv);
                let mut env2 = env.clone();
                env2.insert(Sym::from(x), g);
                self.synth(&env2, b)
            }
            Expr::Lam(ps, body) => {
                let mut env2 = env.clone();
                let mut doms = Vec::new();
                for p in ps {
                    let ex = self.push_ex();
                    env2.insert(Sym::from(&p.name), Type::Exist(ex));
                    doms.push(Type::Exist(ex));
                }
                let ret = self.push_ex();
                // A lambda delimits its own effect row: its body's effects are
                // captured on the arrow type, not bled into the enclosing
                // function, and re-emerge only when the closure is applied.
                let row = self.push_ex_row();
                let checked = self.with_row_scope(
                    RowScope {
                        tail: row,
                        prefix: BTreeSet::new(),
                    },
                    |tc| tc.check(&env2, body, &Type::Exist(ret)),
                );
                checked?;
                Ok(self.apply(&Type::fun_eff(doms, EffRow::Exist(row), Type::Exist(ret))))
            }
            Expr::Call(f, args) => {
                if let Expr::Var(x) = &f.node {
                    // `print`/`println` carry a `Show(a)` obligation. It is
                    // emitted procedurally (like the Eq/Ord ladders) rather than
                    // stored on the scheme: a concrete argument is discharged by
                    // the elaborator's structural printer and must not pay a
                    // dictionary (raw strings, empty containers, and un-`derived`
                    // ADTs would otherwise fail to resolve), so only a polymorphic
                    // argument (a rigid type var) raises the constraint. Active
                    // only when the `Show` class is in scope (prelude present); a
                    // prelude-free program keeps the elaborator's own rejection.
                    if matches!(x.as_str(), "print" | "println")
                        && args.len() == 1
                        && self.classes.contains_key(&Sym::from(SHOW_CLASS))
                    {
                        return self.synth_print(env, f, &args[0], span);
                    }
                    if let Some(info) = self.eff_ops.get(x) {
                        // A parametric op, or a non-parametric op whose signature
                        // carries a free effect-row variable (a thunk-taking op),
                        // instantiates its op type through `perform_ty`, which ties
                        // those row variables to the ambient row. That is what lets
                        // a thunk argument's extra effects flow out of the perform
                        // site instead of being absorbed into a fresh, unconnected
                        // row and silently dropped.
                        if !info.eff_params.is_empty() || info.has_free_row_vars() {
                            let info = info.clone();
                            self.synth(env, f)?;
                            let fty = self.perform_ty(&info, span)?;
                            return self.app_synth(env, &fty, args, span);
                        }
                        // A non-parametric op with no thunk row carries no effect
                        // args, so its row obligation (rule 1) is a bare label; emit
                        // it, then type the call through the ordinary env-scheme
                        // path below.
                        let eff = info.effect_name;
                        self.absorb_row(&EffRow::singleton(eff))
                            .map_err(|e| e.at(span))?;
                    }
                }
                let tf = self.synth(env, f)?;
                let tf = self.apply(&tf);
                self.app_synth(env, &tf, args, span)
            }
            Expr::Pipe(x, f) => {
                let tf = self.synth(env, f)?;
                let tf = self.apply(&tf);
                self.app_synth(env, &tf, std::slice::from_ref(x), span)
            }
            Expr::Match(s, arms) => {
                let ts = self.synth(env, s)?;
                let ts = self.apply(&ts);
                let ret = self.push_ex();
                for arm in arms {
                    let env2 = self.check_pat(env, &arm.pat, &ts)?;
                    if let Some(g) = &arm.guard {
                        self.check(&env2, g, &Type::Bool)?;
                    }
                    self.check(&env2, &arm.body, &Type::Exist(ret))?;
                }
                self.check_coverage(arms, span)?;
                Ok(self.apply(&Type::Exist(ret)))
            }
            Expr::Tuple(elems) => {
                let ts: Result<Vec<_>, _> =
                    elems.iter().map(|elem| self.synth(env, elem)).collect();
                let ts = ts?;
                Ok(Type::Tuple(ts.iter().map(|t| self.apply(t)).collect()))
            }
            Expr::List(elems) => {
                let ex = self.push_ex();
                for elem in elems {
                    self.check(env, elem, &Type::Exist(ex))?;
                }
                Ok(Type::Con(LIST.into(), vec![self.apply(&Type::Exist(ex))]))
            }
            Expr::FieldAccess(e, field) => {
                let te = self.synth(env, e)?;
                let te = self.apply(&te);
                let ctor_name = match &te {
                    Type::Con(n, _) => *n,
                    other => {
                        return Err(TypeError::Other {
                            span,
                            msg: format!("field access on non-record type {}", other.show()),
                        })
                    }
                };
                let (field_ty, fi) = self.find_field(span, ctor_name.as_str(), field, &te)?;
                if let Some((cname, info)) = self
                    .ctors
                    .iter()
                    .find(|(_, c)| c.type_name == ctor_name && c.fields.iter().any(|f| *f == field))
                {
                    self.field_res
                        .insert(id, (cname.clone(), fi, info.args.len()));
                }
                Ok(field_ty)
            }
            Expr::RecordCreate(ctor_name, field_exprs) => {
                self.synth_record_create(env, ctor_name, field_exprs, span)
            }
            Expr::RecordUpdate(base_expr, ctor_name, field_exprs) => {
                self.synth_record_update(env, base_expr, ctor_name, field_exprs, span)
            }
            Expr::RecordUpdatePath(base, ups) => self.update_path(env, base, ups, id, span),
            Expr::Handle(body, arms) => self.synth_handle(env, body, arms, span),
            Expr::Mask(eff, body) => self.synth_mask(env, eff, body, span),
            Expr::Ann(inner, ann) => {
                self.check_annot_rows(ann, span)?;
                let t = self.convert_annot_fresh(ann);
                self.check(env, inner, &t)?;
                Ok(self.apply(&t))
            }
            // Sugar is unrepresentable in `Expr<Core>`; the empty match is
            // exhaustive without an ICE or error arm.
            #[expect(
                clippy::uninhabited_references,
                reason = "Never is uninhabited in Core; arm is unreachable"
            )]
            Expr::Sugar(never) | Expr::Marker(never) => match *never {},
        }
    }

    // Explicit instance selection `f(using d)`: `f` must be a constrained name and
    // the instance arguments must match its constraint count one-to-one.
    fn synth_inst(
        &mut self,
        env: &Env,
        f: &S<Expr<Core>>,
        names: &[String],
        id: NodeId,
        span: Span,
    ) -> Result<Type, TypeError> {
        let Expr::Var(x) = &f.node else {
            return Err(TypeError::Other {
                span,
                msg: "explicit instance selection `f(using ..)` requires a named function".into(),
            });
        };
        let t = env
            .get(&Sym::from(x))
            .cloned()
            .ok_or_else(|| TypeError::Unbound {
                span: f.span,
                name: x.clone(),
            })?;
        match self.constrained.get(&Sym::from(x)).cloned() {
            Some((scheme, cs)) if t == scheme && !cs.is_empty() => {
                if names.len() != cs.len() {
                    return Err(TypeError::Other {
                        span,
                        msg: format!(
                            "`{x}` has {} constraint(s), got {} instance argument(s)",
                            cs.len(),
                            names.len()
                        ),
                    });
                }
                Ok(self.instantiate_constrained(&scheme, &cs, id, span, Some(names)))
            }
            _ => Err(TypeError::Other {
                span,
                msg: format!("`{x}` has no class constraints to instantiate"),
            }),
        }
    }

    // `{ base | field = v, .. }` over a known record constructor: the base checks
    // at the record type and each named field at its declared type.
    fn synth_record_update(
        &mut self,
        env: &Env,
        base_expr: &S<Expr<Core>>,
        ctor_name: &str,
        field_exprs: &[(String, S<Expr<Core>>)],
        span: Span,
    ) -> Result<Type, TypeError> {
        let info = self
            .ctors
            .get(ctor_name)
            .cloned()
            .ok_or_else(|| TypeError::Other {
                span,
                msg: format!("unknown record constructor {ctor_name}"),
            })?;
        let (result_ty, tsubs, rsubs) = self.open_ctor(&info);
        self.check(env, base_expr, &result_ty)?;
        for (field_name, field_expr) in field_exprs {
            let fi = info
                .fields
                .iter()
                .position(|f| *f == field_name)
                .ok_or_else(|| TypeError::Other {
                    span,
                    msg: format!("unknown field {field_name} on {ctor_name}"),
                })?;
            let mut ft = info.args[fi].clone();
            for (pn, t) in &tsubs {
                ft = ft.subst_var(*pn, t);
            }
            for (pn, r) in &rsubs {
                ft = ft.subst_row_var(*pn, r);
            }
            let ft = self.apply(&ft);
            self.check(env, field_expr, &ft)?;
        }
        Ok(self.apply(&result_ty))
    }

    // A `handle e { .. }`: pick one instantiation per parametric effect handled,
    // check the body under that scope, then check each return/op clause against a
    // shared result existential.
    fn synth_handle(
        &mut self,
        env: &Env,
        body: &S<Expr<Core>>,
        arms: &[HandlerArm<Core>],
        span: Span,
    ) -> Result<Type, TypeError> {
        let mut scope = Vec::new();
        let mut seen = BTreeSet::new();
        for arm in arms {
            if let HandlerArm::Op(op_name, ..) = arm {
                if let Some(info) = self.eff_ops.get(op_name).cloned() {
                    if !info.eff_params.is_empty() && seen.insert(info.effect_name) {
                        let args: Vec<Type> = info
                            .eff_params
                            .iter()
                            .map(|_| Type::Exist(self.push_ex()))
                            .collect();
                        scope.push((info.effect_name, args));
                    }
                }
            }
        }
        let body_ty = self.synth_handle_body(env, body, &scope, arms, span)?;
        let ret_ex = self.push_ex();
        for arm in arms {
            match arm {
                HandlerArm::Return(x, arm_body) => {
                    let mut env2 = env.clone();
                    env2.insert(Sym::from(x), body_ty.clone());
                    self.check(&env2, arm_body, &Type::Exist(ret_ex))?;
                }
                HandlerArm::Op(op_name, params, k_var, arm_body) => {
                    if let Some(info) = self.eff_ops.get(op_name).cloned() {
                        let eff_sym = info.effect_name;
                        let (mut op_params, mut op_ret) =
                            match scope.iter().find(|(n, _)| *n == eff_sym) {
                                Some((_, args)) => info.instantiate(args),
                                None => (info.params.clone(), info.ret.clone()),
                            };
                        // Open the op's free row variables per handler clause, so a
                        // row-polymorphic argument (`fork`'s fiber thunk) does not
                        // pin the handler's answer row to a rigid variable.
                        self.open_op_rows(&mut op_params, &mut op_ret);
                        let mut env2 = env.clone();
                        for (pname, pty) in params.iter().zip(op_params.iter()) {
                            env2.insert(Sym::from(pname), pty.clone());
                        }
                        // The continuation performs the handler body's residual
                        // effects when resumed. That residual is an open row
                        // variable (a fiber row `e` threaded into a `Cmd(a, e)`),
                        // so the continuation's own row must be a fresh existential
                        // that unifies with it: a hardcoded empty row would
                        // `unify_row(Empty, {e})` and solve the residual `e` to
                        // empty, severing the row variable the reified data type
                        // carries.
                        let k_ty = Type::fun_eff(
                            vec![op_ret],
                            EffRow::Exist(self.push_ex_row()),
                            Type::Exist(ret_ex),
                        );
                        env2.insert(Sym::from(k_var), k_ty);
                        self.check(&env2, arm_body, &Type::Exist(ret_ex))?;
                    } else {
                        return Err(TypeError::Other {
                            span,
                            msg: format!("unknown effect operation `{op_name}`"),
                        });
                    }
                }
                #[expect(
                    clippy::uninhabited_references,
                    reason = "Never is uninhabited in Core; arm is unreachable"
                )]
                HandlerArm::Sugar(never) => match *never {},
            }
        }
        Ok(self.apply(&Type::Exist(ret_ex)))
    }

    // `{ base | a.b.c = v, .. }`: each segment must land on a single-constructor
    // record so the rebuild is unconditional. The resolved chains drive
    // elaboration via `path_res`.
    fn update_path(
        &mut self,
        env: &Env,
        base: &S<Expr<Core>>,
        ups: &[(Vec<PathStep<Core>>, PathOp<Core>)],
        id: NodeId,
        span: Span,
    ) -> Result<Type, TypeError> {
        let tb = self.synth(env, base)?;
        let tb = self.apply(&tb);
        for (i, (p, _)) in ups.iter().enumerate() {
            for (q, _) in &ups[i + 1..] {
                // Post-desugar paths are `Field`-only, so a plain field-name
                // prefix decides overlap.
                if field_prefix(p, q) || field_prefix(q, p) {
                    return Err(TypeError::Other {
                        span,
                        msg: format!(
                            "conflicting update paths `{}` and `{}`",
                            show_path(p),
                            show_path(q)
                        ),
                    });
                }
            }
        }
        let mut chains = Vec::new();
        for (path, op) in ups {
            let mut cur = tb.clone();
            let mut chain = Vec::new();
            for seg in path {
                // Optic steps are lowered in desugar, so only `Field` reaches here.
                let PathStep::Field(seg) = seg else {
                    return Err(TypeError::Other {
                        span,
                        msg: "internal: optic path step survived desugaring".into(),
                    });
                };
                let Type::Con(tname, _) = cur.clone() else {
                    return Err(TypeError::Other {
                        span,
                        msg: format!(
                            "field path segment `{seg}` on non-record type {}",
                            cur.show()
                        ),
                    });
                };
                let mut named: Vec<_> = self
                    .ctors
                    .iter()
                    .filter(|(_, c)| c.type_name == tname.as_str())
                    .map(|(n, c)| (n.clone(), c.args.len()))
                    .collect();
                let Some((cname, arity)) = named.pop().filter(|_| named.is_empty()) else {
                    return Err(TypeError::Other {
                        span,
                        msg: format!(
                            "update path needs a single-constructor record, `{tname}` has {} constructors",
                            named.len() + 1
                        ),
                    });
                };
                let (ft, fi) = self.find_field(span, tname.as_str(), seg, &cur)?;
                chain.push((cname, fi, arity));
                cur = ft;
            }
            // `= v` sets, so `v` must have the focus type; `~ f` modifies, so `f`
            // must be a pure endo-function on the focus. The modify function is
            // required pure: its call is synthesized in elaboration, where a
            // residual effect row would escape the syntactic effect analysis.
            match op {
                PathOp::Set(val) => self.check(env, val, &cur)?,
                PathOp::Modify(f) => {
                    self.check(env, f, &Type::fun(vec![cur.clone()], cur.clone()))?;
                }
            }
            chains.push(chain);
        }
        self.path_res.insert(id, chains);
        Ok(self.apply(&tb))
    }

    // `recv[key]`: a failable read dispatched on `recv`'s head. Dispatch eagerly
    // when the receiver type is already a concrete container; defer it (to
    // `resolve_all`) when the receiver is still an unsolved existential, since a
    // `var`'s state type is only fixed once its initializer is checked.
    fn synth_index(
        &mut self,
        env: &Env,
        recv: &S<Expr<Core>>,
        key: &S<Expr<Core>>,
        span: Span,
    ) -> Result<Type, TypeError> {
        let recv_ty = self.synth(env, recv)?;
        let recv_ty = self.apply(&recv_ty);
        self.absorb_row(&EffRow::singleton(Sym::from(crate::names::FAIL_EFFECT)))
            .map_err(|e| e.at(span))?;
        if let Some((kty, elem, _)) = index_container(&recv_ty) {
            self.check(env, key, &kty)?;
            Ok(self.apply(&elem))
        } else if matches!(recv_ty, Type::Exist(_)) {
            let key_ty = self.synth(env, key)?;
            let result = self.push_ex();
            self.index_ops.push(IndexOp {
                span,
                recv_span: recv.span,
                recv: recv_ty,
                key: key_ty,
                result,
                val: None,
            });
            Ok(Type::Exist(result))
        } else {
            Err(TypeError::Other {
                span: recv.span,
                msg: format!("type `{}` is not indexable with `[]`", recv_ty.show()),
            })
        }
    }

    // `recv[key] := val`: a total in-place write returning the container. Same
    // eager/deferred split as `synth_index`; only `Array`/`HashMap` are writable.
    fn synth_index_set(
        &mut self,
        env: &Env,
        recv: &S<Expr<Core>>,
        key: &S<Expr<Core>>,
        val: &S<Expr<Core>>,
        span: Span,
    ) -> Result<Type, TypeError> {
        let recv_ty = self.synth(env, recv)?;
        let recv_ty = self.apply(&recv_ty);
        match index_container(&recv_ty) {
            Some((kty, elem, true)) => {
                self.check(env, key, &kty)?;
                let elem = self.apply(&elem);
                self.check(env, val, &elem)?;
                Ok(recv_ty)
            }
            None if matches!(recv_ty, Type::Exist(_)) => {
                let key_ty = self.synth(env, key)?;
                let val_ty = self.synth(env, val)?;
                let result = self.push_ex();
                self.index_ops.push(IndexOp {
                    span,
                    recv_span: recv.span,
                    recv: recv_ty.clone(),
                    key: key_ty,
                    result,
                    val: Some(val_ty),
                });
                Ok(recv_ty)
            }
            _ => Err(TypeError::Other {
                span: recv.span,
                msg: format!(
                    "type `{}` does not support indexed assignment `a[i] := v`",
                    recv_ty.show()
                ),
            }),
        }
    }

    // The numeric defaulting rule, in one place: an ambiguous operand defaults
    // to `Int`. `==`/`!=` invoke it for an unconstrained (existential) operand;
    // the ordered and arithmetic operators invoke it for any operand that is not
    // already a fixed-width integer. This is the only site the `Int` literal and
    // its `subtype` decision live, so Eq and Ord share one rule.
    pub(super) fn default_numeric(&mut self, ty: &Type, span: Span) -> Result<Type, TypeError> {
        self.subtype(ty, &Type::Int).map_err(|e| {
            e.or(TypeError::Mismatch {
                span,
                expected: Type::Int.show(),
                found: ty.show(),
            })
        })?;
        Ok(Type::Int)
    }

    // The defer-or-fix ladder shared by every numeric/comparison operator, over
    // the already-applied left-operand type `t`. `Int` is the default lane and is
    // accepted as-is; a fixed-width lane pins `id` so later width inference agrees;
    // an unsolved existential defers to the `resolve_all` pass, where a still-later
    // use can pin its width before the `Int` default fires. Only the leftover case
    // differs per operator family (`NumClass`), and `blame` is the span the
    // numeric rejection points at. Callers own the operator's result type; this
    // only records the classification side effects.
    fn numeric_ladder(
        &mut self,
        class: NumClass,
        t: &Type,
        id: NodeId,
        span: Span,
        blame: Span,
    ) -> Result<(), TypeError> {
        match t {
            Type::Int => Ok(()),
            Type::I64 | Type::U64 => {
                self.fixed.insert(id, t.clone());
                Ok(())
            }
            Type::Exist(_) => {
                self.num_default.push((id, span, t.clone()));
                Ok(())
            }
            _ => match class {
                NumClass::Eq => match t {
                    Type::Float | Type::Bool | Type::Str => {
                        self.fixed.insert(id, t.clone());
                        Ok(())
                    }
                    _ => {
                        self.wanted.push(Wanted {
                            id,
                            span,
                            items: vec![(EQ_CLASS.into(), t.clone(), None)],
                        });
                        Ok(())
                    }
                },
                NumClass::Ord => {
                    if matches!(t, Type::Float) {
                        self.fixed.insert(id, t.clone());
                    } else {
                        self.wanted.push(Wanted {
                            id,
                            span,
                            items: vec![(ORD_CLASS.into(), t.clone(), None)],
                        });
                    }
                    Ok(())
                }
                NumClass::Arith => match t {
                    // `Float` joined the arithmetic operators with the tower;
                    // record the lane for the elaborator like the fixed-width
                    // lanes. Anything else here is a non-numeric operand (a
                    // deferred existential that unified with, say, `String`), still
                    // rejected blaming the operand.
                    Type::Float => {
                        self.fixed.insert(id, t.clone());
                        Ok(())
                    }
                    _ => self.default_numeric(t, blame).map(|_| ()),
                },
            },
        }
    }

    // Which tower class an arithmetic operator dispatches through: `+`/`-`/`*`
    // carry `Num`, `/`/`%` carry `Div`. Only the arithmetic ops reach this (the
    // comparison and boolean ops are handled on their own `synth_bin` arms).
    const fn arith_class(op: BinOp) -> &'static str {
        match op {
            BinOp::Div | BinOp::Rem => DIV_CLASS,
            _ => NUM_CLASS,
        }
    }

    // Whether the rigid type variable `v` carries a `Num` constraint in the
    // current declaration's `given` clause. A signature variable is stored in the
    // constraint list verbatim (rigid, never an existential), so this is a direct
    // match with no zonking. Gates the polymorphic-literal `check` arm so a
    // literal only adopts a variable the signature actually promised is numeric.
    fn num_var_in_scope(&self, v: Sym) -> bool {
        self.cur_self.as_ref().is_some_and(|s| {
            s.constraints
                .iter()
                .any(|(c, t)| c == NUM_CLASS && matches!(t, Type::Var(cv) if *cv == v))
        })
    }

    // The signed lanes unary minus is defined on, in one place so `synth_neg`,
    // `neg_lane`, and the `check` fast path agree.
    pub(super) fn neg_unsigned(span: Span) -> TypeError {
        TypeError::Other {
            span,
            msg: "cannot negate an unsigned `U64` value; unary minus is defined on `Int`, `I64`, and `Float`"
                .into(),
        }
    }

    // A bare integer literal (no width suffix), the operand shape a leading minus
    // folds against so `-5` can take a fixed-width lane from its context exactly
    // as `5` does.
    fn bare_int_lit(e: &S<Expr<Core>>) -> Option<&ast::IntLit> {
        match &e.node {
            Expr::Int(lit) if lit.suffix == ast::Suffix::None => Some(lit),
            _ => None,
        }
    }

    // Classify a unary-minus whose operand type is already applied. The lane is
    // recorded on the node for the elaborator (I64 wrap, Float sign flip); `Int`
    // is the default and needs no record; `U64` is rejected; an unsolved operand
    // defers to `resolve_all`.
    fn neg_lane(&mut self, t: &Type, id: NodeId, span: Span) -> Result<Type, TypeError> {
        match t {
            Type::Int => Ok(Type::Int),
            Type::I64 | Type::Float => {
                self.fixed.insert(id, t.clone());
                Ok(t.clone())
            }
            Type::U64 => Err(Self::neg_unsigned(span)),
            Type::Exist(_) => {
                self.neg_default.push((id, span, t.clone()));
                Ok(t.clone())
            }
            // A `given Num(a)` operand dispatches unary minus through the class's
            // `negated` method, exactly as the binary operators raise `Num`;
            // resolution finds the dictionary, or reports "no instance" for a
            // genuinely non-numeric operand.
            other => {
                self.wanted.push(Wanted {
                    id,
                    span,
                    items: vec![(NUM_CLASS.into(), other.clone(), None)],
                });
                Ok(other.clone())
            }
        }
    }

    // Unary minus. Defined on the signed lanes only: `Int` (exact bignum), `I64`
    // (two's-complement wrap), and `Float` (IEEE sign flip). A literal operand
    // folds the minus into its magnitude, so `-9223372036854775808i64` is the
    // I64 minimum (one past the positive max) while the bare positive literal is
    // out of range; the negated value is what gets range-checked.
    fn synth_neg(
        &mut self,
        env: &Env,
        e: &S<Expr<Core>>,
        id: NodeId,
        span: Span,
    ) -> Result<Type, TypeError> {
        if let Expr::Int(lit) = &e.node {
            let ty = match lit.suffix {
                ast::Suffix::None => return Ok(Type::Int),
                ast::Suffix::I64 => Type::I64,
                ast::Suffix::U64 => return Err(Self::neg_unsigned(span)),
            };
            let negated = ast::IntLit {
                value: -lit.value.clone(),
                suffix: lit.suffix,
            };
            Self::lit_range(&negated, &ty, span)?;
            self.fixed.insert(id, ty.clone());
            return Ok(ty);
        }
        if matches!(&e.node, Expr::Float(_)) {
            return Ok(Type::Float);
        }
        let t = self.synth(env, e)?;
        let t = self.apply(&t);
        self.neg_lane(&t, id, span)
    }

    fn synth_bin(
        &mut self,
        env: &Env,
        op: BinOp,
        a: &S<Expr<Core>>,
        b: &S<Expr<Core>>,
        id: NodeId,
        span: Span,
    ) -> Result<Type, TypeError> {
        match op {
            BinOp::And | BinOp::Or => {
                self.check(env, a, &Type::Bool)?;
                self.check(env, b, &Type::Bool)?;
                Ok(Type::Bool)
            }
            BinOp::Addf | BinOp::Subf | BinOp::Mulf | BinOp::Divf => {
                self.check(env, a, &Type::Float)?;
                self.check(env, b, &Type::Float)?;
                Ok(Type::Float)
            }
            BinOp::Eqf | BinOp::Nef | BinOp::Ltf | BinOp::Lef | BinOp::Gtf | BinOp::Gef => {
                self.check(env, a, &Type::Float)?;
                self.check(env, b, &Type::Float)?;
                Ok(Type::Bool)
            }
            BinOp::Eq | BinOp::Ne => {
                let ta = self.synth(env, a)?;
                let ta = self.apply(&ta);
                let ta = self.instantiate_constrained(&ta, &[], id, span, None);
                self.check(env, b, &ta)?;
                let ta = self.apply(&ta);
                self.numeric_ladder(NumClass::Eq, &ta, id, span, a.span)?;
                Ok(Type::Bool)
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let ta = self.synth(env, a)?;
                let ta = self.apply(&ta);
                let ta = self.instantiate_constrained(&ta, &[], id, span, None);
                self.check(env, b, &ta)?;
                let ta = self.apply(&ta);
                self.numeric_ladder(NumClass::Ord, &ta, id, span, a.span)?;
                Ok(Type::Bool)
            }
            _ => {
                // The tower arithmetic operators `+`/`-`/`*` (dispatched through
                // `Num`) and `/`/`%` (through `Div`). A concrete lane drives the
                // operator directly: a fixed-width or `Float` lane fixes both sides
                // and keeps the direct primitive (byte-identical Core, no
                // dictionary). An unsolved existential left operand is not
                // defaulted to `Int` here; check the right operand against it (so
                // the right can pin the lane), and if both stay ambiguous defer to
                // one pass at `resolve_all` where a later use can still fix the
                // width. This lets `y + x` with `x : I64` type when `y` was left
                // open. Anything else (a `given Num(a)` rigid variable, or a
                // non-numeric operand) raises the class constraint exactly as
                // `==`/`<` raise `Eq`/`Ord`; resolution finds the dictionary or
                // reports "no instance", the honest error for a non-numeric lane.
                let ta = self.synth(env, a)?;
                let ta = self.apply(&ta);
                let t = match &ta {
                    Type::I64 | Type::U64 | Type::Float => {
                        self.check(env, b, &ta)?;
                        self.fixed.insert(id, ta.clone());
                        ta
                    }
                    Type::Int => {
                        self.check(env, b, &ta)?;
                        ta
                    }
                    Type::Exist(_) => {
                        self.check(env, b, &ta)?;
                        let t = self.apply(&ta);
                        self.numeric_ladder(NumClass::Arith, &t, id, span, b.span)?;
                        t
                    }
                    other => {
                        // Relate the right operand to the left only for a type that
                        // might carry an instance (a variable, or a nominal type). A
                        // concrete non-numeric primitive (`Bool`, `String`, ...)
                        // carries none, so raise the obligation on its own type and
                        // skip the operand check, whose "expected Bool, got Int"
                        // would misleadingly blame a literal right operand for the
                        // left operand not being numeric.
                        if matches!(other, Type::Var(_) | Type::Con(..) | Type::App(..)) {
                            self.check(env, b, &ta)?;
                        }
                        self.wanted.push(Wanted {
                            id,
                            span,
                            items: vec![(Self::arith_class(op).into(), ta.clone(), None)],
                        });
                        ta
                    }
                };
                Ok(t)
            }
        }
    }

    fn app_synth(
        &mut self,
        env: &Env,
        fty: &Type,
        args: &[S<Expr<Core>>],
        span: Span,
    ) -> Result<Type, TypeError> {
        match fty {
            Type::Forall(n, b) => {
                let ex = self.push_ex();
                let b2 = b.subst_var(*n, &Type::Exist(ex));
                self.app_synth(env, &b2, args, span)
            }
            Type::RowForall(n, b) => {
                let r = self.push_ex_row();
                let b2 = b.subst_row_var(*n, &EffRow::Exist(r));
                self.app_synth(env, &b2, args, span)
            }
            Type::Exist(a) => {
                let ret = self.fresh_id();
                let row = self.fresh_id();
                let arg_exs: Vec<u32> = args.iter().map(|_| self.fresh_id()).collect();
                self.articulate(*a, &arg_exs, row, ret)
                    .map_err(|e| e.at(span))?;
                for (ex, arg) in arg_exs.iter().zip(args) {
                    self.check(env, arg, &Type::Exist(*ex))?;
                }
                // Applying a function value performs its effects: fold the
                // still-unknown callee row into the ambient obligation.
                self.absorb_row(&EffRow::Exist(row))
                    .map_err(|e| e.at(span))?;
                Ok(self.apply(&Type::Exist(ret)))
            }
            Type::Fun(doms, eff, r) => {
                if args.len() > doms.len() {
                    return Err(TypeError::Other {
                        span,
                        msg: format!(
                            "function expects {} arguments, got {}",
                            doms.len(),
                            args.len()
                        ),
                    });
                }
                // Check non-lambda arguments before lambda ones: a concrete
                // argument can solve type variables a sibling lambda's body
                // depends on. `map(\e -> e.f, xs)` solves the element type from
                // `xs` first, so the annotation-free lambda checks against it.
                for lam_pass in [false, true] {
                    for (d, arg) in doms.iter().zip(args) {
                        if matches!(arg.node, Expr::Lam(..)) != lam_pass {
                            continue;
                        }
                        let d = self.apply(d);
                        self.check(env, arg, &d)?;
                    }
                }
                if args.len() == doms.len() {
                    self.link_row(eff, span)?;
                    // The callee's effects become the caller's: fold its row
                    // into the ambient obligation (open-row dedups, and a
                    // flexible callee tail propagates as a row variable).
                    self.absorb_row(eff).map_err(|e| e.at(span))?;
                    Ok(self.apply(r))
                } else {
                    let remaining: Vec<Type> =
                        doms[args.len()..].iter().map(|d| self.apply(d)).collect();
                    Ok(Type::Fun(remaining, eff.clone(), Box::new(self.apply(r))))
                }
            }
            other => Err(TypeError::Other {
                span,
                msg: format!("cannot apply non-function {}", other.show()),
            }),
        }
    }

    // Type a `print`/`println` call, raising the `Show(a)` obligation only for a
    // polymorphic argument. `print`'s scheme is `forall a. (a) -> Unit ! {row}`:
    // instantiate the leading `forall` locally so the argument existential is in
    // hand, type the application (which absorbs the latent row and checks the
    // argument), then read the solved argument type back. A rigid type variable
    // there is the polymorphic case the structural printer cannot see, so a
    // `Show` dictionary is wanted (satisfied by an enclosing `given Show(a)`, or
    // the call is rejected by ordinary resolution); a concrete or existential
    // argument raises nothing and lowers through the structural printer as before.
    fn synth_print(
        &mut self,
        env: &Env,
        f: &S<Expr<Core>>,
        arg: &S<Expr<Core>>,
        span: Span,
    ) -> Result<Type, TypeError> {
        let scheme = self.synth(env, f)?;
        let scheme = self.apply(&scheme);
        let Type::Forall(n, body) = &scheme else {
            return self.app_synth(env, &scheme, std::slice::from_ref(arg), span);
        };
        let ex = self.push_ex();
        let fun = body.subst_var(*n, &Type::Exist(ex));
        let res = self.app_synth(env, &fun, std::slice::from_ref(arg), span)?;
        let at = self.apply(&Type::Exist(ex));
        let mut vars = BTreeSet::new();
        collect_type_vars(&at, &mut vars);
        if !vars.is_empty() {
            self.wanted.push(Wanted {
                id: f.id,
                span,
                items: vec![(SHOW_CLASS.into(), at, None)],
            });
        }
        Ok(res)
    }

    // Unify each instantiated label of a callee's latent row with the
    // instantiation in force (innermost handler or the declaration's latent).
    fn link_row(&mut self, eff: &EffRow, span: Span) -> Result<(), TypeError> {
        let eff = self.apply_row(eff);
        for l in eff.labels() {
            if l.args.is_empty() {
                continue;
            }
            let Some((_, args)) = self.row_ctx.iter().rev().find(|(n, _)| *n == l.name) else {
                continue;
            };
            let args = args.clone();
            for (x, y) in l.args.iter().zip(&args) {
                self.equate(x, y).map_err(|e| {
                    e.or(TypeError::Other {
                        span,
                        msg: format!(
                            "effect instantiation mismatch: `{}` is not compatible with `{}`",
                            self.show_label(l),
                            self.show_label(&Label {
                                name: l.name,
                                args: args.clone(),
                            })
                        ),
                    })
                })?;
            }
        }
        Ok(())
    }

    // Open every free effect-row variable in an operation signature to a fresh
    // row existential, once per use. A row-polymorphic op such as
    // `fork(() -> a ! {Async(a) | e})` carries `e` as a free row variable in its
    // stored signature; a handler clause opens it fresh so it unifies downstream
    // with the reified answer row instead of leaking a rigid variable. Ops with
    // no free row variable are untouched.
    fn open_op_rows(&mut self, params: &mut [Type], ret: &mut Type) {
        let mut rows = BTreeSet::new();
        for p in params.iter() {
            super::env::collect_row_vars(p, &mut rows);
        }
        super::env::collect_row_vars(ret, &mut rows);
        for v in rows {
            let e = EffRow::Exist(self.push_ex_row());
            for p in params.iter_mut() {
                *p = p.subst_row_var(v, &e);
            }
            *ret = ret.subst_row_var(v, &e);
        }
    }

    // Tie an operation's free effect-row variables to the ambient effect row at a
    // perform site. `fork(() -> a ! {Async | e})` shares the caller's open row
    // tail for `e`, so a forked computation's effects are absorbed into the
    // caller's obligation and flow out to whoever handles the effect: a fiber
    // performing `Log` makes the caller (and `run_async`) demand a `Log` handler
    // rather than smuggling it past the scheduler. Outside any function body (no
    // ambient scope) it falls back to a fresh row. Ops with no free row variable
    // are untouched, so the rest of the corpus is unaffected.
    fn bind_op_rows_to_ambient(&mut self, params: &mut [Type], ret: &mut Type) {
        let existing_tail = self.cur_row.as_ref().map(|s| s.tail);
        let tail = existing_tail.unwrap_or_else(|| self.push_ex_row());
        let target = EffRow::Exist(tail);
        let mut rows = BTreeSet::new();
        for p in params.iter() {
            super::env::collect_row_vars(p, &mut rows);
        }
        super::env::collect_row_vars(ret, &mut rows);
        for v in rows {
            for p in params.iter_mut() {
                *p = p.subst_row_var(v, &target);
            }
            *ret = ret.subst_row_var(v, &target);
        }
    }

    // The type of a perform site for a parametric op: the op signature with
    // effect parameters replaced by the instantiation in force, and any
    // leftover return-only variables opened fresh per site. The op's own effect
    // label is absorbed into the ambient row here, so a direct `do op` demands
    // its effect by inference (rule 1); the label's args are the same
    // existentials that instantiate the op type, so the value- and row-level
    // views of the effect stay tied.
    fn perform_ty(&mut self, info: &super::EffOpInfo, span: Span) -> Result<Type, TypeError> {
        let eff_sym = info.effect_name;
        let found = self
            .row_ctx
            .iter()
            .rev()
            .find(|(n, _)| *n == eff_sym)
            .map(|(_, args)| args.clone());
        let args = found.unwrap_or_else(|| {
            info.eff_params
                .iter()
                .map(|_| Type::Exist(self.push_ex()))
                .collect()
        });
        let label = Label {
            name: eff_sym,
            args: args.clone(),
        };
        self.absorb_row(&EffRow::Extend(label, Box::new(EffRow::Empty)))
            .map_err(|e| e.at(span))?;
        let (mut params, mut ret) = info.instantiate(&args);
        let mut pv = BTreeSet::new();
        for p in &params {
            collect_type_vars(p, &mut pv);
        }
        let mut rv = BTreeSet::new();
        collect_type_vars(&ret, &mut rv);
        for v in rv {
            if !pv.contains(&v) {
                let e = self.push_ex();
                ret = ret.subst_var(v, &Type::Exist(e));
            }
        }
        self.bind_op_rows_to_ambient(&mut params, &mut ret);
        Ok(Type::fun(params, ret))
    }

    // Effect-type parameter count for `eff`. Not-found means zero, correct both
    // ways: builtins (`IO`, `Exn`) have none, and an undeclared effect (e.g.
    // `mask<Nope>`) reaches here before the perform/mask existence check rejects
    // it, so zero is a superseded placeholder.
    fn eff_arity(&self, eff: Sym) -> usize {
        self.eff_ops
            .values()
            .find(|i| i.effect_name == eff)
            .map_or(0, |i| i.eff_params.len())
    }

    // `mask<E>(body)`: the masked ops bypass the innermost `E` handler, so the
    // expression still demands an enclosing one. Inject one `E` label into the
    // ambient row so the unifier does not under-report it, and mark the nearest
    // enclosing `E` handler so it leaves the label in its residual row instead of
    // discharging it.
    fn synth_mask(
        &mut self,
        env: &Env,
        eff: &str,
        body: &S<Expr<Core>>,
        span: Span,
    ) -> Result<Type, TypeError> {
        let eff_sym = Sym::from(eff);
        if !self.eff_ops.values().any(|i| i.effect_name == eff_sym)
            && !super::env::is_builtin_effect(eff)
        {
            return Err(TypeError::Other {
                span,
                msg: format!("unknown effect `{eff}` in mask"),
            });
        }
        let t = self.synth(env, body)?;
        let args = (0..self.eff_arity(eff_sym))
            .map(|_| Type::Exist(self.push_ex()))
            .collect();
        let label = Label {
            name: eff_sym,
            args,
        };
        self.absorb_row(&EffRow::Extend(label, Box::new(EffRow::Empty)))
            .map_err(|e| e.at(span))?;
        if let Some(frame) = self
            .handler_stack
            .iter_mut()
            .rev()
            .find(|f| f.handled.contains(&eff_sym))
        {
            frame.masked.insert(eff_sym);
        }
        Ok(t)
    }

    // Synthesize a handler body under a fresh effect obligation, then discharge
    // the labels this handler names back into the enclosing row, so a handled
    // effect (even one that arrived through a function value) vanishes from the
    // surrounding function's row while the unhandled residual flows outward.
    fn synth_handle_body(
        &mut self,
        env: &Env,
        body: &S<Expr<Core>>,
        scope: &[(Sym, Vec<Type>)],
        arms: &[HandlerArm<Core>],
        span: Span,
    ) -> Result<Type, TypeError> {
        let body_row = self.push_ex_row();
        // A handler scopes a fresh ambient tail for its body but keeps the
        // enclosing fixed prefix.
        let prefix = self
            .cur_row
            .as_ref()
            .map_or_else(BTreeSet::new, |s| s.prefix.clone());
        let saved_row = self.cur_row.replace(RowScope {
            tail: body_row,
            prefix,
        });
        // This handler joins the active stack while its body is checked, so a
        // `mask` inside the body can find it and tunnel an effect past it.
        let handled: BTreeSet<Sym> = arms
            .iter()
            .filter_map(|a| match a {
                HandlerArm::Op(op, ..) => self.eff_ops.get(op).map(|i| i.effect_name),
                _ => None,
            })
            .collect();
        self.handler_stack.push(HandlerFrame {
            handled,
            masked: BTreeSet::new(),
        });
        let body_ty = self.in_row_scope(scope, |tc| tc.synth(env, body));
        let frame = self.handler_stack.pop().expect("handler frame");
        self.cur_row = saved_row;
        let body_ty = self.apply(&body_ty?);
        // A masked effect tunnels past this handler: keep it in the residual row
        // rather than discharging it, so the surrounding function still demands
        // an enclosing handler for it.
        let discharged: BTreeSet<Sym> = frame.handled.difference(&frame.masked).copied().collect();
        self.discharge_row(body_row, &discharged)
            .map_err(|e| e.at(span))?;
        Ok(body_ty)
    }

    // A single acyclic (or self-recursive) function: seed its monomorphic
    // self-type, infer its body against it, then generalize. The three stages
    // are factored so a mutually recursive group (`infer_scc`) can interleave
    // them: seed every member first, infer every body against the shared
    // monomorphic variables, then generalize the whole group.
    pub(super) fn infer_decl(&mut self, env: &Env, d: &Decl<Core>) -> Result<Type, TypeError> {
        self.reset_ctx();
        let seed = self.seed_decl(d)?;
        self.infer_body(env, d, &seed).map_err(|e| {
            // A self-recursive call typed monomorphically cannot be used at a
            // second type without a signature; name the remedy (only on the error
            // path, and only for an actually self-recursive function).
            if crate::types::effects::is_self_recursive(d) {
                poly_recursion_hint(e, d)
            } else {
                e
            }
        })?;
        self.finish_decl(env, d, &seed)
    }

    // SCC-granular inference for a mutually recursive group (two or more members
    // that reference each other). Seed every member's environment entry before
    // inferring any body: an unannotated member is seeded with its monomorphic
    // self-type (existentials shared between its entry and its own body), so a
    // mutual call unifies structure between siblings rather than instantiating a
    // structure-free stub. An annotated member is seeded with its generalized
    // annotation scheme, so calls to it check against the annotation (decidable
    // polymorphic recursion). Every member is then generalized against the
    // environment that held before the group, so a recursion group is generalized
    // once, after the whole group is inferred.
    pub(super) fn infer_scc(
        &mut self,
        env: &mut Env,
        members: &[&Decl<Core>],
    ) -> Result<Vec<Type>, TypeError> {
        let env_outer = env.clone();
        self.reset_ctx();
        // Stage 1: seed every member. `env` accumulates the group's env-visible
        // schemes so a sibling reference resolves to a real (monomorphic or
        // annotated) type, not a placeholder stub.
        let mut seeds = Vec::with_capacity(members.len());
        for d in members {
            let seed = if d.konst {
                self.seed_konst(d).map_err(|e| e.in_fn(&d.name))?
            } else {
                self.seed_decl(d).map_err(|e| e.in_fn(&d.name))?
            };
            // A constant or an unannotated function exposes its monomorphic
            // self-type (shared existentials let a sibling unify structure); a
            // fully annotated function exposes its generalized annotation scheme
            // (a sibling call checks against it, supporting polymorphic recursion).
            let visible =
                super::env::annotation_scheme(d, self.data).unwrap_or_else(|| seed.self_ty.clone());
            env.insert(Sym::from(&d.name), visible);
            seeds.push(seed);
        }
        // Stage 2: infer every body against the seeded group.
        for (d, seed) in members.iter().zip(&seeds) {
            // A monomorphic mutual call that needs the sibling at a second type
            // cannot be typed without a signature; name the remedy.
            self.infer_body(env, d, seed)
                .map_err(|e| poly_recursion_hint(e, d).in_fn(&d.name))?;
            // A `konst` member must be pure: its body's effects accumulated into
            // the seeded ambient row, so hold it to an empty inferred row.
            if d.konst {
                let effs = self.apply_row(&EffRow::Exist(seed.mu)).label_names();
                super::require_pure_konst(d, &effs)?;
            }
        }
        // Stage 3: generalize every member once, against the pre-group env, so the
        // group's shared existentials all generalize.
        let mut out = Vec::with_capacity(members.len());
        for (d, seed) in members.iter().zip(&seeds) {
            let g = self
                .finish_decl(&env_outer, d, seed)
                .map_err(|e| e.in_fn(&d.name))?;
            env.insert(Sym::from(&d.name), g.clone());
            out.push(g);
        }
        Ok(out)
    }

    // Stage 1 of declaration inference: allocate the parameter, return, and
    // effect-row existentials and build the monomorphic self-type, without
    // touching any shared environment. Does not reset the context, so a caller
    // can seed several members into one shared context before inferring them.
    fn seed_decl(&mut self, d: &Decl<Core>) -> Result<DeclSeed, TypeError> {
        for p in &d.params {
            if let Some(ann) = &p.ty {
                self.check_annot_rows(ann, d.span)?;
            }
        }
        if let Some(ann) = &d.ret {
            self.check_annot_rows(ann, d.span)?;
        }
        if let Some(ls) = &d.eff {
            self.check_labels(ls, d.span)?;
        }
        for c in &d.constraints {
            self.check_annot_rows(&c.ty, c.span)?;
        }
        let mut ty_ex = BTreeMap::new();
        let mut row_ex = BTreeMap::new();
        // A bare signature type variable is an implicit `forall a` and enters the
        // body check rigid (a `Type::Var`, which the unifier refuses to equate
        // with a concrete type or a second rigid variable), so a body that would
        // narrow `a` to `Int` is a type error rather than a silent specialization;
        // `finish_decl` re-quantifies these into the exported polymorphic scheme.
        // Row variables stay flexible (effect inference is principal).
        let rigid_ty = super::env::signature_ty_vars(d, self.data);
        let no_rigid = BTreeSet::new();
        let mut doms = Vec::new();
        for p in &d.params {
            let t = match &p.ty {
                Some(ann) => {
                    let mut a = Annot::with_rigid(&mut ty_ex, &mut row_ex, &rigid_ty, &no_rigid);
                    self.convert_annot(ann, &mut a)
                }
                None => Type::Exist(self.push_ex()),
            };
            doms.push(t);
        }
        let ret = match &d.ret {
            Some(ann) => {
                let mut a = Annot::with_rigid(&mut ty_ex, &mut row_ex, &rigid_ty, &no_rigid);
                self.convert_annot(ann, &mut a)
            }
            None => Type::Exist(self.push_ex()),
        };
        let mut cur = Vec::new();
        for c in &d.constraints {
            let mut a = Annot::with_rigid(&mut ty_ex, &mut row_ex, &rigid_ty, &no_rigid);
            let t = self.convert_annot(&c.ty, &mut a);
            cur.push((c.class.clone(), t));
        }
        // Effect inference is principal: the function's row starts empty and
        // open, and the labels are discovered by inference alone (rule-1 direct
        // performs, applied effect-carrying callees, builtin rows, and `mask`),
        // never seeded from the syntactic set pass. The only thing the annotation
        // contributes here is the *argument* instantiation of a parametric effect
        // it names: scoping `(effect, declared args)` makes a perform of that
        // effect unify against the declared types (so `!{Emit(String)}` rejects
        // `emit(1)`), while the prefix stays empty so the label is still
        // discovered by inference and a declared-but-unperformed effect still
        // warns in `finalize_fn`.
        let mut scope: Vec<(Sym, Vec<Type>)> = Vec::new();
        if let Some(ls) = &d.eff {
            for al in ls {
                if al.args.is_empty() {
                    continue;
                }
                let args: Vec<Type> = al
                    .args
                    .iter()
                    .map(|t| {
                        let mut a =
                            Annot::with_rigid(&mut ty_ex, &mut row_ex, &rigid_ty, &no_rigid);
                        self.convert_annot(t, &mut a)
                    })
                    .collect();
                scope.push((Sym::from(&al.name), args));
            }
        }
        let mu = self.push_ex_row();
        let self_ty = Type::fun_eff(doms.clone(), EffRow::Exist(mu), ret.clone());
        Ok(DeclSeed {
            doms,
            ret,
            cur,
            scope,
            mu,
            self_ty,
        })
    }

    // Stage 1 for a constant member of a recursion group: its self-type is its
    // value type (no arrow, no effects), from the annotation if given else a fresh
    // existential. A constant is generalized by value restriction in `finish_decl`
    // exactly as `infer_const` does; the dummy row tail keeps the shared seed shape
    // and never carries a label, so it defaults to empty.
    fn seed_konst(&mut self, d: &Decl<Core>) -> Result<DeclSeed, TypeError> {
        let val = match &d.ret {
            Some(ann) => {
                self.check_annot_rows(ann, d.span)?;
                self.convert_annot_fresh(ann)
            }
            None => Type::Exist(self.push_ex()),
        };
        let mu = self.push_ex_row();
        Ok(DeclSeed {
            doms: Vec::new(),
            ret: val.clone(),
            cur: Vec::new(),
            scope: Vec::new(),
            mu,
            self_ty: val,
        })
    }

    // Stage 2: check the body against the seeded self-type. `env` holds the
    // entry for this member's own name (a recursive call) and the env-visible
    // schemes of any siblings (a mutual call). The self-entry is re-inserted last
    // so it wins over any colliding parameter name, matching the pre-split order.
    //
    // The self-entry for a plain annotated function is its generalized annotation
    // scheme, so a recursive call instantiates it and may be used at a second type
    // (annotated polymorphic recursion, e.g. over a nested datatype). An
    // unannotated function uses its monomorphic self-type, so a recursive call
    // unifies against the same variables (monomorphic recursion, the only sound
    // option without a signature). A *constrained* function keeps the monomorphic
    // self-type so its recursive call still discharges the constraint against the
    // enclosing dictionary parameter (`cur_self`) rather than re-resolving it.
    // Reset the per-declaration obligation buffers (class constraints, numeric
    // defaulting candidates, index-op resolutions) before checking a new body.
    fn clear_obligations(&mut self) {
        self.wanted.clear();
        self.num_default.clear();
        self.neg_default.clear();
        self.index_ops.clear();
    }

    fn infer_body(&mut self, env: &Env, d: &Decl<Core>, seed: &DeclSeed) -> Result<(), TypeError> {
        self.clear_obligations();
        let mut env2 = env.clone();
        for (p, t) in d.params.iter().zip(&seed.doms) {
            env2.insert(Sym::from(&p.name), t.clone());
        }
        let self_entry = if d.constraints.is_empty() {
            super::env::annotation_scheme(d, self.data).unwrap_or_else(|| seed.self_ty.clone())
        } else {
            seed.self_ty.clone()
        };
        env2.insert(Sym::from(&d.name), self_entry);
        let saved_row = self.cur_row.replace(RowScope {
            tail: seed.mu,
            prefix: BTreeSet::new(),
        });
        let checked = self.in_row_scope(&seed.scope, |tc| {
            tc.with_self(
                d.name.clone(),
                seed.self_ty.clone(),
                seed.cur.clone(),
                |tc| {
                    tc.check(&env2, &d.body, &seed.ret)?;
                    tc.resolve_all()
                },
            )
        });
        self.cur_row = saved_row;
        checked?;
        self.flush_spans();
        Ok(())
    }

    // Stage 3: generalize the inferred self-type against `env` (the environment
    // as it was before this member or its group was seeded, so the group's shared
    // existentials all generalize) and record any class constraints.
    fn finish_decl(
        &mut self,
        env: &Env,
        d: &Decl<Core>,
        seed: &DeclSeed,
    ) -> Result<Type, TypeError> {
        // Unconstrained ambient rows default to empty (pure); only rows tied to
        // a parameter's row variable survive as effect polymorphism. A function
        // additionally keeps its own latent row open so it fits an effectful
        // context by solving that variable under row unification.
        let self_ty = default_open_rows(&self.apply(&seed.self_ty));
        let (g, renames) = self.generalize_map(env, &self_ty);
        if !d.constraints.is_empty() {
            // The scheme's quantified type variables; a constraint may mention only
            // these. A rigid signature variable that no parameter or result uses is
            // not among them, so `given C(b)` on an unused `b` is ambiguous.
            let mut quantified = BTreeSet::new();
            forall_ty_binders(&g, &mut quantified);
            let mut final_cs = Vec::new();
            for ((class, t), c) in seed.cur.iter().zip(&d.constraints) {
                let mut t2 = renames.apply(&self.apply(t));
                // Ambiguous if the constraint carries an existential inference never
                // fixed, or a type variable the scheme does not quantify: no call
                // site could ever determine which instance to pass.
                let mut left = BTreeSet::new();
                t2.free_exist(&mut left);
                let mut tvars = BTreeSet::new();
                super::env::collect_type_vars(&t2, &mut tvars);
                let stray = !tvars.is_subset(&quantified);
                if !left.is_empty() || stray {
                    for e in &left {
                        t2 = t2.subst_exist(*e, &Type::Var("_".into()));
                    }
                    return Err(TypeError::Other {
                        span: c.span,
                        msg: format!(
                            "ambiguous constraint {class}({}): it must mention a type variable from the signature of `{}`",
                            t2.show(),
                            d.name
                        ),
                    });
                }
                final_cs.push((Sym::from(class), t2));
            }
            self.constrained
                .insert(Sym::from(&d.name), (g.clone(), final_cs));
        }
        Ok(g)
    }

    // Run `f` (a body inference ending in `resolve_all`) under a fresh ambient
    // effect row, and return the concrete labels the body accumulated alongside
    // its result. A value or expression has no function arrow to read its row
    // off, so the purity checks (konst, pure instance methods) and the REPL get
    // the principal inferred effects this way instead of a syntactic set pass.
    pub(super) fn scoped_effects<R>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<R, TypeError>,
    ) -> Result<(R, Effects), TypeError> {
        let mu = self.push_ex_row();
        let (r, effs) = self.with_row_scope(
            RowScope {
                tail: mu,
                prefix: BTreeSet::new(),
            },
            |tc| {
                let r = f(tc);
                let effs = if r.is_ok() {
                    tc.apply_row(&EffRow::Exist(mu)).label_names()
                } else {
                    Effects::new()
                };
                (r, effs)
            },
        );
        Ok((r?, effs))
    }

    // A top-level constant: its type is the body's value type (no arrow). With
    // an annotation the body is checked against it, else it is synthesized. The
    // result is generalized so polymorphic constants (`map_empty = Tip`)
    // instantiate fresh at each reference. The inferred effects are returned so
    // the caller can hold a `konst` to purity.
    pub(super) fn infer_const(
        &mut self,
        env: &Env,
        d: &Decl<Core>,
    ) -> Result<(Type, Effects), TypeError> {
        self.reset_ctx();
        self.clear_obligations();
        let (ty, effs) = self.scoped_effects(|tc| {
            let ty = if let Some(ann) = &d.ret {
                tc.check_annot_rows(ann, d.span)?;
                let t = tc.convert_annot_fresh(ann);
                tc.check(env, &d.body, &t)?;
                Ok(t)
            } else {
                tc.synth(env, &d.body)
            };
            let ty = ty?;
            tc.resolve_all()?;
            Ok(ty)
        })?;
        self.flush_spans();
        let t = self.apply(&ty);
        Ok((self.generalize(env, &t), effs))
    }

    pub(super) fn check_instance(
        &mut self,
        env: &Env,
        inst: &ast::InstanceDecl<Core>,
        info: &InstInfo,
        class: &ClassInfo,
    ) -> Result<(), TypeError> {
        for m in &inst.methods {
            self.reset_ctx();
            self.clear_obligations();
            let (_, sig) = class
                .methods
                .iter()
                .find(|(n, _)| n.as_str() == m.name.as_str())
                .ok_or_else(|| TypeError::Ice {
                    msg: format!("instance method `{}` missing from class", m.name),
                })?;
            // An effect-polymorphic method (its class signature carries a row
            // variable, like `fmap`) may perform the effects flowing through that
            // row. A method with a pure signature must be pure: its body is
            // checked under a fresh ambient row whose inferred labels are held to
            // empty, replacing the old syntactic set pass.
            let poly = {
                let mut rv = BTreeSet::new();
                super::env::collect_row_vars(sig, &mut rv);
                !rv.is_empty()
            };
            let expected = sig.subst_var(class.param, &info.head);
            let Type::Fun(doms, _, ret) = &expected else {
                return Err(TypeError::Ice {
                    msg: format!("class method `{}` signature is not a function type", m.name),
                });
            };
            let mut env2 = env.clone();
            for (p, t) in m.params.iter().zip(doms) {
                env2.insert(Sym::from(&p.name), t.clone());
            }
            let qual = format!("{}.{}", inst.name, m.name);
            let ((), effs) = self.scoped_effects(|tc| {
                let ctx = info
                    .context
                    .iter()
                    .map(|(c, t)| (c.to_string(), t.clone()))
                    .collect();
                tc.with_self(qual.clone(), expected.clone(), ctx, |tc| {
                    tc.check(&env2, &m.body, ret)
                        .and_then(|()| tc.resolve_all())
                })
                .map_err(|e| e.in_fn(&qual))
            })?;
            self.flush_spans();
            if !poly && !effs.is_empty() {
                let list: Vec<String> = effs.iter().map(Sym::to_string).collect();
                return Err(TypeError::Other {
                    span: m.body.span,
                    msg: format!(
                        "instance method `{}.{}` must be pure; it performs {}",
                        inst.name,
                        m.name,
                        list.join(", ")
                    ),
                });
            }
        }
        Ok(())
    }
}

// For a known indexable container head, the (expected key type, element type,
// writable) triple; `None` for any other (or not-yet-resolved) type. `Array`/
// `HashMap` are writable; `List`/`String` are read-only.
pub(super) fn index_container(ty: &Type) -> Option<(Type, Type, bool)> {
    match ty {
        Type::Con(n, args) if n.as_str() == "Array" && args.len() == 1 => {
            Some((Type::Int, args[0].clone(), true))
        }
        Type::Con(n, args) if n.as_str() == "HashMap" && args.len() == 1 => {
            Some((Type::Str, args[0].clone(), true))
        }
        // Writable through `list_set` (functional, O(n)); the in-place `array_set`
        // is the `Array` case above.
        Type::Con(n, args) if n.as_str() == LIST && args.len() == 1 => {
            Some((Type::Int, args[0].clone(), true))
        }
        Type::Str => Some((Type::Int, Type::Int, false)),
        _ => None,
    }
}
