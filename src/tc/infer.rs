use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use super::env::{collect_type_vars, Annot};
use super::{ClassInfo, Entry, Env, IndexOp, InstInfo, RowScope, SelfRef, Tc, Wanted};
use crate::error::TypeError;
use crate::sym::Sym;
use crate::syntax::ast::{self, BinOp, Core, Decl, Expr, HandlerArm, PathOp, PathStep, S};
use crate::types::ty::{EffRow, Label, Type, EQ_CLASS, LIST};

// Whether the `Field`-only path `short` is a prefix of `long`. tc only ever
// sees `Field` steps (optic steps are desugared away), so this decides overlap.
fn field_prefix<P: crate::syntax::ast::Phase>(short: &[PathStep<P>], long: &[PathStep<P>]) -> bool {
    short.len() <= long.len()
        && short.iter().zip(long).all(|(a, b)| match (a, b) {
            (PathStep::Field(x), PathStep::Field(y)) => x == y,
            _ => false,
        })
}

// Render an update path for diagnostics; optic steps are gone by tc, but the
// match is kept total.
fn show_path<P: crate::syntax::ast::Phase>(steps: &[PathStep<P>]) -> String {
    steps
        .iter()
        .map(|s| match s {
            PathStep::Field(f) => f.clone(),
            PathStep::Each => "each".into(),
            PathStep::Case(c) => format!("?{c}"),
            PathStep::Index(_) => "[..]".into(),
        })
        .collect::<Vec<_>>()
        .join(".")
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
            (Expr::Lam(ps, body), Type::Fun(doms, _eff, ret)) if ps.len() == doms.len() => {
                let mut env2 = env.clone();
                for (p, d) in ps.iter().zip(doms.iter()) {
                    env2.insert(Sym::from(&p.name), d.clone());
                }
                self.check(&env2, body, ret)
            }
            (Expr::If(c, t, e2), _) => {
                self.check(env, c, &Type::Bool)?;
                self.check(env, t, ty)?;
                self.check(env, e2, ty)
            }
            (Expr::Let(x, v, b), _) => {
                let tv = self.synth(env, v)?;
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
            (Expr::Int(lit), Type::I64 | Type::U64) if lit.suffix == ast::Suffix::None => {
                Self::lit_range(lit, ty, span)?;
                self.fixed.insert(span, ty.clone());
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
        self.pending.push((e.span, t.clone()));
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

    // Zonk after resolve_all, while this declaration's solutions are still in ctx.
    fn flush_spans(&mut self) {
        for (span, t) in std::mem::take(&mut self.pending) {
            let t = self.apply(&t);
            self.span_types.insert(span, t);
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
        let map: Vec<(Sym, Type)> = info
            .params
            .iter()
            .map(|pn| (*pn, Type::Exist(self.push_ex())))
            .collect();
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
            for (pn, t) in &map {
                ft = ft.subst_var(*pn, t);
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
        Ok(Type::Con(
            info.type_name,
            map.iter().map(|(_, t)| self.apply(t)).collect(),
        ))
    }

    fn synth_node(&mut self, env: &Env, e: &S<Expr<Core>>) -> Result<Type, TypeError> {
        let span = e.span;
        match &e.node {
            Expr::Int(lit) => {
                let ty = match lit.suffix {
                    ast::Suffix::None => return Ok(Type::Int),
                    ast::Suffix::I64 => Type::I64,
                    ast::Suffix::U64 => Type::U64,
                };
                Self::lit_range(lit, &ty, span)?;
                self.fixed.insert(span, ty.clone());
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
                if let Some((scheme, cs)) = self.constrained.get(x).cloned() {
                    if t == scheme && !cs.is_empty() {
                        return Ok(self.instantiate_constrained(&scheme, &cs, span, None));
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
                        self.wanted.push(Wanted { span, items });
                    }
                }
                Ok(t)
            }
            Expr::Inst(f, names) => {
                let Expr::Var(x) = &f.node else {
                    return Err(TypeError::Other {
                        span,
                        msg: "explicit instance selection `f(using ..)` requires a named function"
                            .into(),
                    });
                };
                let t = env
                    .get(&Sym::from(x))
                    .cloned()
                    .ok_or_else(|| TypeError::Unbound {
                        span: f.span,
                        name: x.clone(),
                    })?;
                match self.constrained.get(x).cloned() {
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
                        Ok(self.instantiate_constrained(&scheme, &cs, span, Some(names)))
                    }
                    _ => Err(TypeError::Other {
                        span,
                        msg: format!("`{x}` has no class constraints to instantiate"),
                    }),
                }
            }
            Expr::Index(recv, key) => self.synth_index(env, recv, key, span),
            Expr::IndexSet(recv, key, val) => self.synth_index_set(env, recv, key, val, span),
            Expr::Bin(op, a, b) => self.synth_bin(env, *op, a, b, span),
            Expr::If(c, t, e2) => {
                self.check(env, c, &Type::Bool)?;
                let tt = self.synth(env, t)?;
                let tt = self.apply(&tt);
                self.check(env, e2, &tt)?;
                Ok(self.apply(&tt))
            }
            Expr::Let(x, v, b) => {
                let tv = self.synth(env, v)?;
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
                self.check(&env2, body, &Type::Exist(ret))?;
                Ok(self.apply(&Type::fun(doms, Type::Exist(ret))))
            }
            Expr::Call(f, args) => {
                if let Expr::Var(x) = &f.node {
                    if let Some(info) = self.eff_ops.get(x) {
                        if !info.eff_params.is_empty() {
                            let info = info.clone();
                            self.synth(env, f)?;
                            let fty = self.perform_ty(&info);
                            return self.app_synth(env, &fty, args, span);
                        }
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
                        .insert(span, (cname.clone(), fi, info.args.len()));
                }
                Ok(field_ty)
            }
            Expr::RecordCreate(ctor_name, field_exprs) => {
                self.synth_record_create(env, ctor_name, field_exprs, span)
            }
            Expr::RecordUpdate(base_expr, ctor_name, field_exprs) => {
                let info = self
                    .ctors
                    .get(ctor_name)
                    .cloned()
                    .ok_or_else(|| TypeError::Other {
                        span,
                        msg: format!("unknown record constructor {ctor_name}"),
                    })?;
                let result_ty = Type::Con(
                    info.type_name,
                    info.params
                        .iter()
                        .map(|_| Type::Exist(self.push_ex()))
                        .collect(),
                );
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
                    let ft = self.apply(&info.args[fi]);
                    self.check(env, field_expr, &ft)?;
                }
                Ok(self.apply(&result_ty))
            }
            Expr::RecordUpdatePath(base, ups) => self.update_path(env, base, ups, span),
            Expr::Handle(body, arms) => {
                // The handler picks one instantiation per parametric effect it
                // handles. The body checks under that scope, so every perform
                // and callee row inside unifies with the handler's choice.
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
                                let mut op_params = info.params.clone();
                                let mut op_ret = info.ret.clone();
                                let eff_sym = info.effect_name;
                                if let Some((_, args)) = scope.iter().find(|(n, _)| *n == eff_sym) {
                                    for (p, t) in info.eff_params.iter().zip(args) {
                                        let p = *p;
                                        for q in &mut op_params {
                                            *q = q.subst_var(p, t);
                                        }
                                        op_ret = op_ret.subst_var(p, t);
                                    }
                                }
                                let mut env2 = env.clone();
                                for (pname, pty) in params.iter().zip(op_params.iter()) {
                                    env2.insert(Sym::from(pname), pty.clone());
                                }
                                let k_ty = Type::fun(vec![op_ret], Type::Exist(ret_ex));
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
            Expr::Mask(eff, body) => {
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
                // The masked ops bypass the innermost handler, so the expression
                // still demands an enclosing handler. Inject one label into the
                // ambient row, mirroring the set pass (effects.rs `Expr::Mask`),
                // so the unifier does not under-report a masked effect.
                let args = (0..self.eff_arity(eff_sym))
                    .map(|_| Type::Exist(self.push_ex()))
                    .collect();
                let label = Label {
                    name: eff_sym,
                    args,
                };
                self.absorb_row(&EffRow::Extend(label, Box::new(EffRow::Empty)))
                    .map_err(|e| e.at(span))?;
                Ok(t)
            }
            Expr::Ann(inner, ann) => {
                self.check_annot_rows(ann, span)?;
                let mut ty_ex = BTreeMap::new();
                let mut row_ex = BTreeMap::new();
                let no_rigid = BTreeSet::new();
                let mut a = Annot::new(&mut ty_ex, &mut row_ex, &no_rigid);
                let t = self.convert_annot(ann, &mut a);
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

    // `{ base | a.b.c = v, .. }`: each segment must land on a single-constructor
    // record so the rebuild is unconditional. The resolved chains drive
    // elaboration via `path_res`.
    fn update_path(
        &mut self,
        env: &Env,
        base: &S<Expr<Core>>,
        ups: &[(Vec<PathStep<Core>>, PathOp<Core>)],
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
        self.path_res.insert(span, chains);
        Ok(self.apply(&tb))
    }

    // The numeric defaulting rule, in one place: an ambiguous operand defaults
    // to `Int`. `==`/`!=` invoke it for an unconstrained (existential) operand;
    // the ordered and arithmetic operators invoke it for any operand that is not
    // already a fixed-width integer. This is the only site the `Int` literal and
    // its `subtype` decision live, so Eq and Ord share one rule.
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
        let fail = Label {
            name: Sym::from(crate::names::FAIL_EFFECT),
            args: vec![],
        };
        self.absorb_row(&EffRow::Extend(fail, Box::new(EffRow::Empty)))
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

    fn synth_bin(
        &mut self,
        env: &Env,
        op: BinOp,
        a: &S<Expr<Core>>,
        b: &S<Expr<Core>>,
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
                let ta = self.instantiate_constrained(&ta, &[], span, None);
                self.check(env, b, &ta)?;
                let ta = self.apply(&ta);
                match &ta {
                    Type::Int => {}
                    Type::I64 | Type::U64 | Type::Float | Type::Bool | Type::Str => {
                        self.fixed.insert(span, ta);
                    }
                    // Defer like the arithmetic arm: a later use may still pin
                    // this to a fixed-width lane before the `Int` default applies.
                    Type::Exist(_) => self.num_default.push((span, ta)),
                    _ => self.wanted.push(Wanted {
                        span,
                        items: vec![(EQ_CLASS.into(), ta, None)],
                    }),
                }
                Ok(Type::Bool)
            }
            _ => {
                let ta = self.synth(env, a)?;
                let ta = self.apply(&ta);
                // A concrete or rigid left operand drives the operator, exactly as
                // before: a fixed-width lane fixes both sides, and a non-numeric
                // one is rejected at its own span (good blame). The new case is an
                // unsolved existential left operand: rather than defaulting it to
                // `Int` here, check the right operand against it (so the right can
                // pin the lane) and, if both stay ambiguous, defer to one pass at
                // `resolve_all` where a later use can still fix the width. This is
                // what lets `y + x` with `x : I64` type when `y` was left open.
                let t = match &ta {
                    Type::I64 | Type::U64 => {
                        self.check(env, b, &ta)?;
                        self.fixed.insert(span, ta.clone());
                        ta
                    }
                    Type::Int => {
                        self.check(env, b, &ta)?;
                        ta
                    }
                    Type::Exist(_) => {
                        self.check(env, b, &ta)?;
                        let t = self.apply(&ta);
                        match &t {
                            Type::I64 | Type::U64 => {
                                self.fixed.insert(span, t.clone());
                            }
                            Type::Int => {}
                            Type::Exist(_) => self.num_default.push((span, t.clone())),
                            other => {
                                self.default_numeric(other, b.span)?;
                            }
                        }
                        t
                    }
                    // Float belongs to the dotted operators; anything else is not
                    // numeric. `default_numeric` rejects both, blaming the left.
                    other => self.default_numeric(other, a.span)?,
                };
                Ok(if is_cmp(op) { Type::Bool } else { t })
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
                self.articulate(*a, &arg_exs, row, ret);
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

    // The type of a perform site for a parametric op: the op signature with
    // effect parameters replaced by the instantiation in force, and any
    // leftover return-only variables opened fresh per site.
    fn perform_ty(&mut self, info: &super::EffOpInfo) -> Type {
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
        let mut params = info.params.clone();
        let mut ret = info.ret.clone();
        for (p, t) in info.eff_params.iter().zip(&args) {
            let p = *p;
            for q in &mut params {
                *q = q.subst_var(p, t);
            }
            ret = ret.subst_var(p, t);
        }
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
        Type::fun(params, ret)
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
        // enclosing fixed prefix, matching the old standalone `cur_labels`.
        let prefix = self
            .cur_row
            .as_ref()
            .map_or_else(BTreeSet::new, |s| s.prefix.clone());
        let saved_row = self.cur_row.replace(RowScope {
            tail: body_row,
            prefix,
        });
        let body_ty = self.in_row_scope(scope, |tc| tc.synth(env, body));
        self.cur_row = saved_row;
        let body_ty = self.apply(&body_ty?);
        let handled: BTreeSet<Sym> = arms
            .iter()
            .filter_map(|a| match a {
                HandlerArm::Op(op, ..) => self.eff_ops.get(op).map(|i| i.effect_name),
                _ => None,
            })
            .collect();
        self.discharge_row(body_row, &handled)
            .map_err(|e| e.at(span))?;
        Ok(body_ty)
    }

    pub(super) fn infer_decl(
        &mut self,
        env: &Env,
        d: &Decl<Core>,
        latent: &EffRow,
    ) -> Result<Type, TypeError> {
        self.reset_ctx();
        self.wanted.clear();
        self.num_default.clear();
        self.index_ops.clear();
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
        let mut env2 = env.clone();
        let mut ty_ex = BTreeMap::new();
        let mut row_ex = BTreeMap::new();
        let no_rigid = BTreeSet::new();
        let mut doms = Vec::new();
        for p in &d.params {
            let t = match &p.ty {
                Some(ann) => {
                    let mut a = Annot::new(&mut ty_ex, &mut row_ex, &no_rigid);
                    self.convert_annot(ann, &mut a)
                }
                None => Type::Exist(self.push_ex()),
            };
            env2.insert(Sym::from(&p.name), t.clone());
            doms.push(t);
        }
        let ret = match &d.ret {
            Some(ann) => {
                let mut a = Annot::new(&mut ty_ex, &mut row_ex, &no_rigid);
                self.convert_annot(ann, &mut a)
            }
            None => Type::Exist(self.push_ex()),
        };
        let mut cur = Vec::new();
        for c in &d.constraints {
            let mut a = Annot::new(&mut ty_ex, &mut row_ex, &no_rigid);
            let t = self.convert_annot(&c.ty, &mut a);
            cur.push((c.class.clone(), t));
        }
        // Instantiate the latent row's parametric labels. Arguments come from
        // the declared annotation (sharing its variable scope) or are opened
        // fresh. Scope the body so perform sites pick them up.
        let mut labels = Vec::new();
        let mut scope = Vec::new();
        for l in latent.labels() {
            let arity = self.eff_arity(l.name);
            let ann = d
                .eff
                .as_ref()
                .and_then(|ls| {
                    ls.iter()
                        .find(|al| l.name == al.name.as_str() && !al.args.is_empty())
                })
                .cloned();
            let args: Vec<Type> = match ann {
                Some(al) => al
                    .args
                    .iter()
                    .map(|t| {
                        let mut a = Annot::new(&mut ty_ex, &mut row_ex, &no_rigid);
                        self.convert_annot(t, &mut a)
                    })
                    .collect(),
                None => (0..arity).map(|_| Type::Exist(self.push_ex())).collect(),
            };
            if !args.is_empty() {
                scope.push((l.name, args.clone()));
            }
            labels.push(Label { name: l.name, args });
        }
        // The function's own effect row is open: the set-pass labels plus a
        // fresh existential tail the body's applications extend, so effects
        // performed through function values flow into this row.
        let mu = self.push_ex_row();
        let prefix: BTreeSet<Sym> = labels.iter().map(|l| l.name).collect();
        let latent = labels
            .into_iter()
            .rev()
            .fold(EffRow::Exist(mu), |acc, l| EffRow::Extend(l, Box::new(acc)));
        let self_ty = Type::fun_eff(doms, latent, ret.clone());
        env2.insert(Sym::from(&d.name), self_ty.clone());
        let saved_row = self.cur_row.replace(RowScope { tail: mu, prefix });
        let checked = self.in_row_scope(&scope, |tc| {
            tc.with_self(d.name.clone(), self_ty.clone(), cur.clone(), |tc| {
                tc.check(&env2, &d.body, &ret)?;
                tc.resolve_all()
            })
        });
        self.cur_row = saved_row;
        checked?;
        self.flush_spans();
        // Unconstrained ambient rows default to empty (pure); only rows tied to
        // a parameter's row variable survive as effect polymorphism.
        let self_ty = default_open_rows(&self.apply(&self_ty));
        let (g, mapping) = self.generalize_map(env, &self_ty);
        if !d.constraints.is_empty() {
            let mut final_cs = Vec::new();
            for ((class, t), c) in cur.iter().zip(&d.constraints) {
                let mut t2 = self.apply(t);
                for (e, name) in &mapping {
                    t2 = t2.subst_exist(*e, &Type::Var(Sym::from(name)));
                }
                let mut left = BTreeSet::new();
                t2.free_exist(&mut left);
                if !left.is_empty() {
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
                final_cs.push((class.clone(), t2));
            }
            self.constrained
                .insert(d.name.clone(), (g.clone(), final_cs));
        }
        Ok(g)
    }

    // A top-level constant: its type is the body's value type (no arrow). With
    // an annotation the body is checked against it, else it is synthesized. The
    // result is generalized so polymorphic constants (`map_empty = Tip`)
    // instantiate fresh at each reference.
    pub(super) fn infer_const(&mut self, env: &Env, d: &Decl<Core>) -> Result<Type, TypeError> {
        self.reset_ctx();
        self.wanted.clear();
        self.num_default.clear();
        self.index_ops.clear();
        let ty = if let Some(ann) = &d.ret {
            self.check_annot_rows(ann, d.span)?;
            let mut ty_ex = BTreeMap::new();
            let mut row_ex = BTreeMap::new();
            let no_rigid = BTreeSet::new();
            let mut a = Annot::new(&mut ty_ex, &mut row_ex, &no_rigid);
            let t = self.convert_annot(ann, &mut a);
            self.check(env, &d.body, &t)?;
            t
        } else {
            self.synth(env, &d.body)?
        };
        self.resolve_all()?;
        self.flush_spans();
        let t = self.apply(&ty);
        Ok(self.generalize(env, &t))
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
            self.wanted.clear();
            self.num_default.clear();
            self.index_ops.clear();
            let (_, sig) = class
                .methods
                .iter()
                .find(|(n, _)| n == &m.name)
                .ok_or_else(|| TypeError::Ice {
                    msg: format!("instance method `{}` missing from class", m.name),
                })?;
            let expected = sig.subst_var(Sym::from(&class.param), &info.head);
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
            self.with_self(qual.clone(), expected.clone(), info.context.clone(), |tc| {
                tc.check(&env2, &m.body, ret)
                    .and_then(|()| tc.resolve_all())
            })
            .map_err(|e| e.in_fn(&qual))?;
            self.flush_spans();
        }
        Ok(())
    }
}

// A row existential left open after checking but not reachable from any
// parameter row is unconstrained: default it to empty (pure). Rows a parameter
// mentions are genuine effect polymorphism, kept for generalization
// (e.g. `apply : ((b)->a!{e}, b) ->{e} a`).
fn default_open_rows(ty: &Type) -> Type {
    let Type::Fun(doms, _, _) = ty else {
        return ty.clone();
    };
    let mut param_rows = BTreeSet::new();
    for p in doms {
        p.free_exist_row(&mut param_rows);
    }
    let mut all_rows = BTreeSet::new();
    ty.free_exist_row(&mut all_rows);
    let mut out = ty.clone();
    for r in all_rows.difference(&param_rows) {
        out = out.subst_row_exist(*r, &EffRow::Empty);
    }
    out
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

const fn is_cmp(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq
            | BinOp::Ne
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
            | BinOp::Eqf
            | BinOp::Nef
            | BinOp::Ltf
            | BinOp::Lef
            | BinOp::Gtf
            | BinOp::Gef
    )
}
