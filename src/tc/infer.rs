use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use super::env::collect_type_vars;
use super::{Entry, Env, HandlerFrame, IndexOp, RowScope, Tc, Wanted};
use crate::error::{suggest, ErrKind, TypeError};
use crate::kw;
use crate::names;
use crate::sym::Sym;
use crate::syntax::ast::{self, Core, Expr, HandlerArm, NodeId, S};
use crate::types::is_or_null_element;
use crate::types::ty::{EffRow, Label, Type, LIST, NUM_CLASS, SHOW_CLASS};
use crate::wired::Indexable;

mod decl;
mod defaulting;
mod diagnostics;
mod numeric;
mod paths;
mod records;

impl Tc<'_> {
    fn check(&mut self, env: &Env, e: &S<Expr<Core>>, ty: &Type) -> Result<(), TypeError> {
        let span = e.span;
        let id = e.id;
        match (&e.node, ty) {
            (_, Type::Forall(n, b)) => {
                // Skolemize with a fresh identity rendering as `n`: nested
                // same-name `forall` binders get distinct context entries.
                let sk = Sym::fresh_named(*n);
                let b1 = b.subst_var(*n, &Type::Var(sk));
                self.ctx.push(Entry::Uni(sk));
                self.check(env, e, &b1)?;
                self.drop_uni(sk);
                Ok(())
            }
            (_, Type::RowForall(n, b)) => {
                let sk = Sym::fresh_named(*n);
                let b1 = b.subst_row_var(*n, &EffRow::Var(sk));
                self.ctx.push(Entry::RowUni(sk));
                self.check(env, e, &b1)?;
                self.drop_row_uni(sk);
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
                let mut prefix = Vec::new();
                let mut cursor = &eff;
                while let EffRow::Extend(l, more) = cursor {
                    prefix.push(l.clone());
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
                    e.or(TypeError::TypeMismatch {
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

    // Run `f` under a delimited ambient effect row, restoring the previous row
    // afterwards (mirrors `with_self`). Any reading of the scoped row (e.g. to
    // collect inferred effects) must happen inside `f`, before the restore.
    fn with_row_scope<R>(&mut self, scope: RowScope, f: impl FnOnce(&mut Self) -> R) -> R {
        let saved = self.cur_row.replace(scope);
        let r = f(self);
        self.cur_row = saved;
        r
    }

    // After inference has solved every existential, hold each `This(e)` to the
    // `OrNull` element rule on its now-zonked element type. A residual existential
    // means the element was never pinned to a concrete type, which is unsound (it
    // could later be `Unit`, the null word), so it is rejected with the same E-code
    // as a bad written annotation.
    pub(super) fn check_or_null_sites(&self) -> Result<(), TypeError> {
        for (span, elem) in &self.or_null_sites {
            let elem = self.apply(elem);
            let found = if matches!(elem, Type::Exist(_) | Type::Var(_)) {
                "an un-inferred element type (add an `OrNull(T)` annotation)".to_string()
            } else if is_or_null_element(&elem) {
                continue;
            } else {
                format!("`{}`", elem.show())
            };
            return Err(ErrKind::OrNullBadElement { found }.at(*span));
        }
        Ok(())
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
            // `Null` is the null word for any element, so it takes a fresh element
            // existential that later unification pins from context. It is always
            // sound (it carries no `a`), so it records no `or_null_sites` entry.
            Expr::Var(x) if x == kw::CTOR_NULL => {
                let ty = Type::OrNull(Box::new(Type::Exist(self.push_ex())));
                self.fixed.insert(id, ty.clone());
                Ok(ty)
            }
            // Bare `This` is only meaningful applied to its argument (handled in
            // the call path); a first-class use has no place to check the element.
            Expr::Var(x) if x == kw::CTOR_THIS => Err(ErrKind::UnboundVar {
                name: format!("{x} (write `This(e)`, applied to its argument)"),
            }
            .at(span)),
            Expr::Var(x) => {
                let t = env.get(&Sym::from(x)).cloned().ok_or_else(|| {
                    ErrKind::UnboundVar { name: x.clone() }.at(span).maybe_help(
                        suggest::suggestion(x, env.keys().map(|k| names::bare_name(k.as_str()))),
                    )
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
                        prefix: Vec::new(),
                    },
                    |tc| tc.check(&env2, body, &Type::Exist(ret)),
                );
                checked?;
                Ok(self.apply(&Type::fun_eff(doms, EffRow::Exist(row), Type::Exist(ret))))
            }
            Expr::Call(f, args) => {
                if let Expr::Var(x) = &f.node {
                    // `This(e)` builds a non-allocating nullable from `e`. The
                    // element type is `e`'s type; its non-null soundness is checked
                    // after inference (`or_null_sites`), so `This` is held to the
                    // same rule as a written `OrNull(a)` even with no annotation.
                    if x == kw::CTOR_THIS {
                        let [arg] = args.as_slice() else {
                            return Err(ErrKind::UnboundVar {
                                name: format!(
                                    "This takes exactly one argument, given {}",
                                    args.len()
                                ),
                            }
                            .at(span));
                        };
                        let elem = self.synth(env, arg)?;
                        self.or_null_sites.push((span, elem.clone()));
                        let ty = Type::OrNull(Box::new(elem));
                        self.fixed.insert(id, ty.clone());
                        return Ok(ty);
                    }
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
            // Unboxed products type structurally, exactly like their boxed
            // counterparts; the representation (`Repr::Product`) is carried by the
            // distinct `Type` variant. Only the lowering to Core is still a later
            // slice, so a constructed unboxed value is rejected at elaboration.
            Expr::UnboxedTuple(elems) => {
                let ts: Result<Vec<_>, _> =
                    elems.iter().map(|elem| self.synth(env, elem)).collect();
                let ts = ts?;
                Ok(Type::UnboxedTuple(
                    ts.iter().map(|t| self.apply(t)).collect(),
                ))
            }
            Expr::UnboxedRecord(fields) => {
                let mut fs = Vec::with_capacity(fields.len());
                for (name, elem) in fields {
                    let t = self.synth(env, elem)?;
                    fs.push((Sym::from(name.as_str()), self.apply(&t)));
                }
                Ok(Type::UnboxedRecord(fs))
            }
            Expr::UnboxedField(e, field) => {
                let te = self.synth(env, e)?;
                let te = self.apply(&te);
                match &te {
                    Type::UnboxedRecord(fs) => {
                        let Some(fi) = fs.iter().position(|(n, _)| n.as_str() == field) else {
                            return Err(ErrKind::UnknownField {
                                field: field.clone(),
                                ctor: te.show(),
                            }
                            .at(span));
                        };
                        // Record the field's position and the record arity so
                        // elaboration can lower the projection to a positional
                        // tuple `Case`.
                        self.unboxed_field.insert(id, (fi, fs.len()));
                        Ok(fs[fi].1.clone())
                    }
                    other => Err(ErrKind::FieldAccessNonRecord { ty: other.show() }.at(span)),
                }
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
                        return Err(ErrKind::FieldAccessNonRecord { ty: other.show() }.at(span))
                    }
                };
                let (field_ty, fi) = self.find_field(span, ctor_name.as_str(), field, &te)?;
                if let Some((cname, info)) = self.ctors.iter().find(|(_, c)| {
                    c.type_name == ctor_name && c.fields.iter().any(|f| f.as_str() == field)
                }) {
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
            return Err(ErrKind::InstSelectNeedsName.at(span));
        };
        let t = env.get(&Sym::from(x)).cloned().ok_or_else(|| {
            ErrKind::UnboundVar { name: x.clone() }
                .at(f.span)
                .maybe_help(suggest::suggestion(
                    x,
                    env.keys().map(|k| names::bare_name(k.as_str())),
                ))
        })?;
        match self.constrained.get(&Sym::from(x)).cloned() {
            Some((scheme, cs)) if t == scheme && !cs.is_empty() => {
                if names.len() != cs.len() {
                    return Err(ErrKind::ConstraintArgCountMismatch {
                        name: x.clone(),
                        expected: cs.len(),
                        got: names.len(),
                    }
                    .at(span));
                }
                Ok(self.instantiate_constrained(&scheme, &cs, id, span, Some(names)))
            }
            _ => Err(ErrKind::NoClassConstraints { name: x.clone() }.at(span)),
        }
    }

    // `{ base | field = v, .. }` over a known record constructor: the base checks
    // at the record type and each named field at its declared type.

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
        // A handler binds each operation at most once, carries at most one
        // return clause, and each clause binds exactly the operation's declared
        // arity. Rejected here, before any consumer (row discharge, elaboration,
        // the interpreter, every lowering tier) can see an ambiguous handler:
        // the interpreter's arm map and the free-monad cascade would otherwise
        // resolve a duplicate differently (last-wins versus first-wins), making
        // the lowering tier observable.
        self.validate_handler_arms(arms, span)?;
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
                        return Err(ErrKind::UnknownEffectOp {
                            op: op_name.clone(),
                        }
                        .at(span));
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

    // Structural validity of a handler's clause list: operation uniqueness, at
    // most one return clause, and exact op arity. Unknown operations are left
    // for the main loop's pointed `UnknownEffectOp` error.
    fn validate_handler_arms(
        &self,
        arms: &[HandlerArm<Core>],
        handler_span: Span,
    ) -> Result<(), TypeError> {
        let mut seen_ops: BTreeMap<&str, Span> = BTreeMap::new();
        let mut return_span: Option<Span> = None;
        for arm in arms {
            match arm {
                HandlerArm::Return(_, arm_body) => {
                    if let Some(first) = return_span {
                        return Err(ErrKind::DuplicateReturnArm
                            .at(arm_body.span)
                            .label(first, "first `return` clause here"));
                    }
                    return_span = Some(arm_body.span);
                }
                HandlerArm::Op(op_name, params, _, arm_body) => {
                    if let Some(first) = seen_ops.get(op_name.as_str()) {
                        return Err(ErrKind::DuplicateHandlerArm {
                            op: op_name.clone(),
                        }
                        .at(arm_body.span)
                        .label(*first, format!("first clause for `{op_name}` here")));
                    }
                    seen_ops.insert(op_name.as_str(), arm_body.span);
                    if let Some(info) = self.eff_ops.get(op_name) {
                        if params.len() != info.params.len() {
                            return Err(ErrKind::HandlerArmArity {
                                op: op_name.clone(),
                                declared: info.params.len(),
                                provided: params.len(),
                            }
                            .at(arm_body.span));
                        }
                    }
                }
                #[expect(
                    clippy::uninhabited_references,
                    reason = "Never is uninhabited in Core; arm is unreachable"
                )]
                HandlerArm::Sugar(never) => match *never {},
            }
        }
        // Coverage: a handler discharges every effect its arms name, so it must
        // implement every operation of each such effect. Row discharge is
        // effect-granular; letting an op-granular subset through would remove
        // the whole effect from the body's row and leave the unimplemented
        // operations to escape past their own handler. Partial handlers with a
        // residual row are a future design, not an accident of row subtraction.
        let mut by_effect: BTreeMap<Sym, BTreeSet<&str>> = BTreeMap::new();
        for arm in arms {
            if let HandlerArm::Op(op_name, _, _, _) = arm {
                if let Some(info) = self.eff_ops.get(op_name) {
                    by_effect
                        .entry(info.effect_name)
                        .or_default()
                        .insert(op_name.as_str());
                }
            }
        }
        for (effect, handled) in &by_effect {
            let missing: Vec<&str> = self
                .eff_ops
                .iter()
                .filter(|(name, info)| {
                    info.effect_name == *effect && !handled.contains(name.as_str())
                })
                .map(|(name, _)| name.as_str())
                .collect();
            if !missing.is_empty() {
                let missing = missing
                    .iter()
                    .map(|m| format!("`{m}`"))
                    .collect::<Vec<_>>()
                    .join(", ");
                return Err(ErrKind::IncompleteHandler {
                    effect: effect.to_string(),
                    missing,
                }
                .at(handler_span));
            }
        }
        Ok(())
    }

    // `{ base | a.b.c = v, .. }`: each segment must land on a single-constructor
    // record so the rebuild is unconditional. The resolved chains drive
    // elaboration via `path_res`.

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
            Err(ErrKind::NotIndexable { ty: recv_ty.show() }.at(recv.span))
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
            _ => Err(ErrKind::NotIndexAssignable { ty: recv_ty.show() }.at(recv.span)),
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
            // Applying a usage-annotated closure applies its inner function; the
            // multiplicity contract (`@ once`: at most one use) is enforced by the
            // linear-use pass, not by the call rule.
            Type::Coeffect(inner, _) => self.app_synth(env, inner, args, span),
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
                    return Err(ErrKind::ArgCountMismatch {
                        expected: doms.len(),
                        got: args.len(),
                    }
                    .at(span));
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
            other => Err(ErrKind::ApplyNonFunction { ty: other.show() }.at(span)),
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
                    e.or(ErrKind::EffectInstMismatch {
                        actual: self.show_label(l),
                        expected: self.show_label(&Label {
                            name: l.name,
                            args: args.clone(),
                        }),
                    }
                    .at(span))
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
            return Err(ErrKind::UnknownEffectInMask {
                eff: eff.to_string(),
            }
            .at(span));
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
            .map_or_else(Vec::new, |s| s.prefix.clone());
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
}

// For a known indexable container head, the (expected key type, element type,
// writable) triple; `None` for any other (or not-yet-resolved) type. `Array`/
// `HashMap` are writable; `List`/`String` are read-only.
pub(super) fn index_container(ty: &Type) -> Option<(Type, Type, bool)> {
    Indexable::classify(ty).map(|kind| kind.signature(ty))
}
