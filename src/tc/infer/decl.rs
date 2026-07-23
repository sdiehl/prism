use std::collections::{BTreeMap, BTreeSet};

use super::defaulting::default_open_rows;
use super::diagnostics::{forall_ty_binders, poly_recursion_hint};
use crate::error::{ErrKind, TypeError};
use crate::sym::Sym;
use crate::syntax::ast::{self, Core, Decl};
use crate::types::ty::{EffRow, Effects, Type};

use super::super::env::Annot;
use super::super::{
    ClassInfo, Env, HoleBinding, HoleCandidate, HoleReport, InstInfo, RowScope, SelfRef, Tc,
};

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
    expected_row: EffRow,
    self_ty: Type,
}

// The scheme a sibling or self reference sees during SCC body inference: the
// generalized `annotation_scheme` with its outermost latent effect row bound to
// this member's shared row existential `mu`. Effect inference is monomorphic
// within a recursion group, so a sibling call must propagate the callee's
// inferred effects through `mu` exactly as an unannotated member's monomorphic
// self-type does. Without it, a member whose only effects come from a sibling
// call is inferred pure and its declared row is lost between checking and typed
// Core, producing a false "never performed" warning followed by E9996. Type
// recursion stays polymorphic: the quantified type variables refresh per
// instantiation; only the effect row is shared across the group.
fn with_latent_row(scheme: Type, mu: u32) -> Type {
    match scheme {
        Type::Forall(v, b) => Type::Forall(v, Box::new(with_latent_row(*b, mu))),
        Type::RowForall(v, b) => Type::RowForall(v, Box::new(with_latent_row(*b, mu))),
        Type::Fun(ps, _, r) => Type::Fun(ps, EffRow::Exist(mu), r),
        other => other,
    }
}

impl Tc<'_> {
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
        for (id, t) in std::mem::take(&mut self.pending) {
            let t = self.apply(&t);
            self.span_types.insert(id, t);
        }
        let pending: BTreeMap<_, _> = std::mem::take(&mut self.pending_tooltip_rows)
            .into_iter()
            .collect();
        for (id, row) in pending {
            if let Some(ty) = self.span_types.get(&id).cloned() {
                let rendered = self.report_tooltip(&ty, &row);
                self.tooltip_rows.insert(id, rendered);
            }
        }
        self.touched_tooltip_rows.clear();
        self.tooltip_row_scaffolds.clear();
    }

    // Turn inference-time hole sites into stable public reports while their
    // context solutions are still live. Candidate compatibility uses the real
    // subsumption relation in a rolled-back context, so ranking cannot constrain
    // either the hole or a later candidate.
    pub(in crate::tc) fn flush_holes(&mut self) {
        for site in std::mem::take(&mut self.hole_sites) {
            let expected = self.apply(&site.expected);
            let expected_s = self.report_type(&expected);
            let effects = self.report_row(&site.effects);
            let mut bindings: Vec<HoleBinding> = site
                .env
                .iter()
                .filter(|(name, _)| !name.as_str().contains('@'))
                .map(|(name, ty)| HoleBinding {
                    name: name.to_string(),
                    ty: self.report_type(&self.apply(ty)),
                })
                .collect();
            bindings.sort_by(|a, b| a.name.cmp(&b.name));

            let mut candidates = Vec::new();
            for binding in &bindings {
                let Some(candidate) = site.env.get(&Sym::from(&binding.name)).cloned() else {
                    continue;
                };
                let candidate = self.apply(&candidate);
                let exact = candidate == expected;
                let saved_ctx = self.ctx.clone();
                let saved_next = self.next;
                let fits = self.subtype(&candidate, &expected).is_ok();
                self.ctx = saved_ctx;
                self.next = saved_next;
                if fits {
                    candidates.push(HoleCandidate {
                        name: binding.name.clone(),
                        ty: binding.ty.clone(),
                        exact,
                    });
                }
            }
            candidates.sort_by(|a, b| (!a.exact, &a.name).cmp(&(!b.exact, &b.name)));
            self.holes.push(HoleReport {
                name: site.name,
                start: site.span.start,
                end: site.span.end,
                expected: expected_s,
                effects,
                bindings,
                candidates,
            });
        }
    }

    fn report_type(&self, ty: &Type) -> String {
        self.generalize(&Env::new(), ty).show()
    }

    fn report_row(&self, row: &EffRow) -> String {
        let shown = self.generalize(&Env::new(), &Type::Row(self.apply_row(row)));
        let mut body = &shown;
        while let Type::Forall(_, next) | Type::RowForall(_, next) = body {
            body = next;
        }
        match body {
            Type::Row(row) => Self::show_report_row(row),
            _ => Self::show_report_row(&self.apply_row(row)),
        }
    }

    // Generalize the node type and evaluation row together so metavariables use
    // the same canonical naming pass, then render the row even when it is empty.
    // This is the docs generator's canonical type printer plus the tooltip-only
    // rule that `! {}` is never omitted.
    fn report_tooltip(&self, ty: &Type, row: &EffRow) -> String {
        let pair = Type::Tuple(vec![self.apply(ty), Type::Row(self.apply_row(row))]);
        let shown = self.generalize(&Env::new(), &pair);
        let mut body = &shown;
        while let Type::Forall(_, next) | Type::RowForall(_, next) = body {
            body = next;
        }
        match body {
            Type::Tuple(parts) if parts.len() == 2 => match &parts[1] {
                // A pure expression reads as its type alone: the empty row is
                // the default, so `! {}` would be noise on most spans.
                Type::Row(row) => {
                    let shown_row = Self::show_report_row(row);
                    if shown_row == "{}" {
                        parts[0].show()
                    } else {
                        format!("{} ! {}", parts[0].show(), shown_row)
                    }
                }
                _ => unreachable!("tooltip pair carries an effect row"),
            },
            _ => unreachable!("tooltip generalization preserves its pair"),
        }
    }

    fn show_report_row(row: &EffRow) -> String {
        let mut labels: Vec<String> = row
            .labels()
            .into_iter()
            .map(super::super::Label::show)
            .collect();
        labels.sort();
        let tail = match row.tail() {
            EffRow::Empty => None,
            EffRow::Var(name) => Some(name.to_string()),
            EffRow::Exist(id) => Some(format!("?r{id}")),
            EffRow::Extend(..) => unreachable!(),
        };
        match (labels.is_empty(), tail) {
            (true, None) => "{}".into(),
            (true, Some(tail)) => format!("{{| {tail}}}"),
            (false, None) => format!("{{{}}}", labels.join(", ")),
            (false, Some(tail)) => format!("{{{} | {tail}}}", labels.join(", ")),
        }
    }

    // A single acyclic (or self-recursive) function: seed its monomorphic
    // self-type, infer its body against it, then generalize. The three stages
    // are factored so a mutually recursive group (`infer_scc`) can interleave
    // them: seed every member first, infer every body against the shared
    // monomorphic variables, then generalize the whole group.
    pub(in crate::tc) fn infer_decl(
        &mut self,
        env: &Env,
        d: &Decl<Core>,
    ) -> Result<Type, TypeError> {
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
    pub(in crate::tc) fn infer_scc(
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
            let visible = super::super::env::annotation_scheme(d, self.data)
                .map_or_else(|| seed.self_ty.clone(), |s| with_latent_row(s, seed.mu));
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
                super::super::require_pure_konst(d, &effs)?;
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
        // One kind per variable across every annotation of the declaration
        // (params, return, and constraints share one signature scope).
        let mut var_kinds = BTreeMap::new();
        for p in &d.params {
            if let Some(ann) = &p.ty {
                self.check_annot_rows(ann, d.span)?;
                super::super::env::demand_var_kinds(ann, self.data, &mut var_kinds, d.span)?;
            }
        }
        if let Some(ann) = &d.ret {
            self.check_annot_rows(ann, d.span)?;
            super::super::env::demand_var_kinds(ann, self.data, &mut var_kinds, d.span)?;
        }
        if let Some(ls) = &d.eff {
            self.check_labels(ls, d.span)?;
        }
        for c in &d.constraints {
            // Constraint heads are classes, not datatypes: their parameter
            // kinds (higher-kinded for `Functor`/`Foldable`) live in the class
            // system, which checks them itself, so the per-variable kind pass
            // does not read constraint types (it would wrongly demand `Type`
            // for an HKT class parameter).
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
        let rigid_ty = super::super::env::signature_ty_vars(d, self.data);
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
        let mut expected_labels = Vec::new();
        if let Some(ls) = &d.eff {
            for al in ls {
                let args: Vec<Type> = al
                    .args
                    .iter()
                    .map(|t| {
                        let mut a =
                            Annot::with_rigid(&mut ty_ex, &mut row_ex, &rigid_ty, &no_rigid);
                        self.convert_annot(t, &mut a)
                    })
                    .collect();
                if !args.is_empty() {
                    scope.push((Sym::from(&al.name), args.clone()));
                }
                expected_labels.push(super::super::Label {
                    name: Sym::from(&al.name),
                    args,
                });
            }
        }
        let mu = self.push_ex_row();
        let expected_row = if d.eff.is_some() {
            EffRow::canonical(expected_labels, EffRow::Empty)
        } else {
            EffRow::Exist(mu)
        };
        let self_ty = Type::fun_eff(doms.clone(), EffRow::Exist(mu), ret.clone());
        Ok(DeclSeed {
            doms,
            ret,
            cur,
            scope,
            mu,
            expected_row,
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
                let mut var_kinds = BTreeMap::new();
                super::super::env::demand_var_kinds(ann, self.data, &mut var_kinds, d.span)?;
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
            expected_row: EffRow::Empty,
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
    // defaulting candidates, index-op resolutions, and local operation-use
    // refinement) before checking a new body. Handler residual facts accumulate
    // program-wide, but no in-progress use or continuation summary may cross a
    // declaration/SCC-member boundary.
    fn clear_obligations(&mut self) {
        self.wanted.clear();
        self.num_default.clear();
        self.neg_default.clear();
        self.index_ops.clear();
        self.operation_uses = super::super::OperationUses::default();
        self.precise_calls.clear();
        debug_assert!(self.handler_stack.is_empty());
    }

    fn infer_body(&mut self, env: &Env, d: &Decl<Core>, seed: &DeclSeed) -> Result<(), TypeError> {
        self.clear_obligations();
        let mut env2 = env.clone();
        for (p, t) in d.params.iter().zip(&seed.doms) {
            env2.insert(Sym::from(&p.name), t.clone());
        }
        let self_entry = if d.constraints.is_empty() {
            super::super::env::annotation_scheme(d, self.data)
                .map_or_else(|| seed.self_ty.clone(), |s| with_latent_row(s, seed.mu))
        } else {
            seed.self_ty.clone()
        };
        env2.insert(Sym::from(&d.name), self_entry);
        let saved_row = self.cur_row.replace(RowScope {
            tail: seed.mu,
            prefix: Vec::new(),
            expected: seed.expected_row.clone(),
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
        self.flush_holes();
        // Record the principal-body-effect witness while the solutions are
        // live: the ambient row the body actually accumulated, read before
        // generalization (`default_open_rows`) re-opens a pure row for context
        // fit and destroys the closedness fact. The row is closed for the
        // borrow rule exactly when its tail stayed this declaration's own
        // ambient (or emptied): a tail that solved to a row variable or
        // existential also reachable from the parameter or return types means
        // the body forwards interface effects (a higher-order argument's, or a
        // returned computation's), which can suspend.
        let row = self.apply_row(&EffRow::Exist(seed.mu));
        let closed = match row.tail() {
            EffRow::Empty => true,
            tail @ (EffRow::Var(_) | EffRow::Exist(_)) => {
                let mut in_iface = false;
                let mut scan = |t: &Type| {
                    super::super::env::for_each_row_tail(t, &mut |other| in_iface |= other == tail);
                };
                for dom in &seed.doms {
                    scan(&self.apply(dom));
                }
                scan(&self.apply(&seed.ret));
                !in_iface
            }
            EffRow::Extend(..) => false,
        };
        self.body_witness.insert(
            d.name.clone(),
            super::super::BodyWitness {
                effects: row.label_names(),
                closed,
            },
        );
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
                super::super::env::collect_type_vars(&t2, &mut tvars);
                let stray = !tvars.is_subset(&quantified);
                if !left.is_empty() || stray {
                    for e in &left {
                        t2 = t2.subst_exist(*e, &Type::Var("_".into()));
                    }
                    return Err(ErrKind::AmbiguousConstraint {
                        class: class.clone(),
                        ty: t2.show(),
                        name: d.name.clone(),
                    }
                    .at(c.span));
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
    pub(in crate::tc) fn scoped_effects<R>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<R, TypeError>,
    ) -> Result<(R, Effects), TypeError> {
        let mu = self.push_ex_row();
        self.scoped_effects_with_tail(mu, EffRow::Exist(mu), f)
    }

    pub(in crate::tc) fn scoped_effects_expected<R>(
        &mut self,
        expected: EffRow,
        f: impl FnOnce(&mut Self) -> Result<R, TypeError>,
    ) -> Result<(R, Effects), TypeError> {
        let mu = self.push_ex_row();
        self.scoped_effects_with_tail(mu, expected, f)
    }

    fn scoped_effects_with_tail<R>(
        &mut self,
        mu: u32,
        expected: EffRow,
        f: impl FnOnce(&mut Self) -> Result<R, TypeError>,
    ) -> Result<(R, Effects), TypeError> {
        let (r, effs) = self.with_row_scope(
            RowScope {
                tail: mu,
                prefix: Vec::new(),
                expected,
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
    pub(in crate::tc) fn infer_const(
        &mut self,
        env: &Env,
        d: &Decl<Core>,
    ) -> Result<(Type, Effects), TypeError> {
        self.reset_ctx();
        self.clear_obligations();
        let (ty, effs) = self.scoped_effects_expected(EffRow::Empty, |tc| {
            let ty = if let Some(ann) = &d.ret {
                tc.check_annot_rows(ann, d.span)?;
                let mut var_kinds = BTreeMap::new();
                super::super::env::demand_var_kinds(ann, tc.data, &mut var_kinds, d.span)?;
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
        self.flush_holes();
        let t = self.apply(&ty);
        Ok((self.generalize(env, &t), effs))
    }

    pub(in crate::tc) fn check_instance(
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
                .ok_or_else(|| TypeError::InternalInvariant {
                    msg: format!("instance method `{}` missing from class", m.name),
                })?;
            // The instance method is checked against the class method's entire
            // instantiated scheme, INCLUDING its effect row, not just its result
            // type. The declared row bounds which concrete effects the body may
            // perform: an effect-polymorphic method (`fmap : ... ! {| e}`) may
            // only forward effects that flow through the row variable, which stay
            // as the variable and never appear as concrete labels, so its
            // declared concrete labels are empty. A universally quantified row
            // obligates parametricity; it is not permission to choose a new
            // concrete effect (the `leak` hole). A pure method (`rank : (a) ->
            // Int`) likewise has an empty declared row and must be pure.
            let expected = sig.subst_var(class.param, &info.head);
            let Type::Fun(doms, exp_row, ret) = &expected else {
                return Err(TypeError::InternalInvariant {
                    msg: format!("class method `{}` signature is not a function type", m.name),
                });
            };
            let declared_labels = exp_row.label_names();
            let mut env2 = env.clone();
            for (p, t) in m.params.iter().zip(doms) {
                env2.insert(Sym::from(&p.name), t.clone());
            }
            let qual = format!("{}.{}", inst.name, m.name);
            let ((), effs) = self.scoped_effects_expected(exp_row.clone(), |tc| {
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
            self.flush_holes();
            let undeclared: Vec<String> = effs
                .iter()
                .filter(|eff| !declared_labels.contains(eff))
                .map(Sym::to_string)
                .collect();
            if !undeclared.is_empty() {
                return Err(ErrKind::InstanceMethodImpure {
                    inst: inst.name.clone(),
                    method: m.name.clone(),
                    effects: undeclared.join(", "),
                }
                .at(m.body.span));
            }
        }
        Ok(())
    }
}
