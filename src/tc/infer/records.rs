use marginalia::Span;

use super::paths::{field_prefix, show_path};
use crate::error::{ErrKind, TypeError};
use crate::syntax::ast::{Core, Expr, NodeId, PathOp, PathStep, S};
use crate::types::ty::Type;

use super::super::{Env, Tc};

impl Tc<'_> {
    pub(super) fn synth_record_create(
        &mut self,
        env: &Env,
        ctor_name: &str,
        field_exprs: &[(String, S<Expr<Core>>)],
        span: Span,
    ) -> Result<Type, TypeError> {
        let info = self.ctors.get(ctor_name).cloned().ok_or_else(|| {
            ErrKind::UnknownRecordCtor {
                ctor: ctor_name.to_string(),
            }
            .at(span)
        })?;
        if info.fields.is_empty() {
            return Err(ErrKind::NotRecordCtor {
                ctor: ctor_name.to_string(),
            }
            .at(span));
        }
        let (result, tsubs, rsubs) = self.open_ctor(&info);
        for (field_name, field_expr) in field_exprs {
            let fi = info
                .fields
                .iter()
                .position(|f| f.as_str() == field_name)
                .ok_or_else(|| {
                    ErrKind::UnknownField {
                        field: field_name.clone(),
                        ctor: ctor_name.to_string(),
                    }
                    .at(span)
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
            return Err(ErrKind::MissingFields {
                fields: missing.join(", "),
                ctor: ctor_name.to_string(),
            }
            .at(span));
        }
        Ok(self.apply(&result))
    }

    pub(super) fn synth_record_update(
        &mut self,
        env: &Env,
        base_expr: &S<Expr<Core>>,
        ctor_name: &str,
        field_exprs: &[(String, S<Expr<Core>>)],
        span: Span,
    ) -> Result<Type, TypeError> {
        let info = self.ctors.get(ctor_name).cloned().ok_or_else(|| {
            ErrKind::UnknownRecordCtor {
                ctor: ctor_name.to_string(),
            }
            .at(span)
        })?;
        let (result_ty, tsubs, rsubs) = self.open_ctor(&info);
        self.check(env, base_expr, &result_ty)?;
        for (field_name, field_expr) in field_exprs {
            let fi = info
                .fields
                .iter()
                .position(|f| f.as_str() == field_name)
                .ok_or_else(|| {
                    ErrKind::UnknownField {
                        field: field_name.clone(),
                        ctor: ctor_name.to_string(),
                    }
                    .at(span)
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

    pub(super) fn update_path(
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
                    return Err(ErrKind::ConflictingUpdatePaths {
                        a: show_path(p),
                        b: show_path(q),
                    }
                    .at(span));
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
                    return Err(ErrKind::OpticPathSurvived.at(span));
                };
                let Type::Con(tname, _) = cur.clone() else {
                    return Err(ErrKind::FieldPathNonRecord {
                        seg: seg.clone(),
                        ty: cur.show(),
                    }
                    .at(span));
                };
                let mut named: Vec<_> = self
                    .ctors
                    .iter()
                    .filter(|(_, c)| c.type_name == tname)
                    .map(|(n, c)| (n.clone(), c.args.len()))
                    .collect();
                let Some((cname, arity)) = named.pop().filter(|_| named.is_empty()) else {
                    return Err(ErrKind::UpdatePathMultiCtor {
                        ty: tname.to_string(),
                        n: named.len() + 1,
                    }
                    .at(span));
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
}
