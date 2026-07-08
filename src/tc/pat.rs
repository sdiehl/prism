use marginalia::Span;

use super::{Env, Tc};
use crate::error::TypeError;
use crate::sym::Sym;
use crate::syntax::ast::{self, Pattern, S};
use crate::types::ty::{EffRow, Kind, Type};

// A constructor opened at a use site: its applied head `Con(T, ..)`, the
// type-variable substitutions, and the row-variable substitutions to apply to
// its field types.
type OpenedCtor = (Type, Vec<(Sym, Type)>, Vec<(Sym, EffRow)>);

impl Tc<'_> {
    // Open a constructor's parameters with a fresh existential of the right sort
    // per parameter (a row existential for a `Row`-kinded one), returning the
    // applied head `Con(T, ..)` and the substitutions to apply to field types.
    pub(super) fn open_ctor(&mut self, info: &super::CtorInfo) -> OpenedCtor {
        let mut head = Vec::with_capacity(info.params.len());
        let mut tsubs = Vec::new();
        let mut rsubs = Vec::new();
        for (pn, k) in info.params.iter().zip(&info.param_kinds) {
            if *k == Kind::Row {
                let r = EffRow::Exist(self.push_ex_row());
                head.push(Type::Row(r.clone()));
                rsubs.push((*pn, r));
            } else {
                let t = Type::Exist(self.push_ex());
                head.push(t.clone());
                tsubs.push((*pn, t));
            }
        }
        (Type::Con(info.type_name, head), tsubs, rsubs)
    }

    pub(super) fn check_pat(
        &mut self,
        env: &Env,
        p: &S<Pattern>,
        ty: &Type,
    ) -> Result<Env, TypeError> {
        let span = p.span;
        match &p.node {
            Pattern::Wild => Ok(env.clone()),
            Pattern::Var(x) => {
                let mut e2 = env.clone();
                e2.insert(Sym::from(x), ty.clone());
                Ok(e2)
            }
            Pattern::Int(lit) => {
                if lit.suffix != ast::Suffix::None {
                    return Err(TypeError::Other {
                        span,
                        msg: "suffixed literal patterns are not supported; match on Int".into(),
                    });
                }
                self.equate(ty, &Type::Int).map_err(|e| e.at(span))?;
                Ok(env.clone())
            }
            Pattern::Float(_) => {
                self.equate(ty, &Type::Float).map_err(|e| e.at(span))?;
                Ok(env.clone())
            }
            Pattern::Char(_) => {
                self.equate(ty, &Type::Char).map_err(|e| e.at(span))?;
                Ok(env.clone())
            }
            Pattern::Bool(_) => {
                self.equate(ty, &Type::Bool).map_err(|e| e.at(span))?;
                Ok(env.clone())
            }
            Pattern::Tuple(pats) => {
                let exs: Vec<u32> = pats.iter().map(|_| self.push_ex()).collect();
                let tup_ty = Type::Tuple(exs.iter().map(|e| Type::Exist(*e)).collect());
                self.equate(ty, &tup_ty).map_err(|e| e.at(span))?;
                let mut env2 = env.clone();
                for (pat, ex) in pats.iter().zip(&exs) {
                    let t = self.apply(&Type::Exist(*ex));
                    env2 = self.check_pat(&env2, pat, &t)?;
                }
                Ok(env2)
            }
            Pattern::Record(ctor_name, field_pats, _spread) => {
                let info = self
                    .ctors
                    .get(ctor_name)
                    .cloned()
                    .ok_or_else(|| TypeError::Other {
                        span,
                        msg: format!("unknown record constructor {ctor_name}"),
                    })?;
                let (result, tsubs, rsubs) = self.open_ctor(&info);
                self.equate(ty, &result).map_err(|e| e.at(span))?;
                let mut env2 = env.clone();
                for (fname, fpat) in field_pats {
                    let fi = info
                        .fields
                        .iter()
                        .position(|f| f.as_str() == fname)
                        .ok_or_else(|| TypeError::Other {
                            span,
                            msg: format!("unknown field {fname} on {ctor_name}"),
                        })?;
                    let mut ft = info.args[fi].clone();
                    for (pn, t) in &tsubs {
                        ft = ft.subst_var(*pn, t);
                    }
                    for (pn, r) in &rsubs {
                        ft = ft.subst_row_var(*pn, r);
                    }
                    let ft = self.apply(&ft);
                    env2 = self.check_pat(&env2, fpat, &ft)?;
                }
                Ok(env2)
            }
            Pattern::Ctor(name, subs) => {
                let info = self
                    .ctors
                    .get(name)
                    .cloned()
                    .ok_or_else(|| TypeError::Other {
                        span,
                        msg: format!("unknown constructor {name}"),
                    })?;
                let (result, tsubs, rsubs) = self.open_ctor(&info);
                self.equate(ty, &result).map_err(|e| e.at(span))?;
                if subs.len() != info.args.len() {
                    return Err(TypeError::Other {
                        span,
                        msg: format!(
                            "constructor {name} expects {} arguments, got {}",
                            info.args.len(),
                            subs.len()
                        ),
                    });
                }
                let mut env2 = env.clone();
                for (sub, arg) in subs.iter().zip(&info.args) {
                    let mut at = arg.clone();
                    for (pn, t) in &tsubs {
                        at = at.subst_var(*pn, t);
                    }
                    for (pn, r) in &rsubs {
                        at = at.subst_row_var(*pn, r);
                    }
                    let at = self.apply(&at);
                    env2 = self.check_pat(&env2, sub, &at)?;
                }
                Ok(env2)
            }
        }
    }

    pub(super) fn find_field(
        &self,
        span: Span,
        ctor_name: &str,
        field: &str,
        ty: &Type,
    ) -> Result<(Type, usize), TypeError> {
        let (info, fi) = self
            .ctors
            .values()
            .filter(|c| c.type_name.as_str() == ctor_name)
            .find_map(|c| Some((c, c.fields.iter().position(|f| f.as_str() == field)?)))
            .ok_or_else(|| TypeError::Other {
                span,
                msg: format!("no field `{field}` on type `{ctor_name}`"),
            })?;
        let params = match ty {
            Type::Con(_, ps) => ps.clone(),
            _ => vec![],
        };
        let mut ft = info.args[fi].clone();
        for ((pn, k), t) in info.params.iter().zip(&info.param_kinds).zip(params.iter()) {
            match (k, t) {
                // A `Row`-kinded argument carries an effect row; substitute the
                // row variable, not a type variable.
                (Kind::Row, Type::Row(r)) => ft = ft.subst_row_var(*pn, r),
                _ => ft = ft.subst_var(*pn, t),
            }
        }
        Ok((self.apply(&ft), fi))
    }
}
