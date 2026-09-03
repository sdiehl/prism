//! First-order type/effect-row unification used by dictionary planning.

use super::planning::{AlphaVariable, PlanParameter, QuantifierKind};
use super::{
    BTreeMap, BTreeSet, CoreInstantiation, CoreQuantifier, CoreType, EffRow, Label, Sym, Type,
};

#[derive(Default)]
pub(super) struct Unifier {
    type_variables: BTreeMap<Sym, AlphaVariable>,
    row_variables: BTreeMap<Sym, AlphaVariable>,
    types: BTreeMap<Sym, Type>,
    rows: BTreeMap<Sym, EffRow>,
}

impl Unifier {
    pub(super) fn insert(&mut self, variable: AlphaVariable) {
        match variable.kind {
            QuantifierKind::Type => {
                self.type_variables.insert(variable.internal, variable);
            }
            QuantifierKind::Row => {
                self.row_variables.insert(variable.internal, variable);
            }
        }
    }

    fn preferred(&self, left: Sym, right: Sym, kind: QuantifierKind) -> (Sym, Sym) {
        let variables = match kind {
            QuantifierKind::Type => &self.type_variables,
            QuantifierKind::Row => &self.row_variables,
        };
        let rank = |name: Sym| match variables[&name].origin {
            PlanParameter::Builder {
                dictionary,
                quantifier,
            } => (0, dictionary, quantifier),
            PlanParameter::Source(index) => (1, index, 0),
        };
        if rank(left) <= rank(right) {
            (left, right)
        } else {
            (right, left)
        }
    }

    pub(super) fn is_root(&mut self, variable: AlphaVariable) -> bool {
        match variable.kind {
            QuantifierKind::Type => {
                self.resolve_type(&Type::Var(variable.internal)) == Type::Var(variable.internal)
            }
            QuantifierKind::Row => {
                self.resolve_row(&EffRow::Var(variable.internal)) == EffRow::Var(variable.internal)
            }
        }
    }

    pub(super) fn finish_argument(
        &mut self,
        argument: &CoreInstantiation,
        roots: &[CoreQuantifier],
        replacements: &[CoreInstantiation],
    ) -> CoreInstantiation {
        match argument {
            CoreInstantiation::Type(ty) => {
                CoreInstantiation::Type(crate::core::typed::verify::substitute_type(
                    &self.resolve_type(ty),
                    roots,
                    replacements,
                ))
            }
            CoreInstantiation::Row(row) => {
                CoreInstantiation::Row(crate::core::typed::verify::substitute_row(
                    &self.resolve_row(row),
                    roots,
                    replacements,
                ))
            }
        }
    }

    pub(super) fn unify_core(&mut self, left: &CoreType, right: &CoreType) -> bool {
        match (left, right) {
            (CoreType::Source(left), CoreType::Source(right)) => self.unify_type(left, right),
            _ => left == right,
        }
    }

    #[allow(clippy::too_many_lines)]
    fn unify_type(&mut self, left: &Type, right: &Type) -> bool {
        let left = self.resolve_type(left);
        let right = self.resolve_type(right);
        if left == right {
            return true;
        }
        if let Type::Var(name) = left {
            if self.type_variables.contains_key(&name) {
                return self.bind_type(name, right);
            }
            return false;
        }
        if let Type::Var(name) = right {
            if self.type_variables.contains_key(&name) {
                return self.bind_type(name, left);
            }
            return false;
        }
        match (left, right) {
            (Type::Fun(lp, le, lr), Type::Fun(rp, re, rr)) => {
                lp.len() == rp.len()
                    && lp.iter().zip(&rp).all(|(l, r)| self.unify_type(l, r))
                    && self.unify_row(&le, &re)
                    && self.unify_type(&lr, &rr)
            }
            (Type::Con(ln, la), Type::Con(rn, ra)) => {
                ln == rn
                    && la.len() == ra.len()
                    && la.iter().zip(&ra).all(|(l, r)| self.unify_type(l, r))
            }
            (Type::App(lh, la), Type::App(rh, ra)) => {
                self.unify_type(&lh, &rh) && self.unify_type(&la, &ra)
            }
            (Type::Tuple(left), Type::Tuple(right))
            | (Type::UnboxedTuple(left), Type::UnboxedTuple(right)) => {
                left.len() == right.len()
                    && left
                        .iter()
                        .zip(&right)
                        .all(|(left, right)| self.unify_type(left, right))
            }
            (Type::UnboxedRecord(left), Type::UnboxedRecord(right)) => {
                left.len() == right.len()
                    && left
                        .iter()
                        .zip(&right)
                        .all(|((ln, lt), (rn, rt))| ln == rn && self.unify_type(lt, rt))
            }
            (Type::OrNull(left), Type::OrNull(right)) => self.unify_type(&left, &right),
            (Type::Row(left), Type::Row(right)) => self.unify_row(&left, &right),
            (Type::Coeffect(left, lc), Type::Coeffect(right, rc)) => {
                lc == rc && self.unify_type(&left, &right)
            }
            (left, right) => left == right,
        }
    }

    fn bind_type(&mut self, name: Sym, value: Type) -> bool {
        if let Type::Var(other) = value {
            if self.type_variables.contains_key(&other) {
                let (keep, bind) = self.preferred(name, other, QuantifierKind::Type);
                self.types.insert(bind, Type::Var(keep));
                return true;
            }
            self.types.insert(name, Type::Var(other));
            return true;
        }
        if occurs_type(name, &value) {
            return false;
        }
        self.types.insert(name, value);
        true
    }

    fn unify_row(&mut self, left: &EffRow, right: &EffRow) -> bool {
        let left = self.resolve_row(left);
        let right = self.resolve_row(right);
        if left == right {
            return true;
        }
        if let EffRow::Var(name) = left {
            if self.row_variables.contains_key(&name) {
                return self.bind_row(name, right);
            }
            return false;
        }
        if let EffRow::Var(name) = right {
            if self.row_variables.contains_key(&name) {
                return self.bind_row(name, left);
            }
            return false;
        }
        match (left, right) {
            (EffRow::Extend(ll, lr), EffRow::Extend(rl, rr)) => {
                ll.name == rl.name
                    && ll.args.len() == rl.args.len()
                    && ll
                        .args
                        .iter()
                        .zip(&rl.args)
                        .all(|(left, right)| self.unify_type(left, right))
                    && self.unify_row(&lr, &rr)
            }
            (left, right) => left == right,
        }
    }

    fn bind_row(&mut self, name: Sym, value: EffRow) -> bool {
        if let EffRow::Var(other) = value {
            if self.row_variables.contains_key(&other) {
                let (keep, bind) = self.preferred(name, other, QuantifierKind::Row);
                self.rows.insert(bind, EffRow::Var(keep));
                return true;
            }
            self.rows.insert(name, EffRow::Var(other));
            return true;
        }
        if occurs_row(name, &value) {
            return false;
        }
        self.rows.insert(name, value);
        true
    }

    fn resolve_type(&mut self, ty: &Type) -> Type {
        match ty {
            Type::Var(name) => {
                if let Some(value) = self.types.get(name).cloned() {
                    let value = self.resolve_type(&value);
                    self.types.insert(*name, value.clone());
                    value
                } else {
                    ty.clone()
                }
            }
            Type::Forall(name, body) => Type::Forall(*name, Box::new(self.resolve_type(body))),
            Type::RowForall(name, body) => {
                Type::RowForall(*name, Box::new(self.resolve_type(body)))
            }
            Type::Fun(params, effects, result) => Type::Fun(
                params.iter().map(|ty| self.resolve_type(ty)).collect(),
                self.resolve_row(effects),
                Box::new(self.resolve_type(result)),
            ),
            Type::Con(name, args) => {
                Type::Con(*name, args.iter().map(|ty| self.resolve_type(ty)).collect())
            }
            Type::App(head, argument) => Type::App(
                Box::new(self.resolve_type(head)),
                Box::new(self.resolve_type(argument)),
            ),
            Type::Tuple(fields) => {
                Type::Tuple(fields.iter().map(|ty| self.resolve_type(ty)).collect())
            }
            Type::UnboxedTuple(fields) => {
                Type::UnboxedTuple(fields.iter().map(|ty| self.resolve_type(ty)).collect())
            }
            Type::UnboxedRecord(fields) => Type::UnboxedRecord(
                fields
                    .iter()
                    .map(|(name, ty)| (*name, self.resolve_type(ty)))
                    .collect(),
            ),
            Type::OrNull(inner) => Type::OrNull(Box::new(self.resolve_type(inner))),
            Type::Row(row) => Type::Row(self.resolve_row(row)),
            Type::Coeffect(inner, row) => {
                Type::Coeffect(Box::new(self.resolve_type(inner)), row.clone())
            }
            other => other.clone(),
        }
    }

    fn resolve_row(&mut self, row: &EffRow) -> EffRow {
        match row {
            EffRow::Var(name) => {
                if let Some(value) = self.rows.get(name).cloned() {
                    let value = self.resolve_row(&value);
                    self.rows.insert(*name, value.clone());
                    value
                } else {
                    row.clone()
                }
            }
            EffRow::Extend(label, rest) => EffRow::Extend(
                Label {
                    name: label.name,
                    args: label.args.iter().map(|ty| self.resolve_type(ty)).collect(),
                },
                Box::new(self.resolve_row(rest)),
            ),
            other => other.clone(),
        }
    }
}

fn occurs_type(name: Sym, ty: &Type) -> bool {
    let mut variables = BTreeSet::new();
    ty.free_ty_vars(&mut variables);
    variables.contains(&name)
}

fn occurs_row(name: Sym, row: &EffRow) -> bool {
    let mut variables = BTreeSet::new();
    eff_row_vars(row, &mut variables);
    variables.contains(&name)
}

pub(super) fn eff_row_vars(row: &EffRow, acc: &mut BTreeSet<Sym>) {
    if let EffRow::Var(tail) = row.tail() {
        acc.insert(*tail);
    }
    for label in row.labels() {
        for argument in &label.args {
            argument.free_row_vars(acc);
        }
    }
}
