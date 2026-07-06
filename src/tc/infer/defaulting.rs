use std::collections::BTreeSet;

use crate::types::ty::{EffRow, Type};

#[derive(Clone, Copy)]
pub(super) enum NumClass {
    Eq,
    Ord,
    Arith,
}

pub(super) fn default_open_rows(ty: &Type) -> Type {
    let Type::Fun(doms, eff, _) = ty else {
        return ty.clone();
    };
    let mut keep = BTreeSet::new();
    for param in doms {
        param.free_exist_row(&mut keep);
    }
    eff.free_exist_row(&mut keep);
    let mut all_rows = BTreeSet::new();
    ty.free_exist_row(&mut all_rows);
    let mut out = ty.clone();
    for row in all_rows.difference(&keep) {
        out = out.subst_row_exist(*row, &EffRow::Empty);
    }
    out
}
