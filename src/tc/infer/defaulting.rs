use std::collections::BTreeSet;

use crate::types::ty::{EffRow, Type};

#[derive(Clone, Copy)]
pub(super) enum NumClass {
    Eq,
    Ord,
    Arith,
}

// Default row existentials that no caller can solve. Keep the function's own
// latent row and rows reachable from parameters; default the rest to empty.
pub(super) fn default_open_rows(ty: &Type) -> Type {
    let mut keep = BTreeSet::new();
    let mut inner = ty;
    while let Type::Forall(_, b) | Type::RowForall(_, b) = inner {
        inner = b;
    }
    if let Type::Fun(doms, eff, _) = inner {
        for param in doms {
            param.free_exist_row(&mut keep);
        }
        eff.free_exist_row(&mut keep);
    }
    let mut all_rows = BTreeSet::new();
    ty.free_exist_row(&mut all_rows);
    let mut out = ty.clone();
    for row in all_rows.difference(&keep) {
        out = out.subst_row_exist(*row, &EffRow::Empty);
    }
    out
}
