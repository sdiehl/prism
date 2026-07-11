use std::collections::BTreeSet;

use crate::error::{ErrKind, TypeError};
use crate::sym::Sym;
use crate::syntax::ast::{Core, Decl};
use crate::types::ty::Type;

pub(super) fn forall_ty_binders(ty: &Type, out: &mut BTreeSet<Sym>) {
    match ty {
        Type::Forall(name, body) => {
            out.insert(*name);
            forall_ty_binders(body, out);
        }
        Type::RowForall(_, body) => forall_ty_binders(body, out),
        _ => {}
    }
}

pub(super) fn poly_recursion_hint(error: TypeError, decl: &Decl<Core>) -> TypeError {
    if super::super::env::fully_annotated(decl) {
        return error;
    }
    match error {
        TypeError::TypeMismatch {
            span,
            expected,
            found,
        } => ErrKind::PolyRecursionMismatch {
            name: decl.name.clone(),
            expected,
            found,
        }
        .at(span),
        other => other,
    }
}
