//! Allocation facts shared by certificate checking and optimizer summaries.
//!
//! Arithmetic on arbitrary-precision integers can leave the immediate range;
//! floating-point results are boxed. Comparisons return tagged booleans.

use super::{CoreOp, IoOp};
use crate::types::{scalar_plan, ScalarPlan, Type};

pub(crate) const fn primitive_is_free(op: CoreOp) -> bool {
    matches!(
        op,
        CoreOp::Eq
            | CoreOp::Ne
            | CoreOp::Lt
            | CoreOp::Le
            | CoreOp::Gt
            | CoreOp::Ge
            | CoreOp::Eqf
            | CoreOp::Nef
            | CoreOp::Ltf
            | CoreOp::Lef
            | CoreOp::Gtf
            | CoreOp::Gef
    )
}

// The generic integer printer materializes a string for bignums.
pub(crate) const fn io_is_free(op: IoOp) -> bool {
    matches!(
        op,
        IoOp::PrintF | IoOp::PrintS | IoOp::PrintNl | IoOp::Srand
    )
}

pub(crate) fn literal_allocates(ty: Option<Type>) -> bool {
    ty.is_some_and(|ty| scalar_plan(&ty).map_or(true, ScalarPlan::owns_fresh_cell))
}
