//! The compiler-side Core seam.
//!
//! The IR, typed passes, hashing, and registries live in the `prism-core`
//! crate; the two checker-coupled bridges (AST elaboration into Core and the
//! capture analysis it leans on) stay here with the front end that produces
//! their inputs.

pub use prism_core::core::*;

pub mod captures;
pub mod elaborate;

pub use elaborate::{builtin_arities, elaborate, elaborate_expr, elaborate_expr_defs, konst_fns};
pub use elaborate::{elaborate_typed, typed_verification_error};
