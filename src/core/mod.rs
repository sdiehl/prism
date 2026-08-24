//! The compiler-side Core seam.
//!
//! The IR, typed passes, hashing, and registries live in the `prism-core`
//! crate; the two checker-coupled bridges (AST elaboration into Core and the
//! capture analysis it leans on) stay here with the front end that produces
//! their inputs.

pub use prism_core::core::*;

pub mod captures;
pub mod elaborate;

#[cfg(feature = "native")]
pub(crate) use elaborate::elaborate_expr_defs;
pub use elaborate::{builtin_arities, elaborate, konst_fns};
pub use elaborate::{elaborate_typed, typed_verification_error};
