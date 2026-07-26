//! The compiler-side surface-syntax seam: the AST, parser entry points, and
//! grammar live in the `prism-syntax` crate; desugaring is semantic and stays
//! here with the rest of the front end.

pub use prism_syntax::ast;
pub use prism_syntax::{ExprParser, ProgramParser, TypeSigParser};

pub mod desugar;
