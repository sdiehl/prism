mod code;
mod diag;
mod lex;
mod parse;
mod phase;
mod render;
mod source;
pub mod suggest;

pub use code::{
    ErrorCode, ErrorPhase, INCOMPLETE_HANDLER, SMT_LOGIC_WELLFORMED, TYPED_CORE_CONSTRUCTION,
    TYPED_CORE_EFFECT_LOWERING, TYPED_CORE_ENVIRONMENT, TYPED_CORE_ERASURE, TYPED_CORE_SIMPLIFY,
    TYPED_CORE_SPECIALIZATION, TYPED_CORE_VERIFICATION, TYPED_HOLE,
};
pub use diag::{Diag, ErrKind, Frame, HoleBinding, HoleCandidate, HoleReport, TypeError};
pub use lex::LexError;
pub use parse::ParseError;
pub use phase::{
    Error, TypedCoreConstructionFailure, TypedCoreEffectLoweringFailure,
    TypedCoreEnvironmentFailure, TypedCoreErasureFailure, TypedCoreSimplifyFailure,
    TypedCoreSpecializationFailure, TypedCoreVerificationFailure, TypedCoreViolation,
};
pub use render::render_warning;
#[cfg(feature = "wasm")]
pub(crate) use source::line_col;
pub use source::SourceMap;

/// Canonical interpreter fault for reaching a deferred typed hole.
#[must_use]
pub fn typed_hole_fault(name: &str, span: marginalia::Span) -> String {
    format!("typed hole ?{name} at {}..{}", span.start, span.end)
}
