use marginalia::Span;
use thiserror::Error;

use super::code::{PARSE_EOF, PARSE_SYNTAX};

/// The payload of a parse failure: the primary span (a caret, `lo == hi`, for
/// an end-of-input fault), the rendered message, and the canonical expectation
/// set.
///
/// `expected` is token wire names (the spelling the `syntax-tokens`
/// artifact uses), deduplicated and sorted so the set is independent of
/// grammar table order; deliberate diagnostics (the migration rewrites) carry
/// an empty set, since their message names the exact rewrite rather than a
/// token menu.
#[derive(Debug)]
pub struct SyntaxFault {
    pub span: Span,
    pub msg: String,
    pub expected: Vec<String>,
}

/// Parse failure with a stable, append-only diagnostic code. The payload is
/// boxed so `Result`s carrying this error stay word-sized on the happy path.
#[derive(Debug, Error)]
pub enum ParseError {
    #[error("{}", .0.msg)]
    Syntax(Box<SyntaxFault>),
    /// The token stream itself was exhausted while the parser wanted more: a
    /// caret at the end, distinct from an unexpected token so an interactive
    /// caller can classify incompleteness without string matching. Only the
    /// expression entry reaches this: the layout pass closes every open block
    /// before the stream ends, so a program-level early end surfaces as
    /// `Syntax` at the zero-width virtual closer instead. The same rule holds
    /// in the stdlib's parse cursor, whose end-of-input code fires exactly
    /// when its position is past the last token it was given.
    #[error("{}", .0.msg)]
    UnexpectedEof(Box<SyntaxFault>),
}

impl ParseError {
    /// A general parse fault (`E7100`).
    #[must_use]
    pub fn syntax(span: Span, msg: String, expected: Vec<String>) -> Self {
        Self::Syntax(Box::new(SyntaxFault {
            span,
            msg,
            expected,
        }))
    }

    /// An exhausted-stream fault (`E7101`).
    #[must_use]
    pub fn eof(span: Span, msg: String, expected: Vec<String>) -> Self {
        Self::UnexpectedEof(Box::new(SyntaxFault {
            span,
            msg,
            expected,
        }))
    }

    #[must_use]
    pub const fn code(&self) -> &'static str {
        match self {
            Self::Syntax(_) => PARSE_SYNTAX,
            Self::UnexpectedEof(_) => PARSE_EOF,
        }
    }

    /// The primary span, a caret (`lo == hi`) for an end-of-input fault.
    #[must_use]
    pub fn span(&self) -> Span {
        self.fault().span
    }

    /// The canonical expectation set, empty when the diagnostic is deliberate.
    #[must_use]
    pub fn expected(&self) -> &[String] {
        &self.fault().expected
    }

    /// The shared payload behind either variant.
    #[must_use]
    pub fn fault(&self) -> &SyntaxFault {
        match self {
            Self::Syntax(f) | Self::UnexpectedEof(f) => f,
        }
    }
}
