use marginalia::Span;
use thiserror::Error;

use super::code::{PARSE_EOF, PARSE_SYNTAX};

/// Parse failure with a stable, append-only diagnostic code.
#[derive(Debug, Error)]
pub enum ParseError {
    #[error("{msg}")]
    Syntax { span: Span, msg: String },
    #[error("unexpected end of input")]
    UnexpectedEof,
}

impl ParseError {
    #[must_use]
    pub const fn code(&self) -> &'static str {
        match self {
            Self::Syntax { .. } => PARSE_SYNTAX,
            Self::UnexpectedEof => PARSE_EOF,
        }
    }
}
