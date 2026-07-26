use thiserror::Error;

use super::code::{
    LEX_EMPTY_HOLE, LEX_INVALID, LEX_NUMBER_SEPARATOR, LEX_UNTERMINATED_HOLE,
    LEX_UNTERMINATED_STRING,
};

/// Lexical failure with a stable, append-only diagnostic code.
#[derive(Debug, Error)]
pub enum LexError {
    #[error("unexpected token")]
    Invalid { offset: usize },
    #[error("empty interpolation hole `{{}}`")]
    EmptyHole { offset: usize },
    #[error("unterminated interpolation hole")]
    UnterminatedHole { offset: usize },
    #[error("unterminated string literal")]
    UnterminatedString { offset: usize },
    #[error("malformed numeric literal: `_` separators must sit between two digits")]
    NumberSeparator { offset: usize },
}

impl LexError {
    #[must_use]
    pub const fn offset(&self) -> usize {
        match self {
            Self::Invalid { offset }
            | Self::EmptyHole { offset }
            | Self::UnterminatedHole { offset }
            | Self::UnterminatedString { offset }
            | Self::NumberSeparator { offset } => *offset,
        }
    }

    #[must_use]
    pub const fn code(&self) -> &'static str {
        match self {
            Self::Invalid { .. } => LEX_INVALID,
            Self::EmptyHole { .. } => LEX_EMPTY_HOLE,
            Self::UnterminatedHole { .. } => LEX_UNTERMINATED_HOLE,
            Self::UnterminatedString { .. } => LEX_UNTERMINATED_STRING,
            Self::NumberSeparator { .. } => LEX_NUMBER_SEPARATOR,
        }
    }
}
