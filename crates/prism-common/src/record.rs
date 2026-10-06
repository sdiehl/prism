//! The refusal every durable JSON record reader returns.
//!
//! A record is refused for one of three reasons, and callers tell them apart by
//! variant rather than by message: the text is not the record's JSON, the record
//! is another format or another version of its own, or it parsed but breaks an
//! invariant its writer guarantees.

use serde::de::DeserializeOwned;

use crate::format::{FormatError, FormatTag};

/// Why a durable record was refused.
#[derive(Debug, thiserror::Error)]
pub enum RecordError {
    /// The text is not the record's JSON shape.
    #[error("{0}")]
    Json(#[from] serde_json::Error),
    /// The record names another format, or another version of its own.
    #[error("{record}: {source}")]
    Format {
        /// The record kind, as a reader names it.
        record: &'static str,
        /// Which way the tag differs.
        #[source]
        source: FormatError,
    },
    /// The record parsed but breaks an invariant its writer guarantees.
    #[error("{0}")]
    Invalid(String),
}

impl RecordError {
    /// Decode `text` as the JSON of `T`.
    ///
    /// # Errors
    /// [`RecordError::Json`] when `text` is not `T`'s JSON.
    pub fn decode<T: DeserializeOwned>(text: &str) -> Result<T, Self> {
        Ok(serde_json::from_str(text)?)
    }

    /// Require the `found` tag of a `record` to be `expected`.
    ///
    /// # Errors
    /// [`RecordError::Format`] when the tags differ.
    pub fn expect_format(
        record: &'static str,
        expected: &FormatTag,
        found: &FormatTag,
    ) -> Result<(), Self> {
        expected
            .expect(found.as_str())
            .map_err(|source| Self::Format { record, source })
    }

    /// A broken invariant, explained.
    pub fn invalid(detail: impl Into<String>) -> Self {
        Self::Invalid(detail.into())
    }
}
