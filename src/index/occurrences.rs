//! The occurrence export: every resolved reference, as a versioned document.
//!
//! `prism dump occurrences` exports the renamer's `resolve::Occurrence` facts.
//! Read forward they support goto-definition; grouped by target they support
//! find-references.
//!
//! A reference appears only where the AST records a span for the name itself:
//! today an expression variable, and an effect-row label. Every other resolution
//! site carries the enclosing construct's span, which is too broad for a link.

use serde::{Deserialize, Serialize};

use crate::error::Error;
use crate::parse::parse;
use crate::resolve::{resolve_modules_seeing, Root};

/// Schema tag for the occurrence document.
pub const OCCURRENCES_FORMAT: &str = "prism-occurrences-v1";

/// One resolved reference, flattened for the wire.
#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Ref {
    /// The dotted module whose source the range indexes into (empty for the
    /// root module, whose coordinates are the compiled source's, prelude
    /// included).
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub module: String,
    /// The canonical name of the declaration the reference sits inside.
    pub owner: String,
    /// Where that declaration starts, in the same coordinates as `start`.
    /// `start - owner_start` places the reference inside the declaration's own
    /// text without knowing which coordinates these are.
    pub owner_start: usize,
    pub start: usize,
    pub end: usize,
    /// The canonical name the reference resolves to. A builtin, an effect
    /// operation, or a prelude name no later phase renames stays bare.
    pub target: String,
}

/// The versioned, source-ordered occurrence document.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Occurrences {
    pub format: String,
    pub refs: Vec<Ref>,
}

impl Occurrences {
    /// Serialize with stable indentation and field order.
    ///
    /// # Errors
    /// Fails only if the derived JSON serializer rejects the document.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Decode and validate an occurrence document.
    ///
    /// # Errors
    /// Refuses an unknown format tag or an empty range (a reference with no
    /// extent is one a consumer cannot render).
    pub fn from_json(text: &str) -> Result<Self, String> {
        let doc: Self = serde_json::from_str(text).map_err(|e| e.to_string())?;
        if doc.format != OCCURRENCES_FORMAT {
            return Err(format!(
                "unsupported occurrences format `{}` (expected `{OCCURRENCES_FORMAT}`)",
                doc.format
            ));
        }
        if let Some(r) = doc.refs.iter().find(|r| r.start >= r.end) {
            return Err(format!(
                "empty occurrence range {}..{} for `{}`",
                r.start, r.end, r.target
            ));
        }
        Ok(doc)
    }
}

/// Collect every resolved reference in `src`.
///
/// # Errors
/// Fails on a parse error or any name-resolution failure.
pub fn extract(src: &str, roots: &[Root]) -> Result<Occurrences, Error> {
    let program = parse(src)?.program;
    let (_, seen) = resolve_modules_seeing(program, roots)?;
    let mut refs: Vec<Ref> = seen
        .into_iter()
        .map(|o| Ref {
            module: o.module,
            owner: o.owner,
            owner_start: o.owner_span.start,
            start: o.span.start,
            end: o.span.end,
            target: o.target,
        })
        .collect();
    // Canonical order: by where the reference is, so the document reads in source
    // order per module and two runs over the same source are byte-identical.
    refs.sort();
    refs.dedup();
    Ok(Occurrences {
        format: OCCURRENCES_FORMAT.to_string(),
        refs,
    })
}
