//! The occurrence export: every resolved reference, as a versioned document.
//!
//! `prism dump occurrences` exports the renamer's `resolve::Occurrence` facts.
//! Read forward they support goto-definition; grouped by target they support
//! find-references.
//!
//! A reference appears only where the AST records a span for the name itself:
//! today an expression variable, and an effect-row label. Every other resolution
//! site carries the enclosing construct's span, which is too broad for a link.
//! Local bindings appear too, binder and uses alike, each keyed by the offset
//! of the binder it names.
//!
//! Beside the references sits a definition table: each top-level definition and
//! each constructor, effect operation, and class method, with the module and
//! range where its name is written, so a reference's target is located without
//! parsing the file that defines it.

use prism_common::format::FormatTag;
use prism_common::record::RecordError;
use serde::{Deserialize, Serialize};

use crate::error::Error;
use crate::parse::parse;
use crate::resolve::{resolve_modules_seeing, Root, Seen};

/// Schema tag for the occurrence document.
pub const OCCURRENCES_FORMAT: FormatTag = FormatTag::new("prism-occurrences-v2");

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
    /// For a local binding, the offset of its binder, in the same coordinates
    /// as `start`. Every use and the binding site itself carry it, so grouping
    /// by `(module, local)` is find-references and the row whose `start` equals
    /// it is the definition. `target` is then the name as written, which no
    /// top-level definition is matched against.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub local: Option<usize>,
}

/// Where a name is defined, flattened for the wire.
#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Def {
    /// The dotted module whose source the range indexes into, as for [`Ref`].
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub module: String,
    pub start: usize,
    pub end: usize,
    /// The canonical name, equal to the `target` of every reference to it.
    pub name: String,
}

/// The versioned, source-ordered occurrence document.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Occurrences {
    pub format: FormatTag,
    pub refs: Vec<Ref>,
    /// Every definition the program can reach, in source order per module.
    #[serde(default)]
    pub defs: Vec<Def>,
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
    pub fn from_json(text: &str) -> Result<Self, RecordError> {
        let doc: Self = RecordError::decode(text)?;
        RecordError::expect_format("occurrences", &OCCURRENCES_FORMAT, &doc.format)?;
        if let Some(r) = doc.refs.iter().find(|r| r.start >= r.end) {
            return Err(RecordError::Invalid(format!(
                "empty occurrence range {}..{} for `{}`",
                r.start, r.end, r.target
            )));
        }
        if let Some(d) = doc.defs.iter().find(|d| d.start >= d.end) {
            return Err(RecordError::Invalid(format!(
                "empty definition range {}..{} for `{}`",
                d.start, d.end, d.name
            )));
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
    let (_, seen) = resolve_modules_seeing(program, src, roots)?;
    Ok(from_seen(seen))
}

/// The occurrence document of what one resolution saw, in canonical order.
pub(crate) fn from_seen(seen: Seen) -> Occurrences {
    let mut refs: Vec<Ref> = seen
        .refs
        .into_iter()
        .map(|o| Ref {
            module: o.module,
            owner: o.owner,
            owner_start: o.owner_span.start,
            start: o.span.start,
            end: o.span.end,
            target: o.target,
            local: o.binder,
        })
        .collect();
    // Canonical order: by where the reference is, so the document reads in source
    // order per module and two runs over the same source are byte-identical.
    refs.sort();
    refs.dedup();
    let mut defs: Vec<Def> = seen
        .defs
        .into_iter()
        .map(|d| Def {
            module: d.module,
            start: d.span.start,
            end: d.span.end,
            name: d.name,
        })
        .collect();
    defs.sort();
    defs.dedup();
    Occurrences {
        format: OCCURRENCES_FORMAT,
        refs,
        defs,
    }
}
