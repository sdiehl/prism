use marginalia::{BuiltinKind, Trivia};

use super::{Fmt, INDENT};
use crate::syntax::ast::Span;

impl Fmt<'_> {
    pub(super) fn verbatim(&self, start: usize, end: usize) -> String {
        self.source.get(start..end).unwrap_or_default().to_string()
    }

    // Preserve the writer's numeric spelling verbatim: reprint a literal from
    // source when it carries a digit separator or an exponent (`1_000_000`,
    // `1e-25`, `1E3`), otherwise use the canonical rendering. Rewriting `1e3`
    // to `1000.0` would be meaning-preserving but erases the writer's chosen
    // notation, so scientific form is the writer's to keep. Idempotent either
    // way, since a reparsed literal re-slices to the same text.
    pub(super) fn lit_text(&self, span: Span, canonical: impl FnOnce() -> String) -> String {
        let src = self.source.get(span.start..span.end).unwrap_or_default();
        if src.contains('_') || src.contains(['e', 'E']) {
            src.to_string()
        } else {
            canonical()
        }
    }

    // Line comments in `[lo, hi)`, each re-emitted on its own line at the given
    // indent and newline-terminated. A blank line between two comments is kept so
    // deliberately spaced comment groups survive; leading and trailing blanks are
    // dropped. Block comments carry no placeable layout, so they are skipped (the
    // same policy `emit_leading_trivia` uses at top level).
    pub(super) fn lead_comments(&self, lo: usize, hi: usize, indent: usize) -> String {
        if lo >= hi {
            return String::new();
        }
        let ind = INDENT.repeat(indent);
        let mut out = String::new();
        let mut gap = false;
        for ev in self.trivia.between(lo, hi) {
            match &ev.trivia {
                Trivia::Comment {
                    kind: BuiltinKind::Line,
                    text,
                } => {
                    if gap && !out.is_empty() {
                        out.push('\n');
                    }
                    gap = false;
                    out.push_str(&ind);
                    out.push_str(text);
                    out.push('\n');
                }
                Trivia::Comment { .. } => {}
                Trivia::BlankLine => gap = true,
            }
        }
        out
    }

    // Whether any line comment sits in `[lo, hi)`. The inline fast paths check
    // this before collapsing a node onto one line: a node carrying comments must
    // take the laid-out path so `lead_comments` has somewhere to place them.
    pub(super) fn has_comments(&self, lo: usize, hi: usize) -> bool {
        lo < hi
            && self.trivia.between(lo, hi).any(|e| {
                matches!(
                    &e.trivia,
                    Trivia::Comment {
                        kind: BuiltinKind::Line,
                        ..
                    }
                )
            })
    }

    // A line comment that opens on the same source line as `after` (no newline
    // in between), i.e. a trailing comment like `let x = 1 -- note`. Returns its
    // text and the offset just past it, so the caller can both append it inline
    // and skip it when emitting the following statement's leading comments.
    pub(super) fn trailing_comment(&self, after: usize) -> Option<(&str, usize)> {
        let eol = self.source[after..]
            .find('\n')
            .map_or(self.source.len(), |i| after + i);
        self.trivia
            .between(after, eol)
            .find_map(|ev| match &ev.trivia {
                Trivia::Comment {
                    kind: BuiltinKind::Line,
                    text,
                } => Some((text.as_str(), ev.span.end)),
                _ => None,
            })
    }

    pub(super) fn emit_leading_trivia(&self, lo: usize, hi: usize, out: &mut String) {
        for ev in self.trivia.between(lo, hi) {
            match &ev.trivia {
                Trivia::Comment {
                    kind: BuiltinKind::Line,
                    text,
                } => {
                    out.push_str(text);
                    out.push('\n');
                }
                Trivia::Comment { .. } => {}
                Trivia::BlankLine => {
                    if !out.is_empty() {
                        out.push('\n');
                    }
                }
            }
        }
    }
}
