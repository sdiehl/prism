//! Doc-comment extraction: associate `-- |` trivia blocks with declarations.
//!
//! Prism has no docstring syntax; comments are `--` line trivia the parser drops
//! (via `marginalia`), kept in a span-indexed table beside the AST. A `-- |`
//! marker promotes the contiguous comment block immediately
//! above a declaration to that declaration's docstring, and a `-- |` block at the
//! top of a file to the module description. Ordinary `--` comments are ignored.
//! Blocks are located by byte span, the same way the formatter re-associates
//! leading trivia (`src/fmt/mod.rs::lead_comments`).

use std::collections::BTreeMap;

use marginalia::{Trivia, TriviaTable};

/// Doc text recovered from a module's trivia, keyed by the byte offset of the
/// declaration each block documents. `module` is the top-of-file description.
pub(crate) struct Docs {
    pub(crate) module: Option<String>,
    by_offset: BTreeMap<usize, String>,
}

impl Docs {
    /// The docstring for the declaration starting at `decl_start`, if any.
    pub(crate) fn get(&self, decl_start: usize) -> Option<&str> {
        self.by_offset.get(&decl_start).map(String::as_str)
    }
}

/// The doc opener: a comment line beginning `-- |`.
fn is_doc_open(text: &str) -> bool {
    let t = text.trim_start();
    t.starts_with("-- |") || t.starts_with("--|")
}

/// Strip the `--` / `-- |` / `-- ^` prefix (and one following space) from one
/// comment line.
pub(crate) fn strip(text: &str) -> &str {
    let t = text.trim_start();
    let body = t
        .strip_prefix("-- |")
        .or_else(|| t.strip_prefix("--|"))
        .or_else(|| t.strip_prefix("-- ^"))
        .or_else(|| t.strip_prefix("--^"))
        .or_else(|| t.strip_prefix("--"))
        .unwrap_or(t);
    body.strip_prefix(' ').unwrap_or(body)
}

/// Render a contiguous comment run into prose. Consecutive non-empty lines form
/// one paragraph joined by spaces (an empty `--` line breaks the paragraph); a
/// fenced code block is kept verbatim. This is the canonical Markdown a `never`-
/// wrap formatter (dprint) produces, so the generated pages stay format-stable.
fn render_block(lines: &[&str]) -> String {
    let mut blocks: Vec<String> = Vec::new();
    let mut para: Vec<String> = Vec::new();
    let mut code: Vec<String> = Vec::new();
    let mut in_code = false;
    for line in lines {
        let body = strip(line);
        let trimmed = body.trim();
        if trimmed.starts_with("```") {
            if in_code {
                code.push(trimmed.to_string());
                blocks.push(code.join("\n"));
                code.clear();
                in_code = false;
            } else if !para.is_empty() {
                blocks.push(para.join(" "));
                para.clear();
                in_code = true;
                code.push(trimmed.to_string());
            } else {
                in_code = true;
                code.push(trimmed.to_string());
            }
        } else if in_code {
            code.push(body.trim_end().to_string());
        } else if trimmed.is_empty() {
            if !para.is_empty() {
                blocks.push(para.join(" "));
                para.clear();
            }
        } else {
            para.push(trimmed.to_string());
        }
    }
    if !para.is_empty() {
        blocks.push(para.join(" "));
    }
    if !code.is_empty() {
        blocks.push(code.join("\n"));
    }
    blocks.join("\n\n")
}

/// Split the trivia in `[lo, hi)` into contiguous comment runs (broken by blank
/// lines), each tagged with the byte offset of its first comment. The bool is
/// true when a blank line follows the final comment, i.e. the last run is *not*
/// adjacent to `hi`.
fn runs(trivia: &TriviaTable, lo: usize, hi: usize) -> (Vec<(usize, Vec<&str>)>, bool) {
    let mut out: Vec<(usize, Vec<&str>)> = Vec::new();
    let mut cur: Vec<&str> = Vec::new();
    let mut cur_start = 0usize;
    let mut trailing_blank = false;
    for ev in trivia.between(lo, hi) {
        match &ev.trivia {
            Trivia::Comment { text, .. } => {
                if cur.is_empty() {
                    cur_start = ev.span.start;
                }
                cur.push(text.as_str());
                trailing_blank = false;
            }
            Trivia::BlankLine => {
                if !cur.is_empty() {
                    out.push((cur_start, std::mem::take(&mut cur)));
                }
                trailing_blank = true;
            }
        }
    }
    if !cur.is_empty() {
        out.push((cur_start, cur));
        trailing_blank = false;
    }
    (out, trailing_blank)
}

/// The docstring block directly above `hi` (a declaration start): the last
/// comment run in `[lo, hi)` when it touches `hi` and opens with `-- |`. Returns
/// the prose and the block's start offset.
fn adjacent_doc(trivia: &TriviaTable, lo: usize, hi: usize) -> Option<(String, usize)> {
    let (rs, trailing_blank) = runs(trivia, lo, hi);
    if trailing_blank {
        return None;
    }
    let (start, lines) = rs.last()?;
    is_doc_open(lines[0]).then(|| (render_block(lines), *start))
}

/// The first `-- |` comment run in `[lo, hi)`, used for the module description.
fn leading_doc(trivia: &TriviaTable, lo: usize, hi: usize) -> Option<String> {
    let (rs, _) = runs(trivia, lo, hi);
    let (_, lines) = rs.first()?;
    is_doc_open(lines[0]).then(|| render_block(lines))
}

/// Associate `-- |` docstrings to each declaration start in `starts` (which must
/// be sorted), and recover the module description. Each declaration's doc is the
/// comment run immediately above it; the previous declaration bounds the search
/// so a comment inside one body never leaks to the next.
pub(crate) fn extract(trivia: &TriviaTable, starts: &[usize]) -> Docs {
    let mut by_offset = BTreeMap::new();
    let mut module = None;
    for (i, &s) in starts.iter().enumerate() {
        let lo = if i == 0 { 0 } else { starts[i - 1] };
        let own = adjacent_doc(trivia, lo, s);
        // The module blurb sits before the first declaration's own doc block (or
        // before the declaration itself when it carries none).
        if i == 0 {
            let upper = own.as_ref().map_or(s, |(_, start)| *start);
            module = leading_doc(trivia, 0, upper);
        }
        if let Some((doc, _)) = own {
            by_offset.insert(s, doc);
        }
    }
    Docs { module, by_offset }
}
