use std::collections::BTreeMap;

use marginalia::pretty::{concat, flat_alt, nil, text, Doc};
use marginalia::TriviaTable;

use crate::ast::{
    Arm, BinOp, CatchArm, ConvDir, Converter, Expr, Grade, HandlerArm, Marker, PathOp, PathStep,
    Pattern, Program, Qualifier, Rung, StableDecl, Sugar, SugarArm, Surface, S,
};
use crate::error::Error;
use crate::parse::{parse, ParseResult};

mod block;
mod breaks;
mod call;
pub mod decl;
mod exprdoc;
mod inline;
mod layout;
mod lit;
mod ops;
mod pat;
mod program;
mod records;
mod stable;
mod stmts;
mod trivia;

const INDENT: &str = "  ";
const LINE_WIDTH: usize = 80;

// A head (an `if`/`while` condition, a `match` scrutinee, a `handle` body, a
// `for` source) shares its line with the keywords that frame it: `if`/`then`,
// `match`/`of`, `handle`/`with`, `while`/`do`, `for`/`in`. The head printer
// measures only the head itself, so it reserves this fixed slack for the
// framing instead of recomputing it per form. One approximation covering every
// head form, not the exact width of any one of them.
const HEAD_FRAMING_RESERVE: usize = 16;

// The single space between an arm's `=>` and an inline body.
const ARM_BODY_GAP: usize = 1;

fn text_width(s: &str) -> usize {
    s.chars().count()
}

// A one-element tuple is a tuple only because of its trailing comma: `(x)`
// reparses as a parenthesized `x` in every position the grammar admits a tuple
// (expression, pattern, type), so dropping the comma silently changes what the
// text means. There is no separator position to put it in, so it rides on the
// sole element, and every tuple printer routes through here rather than
// rediscovering the rule.
const TUPLE_COMMA: &str = ",";

// The `Doc`-building printers (patterns, expressions). A block that already
// emits a trailing separator when it breaks is only missing the comma in the
// flat layout, so `block_trails` says which of the two layouts still needs one;
// supplying it in both would print `,,`.
fn tuple_items<I: IntoIterator<Item = Doc>>(items: I, block_trails: bool) -> Vec<Doc> {
    let mut items: Vec<Doc> = items.into_iter().collect();
    if let [only] = items.as_mut_slice() {
        let tail = if block_trails {
            flat_alt(text(TUPLE_COMMA), nil())
        } else {
            text(TUPLE_COMMA)
        };
        *only = concat([only.clone(), tail]);
    }
    items
}

// The string-building printers (inline expressions, types).
fn tuple_parens(parts: &[String]) -> String {
    let body = parts.join(", ");
    let tail = if parts.len() == 1 { TUPLE_COMMA } else { "" };
    format!("({body}{tail})")
}

// The column the first character of a line indented `indent` levels lands at.
const fn indent_col(indent: usize) -> usize {
    indent * INDENT.len()
}

// The width oracle: does `s` fit on one line when its first character lands at
// column `col`? Every inline/break decision in the printers goes through here.
fn fits_at(col: usize, s: &str) -> bool {
    col + text_width(s) <= LINE_WIDTH
}

// Layout mode prints offside blocks. Flat is for bracketed contexts where
// virtual layout tokens are suppressed, so only inline let/braced arms parse.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Layout,
    Flat,
}

// The formatter's read-only context, threaded through every printer instead of
// living in thread-local state: the original source (for the verbatim fallback,
// since a formatter must never destroy code) and the comment/blank-line trivia
// (so the offside-block printers can re-emit trivia inside a function body, not
// just between declarations). Borrowing both keeps formatting reentrant and
// leaves no state to clear, so a panic mid-format cannot poison the next run.
pub(super) struct Fmt<'a> {
    source: &'a str,
    trivia: &'a TriviaTable,
}

/// # Errors
/// Fails when the source does not parse.
pub fn format(src: &str) -> Result<String, Error> {
    let ParseResult { program, trivia } = parse(src)?;
    let cx = Fmt {
        source: src,
        trivia: &trivia,
    };
    Ok(cx.fmt_program(&program))
}

/// Format an already-parsed program against its source and trivia.
///
/// The seam a caller uses when it mutates the surface tree (digest reseating)
/// before printing. `format` and `format_check` remain the plain-source
/// entries.
#[must_use]
pub fn format_program(source: &str, trivia: &TriviaTable, program: &Program) -> String {
    let cx = Fmt { source, trivia };
    cx.fmt_program(program)
}

/// Render each top-level item of `program` on its own, exactly as
/// [`format_program`] would print it in place.
///
/// Keyed by the item's source start offset and carrying the comment block
/// written directly above it.
///
/// The seam a caller uses to quote one definition's canonical form. Going
/// through the formatter rather than slicing `source` is what makes the
/// rendering canonical: two spellings of one definition quote identically, and
/// the quotation moves only when the definition does.
#[must_use]
pub fn format_items(
    source: &str,
    trivia: &TriviaTable,
    program: &Program,
) -> BTreeMap<usize, String> {
    let cx = Fmt { source, trivia };
    cx.fmt_items(program)
}

/// # Errors
/// Fails when the source does not parse.
pub fn format_check(src: &str) -> Result<bool, Error> {
    let formatted = format(src)?;
    Ok(formatted == src)
}
