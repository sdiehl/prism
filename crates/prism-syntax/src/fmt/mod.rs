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

fn text_width(s: &str) -> usize {
    s.chars().count()
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

/// # Errors
/// Fails when the source does not parse.
pub fn format_check(src: &str) -> Result<bool, Error> {
    let formatted = format(src)?;
    Ok(formatted == src)
}
