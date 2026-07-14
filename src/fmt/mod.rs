use marginalia::TriviaTable;

use crate::error::Error;
use crate::parse::{parse, ParseResult};
use crate::syntax::ast::{
    Arm, BinOp, CatchArm, ConvDir, Converter, Expr, Grade, HandlerArm, Marker, PathOp, PathStep,
    Pattern, Program, Qualifier, Rung, StableDecl, Sugar, SugarArm, Surface, S,
};

mod block;
mod breaks;
mod call;
pub(crate) mod decl;
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

/// Reseat every `stable` block's per-rung shape golden, then format.
///
/// Each shipped rung's `frozen "<digest>"` badge is rewritten to its recomputed
/// shape digest and the current rung's badge is dropped. This is the loud reseat
/// path behind `prism wire --accept`, the analogue of `just snap` for the goldens.
///
/// # Errors
/// Fails when the source does not parse or a `stable` block is malformed.
pub fn format_wire_accept(src: &str) -> Result<String, Error> {
    let ParseResult {
        mut program,
        trivia,
    } = parse(src)?;
    for sd in &mut program.stable {
        let digests = crate::syntax::desugar::stable_rung_digests(sd)?;
        let total = sd.rungs.len();
        for (idx, rung) in sd.rungs.iter_mut().enumerate() {
            rung.frozen = if idx + 1 == total {
                None
            } else {
                digests
                    .iter()
                    .find(|(v, _)| v == &rung.name)
                    .map(|(_, d)| d.clone())
            };
        }
    }
    let cx = Fmt {
        source: src,
        trivia: &trivia,
    };
    Ok(cx.fmt_program(&program))
}

/// # Errors
/// Fails when the source does not parse.
pub fn format_check(src: &str) -> Result<bool, Error> {
    let formatted = format(src)?;
    Ok(formatted == src)
}
