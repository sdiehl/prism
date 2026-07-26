//! The digest-reseating formatter entry.
//!
//! Parses, recomputes each `stable` block's per-rung shape golden, rewrites
//! the `frozen "<digest>"` badges, and prints. Lives above the syntax crate
//! because rung digests are semantic (shape hashing), while the plain
//! formatter entries stay purely syntactic.

use prism_syntax::error::Error;
use prism_syntax::fmt::format_program;
use prism_syntax::parse::{parse, ParseResult};

use crate::syntax::desugar::stable_rung_digests;

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
        let digests = stable_rung_digests(sd)?;
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
    Ok(format_program(src, &trivia, &program))
}
