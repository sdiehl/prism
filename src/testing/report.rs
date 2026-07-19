//! Human reporter: one concise line per result and a final summary. Captured
//! output is printed on a failure, and on a pass only under `--show-output`.

use std::io::Write;

use super::runner::{Outcome, OutcomeKind};

const fn status(kind: Option<OutcomeKind>) -> &'static str {
    match kind {
        None => "ok",
        Some(OutcomeKind::Fail) => "FAILED",
        Some(OutcomeKind::Fault) => "FAULT",
        Some(OutcomeKind::UnhandledEffect) => "UNHANDLED EFFECT",
        Some(OutcomeKind::Exit) => "EXIT",
        Some(OutcomeKind::Infrastructure) => "HARNESS ERROR",
    }
}

/// Write one result line, then the captured output when it should be shown.
///
/// # Errors
/// Propagates a write error from the sink.
pub(crate) fn line(
    out: &mut dyn Write,
    id: &str,
    outcome: &Outcome,
    show_output: bool,
) -> std::io::Result<()> {
    writeln!(out, "test {id} ... {}", status(outcome.kind))?;
    if !outcome.passed() && !outcome.message.is_empty() {
        writeln!(out, "  {}", outcome.message)?;
    }
    let show = !outcome.passed() || show_output;
    if show && !outcome.output.is_empty() {
        writeln!(out, "  --- output ---")?;
        for l in outcome.output.lines() {
            writeln!(out, "  {l}")?;
        }
    }
    Ok(())
}

/// Write the final summary line.
///
/// # Errors
/// Propagates a write error from the sink.
pub(crate) fn summary(
    out: &mut dyn Write,
    passed: usize,
    failed: usize,
    infrastructure: usize,
) -> std::io::Result<()> {
    let result = if failed == 0 && infrastructure == 0 {
        "ok"
    } else {
        "FAILED"
    };
    if infrastructure == 0 {
        writeln!(
            out,
            "test result: {result}. {passed} passed; {failed} failed"
        )
    } else {
        writeln!(
            out,
            "test result: {result}. {passed} passed; {failed} failed; {infrastructure} harness error(s)"
        )
    }
}
