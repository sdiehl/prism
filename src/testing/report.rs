//! Human reporter: one concise line per result and a final summary. Captured
//! output is printed on a failure, and on a pass only under `--show-output`.

use std::io::Write;

use super::runner::{Outcome, OutcomeKind, Tally};

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
    if let Some(reason) = &outcome.skipped {
        return writeln!(out, "test {id} ... skipped ({reason})");
    }
    writeln!(out, "test {id} ... {}", status(outcome.kind))?;
    if !outcome.passed() && !outcome.message.is_empty() {
        writeln!(out, "  {}", outcome.message)?;
    }
    if let Some(failure) = &outcome.failure {
        for (label, value) in [("expected", &failure.expected), ("actual", &failure.actual)] {
            match value {
                Some(value) if value.contains('\n') => {
                    writeln!(out, "  {label}:")?;
                    for l in value.lines() {
                        writeln!(out, "    {l}")?;
                    }
                }
                Some(value) => writeln!(out, "  {label}: {value}")?,
                None => {}
            }
        }
        if let Some(diff) = &failure.diff {
            writeln!(out, "  --- diff ---")?;
            for l in diff.lines() {
                writeln!(out, "  {l}")?;
            }
        }
        for entry in &failure.context {
            writeln!(out, "  context: {entry}")?;
        }
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
pub(crate) fn summary(out: &mut dyn Write, tally: &Tally) -> std::io::Result<()> {
    let result = if tally.failed == 0 && tally.infrastructure == 0 {
        "ok"
    } else {
        "FAILED"
    };
    write!(
        out,
        "test result: {result}. {} passed; {} failed",
        tally.passed, tally.failed
    )?;
    if tally.skipped > 0 {
        write!(out, "; {} skipped", tally.skipped)?;
    }
    if tally.infrastructure > 0 {
        write!(out, "; {} harness error(s)", tally.infrastructure)?;
    }
    writeln!(out)
}
