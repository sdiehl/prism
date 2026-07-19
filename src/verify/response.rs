//! The solver-response parser. It normalizes the small accepted result vocabulary
//! (`sat`, `unsat`, `unknown`) from a solver's stdout and rejects empty,
//! unrecognized, contradictory, or `(error ...)` output. It never launches a
//! process: it is a pure function of the bytes a solver produced, so it is tested
//! with no solver present. The out-of-process adapters that feed it real bytes
//! live in `solver`.

/// The normalized result of a single `check-sat`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum SolverStatus {
    Sat,
    Unsat,
    Unknown,
}

/// Why a solver's output was not a usable status.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum ResponseError {
    /// No non-blank output at all.
    Empty,
    /// Output was present but named no status token.
    Unrecognized,
    /// Two different status tokens appeared; the output is not trustworthy.
    Contradictory,
    /// The solver reported an error line.
    Solver(String),
}

/// Parse one solver response. Blank lines and `;` comments are ignored; a
/// `(error ...)` line fails immediately; model bodies and `success` acks are not
/// statuses. Exactly one distinct status must appear.
pub(crate) fn parse(output: &str) -> Result<SolverStatus, ResponseError> {
    let mut found: Option<SolverStatus> = None;
    let mut saw_content = false;
    for raw in output.lines() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with(';') {
            continue;
        }
        saw_content = true;
        if line.starts_with("(error") {
            return Err(ResponseError::Solver(line.to_string()));
        }
        let status = match line {
            "sat" => Some(SolverStatus::Sat),
            "unsat" => Some(SolverStatus::Unsat),
            "unknown" => Some(SolverStatus::Unknown),
            // `success` acks and model/get-value bodies are not statuses.
            _ => None,
        };
        if let Some(s) = status {
            match found {
                None => found = Some(s),
                Some(prev) if prev == s => {}
                Some(_) => return Err(ResponseError::Contradictory),
            }
        }
    }
    match found {
        Some(s) => Ok(s),
        None if saw_content => Err(ResponseError::Unrecognized),
        None => Err(ResponseError::Empty),
    }
}
