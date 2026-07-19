//! The `prism-test-events-v1` newline-delimited event stream.
//!
//! Events are emitted as one canonical JSON object per line. The bytes are
//! deterministic: no absolute paths, timings, process IDs, or hash-map order.
//! Serial execution makes the event order itself deterministic. The encoder is
//! hand-written so field order and escaping are fixed, independent of any
//! serializer's map ordering.

use std::fmt::Write;

use super::runner::{Outcome, OutcomeKind};
use super::Failure;

/// The outcome kind tag carried by a `test_failed` event, matching the
/// `OutcomeKind` classification.
const fn kind_tag(kind: OutcomeKind) -> &'static str {
    match kind {
        OutcomeKind::Fail => "fail",
        OutcomeKind::Fault => "fault",
        OutcomeKind::UnhandledEffect => "unhandled_effect",
        OutcomeKind::Exit => "exit",
        OutcomeKind::Infrastructure => "infrastructure",
    }
}

/// The suite-started event.
#[must_use]
pub(crate) fn suite_started(selected: usize) -> String {
    format!(
        "{{\"event\":\"suite_started\",\"schema\":\"{}\",\"selected\":{selected}}}",
        super::TEST_EVENTS_SCHEMA
    )
}

/// The per-test started event.
#[must_use]
pub(crate) fn test_started(id: &str) -> String {
    format!("{{\"event\":\"test_started\",\"id\":{}}}", json_str(id))
}

/// A captured-output event for a test. `stream` is `stdout` (the ambient
/// output channel); `bytes` is the captured text.
#[must_use]
pub(crate) fn test_output(id: &str, stream: &str, bytes: &str) -> String {
    format!(
        "{{\"event\":\"test_output\",\"id\":{},\"stream\":{},\"bytes\":{}}}",
        json_str(id),
        json_str(stream),
        json_str(bytes)
    )
}

/// The passing-test event.
#[must_use]
pub(crate) fn test_passed(id: &str) -> String {
    format!("{{\"event\":\"test_passed\",\"id\":{}}}", json_str(id))
}

/// The failing-test event, carrying the classified kind and a message.
#[must_use]
pub(crate) fn test_failed(id: &str, kind: OutcomeKind, message: &str) -> String {
    format!(
        "{{\"event\":\"test_failed\",\"id\":{},\"kind\":{},\"message\":{}}}",
        json_str(id),
        json_str(kind_tag(kind)),
        json_str(message)
    )
}

/// The failing-test event for a structured [`Failure`]: always a `fail` kind, with
/// the optional expected/actual/diff/context/site fields appended in canonical
/// order and omitted when absent, so a payload-free failure's bytes are unchanged.
#[must_use]
pub(crate) fn test_failed_structured(id: &str, failure: &Failure) -> String {
    let mut s = format!(
        "{{\"event\":\"test_failed\",\"id\":{},\"kind\":{},\"message\":{}",
        json_str(id),
        json_str(kind_tag(OutcomeKind::Fail)),
        json_str(&failure.message)
    );
    append_opt(&mut s, "expected", failure.expected.as_deref());
    append_opt(&mut s, "actual", failure.actual.as_deref());
    append_opt(&mut s, "diff", failure.diff.as_deref());
    if !failure.context.is_empty() {
        let items = failure
            .context
            .iter()
            .map(|c| json_str(c))
            .collect::<Vec<_>>()
            .join(",");
        let _ = write!(s, ",\"context\":[{items}]");
    }
    append_opt(&mut s, "site", failure.site.as_deref());
    s.push('}');
    s
}

// Append a `,"field":"value"` pair when the optional value is present.
fn append_opt(out: &mut String, field: &str, value: Option<&str>) {
    if let Some(value) = value {
        let _ = write!(out, ",{}:{}", json_str(field), json_str(value));
    }
}

/// The suite-finished event with the tallied counts.
#[must_use]
pub(crate) fn suite_finished(
    passed: usize,
    failed: usize,
    skipped: usize,
    infrastructure: usize,
) -> String {
    format!(
        "{{\"event\":\"suite_finished\",\"passed\":{passed},\"failed\":{failed},\"skipped\":{skipped},\"infrastructure_failed\":{infrastructure}}}"
    )
}

/// Emit every event for one completed test outcome to `out`, in canonical order:
/// `test_started`, an optional `test_output`, then `test_passed`/`test_failed`.
/// Output is emitted for a failing test always, and for a passing test only when
/// `show_output` is set.
///
/// # Errors
/// Propagates a write error from the sink.
pub(crate) fn emit_outcome(
    out: &mut dyn std::io::Write,
    id: &str,
    outcome: &Outcome,
    show_output: bool,
) -> std::io::Result<()> {
    writeln!(out, "{}", test_started(id))?;
    let show = !outcome.passed() || show_output;
    if show && !outcome.output.is_empty() {
        writeln!(out, "{}", test_output(id, "stdout", &outcome.output))?;
    }
    match (outcome.kind, outcome.failure.as_ref()) {
        (None, _) => writeln!(out, "{}", test_passed(id)),
        (Some(_), Some(failure)) => writeln!(out, "{}", test_failed_structured(id, failure)),
        (Some(kind), None) => writeln!(out, "{}", test_failed(id, kind, &outcome.message)),
    }
}

// A JSON string literal with the mandatory escapes. Kept minimal and explicit so
// the bytes never depend on a serializer's escaping policy.
fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escapes_control_and_quotes() {
        assert_eq!(json_str("a\"b\\c\n"), "\"a\\\"b\\\\c\\n\"");
    }

    // The failure classes carry pairwise-distinct event tags, so a runtime fault,
    // an explicit exit, and an unhandled effect never collapse into one kind on the
    // wire. Runtime distinctness of fault vs exit is covered end to end elsewhere;
    // the unhandled-effect class is a defensive one (the signature check rejects
    // residual effects at check time), so its distinct tag is pinned here.
    #[test]
    fn every_failure_kind_has_a_distinct_tag() {
        let kinds = [
            OutcomeKind::Fail,
            OutcomeKind::Fault,
            OutcomeKind::UnhandledEffect,
            OutcomeKind::Exit,
            OutcomeKind::Infrastructure,
        ];
        let tags: std::collections::BTreeSet<&str> = kinds.iter().map(|k| kind_tag(*k)).collect();
        assert_eq!(tags.len(), kinds.len(), "two failure kinds share a tag");
    }
}
