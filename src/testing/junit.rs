//! `JUnit` XML: a projection of the runner's `(id, outcome)` results for CI systems
//! that read test reports. One `testsuite` per defining module (the logical ID up
//! to its last `::`), in logical-ID order. Like the event stream it carries no
//! timings, hostnames, or paths, so the bytes are deterministic.

use std::collections::BTreeMap;
use std::fmt::Write;

use super::runner::{Outcome, OutcomeKind};

/// Render the results as a `JUnit` XML document.
#[must_use]
pub(crate) fn render(results: &[(String, Outcome)]) -> String {
    let mut suites: BTreeMap<&str, Vec<(&str, &Outcome)>> = BTreeMap::new();
    for (id, outcome) in results {
        let (suite, name) = id.rsplit_once("::").unwrap_or(("", id));
        suites.entry(suite).or_default().push((name, outcome));
    }
    let mut out = String::from("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n");
    let _ = writeln!(
        out,
        "<testsuites name=\"prism test\" tests=\"{}\" failures=\"{}\" errors=\"{}\" skipped=\"{}\">",
        results.len(),
        count(results.iter().map(|(_, o)| o), Bucket::Failure),
        count(results.iter().map(|(_, o)| o), Bucket::Error),
        count(results.iter().map(|(_, o)| o), Bucket::Skipped),
    );
    for (suite, cases) in &suites {
        let _ = writeln!(
            out,
            "  <testsuite name=\"{}\" tests=\"{}\" failures=\"{}\" errors=\"{}\" skipped=\"{}\">",
            escape(suite),
            cases.len(),
            count(cases.iter().map(|(_, o)| *o), Bucket::Failure),
            count(cases.iter().map(|(_, o)| *o), Bucket::Error),
            count(cases.iter().map(|(_, o)| *o), Bucket::Skipped),
        );
        for (name, outcome) in cases {
            case(&mut out, suite, name, outcome);
        }
        out.push_str("  </testsuite>\n");
    }
    out.push_str("</testsuites>\n");
    out
}

// JUnit's three non-pass buckets. A `fail()` or assertion is a `failure`; a
// fault, exit, unhandled effect, or harness problem is an `error`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Bucket {
    Pass,
    Failure,
    Error,
    Skipped,
}

const fn bucket(outcome: &Outcome) -> Bucket {
    match (outcome.skipped.is_some(), outcome.kind) {
        (true, _) => Bucket::Skipped,
        (false, None) => Bucket::Pass,
        (false, Some(OutcomeKind::Fail)) => Bucket::Failure,
        (false, Some(_)) => Bucket::Error,
    }
}

fn count<'a>(outcomes: impl Iterator<Item = &'a Outcome>, b: Bucket) -> usize {
    outcomes.filter(|o| bucket(o) == b).count()
}

fn case(out: &mut String, suite: &str, name: &str, outcome: &Outcome) {
    let _ = write!(
        out,
        "    <testcase classname=\"{}\" name=\"{}\"",
        escape(suite),
        escape(name)
    );
    let body = match bucket(outcome) {
        Bucket::Pass => None,
        Bucket::Skipped => Some(format!(
            "      <skipped message=\"{}\"/>\n",
            escape(outcome.skipped.as_deref().unwrap_or_default())
        )),
        b => {
            let tag = if b == Bucket::Failure {
                "failure"
            } else {
                "error"
            };
            Some(format!(
                "      <{tag} message=\"{}\">{}</{tag}>\n",
                escape(&outcome.message),
                escape_text(&detail(outcome))
            ))
        }
    };
    let output = (!outcome.output.is_empty() && !outcome.passed()).then(|| {
        format!(
            "      <system-out>{}</system-out>\n",
            escape_text(&outcome.output)
        )
    });
    if body.is_none() && output.is_none() {
        out.push_str("/>\n");
        return;
    }
    out.push_str(">\n");
    out.push_str(&body.unwrap_or_default());
    out.push_str(&output.unwrap_or_default());
    out.push_str("    </testcase>\n");
}

// The failure body: the structured fields the human report shows.
fn detail(outcome: &Outcome) -> String {
    let Some(failure) = &outcome.failure else {
        return String::new();
    };
    let mut s = String::new();
    for (label, value) in [
        ("expected", &failure.expected),
        ("actual", &failure.actual),
        ("diff", &failure.diff),
    ] {
        if let Some(value) = value {
            let _ = writeln!(s, "{label}:\n{value}");
        }
    }
    s
}

// Escape for an attribute value, dropping the C0 controls XML 1.0 cannot carry.
// A line break is a character reference so attribute normalization keeps it.
fn escape(s: &str) -> String {
    escape_with(s, true)
}

// Escape for text content, where a line break stays literal.
fn escape_text(s: &str) -> String {
    escape_with(s, false)
}

fn escape_with(s: &str, attribute: bool) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&apos;"),
            '\n' if attribute => out.push_str("&#10;"),
            '\n' => out.push('\n'),
            '\t' | '\r' => out.push(c),
            c if (c as u32) < 0x20 => {}
            c => out.push(c),
        }
    }
    out
}
