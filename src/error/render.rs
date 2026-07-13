use std::ops::Range;

use ariadne::{Color, Config, Label, Report, ReportKind, Source};
use marginalia::Span;

use super::source::SourceMap;
use super::{Diag, Error, ErrorCode, ParseError, TypeError};

impl Error {
    /// A short origin label for the failure, so diagnostics name their
    /// component ("Scope Error", "Type Error") rather than a bare "Error".
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::Lex(_) => "Lexical Error",
            Self::Parse(_) => "Parse Error",
            Self::Type(e) => e.kind(),
            Self::CodegenBackend(_)
            | Self::CodegenDocs(_)
            | Self::CodegenFormat(_)
            | Self::CodegenDump(_)
            | Self::CodegenVerification(_) => "Codegen Error",
            Self::ResolveModule(_)
            | Self::ResolveProject(_)
            | Self::ResolvePackage(_)
            | Self::ResolveLineage(_)
            | Self::ResolveCommand(_) => "Module Error",
            Self::Io(_) => "IO Error",
            Self::RuntimeEvaluation(_) | Self::RuntimeReplay(_) | Self::RuntimeDebugger(_) => {
                "Runtime Error"
            }
            Self::InternalInvariant(_) => "Internal Error",
        }
    }

    /// The byte range in the full source this error points at, if any.
    #[must_use]
    pub fn primary_span(&self) -> Option<Range<usize>> {
        match self {
            Self::Lex(e) => Some(e.offset()..e.offset()),
            Self::Parse(ParseError::Syntax { span, .. }) => Some(span_range(span)),
            Self::Type(e) => e.span().map(span_range),
            _ => None,
        }
    }

    /// Render with ANSI color, for an interactive terminal.
    #[must_use]
    pub fn render(&self, src: &str, name: &str) -> String {
        self.render_with(src, name, true)
    }

    /// Render without color, for captured/piped output (the `report` dump and
    /// snapshot tests) where ANSI escapes would be noise.
    #[must_use]
    pub fn render_plain(&self, src: &str, name: &str) -> String {
        self.render_with(src, name, false)
    }

    fn render_with(&self, src: &str, name: &str, color: bool) -> String {
        let map = SourceMap::new(src);
        let kind = self.kind();
        let code = self.code();
        let mut buf = Vec::<u8>::new();
        let ok = match self {
            Self::Lex(e) => {
                let off = e.offset();
                let msg = format!("{e} at {}", map.at(off));
                write_report(
                    &map,
                    kind,
                    code,
                    name,
                    off..off,
                    &msg,
                    "here",
                    color,
                    &mut buf,
                )
                .is_ok()
            }
            Self::Parse(e) => {
                let (range, label) = match e {
                    ParseError::Syntax { span, .. } => (span_range(span), "here"),
                    ParseError::UnexpectedEof => (src.len()..src.len(), "expected more input here"),
                };
                write_report(
                    &map,
                    kind,
                    code,
                    name,
                    range,
                    &e.to_string(),
                    label,
                    color,
                    &mut buf,
                )
                .is_ok()
            }
            // A structured diagnostic renders its code, secondary spans, help,
            // and notes (the catalogue is the one place carrying them).
            Self::Type(TypeError::Kind(diag)) => {
                write_report_rich(&map, kind, name, diag, color, &mut buf).is_ok()
            }
            Self::Type(e) => {
                let located = match e {
                    TypeError::UnboundVariable { span, name: n } => {
                        Some((span, format!("'{n}' not in scope")))
                    }
                    TypeError::TypeMismatch {
                        span,
                        expected,
                        found,
                    } => Some((span, format!("expected {expected}, got {found}"))),
                    TypeError::ScopeFailure { span, msg }
                    | TypeError::TypeFailure { span, msg } => Some((span, msg.clone())),
                    TypeError::Kind(_) => unreachable!("handled above"),
                    // No span to point at; fall through to the plain message.
                    TypeError::InternalInvariant { .. } => None,
                };
                located.is_some_and(|(span, label)| {
                    write_report(
                        &map,
                        kind,
                        code,
                        name,
                        span_range(span),
                        &e.to_string(),
                        &label,
                        color,
                        &mut buf,
                    )
                    .is_ok()
                })
            }
            _ => false,
        };
        if !ok {
            return format!("{kind}[{code}]: {self}");
        }
        let rendered = String::from_utf8_lossy(&buf).into_owned();
        if color {
            rendered
        } else {
            strip_ansi(&rendered)
        }
    }
}

// Drop CSI escape sequences (`\x1b[ ... m`). ariadne colors the report-kind
// label independently of `Config::with_color`, so the no-color path scrubs the
// residual escapes for stable, pipe-safe output.
fn strip_ansi(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '\x1b' {
            for d in chars.by_ref() {
                if d.is_ascii_alphabetic() {
                    break;
                }
            }
        } else {
            out.push(c);
        }
    }
    out
}

const fn span_range(s: &Span) -> Range<usize> {
    s.start..s.end
}

/// Render a non-fatal warning against `src`.
///
/// Produces a yellow source caret when `span` is a non-empty range inside `src`,
/// and a plain `warning: ...` line otherwise (e.g. a warning about a definition
/// in another module, whose span does not index this source). Always ends with a
/// newline.
#[must_use]
pub fn render_warning(src: &str, name: &str, span: &Span, msg: &str, color: bool) -> String {
    let range = span_range(span);
    let plain = || format!("warning: {msg}\n");
    if range.start >= range.end || range.end > src.len() {
        return plain();
    }
    let map = SourceMap::new(src);
    let n = map.prelude_len();
    let (body, file, at) = if range.start < n {
        (&map.full()[..n], "<prelude>", range.start..range.end.min(n))
    } else {
        (map.user(), name, range.start - n..range.end - n)
    };
    let mut buf = Vec::<u8>::new();
    let ok = Report::build(
        ReportKind::Custom("warning", Color::Yellow),
        (file, at.clone()),
    )
    .with_config(Config::default().with_color(color))
    .with_message(msg)
    .with_label(
        Label::new((file, at))
            .with_message("here")
            .with_color(Color::Yellow),
    )
    .finish()
    .write((file, Source::from(body)), &mut buf)
    .is_ok();
    if !ok {
        return plain();
    }
    let rendered = String::from_utf8_lossy(&buf).into_owned();
    if color {
        rendered
    } else {
        strip_ansi(&rendered)
    }
}

#[allow(clippy::too_many_arguments)]
fn write_report(
    map: &SourceMap<'_>,
    kind: &str,
    code: ErrorCode,
    name: &str,
    range: Range<usize>,
    msg: &str,
    label: &str,
    color: bool,
    out: &mut Vec<u8>,
) -> std::io::Result<()> {
    let n = map.prelude_len();
    let (src, name, range) = if range.start < n {
        (&map.full()[..n], "<prelude>", range.start..range.end.min(n))
    } else {
        (map.user(), name, range.start - n..range.end - n)
    };
    // `Config::with_color(false)` suppresses every ANSI escape, so the label
    // hue below is rendered only when `color` is set.
    Report::build(ReportKind::Custom(kind, Color::Red), (name, range.clone()))
        .with_config(Config::default().with_color(color))
        .with_code(code)
        .with_message(msg)
        .with_label(
            Label::new((name, range))
                .with_message(label)
                .with_color(Color::Red),
        )
        .finish()
        .write((name, Source::from(src)), out)
}

// Render a structured [`Diag`]: the code in the header, the primary span, any
// secondary spans (contributing locations), and the help/notes. Best-practice
// diagnostic shape (a code you can look up, blame across several locations, and
// an actionable suggestion), all from the one catalogue entry.
fn write_report_rich(
    map: &SourceMap<'_>,
    kind: &str,
    name: &str,
    diag: &Diag,
    color: bool,
    out: &mut Vec<u8>,
) -> std::io::Result<()> {
    let n = map.prelude_len();
    let prim = span_range(&diag.span);
    // Labels must all index the same source, so pick the region the primary span
    // falls in and keep only same-region secondaries.
    let in_user = prim.start >= n;
    let (src, sname) = if in_user {
        (map.user(), name)
    } else {
        (&map.full()[..n], "<prelude>")
    };
    let adj = |r: &Range<usize>| -> Range<usize> {
        if in_user {
            (r.start - n)..(r.end - n)
        } else {
            r.start..r.end.min(n)
        }
    };
    let msg = diag.to_string();
    let mut report = Report::build(ReportKind::Custom(kind, Color::Red), (sname, adj(&prim)))
        .with_config(Config::default().with_color(color))
        .with_code(diag.kind.code())
        .with_message(&msg)
        .with_label(
            Label::new((sname, adj(&prim)))
                .with_message(&msg)
                .with_color(Color::Red)
                .with_order(0),
        );
    for (i, (lspan, lmsg)) in diag.labels.iter().enumerate() {
        let lr = span_range(lspan);
        let same_region = (lr.start >= n) == in_user;
        if same_region && lr.start < lr.end {
            report = report.with_label(
                Label::new((sname, adj(&lr)))
                    .with_message(lmsg)
                    .with_color(Color::Blue)
                    .with_order(i32::try_from(i).unwrap_or(0) + 1),
            );
        }
    }
    if let Some(help) = &diag.help {
        report = report.with_help(help);
    }
    for note in &diag.notes {
        report = report.with_note(note);
    }
    report.finish().write((sname, Source::from(src)), out)
}
