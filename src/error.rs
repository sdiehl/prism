use std::ops::Range;

use ariadne::{Color, Config, Label, Report, ReportKind, Source};

use crate::driver::PRELUDE;
use marginalia::Span;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("{0}")]
    Lex(#[from] LexError),
    #[error("{0}")]
    Parse(#[from] ParseError),
    #[error("{0}")]
    Type(#[from] TypeError),
    #[error("codegen: {0}")]
    Codegen(String),
    #[error("{0}")]
    Resolve(String),
    #[error("{0}")]
    Io(#[from] std::io::Error),
    #[error("runtime: {0}")]
    Runtime(String),
    #[error("internal compiler error: {0}, please report this")]
    Ice(String),
}

/// Locates the prelude prefix that `with_prelude` prepends, so positions shown
/// to users are relative to their own file. Spans inside the prelude are
/// reported against the prelude explicitly.
#[derive(Debug)]
pub struct SourceMap<'a> {
    full: &'a str,
    prelude: usize,
}

impl<'a> SourceMap<'a> {
    #[must_use]
    pub fn new(full: &'a str) -> Self {
        let n = PRELUDE.len() + 1;
        let prelude =
            if full.len() >= n && full.as_bytes()[n - 1] == b'\n' && full.starts_with(PRELUDE) {
                n
            } else {
                0
            };
        Self { full, prelude }
    }

    #[must_use]
    pub fn user(&self) -> &'a str {
        &self.full[self.prelude..]
    }

    #[must_use]
    pub fn at(&self, byte: usize) -> String {
        if byte < self.prelude {
            let (l, c) = line_col(self.full, byte);
            format!("line {l}:{c} (in prelude)")
        } else {
            let (l, c) = line_col(self.user(), byte - self.prelude);
            format!("line {l}:{c}")
        }
    }
}

fn line_col(src: &str, byte: usize) -> (u32, u32) {
    let (mut line, mut col) = (1u32, 1u32);
    for (i, c) in src.char_indices() {
        if i >= byte {
            break;
        }
        if c == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

#[derive(Debug, Error)]
pub enum LexError {
    #[error("unexpected token")]
    Invalid { offset: usize },
    #[error("empty interpolation hole `{{}}`")]
    EmptyHole { offset: usize },
    #[error("unterminated interpolation hole")]
    UnterminatedHole { offset: usize },
    #[error("unterminated string literal")]
    UnterminatedString { offset: usize },
}

impl LexError {
    #[must_use]
    pub const fn offset(&self) -> usize {
        match self {
            Self::Invalid { offset }
            | Self::EmptyHole { offset }
            | Self::UnterminatedHole { offset }
            | Self::UnterminatedString { offset } => *offset,
        }
    }
}

#[derive(Debug, Error)]
pub enum ParseError {
    #[error("{msg}")]
    Syntax { span: Span, msg: String },
    #[error("unexpected end of input")]
    UnexpectedEof,
}

#[derive(Debug, Error)]
pub enum TypeError {
    #[error("unbound variable '{name}'")]
    Unbound { span: Span, name: String },
    #[error("type mismatch: expected {expected}, got {found}")]
    Mismatch {
        span: Span,
        expected: String,
        found: String,
    },
    #[error("{msg}")]
    Scope { span: Span, msg: String },
    #[error("{msg}")]
    Other { span: Span, msg: String },
    #[error("internal compiler error (please report): {msg}")]
    Ice { msg: String },
}

impl TypeError {
    #[must_use]
    pub const fn span(&self) -> Option<&Span> {
        match self {
            Self::Unbound { span, .. }
            | Self::Mismatch { span, .. }
            | Self::Scope { span, .. }
            | Self::Other { span, .. } => Some(span),
            Self::Ice { .. } => None,
        }
    }

    #[must_use]
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::Unbound { .. } | Self::Scope { .. } => "Scope Error",
            Self::Mismatch { .. } | Self::Other { .. } => "Type Error",
            Self::Ice { .. } => "Internal Error",
        }
    }

    #[must_use]
    pub fn in_fn(self, fn_name: &str) -> Self {
        if let Self::Ice { msg } = self {
            return Self::Ice {
                msg: format!("in `{fn_name}`: {msg}"),
            };
        }
        let msg = format!("in `{fn_name}`: {self}");
        match self {
            // Preserve the scope origin so the wrapped error still reports
            // as a Scope Error rather than collapsing to a generic one.
            Self::Unbound { span, .. } | Self::Scope { span, .. } => Self::Scope { span, msg },
            Self::Mismatch { span, .. } | Self::Other { span, .. } => Self::Other { span, msg },
            Self::Ice { .. } => self,
        }
    }
}

impl Error {
    /// A short origin label for the failure, so diagnostics name their
    /// component ("Scope Error", "Type Error") rather than a bare "Error".
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::Lex(_) => "Lexical Error",
            Self::Parse(_) => "Parse Error",
            Self::Type(e) => e.kind(),
            Self::Codegen(_) => "Codegen Error",
            Self::Resolve(_) => "Module Error",
            Self::Io(_) => "IO Error",
            Self::Runtime(_) => "Runtime Error",
            Self::Ice(_) => "Internal Error",
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
        let mut buf = Vec::<u8>::new();
        let ok = match self {
            Self::Lex(e) => {
                let off = e.offset();
                let msg = format!("{e} at {}", map.at(off));
                write_report(&map, kind, name, off..off, &msg, "here", color, &mut buf).is_ok()
            }
            Self::Parse(e) => {
                let (range, label) = match e {
                    ParseError::Syntax { span, .. } => (span_range(span), "here"),
                    ParseError::UnexpectedEof => (src.len()..src.len(), "expected more input here"),
                };
                write_report(
                    &map,
                    kind,
                    name,
                    range,
                    &e.to_string(),
                    label,
                    color,
                    &mut buf,
                )
                .is_ok()
            }
            Self::Type(e) => {
                let located = match e {
                    TypeError::Unbound { span, name: n } => {
                        Some((span, format!("'{n}' not in scope")))
                    }
                    TypeError::Mismatch {
                        span,
                        expected,
                        found,
                    } => Some((span, format!("expected {expected}, got {found}"))),
                    TypeError::Scope { span, msg } | TypeError::Other { span, msg } => {
                        Some((span, msg.clone()))
                    }
                    // No span to point at; fall through to the plain message.
                    TypeError::Ice { .. } => None,
                };
                located.is_some_and(|(span, label)| {
                    write_report(
                        &map,
                        kind,
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
            return format!("{kind}: {self}");
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

#[allow(clippy::too_many_arguments)]
fn write_report(
    map: &SourceMap<'_>,
    kind: &str,
    name: &str,
    range: Range<usize>,
    msg: &str,
    label: &str,
    color: bool,
    out: &mut Vec<u8>,
) -> std::io::Result<()> {
    let n = map.prelude;
    let (src, name, range) = if range.start < n {
        (&map.full[..n], "<prelude>", range.start..range.end.min(n))
    } else {
        (map.user(), name, range.start - n..range.end - n)
    };
    // `Config::with_color(false)` suppresses every ANSI escape, so the label
    // hue below is rendered only when `color` is set.
    Report::build(ReportKind::Custom(kind, Color::Red), (name, range.clone()))
        .with_config(Config::default().with_color(color))
        .with_message(msg)
        .with_label(
            Label::new((name, range))
                .with_message(label)
                .with_color(Color::Red),
        )
        .finish()
        .write((name, Source::from(src)), out)
}
