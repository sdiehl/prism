/// The always-on prelude text prepended to every checked program; embedded here
/// because the span adjuster below must recognize and subtract it.
pub const PRELUDE: &str = include_str!("../../../../lib/prelude.pr");

/// The marker line stamped between the prelude and user code.
pub const PRELUDE_END_MARK: &str = "-- prism@prelude@end";

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
                custom_prelude_end(full)
            };
        Self { full, prelude }
    }

    #[must_use]
    pub fn user(&self) -> &'a str {
        &self.full[self.prelude..]
    }

    /// The full source, prelude prefix included.
    #[must_use]
    pub const fn full(&self) -> &'a str {
        self.full
    }

    /// Byte offset where the user's own source begins (0 when no prelude prefix
    /// is present). Spans below it belong to the prepended prelude.
    #[must_use]
    pub const fn prelude_len(&self) -> usize {
        self.prelude
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

// Locate the boundary a custom prelude stamped (`with_custom_prelude`): the
// byte offset just past the first `PRELUDE_END_MARK` line, or 0 when the source
// carries no custom prelude. The first occurrence is authoritative; the mark's
// spelling is not one ordinary source or the formatter produces.
fn custom_prelude_end(full: &str) -> usize {
    let line = format!("{PRELUDE_END_MARK}\n");
    if full.starts_with(&line) {
        return line.len();
    }
    let sep = format!("\n{line}");
    full.find(&sep).map_or(0, |pos| pos + sep.len())
}

// The line terminators the caret renderer splits on. A position quoted in a
// message and the one drawn in the caret row must come from the same line table,
// or one report names two different lines for one span. A carriage return
// followed by a line feed is one terminator, not two.
const LINE_SEPS: [char; 7] = [
    '\r', '\n', '\u{b}', '\u{c}', '\u{85}', '\u{2028}', '\u{2029}',
];

pub fn line_col(src: &str, byte: usize) -> (u32, u32) {
    let (mut line, mut col) = (1u32, 1u32);
    let mut after_cr = false;
    for (i, c) in src.char_indices() {
        if i >= byte {
            break;
        }
        if c == '\n' && after_cr {
            after_cr = false;
            continue;
        }
        after_cr = c == '\r';
        if LINE_SEPS.contains(&c) {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}
