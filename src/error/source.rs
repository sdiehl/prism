use crate::driver::{PRELUDE, PRELUDE_END_MARK};

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
    pub(crate) const fn full(&self) -> &'a str {
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

pub(crate) fn line_col(src: &str, byte: usize) -> (u32, u32) {
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

#[cfg(test)]
mod tests {
    use super::SourceMap;
    use crate::driver::{with_custom_prelude, with_prelude};

    // Diagnostics under a custom prelude must be user-relative, exactly like
    // the built-in path: the composed source carries the boundary mark, and
    // SourceMap reads it back. This was silently wrong (offset by the whole
    // custom prelude) before the mark existed.
    #[test]
    fn custom_prelude_positions_are_user_relative() {
        let user_src = "fn main() =\n  oops()\n";
        let full = with_custom_prelude("fn helper() = 1\nfn helper2() = 2", user_src);
        let map = SourceMap::new(&full);
        assert_eq!(map.user(), user_src);
        let off = map.prelude_len() + map.user().find("oops").unwrap();
        assert_eq!(map.at(off), "line 2:3");
    }

    // The built-in prelude path is unchanged: located by its known text, no
    // boundary mark involved.
    #[test]
    fn builtin_prelude_positions_are_user_relative() {
        let user_src = "fn main() = 1\n";
        let full = with_prelude(user_src);
        let map = SourceMap::new(&full);
        assert_eq!(map.user(), user_src);
        assert_eq!(map.at(map.prelude_len()), "line 1:1");
    }
}
