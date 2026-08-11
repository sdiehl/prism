//! `prism explain CODE`: the prose behind every diagnostic code.
//!
//! Each catalogued code carries a title, an explanation of what the compiler
//! saw, a minimal reproducing example, and the fix. Content is sharded by code
//! band so each band stays a readable file; the registry below concatenates the
//! shards. A coverage test pins that every code assigned in the two diagnostic
//! catalogues (`error/code.rs` constants and the `ErrKind::code()` table) has an
//! entry here, and that no entry names a dead code.

mod band_e6;
mod band_early;
mod band_late;
mod band_mid;

use crate::cli::CmdResult;
use crate::error::{Error, ERROR_CODE_DIGITS, ERROR_CODE_PREFIX};

const LOWERCASE_ERROR_CODE_PREFIX: char = 'e';

/// The full explanation behind one diagnostic code.
#[derive(Debug)]
pub struct Explanation {
    /// The stable code, spelled `Ennnn`.
    pub code: &'static str,
    /// A one-line title for the diagnostic.
    pub title: &'static str,
    /// What the compiler saw and why it is an error.
    pub prose: &'static str,
    /// A minimal program that reproduces the diagnostic.
    pub example: &'static str,
    /// How to repair the program.
    pub fix: &'static str,
}

/// Every shard, in band order. The registry is the concatenation.
const BANDS: &[&[Explanation]] = &[
    band_early::ENTRIES,
    band_mid::ENTRIES,
    band_e6::ENTRIES,
    band_late::ENTRIES,
];

/// Look up the explanation for a code spelled `Ennnn` (case-insensitive; a bare
/// `nnnn` is accepted).
#[must_use]
pub fn lookup(code: &str) -> Option<&'static Explanation> {
    let normalized = normalize(code)?;
    BANDS
        .iter()
        .flat_map(|band| band.iter())
        .find(|entry| entry.code == normalized)
}

/// All explanations, in band order.
pub fn all() -> impl Iterator<Item = &'static Explanation> {
    BANDS.iter().flat_map(|band| band.iter())
}

// Accept `E1001`, `e1001`, or `1001`; canonicalize to `E1001`.
fn normalize(code: &str) -> Option<String> {
    let digits = code
        .strip_prefix(ERROR_CODE_PREFIX)
        .or_else(|| code.strip_prefix(LOWERCASE_ERROR_CODE_PREFIX))
        .unwrap_or(code);
    if digits.len() == ERROR_CODE_DIGITS && digits.bytes().all(|b| b.is_ascii_digit()) {
        Some(format!("{ERROR_CODE_PREFIX}{digits}"))
    } else {
        None
    }
}

/// Render one explanation as the terminal page `prism explain` prints.
#[must_use]
pub fn render(entry: &Explanation) -> String {
    let mut out = format!("{}: {}\n\n", entry.code, entry.title);
    out.push_str(entry.prose);
    out.push_str("\n\nExample:\n\n");
    for line in entry.example.lines() {
        out.push_str("    ");
        out.push_str(line);
        out.push('\n');
    }
    out.push_str("\nFix: ");
    out.push_str(entry.fix);
    out.push('\n');
    out
}

// `prism explain CODE`: print the page for one diagnostic code.
pub fn explain_cmd(code: &str) -> CmdResult {
    lookup(code).map_or_else(
        || {
            Err((
                Error::ResolveCommand(format!(
                    "unknown diagnostic code `{code}`: codes are spelled Ennnn, as printed \
                     at the head of a diagnostic"
                )),
                String::new(),
                code.to_string(),
            ))
        },
        |entry| {
            print!("{}", render(entry));
            Ok(())
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE: Explanation = Explanation {
        code: "E1001",
        title: "a title",
        prose: "First line.\nSecond line.",
        example: "fn main() -> Int =\n  0",
        fix: "do the other thing",
    };

    // A code is copied off a terminal, where it may have been lowercased or
    // quoted without its prefix; all three spellings name one entry.
    #[test]
    fn normalize_accepts_the_spellings_a_user_types() {
        for spelling in ["E1001", "e1001", "1001"] {
            assert_eq!(normalize(spelling).as_deref(), Some("E1001"), "{spelling}");
        }
    }

    // Anything that is not four digits is not a code. Rejecting here is what
    // makes `lookup` on junk a clean "unknown code" rather than a silent miss
    // against a well-formed but absent entry.
    #[test]
    fn normalize_rejects_anything_else() {
        for junk in [
            "", "E", "E101", "E10010", "1O01", "E1001x", " E1001", "warning",
        ] {
            assert!(normalize(junk).is_none(), "{junk:?} must not normalize");
            assert!(lookup(junk).is_none(), "{junk:?} must not resolve");
        }
    }

    // The page is plain text a terminal prints verbatim: a `code: title` head,
    // the prose, the example indented one block, then the fix on one line.
    #[test]
    fn render_lays_out_the_page() {
        let expected = [
            "E1001: a title",
            "",
            "First line.",
            "Second line.",
            "",
            "Example:",
            "",
            "    fn main() -> Int =",
            "      0",
            "",
            "Fix: do the other thing",
            "",
        ]
        .join("\n");
        assert_eq!(render(&SAMPLE), expected);
    }
}
