//! Expect blocks: auto-updating inline output expectations for doctests.
//!
//! A ```` ```prism ```` doctest inside a `-- |` doc comment may be followed
//! immediately by a ```` ```output ```` block holding the example's expected
//! observable output (its `print` transcript, or the result value when it prints
//! nothing). `prism docs --test` checks each expectation; `prism docs --test
//! --accept` (alias `--bless`) rewrites a stale or empty block in place with the
//! actual output, the way `ppx_expect` rewrites `[%expect]`.
//!
//! The rewriter works on raw source lines, never the rendered prose, so it
//! touches only the expectation body: it keeps every code line, the `--` comment
//! prefixes, the indentation, and the surrounding blank lines byte-for-byte. Only
//! the lines between an `output` fence and its close are replaced, so a rewritten
//! file stays formatter-idempotent and the doctest passes on the next run.

use std::fs;
use std::ops::Range;
use std::path::{Path, PathBuf};

use crate::resolve::Root;

use super::doctest::{
    actual_output, is_reference_fence, lang_of, mode_of, unhide, Mode, FENCE_OUTPUT, FENCE_PRISM,
};
use super::extract::strip;

// The CommonMark fenced-code delimiter.
const FENCE_MARK: &str = "```";
// The characters a line-comment doc marker is built from before a fence: the
// `--` opener plus the optional `|`/`^` doc sigils and spacing.
const DOC_MARKER_CHARS: [char; 3] = [' ', '|', '^'];

/// A source file to check or rewrite.
///
/// Carries its path on disk, the source text that was parsed (used to detect an
/// on-disk change before writing), and the dotted module it defines (the
/// doctest auto-import; see `doctest::runnable`).
#[derive(Debug)]
pub struct ExpectFile {
    pub path: PathBuf,
    pub source: String,
    pub module: String,
}

/// The outcome of an expect pass, reported loudly like `just snap`.
#[derive(Default, Debug)]
pub struct ExpectReport {
    /// How many expect blocks were examined.
    pub checked: usize,
    /// `file:line` origins whose expectation was rewritten (accept mode only).
    pub rewritten: Vec<String>,
    /// `file:line` origin plus reason for each block that failed to run, or (in
    /// check mode) whose expectation did not match.
    pub failures: Vec<(String, String)>,
}

// One `prism` doctest paired with the `output` block directly beneath it.
struct Block {
    origin: String,
    code: String,
    mode: Mode,
    // The output block's body: the line range between the fences (exclusive), in
    // the file's line vector. An empty range is an empty `output` block.
    body: Range<usize>,
    // The exact text before the fence backticks on the `output` opener (indent +
    // `-- `), reused verbatim to prefix each rewritten body line.
    prefix: String,
    expected: Vec<String>,
}

/// Check (or, with `write`, rewrite) the expect blocks in every file. Doctests
/// resolve against `roots`; examples run relative to `base`.
#[must_use]
pub fn accept(files: &[ExpectFile], roots: &[Root], base: &Path, write: bool) -> ExpectReport {
    let mut report = ExpectReport::default();
    for file in files {
        accept_file(file, roots, base, write, &mut report);
    }
    report
}

fn accept_file(
    file: &ExpectFile,
    roots: &[Root],
    base: &Path,
    write: bool,
    report: &mut ExpectReport,
) {
    let disp = file.path.display().to_string();
    let lines: Vec<&str> = file.source.split('\n').collect();
    let blocks = scan(&disp, &lines);
    if blocks.is_empty() {
        return;
    }

    // Collect the edits first (ascending by position), then apply them bottom-up
    // so an earlier block's line range is never shifted by a later rewrite.
    let mut edits: Vec<(Range<usize>, Vec<String>, String)> = Vec::new();
    for blk in &blocks {
        if blk.mode != Mode::Check {
            continue;
        }
        report.checked += 1;
        match actual_output(&file.module, &blk.code, roots, base) {
            Err(reason) => report.failures.push((blk.origin.clone(), reason)),
            Ok(actual) if actual == blk.expected => {}
            Ok(actual) => {
                let replacement = reflow(&blk.prefix, &actual);
                if write {
                    edits.push((blk.body.clone(), replacement, blk.origin.clone()));
                } else {
                    report
                        .failures
                        .push((blk.origin.clone(), mismatch_reason(&blk.expected, &actual)));
                }
            }
        }
    }

    if edits.is_empty() {
        return;
    }

    // Refuse to write if the file changed on disk since it was parsed.
    if fs::read_to_string(&file.path).ok().as_deref() != Some(file.source.as_str()) {
        for (_, _, origin) in &edits {
            report.failures.push((
                origin.clone(),
                "file changed on disk since parse; not rewritten".into(),
            ));
        }
        return;
    }

    let mut out: Vec<String> = lines.iter().map(|s| (*s).to_string()).collect();
    for (range, replacement, origin) in edits.iter().rev() {
        out.splice(range.clone(), replacement.clone());
        report.rewritten.push(origin.clone());
    }
    report.rewritten.reverse();
    match fs::write(&file.path, out.join("\n")) {
        Ok(()) => {}
        Err(e) => report.failures.push((disp, format!("write failed: {e}"))),
    }
}

// Find every `prism` doctest that is immediately followed by an `output` block.
fn scan(disp: &str, lines: &[&str]) -> Vec<Block> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        let Some((_, info)) = doc_fence(lines[i]) else {
            i += 1;
            continue;
        };
        if lang_of(info) != FENCE_PRISM || is_reference_fence(info) {
            i += 1;
            continue;
        }
        let open = i;
        let mode = mode_of(info);
        let close = fence_close(lines, open + 1);
        // The `output` block, if it opens on the very next line.
        if let Some((prefix, out_info)) = lines.get(close + 1).and_then(|l| doc_fence(l)) {
            if lang_of(out_info) == FENCE_OUTPUT {
                let out_open = close + 1;
                let out_close = fence_close(lines, out_open + 1);
                if out_close < lines.len() {
                    let mut code = String::new();
                    for l in &lines[open + 1..close] {
                        code.push_str(unhide(strip(l).trim_end()));
                        code.push('\n');
                    }
                    let expected = lines[out_open + 1..out_close]
                        .iter()
                        .map(|l| strip(l).trim_end().to_string())
                        .collect();
                    out.push(Block {
                        origin: format!("{disp}:{}", open + 1),
                        code,
                        mode,
                        body: out_open + 1..out_close,
                        prefix: prefix.to_string(),
                        expected,
                    });
                    i = out_close + 1;
                    continue;
                }
            }
        }
        i = close + 1;
    }
    out
}

// The index of the closing fence at or after `from`, or `lines.len()` if the
// block is unterminated.
fn fence_close(lines: &[&str], from: usize) -> usize {
    (from..lines.len())
        .find(|&j| doc_fence(lines[j]).is_some())
        .unwrap_or(lines.len())
}

// If `line` is a doc-comment line carrying a fence, return the text before the
// backticks (indent + comment marker) and the fence info string. A fence is only
// recognized inside a line comment, so a `` ``` `` inside code is never matched.
fn doc_fence(line: &str) -> Option<(&str, &str)> {
    let mark = line.find(FENCE_MARK)?;
    let (before, rest) = line.split_at(mark);
    let marker = before.trim_start().strip_prefix("--")?;
    (marker.chars().all(|c| DOC_MARKER_CHARS.contains(&c)))
        .then(|| (before, rest[FENCE_MARK.len()..].trim()))
}

// Prefix each actual-output line with the block's comment prefix, trimming any
// trailing space so an empty output line collapses to a bare `--`.
fn reflow(prefix: &str, actual: &[String]) -> Vec<String> {
    actual
        .iter()
        .map(|l| format!("{prefix}{l}").trim_end().to_string())
        .collect()
}

fn mismatch_reason(expected: &[String], actual: &[String]) -> String {
    format!(
        "expected output does not match; run with --accept to update\n  expected: {}\n  actual:   {}",
        expected.join("\\n"),
        actual.join("\\n")
    )
}
