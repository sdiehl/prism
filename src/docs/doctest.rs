//! Doctests: runnable code examples embedded in `-- |` docstrings.
//!
//! A fenced ```` ```prism ```` block inside a docstring is a doctest. The fence
//! info string carries attributes controlling what happens to it:
//!
//! - (none)        type-check it, and run it if it defines `main`
//! - `no_run`      type-check only, never run
//! - `ignore`      skip entirely (illustrative, not expected to compile)
//! - `compile_fail` expect a type error (fail the test if it compiles)
//!
//! `prism docs --test` extracts every example and executes it, keeping the
//! documentation compilable and in sync with the code. Non-`prism` fences
//! (```` ```text ````, ```` ```console ````) are never treated as doctests.

use std::path::Path;

use crate::driver::{example_program, interpret_at, with_prelude};
use crate::names::ENTRY_POINT;
use crate::resolve::Root;

use super::check_quiet;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Mode {
    Check,
    NoRun,
    Ignore,
    CompileFail,
}

/// One runnable example lifted from a docstring, tagged with where it came from.
#[derive(Clone, Debug)]
pub(crate) struct Example {
    pub origin: String,
    pub code: String,
    pub mode: Mode,
}

/// The result of running a batch of doctests.
#[derive(Default, Debug)]
pub struct Report {
    pub passed: usize,
    pub ignored: usize,
    pub failures: Vec<(String, String)>,
}

// Map fence attributes to a mode; unknown attributes are ignored so a future
// attribute does not break an older compiler.
fn mode_of(info: &str) -> Mode {
    for tok in info
        .split([',', ' '])
        .map(str::trim)
        .filter(|t| !t.is_empty())
    {
        match tok {
            "ignore" => return Mode::Ignore,
            "no_run" => return Mode::NoRun,
            "compile_fail" => return Mode::CompileFail,
            _ => {}
        }
    }
    Mode::Check
}

// The language tag of a fence info string is the first token (`prism`,
// `prism,no_run`, `text`, ...).
fn lang_of(info: &str) -> &str {
    info.split([',', ' ']).next().unwrap_or("").trim()
}

/// Pull every ```` ```prism ```` fenced block out of one docstring, tagging each
/// with `origin` for diagnostics.
pub(crate) fn examples_in(origin: &str, doc: &str) -> Vec<Example> {
    let mut out = Vec::new();
    let mut lines = doc.lines();
    while let Some(line) = lines.next() {
        let trimmed = line.trim_start();
        let Some(info) = trimmed.strip_prefix("```") else {
            continue;
        };
        // `sig`/`def` are non-runnable reference blocks (generated signatures and
        // declarations), never doctests.
        let is_doctest = lang_of(info) == "prism"
            && !info
                .split([',', ' '])
                .any(|t| matches!(t.trim(), "sig" | "def"));
        let mode = mode_of(info);
        let mut code = String::new();
        for body in lines.by_ref() {
            if body.trim_start().starts_with("```") {
                break;
            }
            code.push_str(body);
            code.push('\n');
        }
        if is_doctest {
            out.push(Example {
                origin: origin.to_string(),
                code,
                mode,
            });
        }
    }
    out
}

/// Compile (and, where applicable, run) each example, collecting a report. Type
/// checking resolves against `roots`; running an example that defines `main`
/// resolves imports relative to `base`.
pub(crate) fn run(examples: &[Example], roots: &[Root], base: &Path) -> Report {
    let mut r = Report::default();
    for ex in examples {
        if ex.mode == Mode::Ignore {
            r.ignored += 1;
            continue;
        }
        // An example without `main` (a bare expression or `let`-block) is wrapped
        // as the body of an implicit `main`, so it runs like a REPL line.
        let full = with_prelude(&example_program(&ex.code));
        let checked = check_quiet(&full, roots);
        if ex.mode == Mode::CompileFail {
            match checked {
                Ok(_) => r.failures.push((
                    ex.origin.clone(),
                    "expected a compile error, but it compiled".into(),
                )),
                Err(_) => r.passed += 1,
            }
            continue;
        }
        match checked {
            Err(e) => r
                .failures
                .push((ex.origin.clone(), format!("compile error: {e}"))),
            Ok(checked) => {
                let has_main = checked.decls.iter().any(|d| d.name == ENTRY_POINT);
                if ex.mode == Mode::Check && has_main {
                    match interpret_at(&full, base) {
                        Ok(_) => r.passed += 1,
                        Err(e) => r
                            .failures
                            .push((ex.origin.clone(), format!("run error: {e}"))),
                    }
                } else {
                    r.passed += 1;
                }
            }
        }
    }
    r
}
