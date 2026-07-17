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
//!
//! Two conveniences keep examples down to their intuition-pump line:
//!
//! - **Auto-import.** An example runs with its enclosing module glob-imported
//!   (`import Data.Tensor (..)` for an example in `Data.Tensor`), so the names
//!   being documented are simply in scope. The prelude documents itself and
//!   needs no import; an example that already imports its module is left alone
//!   (a duplicate glob would be harmless, but the intent reads better).
//! - **Hidden lines.** A code line beginning `# ` compiles as part of the
//!   example but never appears in rendered documentation: setup a reader does
//!   not need (an extra binding, a sample value) stays out of the page.

use std::fmt::Write as _;
use std::path::Path;

use crate::driver::{example_program, interpret_on, with_prelude};
use crate::names::ENTRY_POINT;
use crate::resolve::Root;

use super::check_quiet;

/// The fence language tag marking a runnable example (```` ```prism ````).
pub(crate) const FENCE_PRISM: &str = "prism";
/// The fence language tag marking an expected-output block (```` ```output ````)
/// that follows an example; see `super::accept`.
pub(crate) const FENCE_OUTPUT: &str = "output";
// Fence attributes that make a `prism` block a non-runnable reference block
// (generated signatures / declarations), never a doctest.
const REFERENCE_ATTRS: [&str; 2] = ["sig", "def"];
/// The hidden-line marker inside a ```` ```prism ```` fence: the line compiles
/// but is stripped from rendered docs (the doc-example convention Rust uses).
pub(crate) const HIDDEN_PREFIX: &str = "# ";
/// The fence attribute naming an example's enclosing module
/// (```` ```prism,mod=Data.Map ````). Stamped by the page renderer and consumed
/// by the book preprocessor, so both rebuild the same runnable program the
/// doctest runner checks.
pub(crate) const MOD_ATTR: &str = "mod=";
/// The prelude's dotted module name in doc specs; it documents itself, so its
/// examples never get an auto-import.
pub(crate) const PRELUDE_DOTTED: &str = "Prelude";

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Mode {
    Check,
    NoRun,
    Ignore,
    CompileFail,
}

/// One runnable example lifted from a docstring, tagged with where it came from
/// and the dotted module it documents (empty when none, e.g. an index page).
#[derive(Clone, Debug)]
pub(crate) struct Example {
    pub origin: String,
    pub module: String,
    pub code: String,
    pub mode: Mode,
}

/// Strip the hidden-line marker: `# code` compiles as `code`, a lone `#` as a
/// blank line, anything else unchanged. The marker sits at column 0 of the
/// code line and any code indentation follows it (`# ` then `  body`), so the
/// layout-sensitive indent survives the strip.
pub(crate) fn unhide(line: &str) -> &str {
    line.strip_prefix(HIDDEN_PREFIX)
        .map_or_else(|| if line == "#" { "" } else { line }, |code| code)
}

/// Whether a code line is hidden from rendered docs (see [`HIDDEN_PREFIX`]).
pub(crate) fn is_hidden(line: &str) -> bool {
    line == "#" || line.starts_with(HIDDEN_PREFIX)
}

/// Split an example into its leading `import` lines and the remaining code.
/// Imports must sit at the top of a program, so a doctest's own imports
/// (typically hidden `# import X (..)` preamble) are hoisted above the
/// implicit-`main` wrap rather than swallowed into the body. Returns the count
/// of leading lines consumed (imports and the blank lines between them) and the
/// remaining code.
pub(crate) fn split_imports(code: &str) -> (usize, String) {
    let lines: Vec<&str> = code.lines().collect();
    let mut last_import = None;
    for (index, line) in lines.iter().enumerate() {
        let t = line.trim();
        if t.starts_with("import ") {
            last_import = Some(index);
        } else if !t.is_empty() {
            break;
        }
    }
    let Some(last) = last_import else {
        return (0, code.to_string());
    };
    let mut rest = lines[last + 1..].join("\n");
    if code.ends_with('\n') {
        rest.push('\n');
    }
    (last + 1, rest)
}

/// Add the enclosing module import used by a doctest without adding its
/// implicit `main`. The browser stores this source beside the concise visible
/// snippet and performs the final wrapping when the reader runs it.
pub(crate) fn imported(module: &str, code: &str) -> String {
    if module.is_empty() || module == PRELUDE_DOTTED || code.contains(&format!("import {module}")) {
        return code.to_string();
    }
    format!("import {module} (..)\n\n{code}")
}

/// The program a doctest actually runs: the example's own leading imports, then
/// the rest wrapped as an implicit `main` where needed, all under the enclosing
/// module's glob import. Imports go outside the wrap (an import inside a
/// function body would not parse); the module import is skipped for the
/// prelude, for module-less origins, and when the example already imports the
/// module itself.
pub(crate) fn runnable(module: &str, code: &str) -> String {
    let imported = imported(module, code);
    let (consumed, rest) = split_imports(&imported);
    let mut own = String::new();
    for line in imported
        .lines()
        .take(consumed)
        .filter(|line| !line.trim().is_empty())
    {
        writeln!(own, "{line}").expect("writing to a String cannot fail");
    }
    format!("{own}{}", example_program(&rest))
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
pub(crate) fn mode_of(info: &str) -> Mode {
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
pub(crate) fn lang_of(info: &str) -> &str {
    info.split([',', ' ']).next().unwrap_or("").trim()
}

// Whether a `prism` fence carries a reference attribute (`sig`/`def`), marking a
// generated signature/declaration block that is shown but never executed.
pub(crate) fn is_reference_fence(info: &str) -> bool {
    info.split([',', ' '])
        .any(|t| REFERENCE_ATTRS.contains(&t.trim()))
}

/// Pull every ```` ```prism ```` fenced block out of one docstring, tagging each
/// with `origin` for diagnostics and `module` (the enclosing dotted module) for
/// the auto-import. Hidden-line markers are stripped here, so `code` is always
/// the compilable text.
pub(crate) fn examples_in(origin: &str, module: &str, doc: &str) -> Vec<Example> {
    let mut out = Vec::new();
    let mut lines = doc.lines();
    while let Some(line) = lines.next() {
        let trimmed = line.trim_start();
        let Some(info) = trimmed.strip_prefix("```") else {
            continue;
        };
        // `sig`/`def` are non-runnable reference blocks (generated signatures and
        // declarations), never doctests.
        let is_doctest = lang_of(info) == FENCE_PRISM && !is_reference_fence(info);
        let mode = mode_of(info);
        let mut code = String::new();
        for body in lines.by_ref() {
            if body.trim_start().starts_with("```") {
                break;
            }
            code.push_str(unhide(body));
            code.push('\n');
        }
        if is_doctest {
            out.push(Example {
                origin: origin.to_string(),
                module: module.to_string(),
                code,
                mode,
            });
        }
    }
    out
}

/// Compile (and, where applicable, run) each example against the same explicit
/// module search path.
pub(crate) fn run(examples: &[Example], roots: &[Root], _base: &Path) -> Report {
    let mut r = Report::default();
    for ex in examples {
        if ex.mode == Mode::Ignore {
            r.ignored += 1;
            continue;
        }
        // An example without `main` (a bare expression or `let`-block) is wrapped
        // as the body of an implicit `main`, so it runs like a REPL line.
        let full = with_prelude(&runnable(&ex.module, &ex.code));
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
                    match interpret_on(&full, roots) {
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

/// Run every runnable example and collect `(location, output)` for those that
/// actually executed: a `Mode::Check` example defining `main`. Non-running
/// examples (`no_run`, `ignore`, `compile_fail`, or an example with no `main`)
/// and any that fail to run produce no entry, so a manifest records the output of
/// doctests that ran, nothing more.
pub(crate) fn ran_outputs(
    examples: &[Example],
    roots: &[Root],
    base: &Path,
) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for ex in examples {
        if ex.mode != Mode::Check {
            continue;
        }
        if let Ok(lines) = actual_output(&ex.module, &ex.code, roots, base) {
            out.push((ex.origin.clone(), lines.join("\n")));
        }
    }
    out
}

/// Run one example as an implicit-`main` program and render its observable
/// output as expectation lines: the `print` transcript if it printed anything,
/// otherwise the result value. Each line is trailing-trimmed so it round-trips
/// through the source formatter. Returns a human-readable reason on a
/// compile/run failure. Shared by the expect-block checker and `--accept`
/// rewriter (`super::accept`) so both agree on what "actual output" means.
pub(crate) fn actual_output(
    module: &str,
    code: &str,
    roots: &[Root],
    _base: &Path,
) -> Result<Vec<String>, String> {
    let full = with_prelude(&runnable(module, code));
    let checked = check_quiet(&full, roots).map_err(|e| format!("compile error: {e}"))?;
    if !checked.decls.iter().any(|d| d.name == ENTRY_POINT) {
        return Err("example has no `main` and no expression to run".into());
    }
    let run = interpret_on(&full, roots).map_err(|e| format!("run error: {e}"))?;
    let text = if run.term.is_empty() {
        run.value.show()
    } else {
        run.term
    };
    Ok(text.lines().map(|l| l.trim_end().to_string()).collect())
}
