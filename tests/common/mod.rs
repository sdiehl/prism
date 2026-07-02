//! Corpus discovery and interpreter-reference helpers shared by the parity
//! oracles (`tests/parity.rs`, `tests/tier_parity.rs`). One definition of "the
//! runnable corpus" keeps the two gates diffing the same programs.

// Each test target compiles this module independently and not every target
// uses every helper, so per-target dead-code analysis would otherwise warn. A
// test binary is its own crate root, so `pub` here is crate-visible only;
// rustc's unreachable_pub and clippy's redundant_pub_crate disagree about the
// spelling, and we side with plain `pub`.
#![allow(dead_code, unreachable_pub)]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, fs};

pub fn cc() -> String {
    env::var("PRISM_CC").unwrap_or_else(|_| "clang".into())
}

pub fn have(tool: &str) -> bool {
    Command::new(tool)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success())
}

/// Assert a C compiler is reachable, panicking with an actionable message if
/// not. The native oracles are meaningless without one, so its absence fails
/// the test loudly rather than passing vacuously.
pub fn require_cc() {
    assert!(
        have(&cc()),
        "C compiler `{}` not found (set PRISM_CC). The native parity oracle \
         requires it; install clang or LLVM so the native backend is exercised.",
        cc()
    );
}

pub fn source(path: &Path) -> String {
    prism::with_prelude(&fs::read_to_string(path).unwrap())
}

/// The interpreter's real terminal output, byte-for-byte what a native binary's
/// stdout must equal. `term` (not a join over `out`) preserves the
/// print/println distinction: a bare `print` adds no newline.
pub fn interpreted(full: &str) -> String {
    prism::interpret(full).unwrap().term
}

/// The runnable corpus: every example/run-case the interpreter executes cleanly
/// on empty stdin, restricted to on-platform programs. The interpret-Ok filter
/// excludes error cases, no-`main` library files, and the interactive examples
/// that block on input; the off-platform filter excludes file/env IO whose
/// native and interpreted runs are not a pure function of the source.
pub fn corpus() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut out = Vec::new();
    for dir in ["examples", "tests/cases/run"] {
        for entry in fs::read_dir(root.join(dir)).unwrap().flatten() {
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) != Some("pr") {
                continue;
            }
            let full = source(&path);
            let on_platform =
                prism::off_platform_builtins(&full, root).is_ok_and(|ops| ops.is_empty());
            if on_platform && prism::interpret(&full).is_ok() {
                out.push(path);
            }
        }
    }
    out.sort();
    out
}

/// Every committed `.pr` under the corpus directories, before the runtime
/// filter. The corpus floor is derived from this so a change that silently
/// breaks interpretation of many programs shrinks the oracle loudly, not
/// quietly.
pub fn candidate_count() -> usize {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut n = 0;
    for dir in ["examples", "tests/cases/run"] {
        for entry in fs::read_dir(root.join(dir)).unwrap().flatten() {
            if entry.path().extension().and_then(|e| e.to_str()) == Some("pr") {
                n += 1;
            }
        }
    }
    n
}
