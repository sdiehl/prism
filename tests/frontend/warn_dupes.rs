//! Duplicate-definition detection: `--warn-dupes` (own clones, off by default)
//! and `--warn-stdlib-dupes` (reimplementing a library function, on by default).
//!
//! Two definitions that elaborate to the same behavior hash are flagged as a
//! clone group, and a user definition matching a standard-library function is
//! named as a reimplementation. `strict` turns either into a compile error with
//! its declaration-family E-code.

use std::path::Path;

use prism::{check_validated_on_in, default_roots, with_prelude, Config, Error, WarnDupes};

// Type-check `src` under the two independent severities, returning its warning
// messages (or the error).
fn check(src: &str, clone: WarnDupes, stdlib: WarnDupes) -> Result<Vec<String>, Error> {
    let mut cfg = Config::default();
    cfg.flags.warn_dupes = clone;
    cfg.flags.warn_stdlib_dupes = stdlib;
    let checked = check_validated_on_in(&with_prelude(src), &default_roots(Path::new(".")), &cfg)?;
    Ok(checked.warnings.iter().map(|w| w.msg.clone()).collect())
}

// Type-check `src` under the shipped defaults (own clones off, stdlib on).
fn check_default(src: &str) -> Result<Vec<String>, Error> {
    let checked = check_validated_on_in(
        &with_prelude(src),
        &default_roots(Path::new(".")),
        &Config::default(),
    )?;
    Ok(checked.warnings.iter().map(|w| w.msg.clone()).collect())
}

// Two structurally identical user functions share one behavior hash.
const CLONES: &str = "fn dupeAlpha(x: Int) = x + 1\n\
                      fn dupeBeta(x: Int) = x + 1\n\
                      fn main() = dupeAlpha(0) + dupeBeta(0)\n";

// A verbatim reimplementation of the prelude's `id`.
const STDLIB_DUPE: &str = "fn myIdentity(x) = x\nfn main() = myIdentity(0)\n";

#[test]
fn clone_group_is_reported_with_all_names() {
    let msgs = check(CLONES, WarnDupes::Warn, WarnDupes::Off).expect("program type checks");
    assert!(
        msgs.iter().any(|m| m.contains("dupeAlpha")
            && m.contains("dupeBeta")
            && m.contains("identical in behavior")),
        "expected a clone-group warning naming both, got {msgs:?}"
    );
}

#[test]
fn reimplementing_a_stdlib_function_names_it() {
    // `fn id(x) = x` lives in the prelude; a verbatim reimplementation matches it.
    let msgs = check(STDLIB_DUPE, WarnDupes::Off, WarnDupes::Warn).expect("program type checks");
    assert!(
        msgs.iter()
            .any(|m| m.contains("myIdentity") && m.contains("reimplements the standard library")),
        "expected a stdlib-reimplementation warning, got {msgs:?}"
    );
}

#[test]
fn stdlib_reimplementation_is_flagged_by_default() {
    // The stdlib-dupe warning ships on: the shipped-default config flags it with no
    // knob set.
    let msgs = check_default(STDLIB_DUPE).expect("program type checks");
    assert!(
        msgs.iter()
            .any(|m| m.contains("myIdentity") && m.contains("reimplements the standard library")),
        "stdlib reimplementation must be flagged by default, got {msgs:?}"
    );
}

#[test]
fn own_clone_group_is_silent_by_default() {
    // The own-clone warning ships off: identical user helpers pass the default
    // config without a clone-group diagnostic.
    let msgs = check_default(CLONES).expect("program type checks");
    assert!(
        !msgs.iter().any(|m| m.contains("identical in behavior")),
        "own clones must not be flagged by default, got {msgs:?}"
    );
}

#[test]
fn off_mode_reports_nothing() {
    let msgs = check(CLONES, WarnDupes::Off, WarnDupes::Off).expect("program type checks");
    assert!(
        !msgs.iter().any(|m| m.contains("identical in behavior")),
        "off mode must not flag duplicates, got {msgs:?}"
    );
}

#[test]
fn strict_clone_mode_fails_with_declaration_code() {
    let err = check(CLONES, WarnDupes::Strict, WarnDupes::Off)
        .expect_err("strict own-clone mode fails the compile");
    assert_eq!(err.code().to_string(), "E6063");
}

#[test]
fn strict_stdlib_mode_fails_with_declaration_code() {
    let err = check(STDLIB_DUPE, WarnDupes::Off, WarnDupes::Strict)
        .expect_err("strict stdlib mode fails the compile");
    assert_eq!(err.code().to_string(), "E6064");
}
