//! Prelude name capture: `--warn-prelude-capture`, on by default.
//!
//! Top-level names share one flat namespace, and the prelude opens a set of
//! library names into it unqualified. A user definition of one of those names
//! wins it for the whole file, silently redirecting every unqualified use. The
//! diagnostic names the library symbol that was displaced; `strict` turns the
//! capture into a compile error with its declaration-family E-code.

use std::path::Path;

use prism::{check_validated_on_in, default_roots, with_prelude, Config, Error, WarnDupes};

// Type-check `src` under a capture severity, returning its warning messages
// (or the error a strict run fails with).
fn check(src: &str, mode: WarnDupes) -> Result<Vec<String>, Error> {
    let mut cfg = Config::default();
    cfg.flags.warn_prelude_capture = mode;
    let checked = check_validated_on_in(&with_prelude(src), &default_roots(Path::new(".")), &cfg)?;
    Ok(checked.warnings.iter().map(|w| w.msg.clone()).collect())
}

// `count` is opened unqualified by the prelude's `import Data.List (..)`, so a
// top-level definition of it takes the name from the library function.
const CAPTURE: &str = "fn count(xs) = 0\nfn main() = println(count([1, 2]))\n";

// No prelude-opened name is touched: `tally` is the author's alone.
const NO_CAPTURE: &str = "fn tally(xs) = 0\nfn main() = println(tally([1, 2]))\n";

#[test]
fn capture_names_the_definition_and_the_library_symbol() {
    let msgs = check(CAPTURE, WarnDupes::Warn).expect("program type checks");
    assert!(
        msgs.iter()
            .any(|m| m.contains("`count`") && m.contains("Data.List.count")),
        "expected a capture warning naming both origins, got {msgs:?}"
    );
}

#[test]
fn capture_is_flagged_by_default() {
    let checked = check_validated_on_in(
        &with_prelude(CAPTURE),
        &default_roots(Path::new(".")),
        &Config::default(),
    )
    .expect("program type checks");
    assert!(
        checked
            .warnings
            .iter()
            .any(|w| w.msg.contains("Data.List.count")),
        "prelude capture must be flagged by default, got {:?}",
        checked.warnings
    );
}

#[test]
fn a_name_of_your_own_is_not_a_capture() {
    let msgs = check(NO_CAPTURE, WarnDupes::Warn).expect("program type checks");
    assert!(
        !msgs.iter().any(|m| m.contains("the prelude opens")),
        "an unclaimed name must not warn, got {msgs:?}"
    );
}

#[test]
fn off_mode_reports_nothing() {
    let msgs = check(CAPTURE, WarnDupes::Off).expect("program type checks");
    assert!(
        !msgs.iter().any(|m| m.contains("the prelude opens")),
        "off mode must not flag a capture, got {msgs:?}"
    );
}

#[test]
fn strict_mode_fails_with_declaration_code() {
    let err = check(CAPTURE, WarnDupes::Strict).expect_err("strict mode fails the compile");
    assert_eq!(err.code().to_string(), "E6073");
}

#[test]
fn strict_mode_accepts_a_program_that_captures_nothing() {
    check(NO_CAPTURE, WarnDupes::Strict).expect("no capture, so strict mode has nothing to reject");
}
