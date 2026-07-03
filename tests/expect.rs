//! `prism docs --accept`: the inline expect-block rewriter. A stale `output`
//! block is rewritten in place, exactly and minimally, and the result is
//! formatter-idempotent; an already-correct block is left untouched.

use std::path::PathBuf;

use prism::{accept, default_roots, format, ExpectFile};

// A fresh temp path unique to this process and `tag`, so parallel test binaries
// never collide on the same fixture file.
fn temp_pr(tag: &str) -> PathBuf {
    let name = format!("prism_expect_{}_{}.pr", std::process::id(), tag);
    std::env::temp_dir().join(name)
}

fn write_and_accept(path: &PathBuf, source: &str) -> prism::ExpectReport {
    std::fs::write(path, source).unwrap();
    let files = vec![ExpectFile {
        path: path.clone(),
        source: source.to_string(),
    }];
    let base = path.parent().unwrap();
    accept(&files, &default_roots(base), base, true)
}

const STALE: &str = "\
-- | Doc.
--
-- ```prism
-- 1 + 1
-- ```
-- ```output
-- 999
-- ```
pub fn noop(x) = x
";

// The same file with the one stale expectation line corrected to the real value.
const BLESSED: &str = "\
-- | Doc.
--
-- ```prism
-- 1 + 1
-- ```
-- ```output
-- 2
-- ```
pub fn noop(x) = x
";

#[test]
fn accept_rewrites_stale_exactly_and_idempotently() {
    let path = temp_pr("stale");
    let report = write_and_accept(&path, STALE);
    assert_eq!(report.rewritten.len(), 1, "one block should be rewritten");
    assert!(
        report.failures.is_empty(),
        "no failures: {:?}",
        report.failures
    );

    let got = std::fs::read_to_string(&path).unwrap();
    assert_eq!(got, BLESSED, "rewrite must be exact and minimal");

    // Every line except the single expectation line is byte-identical.
    for (a, b) in STALE.lines().zip(BLESSED.lines()) {
        if a != b {
            assert_eq!(
                (a, b),
                ("-- 999", "-- 2"),
                "only the expectation line changed"
            );
        }
    }

    // The blessed file is formatter-idempotent and the doctest now passes.
    assert_eq!(
        format(&got).unwrap(),
        got,
        "blessed file must be fmt-stable"
    );
    let second = write_and_accept(&path, &got);
    assert!(second.rewritten.is_empty(), "second bless must be a no-op");
    assert!(second.failures.is_empty());

    std::fs::remove_file(&path).ok();
}

#[test]
fn accept_leaves_correct_block_untouched() {
    let path = temp_pr("correct");
    let report = write_and_accept(&path, BLESSED);
    assert!(report.rewritten.is_empty(), "nothing to rewrite");
    assert!(report.failures.is_empty());
    assert_eq!(report.checked, 1, "the block was still checked");
    assert_eq!(
        std::fs::read_to_string(&path).unwrap(),
        BLESSED,
        "an already-correct file is byte-identical"
    );
    std::fs::remove_file(&path).ok();
}

#[test]
fn accept_refuses_when_file_changed_on_disk() {
    let path = temp_pr("changed");
    // On disk the file already carries the correct expectation, but the source we
    // parsed (and would rewrite from) is the stale one: a concurrent edit.
    std::fs::write(&path, BLESSED).unwrap();
    let files = vec![ExpectFile {
        path: path.clone(),
        source: STALE.to_string(),
    }];
    let base = path.parent().unwrap();
    let report = accept(&files, &default_roots(base), base, true);
    assert!(
        report.rewritten.is_empty(),
        "must not rewrite a changed file"
    );
    assert_eq!(report.failures.len(), 1, "the refusal is reported");
    assert_eq!(
        std::fs::read_to_string(&path).unwrap(),
        BLESSED,
        "the on-disk file is left as it was found"
    );
    std::fs::remove_file(&path).ok();
}

#[test]
fn accept_fills_empty_block() {
    let path = temp_pr("empty");
    let source = "\
-- | Doc.
--
-- ```prism
-- 1 + 1
-- ```
-- ```output
-- ```
pub fn noop(x) = x
";
    let report = write_and_accept(&path, source);
    assert_eq!(report.rewritten.len(), 1, "empty block gets filled");
    let got = std::fs::read_to_string(&path).unwrap();
    assert_eq!(got, BLESSED, "first bless fills an empty expectation");
    assert_eq!(format(&got).unwrap(), got, "filled file is fmt-stable");
    std::fs::remove_file(&path).ok();
}
