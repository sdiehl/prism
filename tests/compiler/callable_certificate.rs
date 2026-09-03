use std::fmt::Write;
use std::fs;
use std::path::{Path, PathBuf};

use rstest::rstest;

#[rstest]
fn callable_certificate_accepts_expected_programs(
    #[files("tests/cases/callable_certificate/accept/*.pr")] path: PathBuf,
) {
    let src = fs::read_to_string(&path).unwrap();
    let got = prism::dump("core", &src);
    assert!(
        got.is_ok(),
        "callable certificate unexpectedly rejected `{}`:\n{got:?}",
        path.display()
    );
}

#[rstest]
fn callable_certificate_rejects_expected_programs(
    #[files("tests/cases/callable_certificate/reject/*.pr")] path: PathBuf,
) {
    let src = fs::read_to_string(&path).unwrap();
    let got = prism::dump("core", &src);
    assert!(
        got.is_err(),
        "callable certificate unexpectedly accepted `{}`",
        path.display()
    );
}

#[test]
fn callable_certificate_diagnostics_are_snapshotted() {
    let mut paths = fixture_paths("tests/cases/callable_certificate/reject");
    paths.sort();

    let mut out = String::new();
    for path in paths {
        let src = fs::read_to_string(&path).unwrap();
        out.push_str("=== ");
        out.push_str(&case_name(&path));
        out.push_str(" ===\n");
        writeln!(
            out,
            "{}",
            prism::dump("core", &src).expect_err("case must fail the callable certificate")
        )
        .unwrap();
    }
    insta::with_settings!({
        snapshot_path => "../snapshots",
        prepend_module_to_snapshot => false,
    }, {
        insta::assert_snapshot!("callable_certificate__callable_certificate_diagnostics", out);
    });
}

#[test]
fn callable_demand_erases_from_executable_core() {
    let annotated =
        fs::read_to_string("tests/cases/callable_certificate/accept/certified_declared_callee.pr")
            .unwrap();
    let plain = annotated.replace("((Int) -> Int) @ noalloc", "(Int) -> Int");
    assert_ne!(annotated, plain, "the twin must actually drop the demand");
    assert_eq!(
        prism::dump("lowered", &annotated).unwrap(),
        prism::dump("lowered", &plain).unwrap(),
        "an accepted demand must erase before executable Core"
    );
}

fn fixture_paths(dir: &str) -> Vec<PathBuf> {
    fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "pr"))
        .collect()
}

fn case_name(path: &Path) -> String {
    path.file_stem()
        .unwrap()
        .to_string_lossy()
        .replace('_', " ")
}
