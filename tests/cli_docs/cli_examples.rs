use std::fs;
use std::path::{Path, PathBuf};
use std::process::{self, Command};

const EXAMPLES_DIR: &str = "examples";
const ALPHA_EXAMPLE: &str = "a.pr";
const BETA_EXAMPLE: &str = "b.pr";
const BETA_INPUT: &str = "b.in";
const BAD_EXAMPLE: &str = "bad.pr";
const GOOD_EXAMPLE: &str = "good.pr";

fn temp_dir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("prism_{name}_{}", process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn write_example(dir: &Path, name: &str, src: &str) {
    fs::write(dir.join(name), src).unwrap();
}

#[test]
fn run_examples_defaults_to_examples_dir_in_sorted_order() {
    let dir = temp_dir("examples_default");
    let examples = dir.join(EXAMPLES_DIR);
    fs::create_dir_all(&examples).unwrap();
    write_example(&examples, BETA_EXAMPLE, "fn main() = println(read_int())\n");
    write_example(&examples, BETA_INPUT, "2\n");
    write_example(&examples, ALPHA_EXAMPLE, "fn main() = println(1)\n");

    let out = Command::new(env!("CARGO_BIN_EXE_prism"))
        .current_dir(&dir)
        .arg("run")
        .arg("--examples")
        .output()
        .unwrap();
    assert!(out.status.success(), "run --examples failed: {out:?}");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let alpha = stdout.find("ok examples/a.pr").unwrap_or_else(|| {
        panic!("missing sorted alpha example in stdout:\n{stdout}");
    });
    let beta = stdout.find("ok examples/b.pr").unwrap_or_else(|| {
        panic!("missing sorted beta example in stdout:\n{stdout}");
    });
    assert!(alpha < beta, "examples must run in sorted order:\n{stdout}");
    assert!(
        stdout.contains("examples: 2 passed"),
        "missing pass summary:\n{stdout}"
    );

    let empty = Command::new(env!("CARGO_BIN_EXE_prism"))
        .current_dir(&dir)
        .arg("run")
        .arg("--examples")
        .arg("--stdin")
        .arg("empty")
        .output()
        .unwrap();
    assert!(
        !empty.status.success(),
        "`--stdin empty` must ignore same-basename input fixtures"
    );

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn run_examples_reports_aggregate_failures() {
    let dir = temp_dir("examples_failures");
    let corpus = dir.join("corpus");
    fs::create_dir_all(&corpus).unwrap();
    write_example(&corpus, GOOD_EXAMPLE, "fn main() = println(1)\n");
    write_example(&corpus, BAD_EXAMPLE, "fn main() = 1 + true\n");

    let out = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("run")
        .arg("--examples")
        .arg(&corpus)
        .output()
        .unwrap();
    assert!(!out.status.success(), "bad corpus unexpectedly passed");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stdout.contains("ok "),
        "good example was not reported:\n{stdout}"
    );
    assert!(
        stdout.contains("FAIL "),
        "bad example was not reported:\n{stdout}"
    );
    assert!(
        stderr.contains("1 of 2 examples failed"),
        "aggregate failure missing:\n{stderr}"
    );

    let _ = fs::remove_dir_all(&dir);
}
