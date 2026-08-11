//! The typed-hole query surface: `prism check --at-hole [--fill] [--json]`.
//!
//! Every case runs the real binary against a real file, so the reported
//! positions are the ones a user reads and the rewrites are the bytes a user
//! ends up with. The prelude is prepended to every checked program, so a report
//! that did not subtract it would name a line hundreds of rows off.

mod support;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde_json::Value;
use support::TempDir;

// Exactly one binding of the expected type (`w`) and nothing else that fits:
// the unambiguous case `--fill` is allowed to rewrite.
const ONE_EXACT: &str = "\
type Widget = Widget { size : Int }

fn resize(w : Widget) : Widget ! {} = ?answer

fn main() = println(resize(Widget { size = 1 }).size)
";

// Two bindings of the expected type: a rewrite would be a coin flip.
const TWO_EXACT: &str = "\
type Widget = Widget { size : Int }

fn choose(a : Widget, b : Widget) : Widget ! {} = ?answer

fn main() = println(choose(Widget { size = 1 }, Widget { size = 2 }).size)
";

// The only candidate is polymorphic: compatible by instantiation, not identical,
// so no rewrite is licensed.
const INEXACT_ONLY: &str = "\
type Widget = Widget { size : Int }

fn identity(x) = x

fn resizer() : ((Widget) -> Widget) ! {} = ?answer

fn main() = println(identity(1))
";

// A hole with no constraint on it fits every name in scope, so the human report
// must truncate where the CLI says it does.
const UNCONSTRAINED: &str = "fn main() = let y = ?h in println(1)\n";

fn write_case(dir: &TempDir, name: &str, source: &str) -> PathBuf {
    let path = dir.join(name);
    fs::write(&path, source).unwrap();
    path
}

fn run(path: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("check")
        .arg(path)
        .args(args)
        .output()
        .unwrap()
}

fn stdout_of(output: &Output) -> String {
    assert!(
        output.status.success(),
        "stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn holes_json(path: &Path, args: &[&str]) -> Vec<Value> {
    let output = run(path, args);
    let text = stdout_of(&output);
    let first = text.lines().next().unwrap_or_default();
    serde_json::from_str(first).unwrap()
}

#[test]
fn one_exact_candidate_is_filled_in_place() {
    let dir = TempDir::new("holes", "fill-one");
    let path = write_case(&dir, "one.pr", ONE_EXACT);
    let out = run(&path, &["--at-hole", "--fill"]);
    let text = stdout_of(&out);
    assert!(text.contains("filled ?answer -> w"), "{text}");
    let filled = fs::read_to_string(&path).unwrap();
    assert_eq!(filled, ONE_EXACT.replace("?answer", "w"));
}

#[test]
fn two_exact_candidates_leave_the_file_untouched() {
    let dir = TempDir::new("holes", "fill-ambiguous");
    let path = write_case(&dir, "two.pr", TWO_EXACT);
    let out = run(&path, &["--at-hole", "--fill"]);
    let text = stdout_of(&out);
    assert!(text.contains("left ?answer: ambiguous: a, b"), "{text}");
    assert_eq!(fs::read_to_string(&path).unwrap(), TWO_EXACT);
}

#[test]
fn a_merely_compatible_candidate_is_never_synthesized() {
    let dir = TempDir::new("holes", "fill-inexact");
    let path = write_case(&dir, "inexact.pr", INEXACT_ONLY);
    let json = holes_json(&path, &["--at-hole", "--json"]);
    let candidates = json[0]["candidates"].as_array().unwrap();
    assert!(
        candidates
            .iter()
            .any(|c| c["name"] == "identity" && c["exact"] == false),
        "{json:?}"
    );
    assert!(
        candidates.iter().all(|c| c["exact"] == false),
        "the fixture must offer no exact fit: {json:?}"
    );
    let out = run(&path, &["--at-hole", "--fill"]);
    let text = stdout_of(&out);
    assert!(text.contains("left ?answer: no exact candidate"), "{text}");
    assert_eq!(fs::read_to_string(&path).unwrap(), INEXACT_ONLY);
}

#[test]
fn positions_are_relative_to_the_user_file_not_the_prelude() {
    let dir = TempDir::new("holes", "offsets");
    let path = write_case(&dir, "one.pr", ONE_EXACT);
    let json = holes_json(&path, &["--at-hole", "--json"]);
    let hole = &json[0];
    let start = usize::try_from(hole["start"].as_u64().unwrap()).unwrap();
    let end = usize::try_from(hole["end"].as_u64().unwrap()).unwrap();
    assert_eq!(start, ONE_EXACT.find("?answer").unwrap());
    assert_eq!(&ONE_EXACT[start..end], "?answer");
    assert_eq!(hole["line"], 3);
    assert_eq!(hole["col"], 39);
    assert_eq!(hole["in_prelude"], false);
    assert_eq!(hole["expected"], "Widget");
    assert_eq!(hole["effects"], "{}");

    // The plain report names the same position.
    let text = stdout_of(&run(&path, &["--at-hole"]));
    assert!(text.contains(":3:39"), "{text}");
    assert!(text.contains("?answer"), "{text}");
}

#[test]
fn an_unconstrained_hole_truncates_its_candidate_list() {
    let dir = TempDir::new("holes", "cap");
    let path = write_case(&dir, "open.pr", UNCONSTRAINED);
    let text = stdout_of(&run(&path, &["--at-hole"]));

    let shown = text
        .lines()
        .filter(|line| line.starts_with("    ") && !line.contains("more ("))
        .count();
    assert!(shown > 0, "the human report must retain a useful prefix");

    // The truncated list still accounts for every candidate: the count line
    // names the total, and the withheld tail is the rest of it.
    let json = holes_json(&path, &["--at-hole", "--json"]);
    let total = json[0]["candidates"].as_array().unwrap().len();
    assert!(total > shown, "the fixture must overflow the cap");
    assert!(text.contains(&format!("candidates {total}")), "{text}");
    assert!(
        text.contains(&format!(
            "... and {} more (--json lists all)",
            total - shown
        )),
        "{text}"
    );
}

#[test]
fn a_hole_free_file_reports_nothing() {
    let dir = TempDir::new("holes", "empty");
    let path = write_case(&dir, "plain.pr", "fn main() = println(1)\n");
    let out = run(&path, &["--at-hole"]);
    assert_eq!(stdout_of(&out), "");
}

#[test]
fn an_ordinary_type_error_still_fails() {
    let dir = TempDir::new("holes", "type-error");
    let path = write_case(&dir, "bad.pr", "fn main() : Int = true\n");
    let out = run(&path, &["--at-hole"]);
    assert!(!out.status.success());
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("Type Error"),
        "stderr:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
}
