//! Type search and bounded, verified hole synthesis through the real CLI.

use std::fs;
use std::process::{Command, Output};

use crate::support::TempDir;
use serde_json::Value;

fn run(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_prism"))
        .args(args)
        .output()
        .expect("runs prism")
}

fn json(output: &Output) -> Value {
    assert!(
        output.status.success(),
        "stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).expect("stdout is JSON")
}

#[test]
fn search_covers_unimported_project_package_and_stdlib_interfaces() {
    let dir = TempDir::new("type-query", "search-world");
    let app = dir.join("app");
    let dep = dir.join("dep");
    fs::create_dir_all(app.join("src")).unwrap();
    fs::create_dir_all(dep.join("src")).unwrap();
    fs::write(
        app.join("prism.toml"),
        r#"[package]
name = "app"
version = "0.0.0"
authors = ["Test Author <test@example.com>"]
maintainers = ["test@example.com"]
license = "MIT"

[bin]
entry = "src/main.pr"

[dependencies]
dep = { path = "../dep" }
"#,
    )
    .unwrap();
    fs::write(
        dep.join("prism.toml"),
        r#"[package]
name = "dep"
version = "0.0.0"
authors = ["Test Author <test@example.com>"]
maintainers = ["test@example.com"]
license = "MIT"

[bin]
entry = "src/dep_main.pr"
"#,
    )
    .unwrap();
    fs::write(app.join("src/main.pr"), "fn main() = ()\n").unwrap();
    fs::write(app.join("src/Own.pr"), "pub fn own(x) = x\n").unwrap();
    fs::write(dep.join("src/dep_main.pr"), "fn main() = ()\n").unwrap();
    fs::write(
        dep.join("src/Package.pr"),
        "pub fn package(n : Int) : Int = n\n",
    )
    .unwrap();

    let manifest = app.join("prism.toml");
    let rows = json(&run(&[
        "search",
        "(Int) -> Int",
        "--in",
        manifest.to_str().unwrap(),
        "--limit",
        "500",
        "--json",
    ]));
    let rows = rows.as_array().unwrap();
    assert!(
        rows.iter()
            .any(|row| row["name"] == "Own.own" && row["source"] == "project"),
        "{rows:?}"
    );
    assert!(
        rows.iter()
            .any(|row| row["name"] == "Package.package" && row["source"] == "package"),
        "{rows:?}"
    );
    assert!(rows.iter().any(|row| row["source"] == "stdlib"), "{rows:?}");
}

#[test]
fn synth_is_depth_bounded_deterministic_and_rechecked() {
    let dir = TempDir::new("type-query", "synth-hole");
    let file = dir.join("hole.pr");
    fs::write(
        &file,
        "type Widget = Widget(Int)\n\nfn make(n : Int) : Widget = Widget(n)\n\nfn choose(n : Int) : Widget = ?answer\n",
    )
    .unwrap();

    let args = [
        "synth",
        file.to_str().unwrap(),
        "--at-hole",
        "answer",
        "--depth",
        "1",
        "--limit",
        "10",
        "--json",
    ];
    let first = json(&run(&args));
    let second = json(&run(&args));
    assert_eq!(first, second);
    let candidates = first[0]["candidates"].as_array().unwrap();
    assert!(
        candidates
            .iter()
            .any(|candidate| candidate["expression"] == "make(n)"),
        "{first:?}"
    );

    let shallow = json(&run(&[
        "synth",
        file.to_str().unwrap(),
        "--at-hole",
        "answer",
        "--depth",
        "0",
        "--json",
    ]));
    assert!(shallow[0]["candidates"].as_array().unwrap().is_empty());
}
