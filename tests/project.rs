//! Project model: a `prism.toml` manifest resolves modules from the project's
//! `src/` root rather than from the entry file's own directory.

use std::path::Path;

use prism::project::load_project;
use prism::{interpret_at, with_prelude};

fn hello() -> &'static Path {
    Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/projects/hello"))
}

fn modlib() -> &'static Path {
    Path::new(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/projects/modlib"
    ))
}

// Build a project's entry to a native binary and assert its stdout matches the
// interpreter, the same oracle as the parity corpus. Returns early when no C
// compiler is available so CI without clang still passes.
fn assert_native_matches_interp(project_dir: &Path) {
    if !have_cc() {
        return;
    }
    let project = load_project(project_dir).expect("manifest loads");
    let full = with_prelude(&std::fs::read_to_string(&project.entry).expect("entry reads"));
    let want = interpret_at(&full, &project.src_dir)
        .expect("interprets")
        .term;
    let bin = std::env::temp_dir().join(format!("prism_{}_{}", project.name, std::process::id()));
    prism::build_at(&full, &project.src_dir, &bin).expect("native build");
    let out = std::process::Command::new(&bin)
        .output()
        .expect("runs binary");
    for ext in ["bc", "ll"] {
        let _ = std::fs::remove_file(bin.with_extension(ext));
    }
    let _ = std::fs::remove_file(&bin);
    assert_eq!(String::from_utf8_lossy(&out.stdout), want);
}

#[test]
fn project_resolves_modules_from_src_root() {
    let project = load_project(hello()).expect("manifest loads");
    assert_eq!(project.name, "hello");
    let src = std::fs::read_to_string(&project.entry).expect("entry reads");
    let run = interpret_at(&with_prelude(&src), &project.src_dir).expect("resolves and runs");
    let out: Vec<String> = run.out.iter().map(prism::eval::Rv::show).collect();
    assert_eq!(out, ["42"]);
}

#[test]
fn modlib_project_interprets() {
    let project = load_project(modlib()).expect("manifest loads");
    let src = std::fs::read_to_string(&project.entry).expect("entry reads");
    let run = interpret_at(&with_prelude(&src), &project.src_dir).expect("resolves and runs");
    let out: Vec<String> = run.out.iter().map(prism::eval::Rv::show).collect();
    assert_eq!(out, ["42", "1", "0"]);
}

#[test]
fn loading_a_missing_manifest_errors() {
    assert!(load_project(Path::new("/nonexistent/prism-project")).is_err());
}

fn cc() -> String {
    std::env::var("PRISM_CC").unwrap_or_else(|_| "clang".into())
}

fn have_cc() -> bool {
    std::process::Command::new(cc())
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success())
}

// End-to-end: a multi-module project compiled to a native binary must reproduce
// the interpreter's output, so the canonical dotted symbols (`Greet.greet` ->
// `prism_Greet.greet`) survive codegen and linking. Skips when no C compiler is
// available, like the parity oracle.
#[test]
fn project_native_build_matches_interpreter() {
    assert_native_matches_interp(hello());
}

// A wider native module surface than `hello`'s single qualified call: a private
// helper (`Counter@step`, never exported), constructors of a type defined in
// another module (`Shape.Circle`/`Shape.Square`), and a derived `Eq` instance
// elaborated in `Shape` but dispatched from `main`. All of these only had
// interpreter coverage; here they must mangle, link, and run natively.
#[test]
fn project_native_multi_module() {
    assert_native_matches_interp(modlib());
}
