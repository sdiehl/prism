//! Project model: a `prism.toml` manifest resolves modules from the project's
//! `src/` root rather than from the entry file's own directory.

use std::path::Path;
use std::process::{self, Command};
use std::{env, fs};

use prism::eval::Rv;
use prism::project::load_project;
use prism::{interpret_at, with_custom_prelude, with_prelude};

fn hello() -> &'static Path {
    Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/projects/hello"))
}

fn customprelude() -> &'static Path {
    Path::new(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/projects/customprelude"
    ))
}

fn modlib() -> &'static Path {
    Path::new(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/projects/modlib"
    ))
}

fn withdep() -> &'static Path {
    Path::new(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/projects/withdep"
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
    let full = with_prelude(&fs::read_to_string(&project.entry).expect("entry reads"));
    let roots = prism::project_roots(&project.src_dir, &project.dep_src_dirs);
    let want = prism::interpret_io_on(&full, &roots, &mut Vec::new(), &mut std::io::empty())
        .expect("interprets")
        .term;
    let bin = env::temp_dir().join(format!("prism_{}_{}", project.name, process::id()));
    prism::build_on(&full, &roots, &bin).expect("native build");
    let out = Command::new(&bin).output().expect("runs binary");
    for ext in ["bc", "ll"] {
        let _ = fs::remove_file(bin.with_extension(ext));
    }
    let _ = fs::remove_file(&bin);
    assert_eq!(String::from_utf8_lossy(&out.stdout), want);
}

#[test]
fn project_resolves_modules_from_src_root() {
    let project = load_project(hello()).expect("manifest loads");
    assert_eq!(project.name, "hello");
    let src = fs::read_to_string(&project.entry).expect("entry reads");
    let run = interpret_at(&with_prelude(&src), &project.src_dir).expect("resolves and runs");
    let out: Vec<String> = run.out.iter().map(Rv::show).collect();
    assert_eq!(out, ["42"]);
}

#[test]
fn project_prelude_override_replaces_builtin() {
    let project = load_project(customprelude()).expect("manifest loads");
    let prelude_path = project.prelude.as_ref().expect("prelude override set");
    let prelude = fs::read_to_string(prelude_path).expect("prelude reads");
    let src = fs::read_to_string(&project.entry).expect("entry reads");
    // The custom prelude defines `triple`; the built-in prelude is not prepended,
    // yet compiler builtins (`show_int`) still resolve.
    let run = interpret_at(&with_custom_prelude(&prelude, &src), &project.src_dir)
        .expect("resolves and runs");
    let out: Vec<String> = run.out.iter().map(Rv::show).collect();
    assert_eq!(out, ["42"]);
}

#[test]
fn modlib_project_interprets() {
    let project = load_project(modlib()).expect("manifest loads");
    let src = fs::read_to_string(&project.entry).expect("entry reads");
    let run = interpret_at(&with_prelude(&src), &project.src_dir).expect("resolves and runs");
    let out: Vec<String> = run.out.iter().map(Rv::show).collect();
    assert_eq!(out, ["42", "1", "0"]);
}

#[test]
fn loading_a_missing_manifest_errors() {
    assert!(load_project(Path::new("/nonexistent/prism-project")).is_err());
}

#[test]
fn manifest_parses_path_dependencies() {
    let project = load_project(withdep()).expect("manifest loads");
    // The dependency's own `src/` is on the search path, resolved through its
    // manifest, so its modules resolve under its root.
    assert_eq!(project.dep_src_dirs.len(), 1);
    assert!(project
        .dep_src_dirs
        .iter()
        .any(|d| d.ends_with("geometry/src")));
}

#[test]
fn path_dependency_modules_resolve_and_run() {
    let project = load_project(withdep()).expect("manifest loads");
    let src = fs::read_to_string(&project.entry).expect("entry reads");
    let roots = prism::project_roots(&project.src_dir, &project.dep_src_dirs);
    // `Geo.Shapes` lives in the `geometry` dependency, not in this project.
    let run = prism::interpret_io_on(
        &with_prelude(&src),
        &roots,
        &mut Vec::new(),
        &mut std::io::empty(),
    )
    .expect("resolves and runs");
    let out: Vec<String> = run.out.iter().map(Rv::show).collect();
    assert_eq!(out, ["25", "48"]);
}

#[test]
fn path_dependency_native_build_matches_interpreter() {
    assert_native_matches_interp(withdep());
}

// `prism clean` removes the package-root `target/` (and nothing else), and is a
// no-op success when it is already absent.
#[test]
fn clean_removes_target_at_package_root() {
    let dir = env::temp_dir().join(format!("prism_clean_{}", process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(dir.join("src")).unwrap();
    fs::write(dir.join("prism.toml"), "[package]\nname = \"c\"\n\n[bin]\nentry = \"src/main.pr\"\n").unwrap();
    let target = dir.join("target");
    fs::create_dir_all(&target).unwrap();
    fs::write(target.join("c"), b"artifact").unwrap();
    let keep = dir.join("src").join("main.pr");
    fs::write(&keep, b"fn main() = print(1)\n").unwrap();

    let prism = env!("CARGO_BIN_EXE_prism");
    // From a nested subdirectory: clean still finds the enclosing manifest.
    let sub = dir.join("src");
    assert!(Command::new(prism).arg("clean").arg(&sub).status().unwrap().success());
    assert!(!target.exists(), "target/ removed");
    assert!(keep.exists(), "source untouched");
    // Second run is a no-op success.
    assert!(Command::new(prism).arg("clean").arg(&dir).status().unwrap().success());

    let _ = fs::remove_dir_all(&dir);
}

fn cc() -> String {
    env::var("PRISM_CC").unwrap_or_else(|_| "clang".into())
}

fn have_cc() -> bool {
    Command::new(cc())
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
