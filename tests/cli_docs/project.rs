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

fn libeffect() -> &'static Path {
    Path::new(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/projects/libeffect"
    ))
}

fn withdep() -> &'static Path {
    Path::new(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/projects/withdep"
    ))
}

// Build a project's entry to a native binary and assert its stdout matches the
// interpreter, the same oracle as the parity corpus. A missing C compiler is a
// hard failure, not a silent skip, so the native path is never vacuously green.
fn assert_native_matches_interp(project_dir: &Path) {
    assert!(
        have_cc(),
        r"C compiler `{}` not found (set PRISM_CC). Native project tests require it; install clang or LLVM so the project backend is exercised.",
        cc()
    );
    let project = load_project(project_dir).expect("manifest loads");
    let full = with_prelude(&fs::read_to_string(&project.entry).expect("entry reads"));
    let roots = prism::project_roots(&project.src_dir, &project.dep_src_dirs);
    let cfg = prism::Config::default();
    let want = prism::interpret_io_on(&full, &roots, &mut Vec::new(), &mut std::io::empty(), &cfg)
        .expect("interprets")
        .term;
    let bin = env::temp_dir().join(format!("prism_{}_{}", project.name, process::id()));
    prism::build_on(&full, &roots, &bin, &cfg).expect("native build");
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
fn why_recompiled_uses_persisted_module_decisions() {
    let store = env::temp_dir().join(format!("prism-why-recompiled-{}", process::id()));
    let source = env::temp_dir().join(format!("prism-why-recompiled-{}.pr", process::id()));
    let _ = fs::remove_dir_all(&store);
    fs::write(&source, "fn main() : Int = 42\n").unwrap();
    let first = Command::new(env!("CARGO_BIN_EXE_prism"))
        .args(["lineage", "why-recompiled", source.to_str().unwrap()])
        .env("PRISM_STORE_PATH", &store)
        .env("PRISM_COMPILER_CACHE", "1")
        .output()
        .unwrap();
    assert!(
        first.status.success(),
        "{}",
        String::from_utf8_lossy(&first.stderr)
    );
    let first_stdout = String::from_utf8(first.stdout).unwrap();
    assert!(first_stdout.contains("recompiled <root>: no previous successful module query"));

    let second = Command::new(env!("CARGO_BIN_EXE_prism"))
        .args(["lineage", "why-recompiled", source.to_str().unwrap()])
        .env("PRISM_STORE_PATH", &store)
        .env("PRISM_COMPILER_CACHE", "1")
        .output()
        .unwrap();
    assert!(
        second.status.success(),
        "{}",
        String::from_utf8_lossy(&second.stderr)
    );
    let second_stdout = String::from_utf8(second.stdout).unwrap();
    assert!(second_stdout.contains("reused <root>"));
    assert!(second_stdout.contains("reused backend-scc main"));
    assert!(
        !second_stdout.contains("effect whole-program"),
        "the retired legacy effect producer must stay absent: {second_stdout}"
    );
    assert!(second_stdout.contains("reused closure-plan native-kont-plan"));
    fs::remove_dir_all(store).unwrap();
    fs::remove_file(source).unwrap();
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
        &prism::Config::default(),
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
    fs::write(
        dir.join("prism.toml"),
        r#"[package]
name = "c"
version = "0.0.0"
authors = ["Test Author <test@example.com>"]
maintainers = ["test@example.com"]
license = "MIT"

[bin]
entry = "src/main.pr"
"#,
    )
    .unwrap();
    let target = dir.join("target");
    fs::create_dir_all(&target).unwrap();
    fs::write(target.join("c"), b"artifact").unwrap();
    let keep = dir.join("src").join("main.pr");
    fs::write(&keep, b"fn main() = print(1)\n").unwrap();

    let prism = env!("CARGO_BIN_EXE_prism");
    // From a nested subdirectory: clean still finds the enclosing manifest.
    let sub = dir.join("src");
    assert!(Command::new(prism)
        .arg("clean")
        .arg(&sub)
        .status()
        .unwrap()
        .success());
    assert!(!target.exists(), "target/ removed");
    assert!(keep.exists(), "source untouched");
    // Second run is a no-op success.
    assert!(Command::new(prism)
        .arg("clean")
        .arg(&dir)
        .status()
        .unwrap()
        .success());

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn check_without_file_checks_enclosing_project() {
    let dir = env::temp_dir().join(format!("prism_check_project_{}", process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(dir.join("src").join("nested")).unwrap();
    fs::write(
        dir.join("prism.toml"),
        r#"[package]
name = "checkproj"
version = "0.0.0"
authors = ["Test Author <test@example.com>"]
maintainers = ["test@example.com"]
license = "MIT"

[bin]
entry = "src/main.pr"
"#,
    )
    .unwrap();
    fs::write(dir.join("src").join("main.pr"), "fn main() = ()\n").unwrap();

    let out = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("check")
        .current_dir(dir.join("src").join("nested"))
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "check failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(out.stdout.is_empty(), "stdout should be quiet: {out:?}");
    assert!(out.stderr.is_empty(), "stderr should be quiet: {out:?}");

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn check_licenses_lists_transitive_spdx_ids_without_license_text() {
    let workspace = env::temp_dir().join(format!("prism_check_licenses_{}", process::id()));
    let _ = fs::remove_dir_all(&workspace);
    for package in ["app", "middle", "copyleft"] {
        fs::create_dir_all(workspace.join(package).join("src")).unwrap();
    }
    fs::write(
        workspace.join("app/prism.toml"),
        r#"[package]
name = "app"
version = "0.0.0"
authors = ["Test Author <test@example.com>"]
maintainers = ["test@example.com"]
license = "MIT"

[bin]
entry = "src/main.pr"

[dependencies]
middle = { path = "../middle" }
"#,
    )
    .unwrap();
    fs::write(
        workspace.join("middle/prism.toml"),
        r#"[package]
name = "middle"
version = "1.2.3"
authors = ["Test Author <test@example.com>"]
maintainers = ["test@example.com"]
license = "Apache-2.0"

[bin]
entry = "src/main.pr"

[dependencies]
copyleft = { path = "../copyleft" }
"#,
    )
    .unwrap();
    fs::write(
        workspace.join("copyleft/prism.toml"),
        r#"[package]
name = "copyleft"
version = "3.0.0"
authors = ["Test Author <test@example.com>"]
maintainers = ["test@example.com"]
license = "AGPL-3.0-only"

[bin]
entry = "src/main.pr"
"#,
    )
    .unwrap();

    let out = Command::new(env!("CARGO_BIN_EXE_prism"))
        .args(["check", "--licenses"])
        .current_dir(workspace.join("app"))
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "license audit failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "Dependency licenses:\n  copyleft 3.0.0 - AGPL-3.0-only\n  middle 1.2.3 - Apache-2.0\n"
    );
    assert!(out.stderr.is_empty(), "stderr should be quiet: {out:?}");

    let _ = fs::remove_dir_all(&workspace);
}

#[test]
fn check_explicit_file_checks_that_file_without_project() {
    let dir = env::temp_dir().join(format!("prism_check_file_{}", process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let file = dir.join("oneoff.pr");
    fs::write(&file, "fn main() = ()\n").unwrap();

    let out = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("check")
        .arg(&file)
        .current_dir(&dir)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "check failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(out.stdout.is_empty(), "stdout should be quiet: {out:?}");
    assert!(out.stderr.is_empty(), "stderr should be quiet: {out:?}");

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn diff_without_paths_semantically_compares_project_head_to_worktree() {
    if !have_git() {
        eprintln!("skipping: git not installed");
        return;
    }
    let dir = env::temp_dir().join(format!("prism_diff_project_{}", process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(dir.join("src").join("nested")).unwrap();
    fs::write(
        dir.join("prism.toml"),
        r#"[package]
name = "git-diff"
version = "0.0.0"
authors = ["Test Author <test@example.com>"]
maintainers = ["test@example.com"]
license = "MIT"

[bin]
entry = "src/main.pr"
"#,
    )
    .unwrap();
    fs::write(
        dir.join("src/main.pr"),
        r"import Logic

fn main() = print(Logic.answer())
",
    )
    .unwrap();
    let logic = dir.join("src/Logic.pr");
    fs::write(&logic, "pub fn answer() : Int = 1\n").unwrap();
    git(&dir, ["init"]);
    git(&dir, ["config", "user.email", "prism@example.test"]);
    git(&dir, ["config", "user.name", "Prism test"]);
    git(&dir, ["add", "."]);
    git(&dir, ["commit", "-m", "baseline"]);

    // Stage the edit as well: no-argument diff means HEAD -> working tree, not
    // only the unstaged portion that plain `git diff` would show.
    fs::write(&logic, "pub fn answer() : Int = 2\n").unwrap();
    git(&dir, ["add", "src/Logic.pr"]);

    let output = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("diff")
        .current_dir(dir.join("src").join("nested"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "diff failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("~ Logic.answer"),
        "unexpected diff:\n{stdout}"
    );
    assert!(
        stdout.contains("cone: 1 affected (main)"),
        "unexpected diff:\n{stdout}"
    );
    assert!(stdout.contains("surface:"), "unexpected diff:\n{stdout}");
    assert!(
        stdout.contains("  Logic.answer\n    - fn answer() : Int = 1\n    + fn answer() : Int = 2"),
        "surface patch missing:\n{stdout}"
    );

    // Explicit source revisions remain valid outside a project.
    let old = dir.join("old.pr");
    let new = dir.join("new.pr");
    fs::write(&old, "fn main() = print(1)\n").unwrap();
    fs::write(&new, "fn main() = print(2)\n").unwrap();
    let explicit = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("diff")
        .arg(&old)
        .arg(&new)
        .output()
        .unwrap();
    assert!(
        explicit.status.success(),
        "explicit diff failed:\n{}",
        String::from_utf8_lossy(&explicit.stderr)
    );
    assert!(
        String::from_utf8_lossy(&explicit.stdout).contains("~ main"),
        "unexpected explicit diff: {explicit:?}"
    );

    let _ = fs::remove_dir_all(&dir);
}

// A local effect operation may share its name with a stdlib operation from a
// module the project never imports (`Clock.sleep` in Concurrent). Operation
// names resolve through the module's own declarations before anything the
// ambient foundation seeds, so the project must check through the module-query
// path, and the interpreted and built program must agree, with the local
// operation in force. This is the regression shape where the seeded stdlib
// operation silently clobbered the local one and the project build reported
// the user's own effect as unknown while `prism run` accepted the program.
#[test]
fn project_effect_op_sharing_a_stdlib_op_name_builds_and_agrees() {
    let dir = env::temp_dir().join(format!("prism_op_clash_{}", process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(dir.join("src")).unwrap();
    fs::write(
        dir.join("prism.toml"),
        r#"[package]
name = "opclash"
version = "0.0.0"
authors = ["Test Author <test@example.com>"]
maintainers = ["test@example.com"]
license = "MIT"

[bin]
entry = "src/main.pr"
"#,
    )
    .unwrap();
    let program = r"effect Timer
  sleep(Int) : Unit

fn nap(d : Int) : Int ! {Timer} =
  sleep(d)
  d * 2

fn main() =
  let r =
    handle nap(21) with
      sleep(_d) resume k => k(())
      return r => r
  println(r)
";
    fs::write(dir.join("src").join("main.pr"), program).unwrap();

    let project = load_project(&dir).expect("manifest loads");
    let roots = prism::project_roots(&project.src_dir, &project.dep_src_dirs);
    let mut cfg = prism::Config::default();
    cfg.flags.compiler_cache = false;
    let full = with_prelude(&fs::read_to_string(&project.entry).expect("entry reads"));
    prism::check_modules_on(&full, &roots, &cfg)
        .expect("a local operation sharing an unimported stdlib operation's name checks");
    let run = interpret_at(&full, &project.src_dir).expect("interprets");
    let out: Vec<String> = run.out.iter().map(Rv::show).collect();
    assert_eq!(
        out,
        ["42"],
        "the local `Timer.sleep` handler must be in force"
    );
    assert_native_matches_interp(&dir);

    let _ = fs::remove_dir_all(&dir);
}

// A handler clause names its operation bare and the grammar admits nothing
// else, so an operation a plain `import M` leaves reachable only as `M.op` is an
// operation no clause can spell. The entry module imports the library without a
// name list and handles its `beep`, and the built program must agree with the
// interpreter, so the clause binds the library's operation on both tiers.
#[test]
fn project_handler_clause_names_an_imported_library_operation() {
    let project = load_project(libeffect()).expect("manifest loads");
    let roots = prism::project_roots(&project.src_dir, &project.dep_src_dirs);
    let mut cfg = prism::Config::default();
    cfg.flags.compiler_cache = false;
    let full = with_prelude(&fs::read_to_string(&project.entry).expect("entry reads"));
    prism::check_modules_on(&full, &roots, &cfg)
        .expect("a clause handling an imported library operation checks");
    let run = interpret_at(&full, &project.src_dir).expect("interprets");
    let out: Vec<String> = run.out.iter().map(Rv::show).collect();
    assert_eq!(out, ["42"], "the imported `Beeper.beep` clause must run");
    assert_native_matches_interp(libeffect());
}

fn have_git() -> bool {
    Command::new("git")
        .arg("--version")
        .output()
        .is_ok_and(|output| output.status.success())
}

fn git<const N: usize>(dir: &Path, args: [&str; N]) {
    let output = Command::new("git")
        .args(args)
        .current_dir(dir)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "git failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
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
