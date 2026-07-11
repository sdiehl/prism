//! The embedded standard library: curated `Data.*` modules resolve
//! like any import from the in-binary stdlib root, the always-on prelude opens
//! them with glob imports, and a glob import (`import M (..)`) brings every
//! export into unqualified scope.

use std::path::Path;

use prism::{check, interpret, with_prelude};

fn out(src: &str) -> String {
    let run = interpret(&with_prelude(src)).expect("resolves and runs");
    run.out.iter().fold(String::new(), |mut s, v| {
        s.push_str(&v.show());
        s.push('\n');
        s
    })
}

fn err(src: &str) -> String {
    check(&with_prelude(src))
        .expect_err("should fail")
        .to_string()
}

#[test]
fn prelude_opens_stdlib_unqualified() {
    // Names that now live in `Data.*` modules stay available without an import,
    // because the prelude glob-opens them.
    assert_eq!(
        out("fn main() = print(sum(map(\\(x) -> x * 2, [1, 2, 3])))"),
        "12\n"
    );
    assert_eq!(
        out("fn main() = print(starts_with(\"he\", \"hello\"))"),
        "true\n"
    );
}

#[test]
fn stdlib_module_is_importable_qualified() {
    // The same module is reachable as an explicit qualified import.
    assert_eq!(
        out("import Data.Foldable\nfn main() = print(Data.Foldable.sum([4, 5, 6]))"),
        "15\n"
    );
}

#[test]
fn stdlib_selective_import() {
    assert_eq!(
        out("import Data.List (reverse)\nfn main() = print(reverse([1, 2, 3]))"),
        "[3, 2, 1]\n"
    );
}

#[test]
fn stdlib_alias_import() {
    assert_eq!(
        out("import Data.Map as M\nfn main() = print(M.map_size(M.map_insert(1, 2, M.map_empty)))"),
        "1\n"
    );
}

#[test]
fn glob_import_opens_all_exports() {
    // `import M (..)` is the unqualified-everything form the prelude uses; a user
    // can spell it too.
    let src = r"import Data.Map (..)
fn main() = print(map_size(map_insert(1, 10, map_insert(2, 20, map_empty))))";
    assert_eq!(out(src), "2\n");
}

#[test]
fn prelude_makes_stdlib_qualifier_available() {
    // The prelude opens the stdlib, so its modules are reachable qualified even
    // without the user importing them.
    assert_eq!(
        out("fn main() = print(Data.Foldable.sum([1, 2, 3]))"),
        "6\n"
    );
}

#[test]
fn unknown_module_qualifier_errors() {
    assert!(err("fn main() = print(Data.Nope.thing(1))").contains("Data.Nope"));
}

#[test]
fn project_module_can_import_stdlib() {
    // A non-root module reaches stdlib functions through an explicit import,
    // exercising cross-module resolution against the embedded stdlib root.
    let base = Path::new(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/stdlib_fixtures"
    ));
    let run = prism::interpret_at(
        &with_prelude("import Helper\nfn main() = print(Helper.total([1,2,3,4]))"),
        base,
    )
    .expect("resolves and runs");
    assert_eq!(run.out[0].show(), "10");
}
