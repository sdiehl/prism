//! Multi-module resolution (M2): qualified, selective, and aliased imports;
//! private-name namespacing; and the eager conflict policy.

use std::path::Path;

use tiny_prism::{check_at, interpret_at, with_prelude};

fn base() -> &'static Path {
    Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/modules"))
}

fn out(src: &str) -> String {
    let run = interpret_at(&with_prelude(src), base()).expect("should resolve and run");
    run.out.iter().fold(String::new(), |mut s, v| {
        s.push_str(&v.show());
        s.push('\n');
        s
    })
}

fn err(src: &str) -> String {
    check_at(&with_prelude(src), base())
        .expect_err("should fail to resolve")
        .to_string()
}

#[test]
fn qualified_import() {
    assert_eq!(
        out("import Math\nfn main() = print(Math.square(Math.bump(3)))"),
        "16\n"
    );
}

#[test]
fn selective_import_is_unqualified() {
    assert_eq!(
        out("import Math (square)\nfn main() = print(square(5))"),
        "25\n"
    );
}

#[test]
fn alias_renames_qualifier() {
    assert_eq!(
        out("import Math as M\nfn main() = print(M.square(6))"),
        "36\n"
    );
}

#[test]
fn qualified_type_and_constructor() {
    let src = "import Shape\nfn main() = print(Shape.area(Shape.Circle(4)))";
    assert_eq!(out(src), "16\n");
}

#[test]
fn private_names_are_namespaced_not_exported() {
    // `make` is exported and works; the module's private `Inner`/`Wrap`/`unwrap`
    // are renamed out of the way and stay reachable from inside the module.
    assert_eq!(out("import Box\nfn main() = print(Box.make(7))"), "7\n");
    assert!(err("import Box (unwrap)\nfn main() = print(0)").contains("does not export `unwrap`"));
}

#[test]
fn selective_synonym_import() {
    let src = "import Pairs (Pair, mk)\n\
               fn snd(p : Pair(Int)) : Int = match p of { (a, b) => b }\n\
               fn main() = print(snd(mk(4)))";
    assert_eq!(out(src), "4\n");
}

#[test]
fn qualified_synonym_import() {
    let src = "import Pairs\nfn main() = match Pairs.mk(9) of { (a, b) => print(a) }";
    assert_eq!(out(src), "9\n");
}

#[test]
fn qualified_newtype_import() {
    // A `pub newtype` exports its type and constructor transparently.
    let src = "import Ids\nfn main() = print(Ids.same(Ids.UserId(3), Ids.mk(3)))";
    assert_eq!(out(src), "true\n");
}

#[test]
fn opaque_type_usable_via_exports() {
    // The type is abstract to importers, but its exported operations work, and
    // its derived Eq instance (instances are global) crosses the boundary.
    let src = "import Stack\n\
               fn main() =\n  \
                 let s = Stack.push(5, Stack.empty())\n  \
                 print(Stack.top(s) == Stack.top(Stack.push(5, Stack.empty())))";
    assert_eq!(out(src), "true\n");
}

#[test]
fn opaque_constructor_is_hidden() {
    let e = err("import Stack\nfn main() = print(Stack.top(Stack.Push(9, Stack.empty())))");
    assert!(e.contains("does not export `Push`"), "{e}");
}

#[test]
fn opaque_constructor_unmatchable_outside() {
    let src = "import Stack\n\
               fn main() = match Stack.empty() of { Stack.Empty => print(0), _ => print(1) }";
    assert!(err(src).contains("does not export `Empty`"));
}

#[test]
fn dotted_module_path() {
    assert_eq!(out("import Geo.Util\nfn main() = print(Util.one())"), "1\n");
}

#[test]
fn export_clash_between_modules_is_eager_error() {
    let e = err("import Apple\nimport Banana\nfn main() = print(0)");
    assert!(e.contains("`dup`") && e.contains("clashes"), "{e}");
}

#[test]
fn export_clash_with_root_is_eager_error() {
    let e = err("import Math\nfn square(x : Int) : Int = x\nfn main() = print(square(1))");
    assert!(e.contains("`square`") && e.contains("clashes"), "{e}");
}

#[test]
fn selective_import_of_missing_name_errors() {
    assert!(err("import Math (nope)\nfn main() = print(0)").contains("does not export `nope`"));
}

#[test]
fn unknown_qualifier_errors() {
    assert!(err("import Math\nfn main() = print(Nope.square(1))").contains("Nope"));
}

#[test]
fn unimported_module_errors() {
    assert!(err("import Missing\nfn main() = print(0)").contains("Missing"));
}
