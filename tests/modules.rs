//! Multi-module resolution: qualified, selective, and aliased imports;
//! private-name namespacing; canonical disjoint namespaces; and the scoping
//! rules that let modules share a short name.

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
fn full_path_qualifier() {
    // The whole module path qualifies too, not just the last component.
    assert_eq!(
        out("import Geo.Util\nfn main() = print(Geo.Util.one())"),
        "1\n"
    );
}

#[test]
fn modules_sharing_a_name_coexist_when_qualified() {
    // Apple and Banana both export `dup`; qualification reaches each disjointly,
    // the case the old eager-uniqueness policy made impossible.
    let src = "import Apple\nimport Banana\nfn main() = print(Apple.dup() + Banana.dup())";
    assert_eq!(out(src), "3\n");
}

#[test]
fn unqualified_use_of_a_shared_name_is_unbound() {
    // Neither module is selectively imported, so bare `dup` reaches no symbol.
    let e = err("import Apple\nimport Banana\nfn main() = print(dup())");
    assert!(e.contains("unbound variable 'dup'"), "{e}");
}

#[test]
fn root_definition_shadows_an_import() {
    // A root binding wins over an imported name: `square` is the root's identity
    // function (5), not Math's squaring one (25).
    let src = "import Math\nfn square(x : Int) : Int = x\nfn main() = print(square(5))";
    assert_eq!(out(src), "5\n");
}

#[test]
fn selective_import_isolates_unselected_names() {
    // `import Math (square)` brings only `square`; `bump` stays out of scope.
    assert_eq!(
        out("import Math (square)\nfn main() = print(square(5))"),
        "25\n"
    );
    let e = err("import Math (square)\nfn main() = print(bump(1))");
    assert!(e.contains("unbound variable 'bump'"), "{e}");
}

#[test]
fn qualified_access_to_a_private_name_is_rejected() {
    let e = err("import Math\nfn main() = print(Math.helper(1))");
    assert!(e.contains("does not export `helper`"), "{e}");
}

#[test]
fn unqualified_ambiguity_is_rejected() {
    let e = err("import LibA (map)\nimport LibB (map)\nfn main() = print(map(1))");
    assert!(e.contains("`map` is ambiguous"), "{e}");
}

#[test]
fn pub_import_reexports_qualified() {
    // Facade `pub import`s square from Math; an importer reaches Facade.square,
    // resolving to Math's definition.
    assert_eq!(
        out("import Facade\nfn main() = print(Facade.square(5))"),
        "25\n"
    );
}

#[test]
fn pub_import_reexport_is_selectively_importable() {
    assert_eq!(
        out("import Facade (square)\nfn main() = print(square(6))"),
        "36\n"
    );
}

#[test]
fn pub_import_without_a_list_reexports_everything() {
    // FacadeAll `pub import`s all of Math, so bump comes through too.
    assert_eq!(
        out("import FacadeAll\nfn main() = print(FacadeAll.bump(3))"),
        "4\n"
    );
}

#[test]
fn plain_import_does_not_reexport() {
    // PlainFacade imports Math without `pub`, so it re-exports nothing.
    let e = err("import PlainFacade\nfn main() = print(PlainFacade.square(5))");
    assert!(e.contains("does not export `square`"), "{e}");
}

#[test]
fn reexports_chain() {
    // Facade2 re-exports from Facade, which re-exports from Math.
    assert_eq!(
        out("import Facade2\nfn main() = print(Facade2.square(7))"),
        "49\n"
    );
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

fn warnings(src: &str) -> Vec<String> {
    check_at(&with_prelude(src), base())
        .expect("should type check")
        .warnings
        .into_iter()
        .map(|w| w.msg)
        .collect()
}

#[test]
fn type_local_instance_is_not_an_orphan() {
    // Stack derives Eq in its own module, anchored to the type: no warning.
    let ws = warnings("import Stack\nfn main() = print(0)");
    assert!(!ws.iter().any(|w| w.contains("orphan")), "{ws:?}");
}

#[test]
fn instance_far_from_class_and_type_warns_orphan() {
    // `Orphan` defines Eq(Widget) but owns neither Eq (prelude) nor Widget (Typ).
    let ws = warnings("import Orphan\nfn main() = print(0)");
    assert!(
        ws.iter().any(|w| w.contains("orphan instance `weq`")),
        "{ws:?}"
    );
}

#[test]
fn overlap_across_modules_warns() {
    let ws = warnings("import Orphan\nimport OrphanB\nfn main() = print(0)");
    assert!(
        ws.iter().any(|w| w.contains("overlapping instances")),
        "{ws:?}"
    );
}
