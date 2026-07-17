//! Scope-directed arena lowering: the load-bearing exclusion.
//!
//! `arena_only = arena_reachable \ otherwise_reachable`. The whole gate is that a
//! shared function (reachable from both an arena and a non-arena path) is NOT
//! rewritten: reifying it would change its non-arena call and break byte-identity.
//! These tests read the two committed corpus examples and check the structural
//! outcome directly in the lowered Core (`init_at` is the reification marker).

use std::fs;

fn lowered(path: &str) -> String {
    let src = fs::read_to_string(path).unwrap();
    prism::dump("lowered", &prism::with_prelude(&src))
        .unwrap_or_else(|e| panic!("lowering `{path}` failed: {e:?}"))
}

/// A genuinely arena-only builder (`build`, reachable only through the
/// `with_arena` thunk) has its `Cons` cells reified into `alloc` + `init_at`.
#[test]
fn arena_only_builder_is_reified() {
    let out = lowered("examples/arena.pr");
    assert!(
        out.contains("init_at"),
        "arena-only constructor was not reified into `init_at`:\n{out}"
    );
}

/// A shared function (`boxed`, called both inside `with_arena` and directly from
/// `main`) MUST stay on the raw path: no `init_at` anywhere, because reifying it
/// would silently change the non-arena call. This is the byte-identity gate.
#[test]
fn shared_function_is_not_reified() {
    let out = lowered("examples/arena_shared.pr");
    assert!(
        !out.contains("init_at"),
        "a shared (non-arena-only) constructor was reified, breaking byte-identity:\n{out}"
    );
}
