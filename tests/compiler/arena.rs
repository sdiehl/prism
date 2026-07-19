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

/// Every reified program carries the region bracket: `arena_enter` before the
/// installer's handler activation and `arena_exit` threading its token and
/// result. Without the bracket, reified `alloc`s would fall to the delegating
/// allocator and the region reclamation claim would be silently vacuous.
#[test]
fn reified_installer_is_bracketed_with_region_hooks() {
    for path in ["examples/arena.pr", "examples/arena_escape.pr"] {
        let out = lowered(path);
        assert!(
            out.contains("arena_enter") && out.contains("arena_exit"),
            "`{path}` reifies allocations but carries no region bracket:\n{out}"
        );
    }
}

/// A program with no `Alloc` handler gets no region hooks at all: the bracket
/// rides only on installers, so the non-arena corpus stays byte-identical.
#[test]
fn non_installer_program_has_no_region_hooks() {
    let src = "fn main() : Unit ! {IO} = println(1 + 2)";
    let out = prism::dump("lowered", &prism::with_prelude(src)).expect("lowering succeeds");
    assert!(
        !out.contains("arena_enter") && !out.contains("arena_exit"),
        "region hooks leaked into a program without an `Alloc` handler:\n{out}"
    );
}
