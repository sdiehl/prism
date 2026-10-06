// A handler around an unannotated thunk parameter owns that thunk's row: the
// labels it handles are part of what the action may perform, not something it
// passes on to its caller. Before this, the handled label stayed in the
// function's own row, so every caller of `run_ask` had to handle `Ask` again.
//
// The tail is only owned when nothing else can produce it. `twice` calls the
// action outside its handler too, so `Ask` there reaches the caller, and its
// signature must not claim otherwise.

use std::collections::BTreeMap;

const PROGRAM: &str = include_str!("../fixtures/language/handled_tail.pr");

fn sigs() -> BTreeMap<String, String> {
    let checked = prism::check(&prism::with_prelude(PROGRAM)).expect("program should type check");
    checked
        .defs
        .decls
        .iter()
        .map(|d| (d.name.clone(), d.ty.show()))
        .collect()
}

#[test]
fn a_handler_discharges_its_labels_from_the_action() {
    let sigs = sigs();
    assert_eq!(
        sigs["run_ask"],
        "forall e0 a. (() -> a ! {Ask, e0}) -> a ! {e0}"
    );
    assert_eq!(
        sigs["collect"],
        "forall e0 a b. (() -> a ! {Put(b), e0}) -> List(b) ! {e0}"
    );
    assert_eq!(
        sigs["both_ops"],
        "forall e0 a. (() -> a ! {Ask, Log, e0}) -> a ! {e0}"
    );
}

#[test]
fn an_action_also_run_outside_the_handler_keeps_its_row() {
    assert_eq!(
        sigs()["twice"],
        "forall e0. (() -> Int ! {e0}) -> Int ! {e0}"
    );
}

#[test]
fn the_handled_program_runs() {
    let run = prism::interpret(&prism::with_prelude(PROGRAM)).expect("program should run");
    assert_eq!(run.term, "43\n[1, 2]\n1\n49\n6\n");
}
