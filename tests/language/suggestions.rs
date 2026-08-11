//! An unknown name is reported with the in-scope names it is closest to. The
//! suggestion is a help line on the diagnostic, so it travels through the same
//! renderer every other hint uses, and it stays silent when nothing in scope is
//! within the edit budget: a wrong guess is worse than no guess.

use prism::report;

fn help_for(src: &str) -> String {
    let out = report(src);
    out.lines()
        .filter(|l| l.contains("did you mean"))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn unbound_variable_names_the_nearest_binding() {
    let out = help_for("fn main() : Int =\n  let counter = 1\n  countr\n");
    assert!(out.contains("did you mean `counter`?"), "{out}");
}

#[test]
fn a_name_nothing_is_close_to_gets_no_guess() {
    let out = help_for("fn main() : Int =\n  let counter = 1\n  zzzzzz\n");
    assert!(out.is_empty(), "{out}");
}

#[test]
fn unknown_field_names_the_nearest_field() {
    let out = help_for(
        "type Shape = Circle { radius: Int }\n\nfn main() : Int =\n  let c = Circle { radiuss = 3 }\n  0\n",
    );
    assert!(out.contains("did you mean `radius`?"), "{out}");
}

#[test]
fn unknown_constructor_names_the_nearest_constructor() {
    let out = help_for(
        "type Shape = Circle { radius: Int }\n\nfn main() : Int =\n  let c = Circel { radius = 3 }\n  0\n",
    );
    assert!(out.contains("did you mean `Circle`?"), "{out}");
}

#[test]
fn unknown_type_names_the_nearest_type() {
    let out = help_for(
        "type Shape = Circle { radius: Int }\n\nfn area(s : Shpe) : Int = 0\n\nfn main() : Int = 0\n",
    );
    assert!(out.contains("did you mean `Shape`?"), "{out}");
}

#[test]
fn unknown_handler_operation_names_the_nearest_operation() {
    let out = help_for(
        "effect Counter\n  tick() : Int\n\nfn go() : Int ! {Counter} = tick()\n\nfn main() : Int =\n  handle go() with {\n    tck() resume k => k(1),\n    return r => r\n  }\n",
    );
    assert!(out.contains("did you mean `tick`?"), "{out}");
}

#[test]
fn unresolved_import_names_the_nearest_module() {
    let out = help_for("import Data.Lst\n\nfn main() : Int = 0\n");
    assert!(out.contains("did you mean `Data.List`"), "{out}");
}
