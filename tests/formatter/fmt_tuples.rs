// A one-element tuple carries its meaning in the trailing comma: `(x)` reparses
// as a parenthesized `x`, so printing a 1-tuple without the comma is a silent
// change of meaning that only shows up when the output is read back. `format`
// reparses its own output, so the loss surfaces as an `Err` here; the printed
// form is asserted too, because a reparse alone would not catch the type
// position (where `(Int)` is a legal type that simply means something else).

fn formatted(src: &str) -> String {
    let once = prism::format(src).expect("input must parse");
    let twice = prism::format(&once).expect("formatted output must reparse");
    assert_eq!(once, twice, "formatter not idempotent: {src:?} -> {once:?}");
    once
}

// Expression, pattern, and type position all spell the 1-tuple the same way, and
// each is printed by a different backend (the doc printer, the pattern printer,
// the inline string printer, the type printer).
#[test]
fn a_one_element_tuple_keeps_its_comma_in_every_position() {
    let out = formatted(
        "fn one(v : (Int,)) : (Int,) =\n  match v of\n    (x,) => (x,)\nfn main() = println(one((1,)))\n",
    );
    for spelling in ["(Int,)", "(x,)", "(1,)"] {
        assert!(
            out.contains(spelling),
            "expected `{spelling}` in the formatted output:\n{out}"
        );
    }
    assert!(
        !out.contains("(Int)"),
        "a 1-tuple type printed as a parenthesized type:\n{out}"
    );
}

// A broken 1-tuple (too wide for one line) still needs the comma: the block
// printer only emits a trailing separator in the broken layout, which is why the
// comma is attached to the element rather than requested from the block.
#[test]
fn a_broken_one_element_tuple_keeps_its_comma() {
    let wide = "a_rather_long_identifier_name + another_long_identifier_name + a_third_one_here";
    let out = formatted(&format!(
        "fn wide(a_rather_long_identifier_name, another_long_identifier_name, a_third_one_here) =\n  ({wide},)\n"
    ));
    let sole_element_line = out
        .lines()
        .find(|line| line.trim_start().starts_with("+ a_third_one_here"))
        .unwrap_or_else(|| panic!("the tuple did not break as expected:\n{out}"));
    assert!(
        sole_element_line.ends_with(',') && !sole_element_line.ends_with(",,"),
        "the broken 1-tuple needs exactly one trailing comma:\n{out}"
    );
}
