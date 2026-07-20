// SMT contract surface (Lane V): `logic fn` declarations and `requires`/`ensures`
// clauses format canonically and round-trip. The `=` is pushed onto its own
// indented line so the offside rule cannot shear it off at column 0, and layout
// idempotence (`format(format(x)) == format(x)`) rides along.

fn fmt(src: &str) -> String {
    let once = prism::format(src).expect("case must parse");
    let twice = prism::format(&once).expect("formatted output must parse");
    assert_eq!(once, twice, "formatter is not idempotent on this case");
    once
}

#[test]
fn logic_fn_and_inline_body_contract() {
    let src = "\
logic fn nonneg(x : Int) : Bool = x >= 0

fn inc(x : Int) : Int
  requires x >= 0
  ensures |r| r > x
  = x + 1
";
    assert_eq!(fmt(src), src);
}

#[test]
fn requires_only_contract() {
    let src = "\
fn diff(a : Int, b : Int) : Int
  requires a <= b
  = b - a
";
    assert_eq!(fmt(src), src);
}

#[test]
fn block_body_contract() {
    let src = "\
fn clamp(x : Int, lo : Int, hi : Int) : Int
  requires lo <= hi
  ensures |r| lo <= r && r <= hi
  =
    if x < lo then
      lo
    elif x > hi then
      hi
    else
      x
";
    assert_eq!(fmt(src), src);
}

#[test]
fn contextual_words_are_reserved_but_body_shapes_are_free() {
    // The clause keywords are reserved, yet an ordinary program without contracts
    // still formats byte-identically to before the feature.
    let src = "fn add(a : Int, b : Int) : Int = a + b\n";
    assert_eq!(fmt(src), src);
}
