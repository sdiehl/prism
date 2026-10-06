// A raw multiline literal is reprinted as written, so the width oracle measures
// it line by line: a literal whose lines each fit stays in argument position
// instead of pushing the call into the broken-argument layout.

fn fmt(src: &str) -> String {
    let once = prism::format(src).expect("case must parse");
    let twice = prism::format(&once).expect("formatted output must parse");
    assert_eq!(once, twice, "formatter is not idempotent on this case");
    once
}

#[test]
fn long_raw_literal_stays_in_argument_position() {
    let src = r#"fn main() =
  println(r"""
    first line of a fairly long block of text here
    second line of a fairly long block of text here
    third line
    """)
  let x = concat("x", r"""
    first line of a fairly long block of text here
    second line of a fairly long block of text here
    """)
  println(x)
"#;
    assert_eq!(fmt(src), src);
}
