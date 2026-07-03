// `deriving (Identifiable)` is surface sugar: it expands to a bundle of classes
// during desugar, but the sugar must survive to the AST the formatter prints.
// The clause round-trips as written, never as its expansion, and a class named
// both explicitly and inside the bundle prints once, not twice. Layout
// idempotence (`format(format(x)) == format(x)`) rides along so the clause can
// never settle into an unstable form.

fn fmt(src: &str) -> String {
    let once = prism::format(src).expect("case must parse");
    let twice = prism::format(&once).expect("formatted output must parse");
    assert_eq!(once, twice, "formatter is not idempotent on this case");
    once
}

#[test]
fn identifiable_sugar_survives_formatting() {
    let src = "type UserId = UserId(Int) deriving (Identifiable)\n";
    assert_eq!(fmt(src), src);
}

#[test]
fn identifiable_with_explicit_class_is_not_expanded() {
    let src = "type Tag = Tag(String) deriving (Show, Identifiable)\n";
    assert_eq!(fmt(src), src);
}
