#[test]
fn test_print() {
    let src = prism::with_prelude(
        r#"
fn main() =
  let msg = "ping"
  println(msg)
"#,
    );
    let run = prism::interpret(&src).unwrap();
    println!("TERM: {}", run.term);
}