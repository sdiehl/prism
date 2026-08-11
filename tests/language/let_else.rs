// The early-return binding is a spelling, not a construct. `let pat = v else fb`
// names exactly the two-arm match a reader writes by hand, so the obligation is
// not "it behaves similarly" but "the compiler cannot tell the two programs
// apart". The content hash is what makes that checkable: it names the
// pre-optimizer elaborated term, so equal hashes mean the optimizer, the effect
// row, and every backend see one program, and no later phase can develop an
// opinion about which surface was written.
//
// The two negative cases pin the edges the desugar deliberately does not smooth
// over. An irrefutable pattern makes the fallback dead, and that is reported as
// the unreachable arm the expansion actually contains rather than silently
// accepted. `?` and `else` are two different answers to a failed step, and
// combining them in one binding is refused by the existing whole-statement rule
// for `?` instead of quietly picking one.

use prism::eval::Rv;
use prism::{check, dump, interpret, with_prelude, Error};

const SUGARED: &str = "\
fn plus_one(o : Option(Int)) : Int =
  let Some(x) = o else 0
  x + 1
";

const EXPANDED: &str = "\
fn plus_one(o : Option(Int)) : Int =
  match o of
    Some(x) => x + 1
    _ => 0
";

const IRREFUTABLE: &str = "\
fn add(p : (Int, Int)) : Int =
  let (a, b) = p else 0
  a + b
";

const WITH_TRY: &str = "\
fn use_it(r : Result(Option(Int), Str)) : Result(Int, Str) =
  let Some(x) = r? else 0
  Ok(x + 1)
";

#[test]
fn desugars_to_the_hand_written_match() {
    let sugared = dump("core-hash", &with_prelude(SUGARED)).expect("the sugar must compile");
    let expanded = dump("core-hash", &with_prelude(EXPANDED)).expect("the match must compile");
    assert_eq!(
        sugared, expanded,
        "the early-return binding must elaborate to the term the hand-written match does"
    );
}

#[test]
fn both_paths_run() {
    let src = with_prelude(&format!(
        "{SUGARED}
fn main() =
  println(plus_one(Some(41)))
  println(plus_one(None))
"
    ));
    let run = interpret(&src).expect("the program must run");
    let out: Vec<String> = run.out.iter().map(Rv::show).collect();
    assert_eq!(out, ["42", "0"]);
}

#[test]
fn irrefutable_pattern_reports_its_dead_fallback() {
    let err = check(&with_prelude(IRREFUTABLE))
        .expect_err("a fallback that can never be taken must be reported");
    let Error::Type(ty) = &err else {
        panic!("expected a type error, got: {err}");
    };
    assert_eq!(ty.code(), Some("E4000"), "got: {err}");
}

#[test]
fn try_in_the_bound_value_is_rejected() {
    let err =
        check(&with_prelude(WITH_TRY)).expect_err("`?` inside the bound value must be rejected");
    let Error::Type(ty) = &err else {
        panic!("expected a type error, got: {err}");
    };
    assert_eq!(ty.code(), Some("E6044"), "got: {err}");
}
