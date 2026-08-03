// Canonical brace-vs-layout presentation for `try`/`catch`. A genuinely short,
// control-free `try` keeps its inline brace body; a `try` that nests another
// `try` or handler (in the tried expression or a catch arm) breaks vertically so
// the nesting is visible instead of running together as inline braces. Each case
// asserts the exact layout plus the two invariants a reformat rests on: the
// output reparses to the same span-stripped meaning, and formatting is
// idempotent.

use rstest::rstest;

use prism::syntax::ast::{Expr, Pattern};

fn ast_no_spans(src: &str) -> String {
    prism::dump("ast", src)
        .expect("must parse")
        .lines()
        .filter(|l| {
            let t = l.trim_start();
            let stripped = t.trim_end_matches(',');
            let is_span = t.starts_with("span:")
                || matches!(stripped.split_once(".."), Some((a, b)) if !a.is_empty()
                    && a.bytes().all(|c| c.is_ascii_digit())
                    && b.bytes().all(|c| c.is_ascii_digit()));
            !is_span
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn pin(src: &str, want: &str) {
    let once = prism::format(src).expect("input must parse");
    assert_eq!(once, want, "layout drift:\n{once}");
    let twice = prism::format(&once).expect("formatted output must reparse");
    assert_eq!(once, twice, "not idempotent:\n{once}\n-->\n{twice}");
    assert_eq!(
        ast_no_spans(src),
        ast_no_spans(&once),
        "formatting changed the parsed meaning:\n{src}\n-->\n{once}"
    );
}

// A lone, control-free `try` stays inline when it fits.
#[test]
fn short_try_stays_inline() {
    pin(
        "fn f() : Int = try g(x) catch { Bad(e) => 0 }\n",
        "fn f() : Int = try g(x) catch { Bad(e) => 0 }\n",
    );
}

#[rstest]
// A `try` whose tried expression is itself a `try` breaks vertically; the inner,
// control-free `try` still prints inline.
#[case::nested_body(
    "fn f() : Int =\n  let p = try try g(a) catch { Bad(e) => 0 } catch { Worse(e) => 1 }\n  p\n",
    "fn f() : Int =\n  let p =\n    try\n      try g(a) catch { Bad(e) => 0 }\n    catch\n      Worse(e) => 1\n  p\n"
)]
// A `try` whose catch arm nests another `try` breaks vertically too.
#[case::nested_arm(
    "fn f() : Int =\n  try compute(x) catch { Bad(e) => try recover(e) catch { Fatal(z) => 0 } }\n",
    "fn f() : Int =\n  try\n    compute(x)\n  catch\n    Bad(e) => try recover(e) catch { Fatal(z) => 0 }\n"
)]
fn nested_control_breaks_vertically(#[case] src: &str, #[case] want: &str) {
    pin(src, want);
}

#[test]
fn statement_try_restores_full_let_patterns() {
    let src = "\
fn tuple_try(r) =
  let (name, c1) = r?
  (name, c1)

fn ctor_record_try(r) =
  let Some(User { name, .. }) = r?
  name
";
    let once = prism::format(src).expect("pattern-bound statement `?` must parse");
    let twice = prism::format(&once).expect("formatted pattern-bound `?` must reparse");
    assert_eq!(once, twice, "pattern-bound statement `?` is not idempotent");
    assert_eq!(
        ast_no_spans(src),
        ast_no_spans(&once),
        "formatting changed the pattern-bound statement `?` lowering"
    );
    assert!(
        once.contains("let (name, c1) = r?"),
        "tuple binder was not restored: {once}"
    );
    assert!(
        once.contains("let Some(User { name = name, .. }) = r?"),
        "constructor/record binder was not restored: {once}"
    );

    let parsed = prism::parse::parse(src).expect("pattern-bound statement `?` must parse");
    let tuple = &parsed
        .program
        .fns
        .iter()
        .find(|d| d.name == "tuple_try")
        .expect("tuple_try declaration")
        .body;
    let Expr::Match(_, arms) = &tuple.node else {
        panic!("tuple-bound `?` did not lower to a match: {tuple:?}");
    };
    assert!(
        tuple.synth,
        "statement `?` match must carry the formatter marker"
    );
    assert!(matches!(
        &arms[0].pat.node,
        Pattern::Ctor(name, subs)
            if name == "Ok" && matches!(subs.as_slice(), [p]
                if matches!(&p.node, Pattern::Tuple(_)))
    ));

    let ctor = &parsed
        .program
        .fns
        .iter()
        .find(|d| d.name == "ctor_record_try")
        .expect("ctor_record_try declaration")
        .body;
    let Expr::Match(_, arms) = &ctor.node else {
        panic!("constructor-bound `?` did not lower to a match: {ctor:?}");
    };
    assert!(matches!(
        &arms[0].pat.node,
        Pattern::Ctor(ok, subs)
            if ok == "Ok" && matches!(subs.as_slice(), [p]
                if matches!(&p.node, Pattern::Ctor(some, args)
                    if some == "Some" && matches!(args.as_slice(), [record]
                        if matches!(&record.node, Pattern::Record(user, _, true)
                            if user == "User"))))
    ));
}

#[test]
fn statement_try_does_not_broaden_let_pattern_syntax() {
    // `LetPat` deliberately requires an outer constructor or tuple. A record
    // remains legal nested inside a constructor, but not as the outer binder.
    let src = "\
fn bad(r) =
  let User { name } = r?
  name
";
    assert!(
        prism::parse::parse(src).is_err(),
        "statement `?` must use the ordinary restricted let-pattern grammar"
    );
}
