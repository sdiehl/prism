// Canonical brace-vs-layout presentation for `try`/`catch`. A genuinely short,
// control-free `try` keeps its inline brace body; a `try` that nests another
// `try` or handler (in the tried expression or a catch arm) breaks vertically so
// the nesting is visible instead of running together as inline braces. Each case
// asserts the exact layout plus the two invariants a reformat rests on: the
// output reparses to the same span-stripped meaning, and formatting is
// idempotent.

use rstest::rstest;

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
