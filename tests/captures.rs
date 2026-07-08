// The two diagnostic dump surfaces over elaborated Core: `dump captures`
// (closure capture facts with a portable / nonportable / unknown classification)
// and `dump usage-summary` (a per-definition table of the allocation, fip/fbip,
// borrow, and effect-row facts the compiler already holds). Both are read-only
// analyses, so these pin their content and their determinism, not compilation.

use prism::{dump, with_prelude};

fn cap(src: &str) -> String {
    dump("captures", &with_prelude(src)).expect("captures")
}

fn usage(src: &str) -> String {
    dump("usage-summary", &with_prelude(src)).expect("usage-summary")
}

// One program exercising every capture class: a lambda that captures a `var`
// cell (nonportable), one that reaches a named handler instance (nonportable),
// one that captures a plain value parameter (portable), and one that calls a
// top-level definition (a portable code reference).
const CAPTURES_SRC: &str = "
effect Signal
  ctl ask(Int) : Int

fn helper(x : Int) : Int = x + 1

fn use_cell(n : Int) : Int =
  var total := 0
  for i in srange(1, n) do
    let f = \\() -> total + helper(i)
    total := f()
  total

fn plain(x : Int) : Int =
  let g = \\() -> x + 1
  g()

fn named(x : Int) : Int =
  with acc <- handler
    ask(v, k) => k(v + x)
    return r => r
  let f = \\() -> acc.ask(x)
  f()

fn main() =
  println(use_cell(5))
  println(plain(3))
  println(named(4))
";

// A `var` cell is nonportable and a plainly-typed value parameter is portable,
// each named in the closure that captures it.
#[test]
fn mutable_cell_is_nonportable_value_is_portable() {
    let out = cap(CAPTURES_SRC);
    assert!(
        out.contains("total") && out.contains("mutable-cell") && out.contains("nonportable"),
        "a captured var cell must classify nonportable:\n{out}"
    );
    assert!(
        out.lines()
            .any(|l| l.contains("x ") && l.contains("value") && l.contains("portable")),
        "a captured value parameter must classify portable:\n{out}"
    );
}

// A named handler instance is nonportable, with a reason that names the instance;
// a call to a top-level definition is a portable code reference.
#[test]
fn handler_instance_nonportable_code_ref_portable() {
    let out = cap(CAPTURES_SRC);
    assert!(
        out.contains("handler-instance") && out.contains("nonportable") && out.contains("`acc`"),
        "a captured handler instance must classify nonportable and name the instance:\n{out}"
    );
    assert!(
        out.lines()
            .any(|l| l.contains("helper") && l.contains("code") && l.contains("portable")),
        "a top-level call inside a closure must classify as a portable code reference:\n{out}"
    );
}

// The dump is a pure function of the source: two runs are byte-identical.
#[test]
fn captures_is_deterministic() {
    assert_eq!(cap(CAPTURES_SRC), cap(CAPTURES_SRC));
}

// A program mixing an owned/borrowed function, an `fbip` accumulator, a `@
// noalloc` certificate, and an effectful definition, so every usage column has a
// distinguishing value to pin.
const USAGE_SRC: &str = "
fn len(borrow xs : List(Int)) : Int =
  match xs of
    Nil => 0
    Cons(h, t) => 1 + len(t)

fbip fn rev_go(xs : List(Int), acc : List(Int)) : List(Int) =
  match xs of
    Nil => acc
    Cons(h, t) => rev_go(t, Cons(h, acc))

fn sum_len(xs : List(Int)) : Int @ noalloc =
  match xs of
    Nil => 0
    Cons(h, t) => h + sum_len(t)

fn shout(s : String) : Int =
  println(s)
  0

fn main() =
  println(len([1, 2, 3]))
  println(sum_len(rev_go([1, 2, 3], Nil)))
  shout(\"hi\")
";

// Each usage column carries the fact from its canonical source: the `@ noalloc`
// certificate, the `fbip` discipline, the borrow mask, and the effect row. The
// table drops prelude and stdlib definitions, keeping the program's own.
#[test]
fn usage_summary_columns_carry_each_fact() {
    let out = usage(USAGE_SRC);
    let line = |name: &str| {
        out.lines()
            .find(|l| l.split('\t').next() == Some(name))
            .unwrap_or_else(|| panic!("no usage line for `{name}` in:\n{out}"))
            .to_string()
    };
    // header names the format and the whole-program tier
    assert!(
        out.lines()
            .next()
            .unwrap()
            .contains("prism-usage-summary-v1")
            && out.lines().next().unwrap().contains("tier="),
        "header must name the format version and tier:\n{out}"
    );
    assert_eq!(line("sum_len").split('\t').nth(1), Some("yes"), "@ noalloc");
    assert_eq!(
        line("rev_go").split('\t').nth(2),
        Some("fbip"),
        "discipline"
    );
    assert_eq!(line("len").split('\t').nth(3), Some("b"), "borrow mask");
    assert_eq!(line("shout").split('\t').nth(4), Some("{IO}"), "effect row");
    // A prelude definition must not leak into the program's own summary.
    assert!(
        !out.lines()
            .any(|l| l.starts_with("pi\t") || l.contains("map_empty")),
        "prelude and stdlib definitions must be filtered:\n{out}"
    );
}

#[test]
fn usage_summary_is_deterministic() {
    assert_eq!(usage(USAGE_SRC), usage(USAGE_SRC));
}
