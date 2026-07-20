// Lane T (totality): `total fn` / `assume total fn` are contextual claims,
// checked for the trivial-acyclic and direct-structural fragments, erased before
// executable Core. `total`/`assume` stay ordinary identifiers.

const CLAIMS: &str = "\
type Nat = Z | S(Nat)

total fn double(x: Int): Int = x + x

total fn quad(x: Int): Int = double(double(x))

total fn depth(n: Nat): Int =
  match n of
    Z => 0
    S(m) => 1 + depth(m)

assume total fn ext(x: Int): Int = x

total fn needs_helper(x: Int): Int = helper(x)

fn helper(x: Int): Int = x + 1

total fn divides(x: Int): Int = x / 2

total fn bad_rec(n: Nat): Int = bad_rec(n)
";

#[test]
fn totality_classifies_every_claim_honestly() {
    let out = prism::dump("totality", CLAIMS).expect("dump totality");
    // Trivial acyclic, and one that only calls another certified-total function.
    assert!(out.contains("double: checked (acyclic)"), "{out}");
    assert!(out.contains("quad: checked (acyclic)"), "{out}");
    // Direct structural recursion on the algebraic parameter.
    assert!(out.contains("depth: checked (structural on n)"), "{out}");
    // Explicit trusted assumption stays distinct from checked.
    assert!(out.contains("ext: trusted (source assumption)"), "{out}");
    // The consumption rule: a plain helper is not certified, so its caller pends.
    assert!(
        out.contains("needs_helper: pending:") && out.contains("helper"),
        "{out}"
    );
    // Partial primitive, and non-decreasing self-recursion, stay pending — never
    // reported as "non-total".
    assert!(out.contains("divides: pending:"), "{out}");
    assert!(out.contains("bad_rec: pending:"), "{out}");
    assert!(!out.contains("non-total"), "never claims non-total: {out}");
}

#[test]
fn totality_claim_is_erased_from_core() {
    let with = "total fn double(x: Int): Int = x + x\nfn use_it(): Int = double(21)\n";
    let without = "fn double(x: Int): Int = x + x\nfn use_it(): Int = double(21)\n";
    assert_eq!(
        prism::dump("core-hash", with).unwrap(),
        prism::dump("core-hash", without).unwrap(),
        "a `total` claim must not move executable Core"
    );
}

#[test]
fn total_and_assume_remain_identifiers() {
    // `total` as a function name and a local; `assume` as a value. All still
    // compile, because the keywords are contextual to the modifier position.
    let src = "\
fn total(xs: Int): Int = xs

fn f(): Int =
  let assume = 3
  total(assume)
";
    assert!(
        prism::check(src).is_ok(),
        "contextual keywords stay identifiers"
    );
}

#[test]
fn total_claim_formats_and_round_trips() {
    let src = "\
total fn double(x : Int) : Int = x + x

assume total fn ext(x : Int) : Int = x
";
    let once = prism::format(src).expect("parses");
    assert_eq!(once, src, "canonical form is stable");
    assert_eq!(
        prism::format(&once).expect("re-parses"),
        once,
        "formatter is idempotent"
    );
}

// -- T2: `decreases` ranking measure -------------------------------------------

const RANKED: &str = "\
total fn count(n: Int): Int
  requires n >= 0
  decreases n
  = if n == 0 then 0 else count(n - 1)
";

#[test]
fn decreases_measure_reports_ranking_obligations() {
    // Solver-free `dump totality` reports that a `decreases` measure produced
    // ranking obligations to discharge; it never claims (or denies) totality on its
    // own, deferring the verdict to `prism verify`.
    let out = prism::dump("totality", RANKED).expect("dump totality");
    assert!(out.contains("count: ranking:"), "{out}");
    assert!(out.contains("recursive edge"), "{out}");
    assert!(out.contains("prism verify"), "{out}");
    assert!(!out.contains("non-total"), "never claims non-total: {out}");
}

#[test]
fn dump_smt_emits_termination_obligations() {
    // The ranking obligations appear as canonical SMT queries under a termination
    // banner, distinct from any partial-correctness obligation.
    let out = prism::dump("smt", RANKED).expect("dump smt");
    assert!(out.contains("count termination #0"), "{out}");
    assert!(out.contains("measure decreases"), "{out}");
    assert!(out.contains("(check-sat)"), "{out}");
    // Deterministic bytes.
    assert_eq!(out, prism::dump("smt", RANKED).unwrap());
}

#[test]
fn decreases_measure_is_erased_from_core() {
    // Adding `requires`/`decreases` to a recursive function must not move its
    // executable Core: the measure is surface-only proof data.
    let with = "\
total fn count(n: Int): Int
  requires n >= 0
  decreases n
  = if n == 0 then 0 else count(n - 1)
";
    let without = "fn count(n: Int): Int = if n == 0 then 0 else count(n - 1)\n";
    assert_eq!(
        prism::dump("core-hash", with).unwrap(),
        prism::dump("core-hash", without).unwrap(),
        "a `decreases` measure must not move executable Core"
    );
}

#[test]
fn decreases_clause_formats_and_round_trips() {
    let once = prism::format(RANKED).expect("parses");
    let twice = prism::format(&once).expect("re-parses");
    assert_eq!(once, twice, "decreases formatting is idempotent");
    assert!(once.contains("decreases n"), "the measure survives: {once}");
}

#[test]
fn decreases_stays_an_identifier() {
    // `decreases` is contextual to the clause position, so it remains a legal
    // function name and value binder everywhere else.
    let src = "\
fn decreases(x: Int): Int = x

fn f(): Int = decreases(3)
";
    assert!(
        prism::check(src).is_ok(),
        "`decreases` must stay a usable identifier"
    );
}
