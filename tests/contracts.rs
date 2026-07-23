// `logic fn` declarations and `requires`/`ensures` contract clauses parse and
// format as surface-only proof data erased before executable Core. The
// load-bearing invariant is that a contract-only edit cannot move any runtime
// artifact.

// The same two functions, once with a `logic fn` and contract clauses, once
// bare. Their executable Core must be byte-identical.
const WITH_CONTRACTS: &str = "\
logic fn nonneg(x: Int): Bool = x >= 0

fn clamp(x: Int, lo: Int, hi: Int): Int
  requires lo <= hi
  ensures |r| nonneg(r)
  = if x < lo then lo else if x > hi then hi else x

fn use_it(): Int = clamp(5, 0, 10)
";

const WITHOUT_CONTRACTS: &str = "\
fn clamp(x: Int, lo: Int, hi: Int): Int =
  if x < lo then lo else if x > hi then hi else x

fn use_it(): Int = clamp(5, 0, 10)
";

#[test]
fn contracts_leave_core_byte_identical() {
    let with = prism::dump("core-hash", WITH_CONTRACTS).expect("contract program compiles");
    let without = prism::dump("core-hash", WITHOUT_CONTRACTS).expect("bare program compiles");
    assert_eq!(
        with, without,
        "a contract-only edit moved the Core hash: contracts are not fully erased"
    );
}

#[test]
fn contract_program_typechecks() {
    // The contracted program is ordinary compilable Prism: the clauses are
    // ignored by resolution and typecheck, not rejected.
    assert!(prism::check(WITH_CONTRACTS).is_ok());
}

#[test]
fn contract_clauses_format_and_round_trip() {
    let once = prism::format(WITH_CONTRACTS).expect("contract program parses");
    let twice = prism::format(&once).expect("formatted contract program re-parses");
    assert_eq!(once, twice, "contract formatting is not idempotent");
    // The clause keywords survive the round trip.
    assert!(once.contains("requires "));
    assert!(once.contains("ensures |r|"));
    assert!(once.contains("logic fn nonneg"));
}

#[test]
fn clause_keywords_are_reserved() {
    // `requires` is now a keyword, so binding it as a function name is a parse
    // error rather than a valid definition.
    let src = "fn requires(x: Int): Int = x\n";
    assert!(
        prism::check(src).is_err(),
        "`requires` must be reserved, not a legal identifier"
    );
}

// -- Logical checker diagnostics ------------------------------------------------

/// The stable diagnostic code for a program the logical checker rejects.
fn err_code(src: &str) -> String {
    prism::check(src)
        .expect_err("program must be rejected")
        .code()
        .as_str()
        .to_string()
}

#[test]
fn logical_checker_diagnostics() {
    // Each category maps to its own stable E8xxx code.
    assert_eq!(err_code("fn f(x: Int): Int requires y >= 0 = x\n"), "E8001"); // unresolved
    assert_eq!(
        err_code("fn g(x: Int): Int = x\n\nfn f(x: Int): Int requires g(x) >= 0 = x\n"),
        "E8002" // a runtime function is not in logical scope
    );
    assert_eq!(
        err_code("fn f(x: Int): Int ensures |r| r + 1 = x\n"),
        "E8003"
    ); // clause not Bool
    assert_eq!(
        err_code("logic fn p(a: Int): Bool = a >= 0\n\nfn f(x: Int): Int requires p(x, x) = x\n"),
        "E8004" // wrong arity
    );
    assert_eq!(
        err_code("logic fn p(a: Int): Bool = a >= 0\nlogic fn p(a: Int): Bool = a <= 0\n\nfn f(x: Int): Int = x\n"),
        "E8005" // duplicate logical declaration
    );
    assert_eq!(err_code("fn f(x: Int): Int requires \"hi\" = x\n"), "E8000"); // unsupported node
    assert_eq!(
        err_code("fn f(x: Int): Int requires x * x >= 0 = x\n"),
        "E8000"
    ); // nonlinear
    assert_eq!(err_code("fn f(x: Float): Int requires true = 3\n"), "E8000"); // unsupported sort
}

#[test]
fn valid_contract_and_logic_fn_check() {
    let src = "\
logic fn nonneg(x: Int): Bool = x >= 0
logic fn between(x: Int, lo: Int, hi: Int): Bool = lo <= x && x <= hi

fn clamp(x: Int, lo: Int, hi: Int): Int
  requires lo <= hi
  ensures |r| between(r, lo, hi)
  ensures |r| nonneg(r)
  = if x < lo then lo else if x > hi then hi else x
";
    assert!(prism::check(src).is_ok());
}

// -- Verification interface and the dual determinism invariant -----------------

fn verify_digest(src: &str) -> String {
    let interface = prism::dump("verify", src).expect("verify dump");
    interface
        .lines()
        .find_map(|l| l.strip_prefix("digest "))
        .expect("interface has a digest line")
        .to_string()
}

const CONTRACT_BODY_A: &str = "fn f(x: Int): Int requires x >= 0 = x + 1\n";
// Same contract, different runtime body.
const CONTRACT_BODY_B: &str = "fn f(x: Int): Int requires x >= 0 = x + 2\n";
// Same runtime body, different contract.
const CONTRACT_C: &str = "fn f(x: Int): Int requires x >= 1 = x + 1\n";

#[test]
fn contract_change_moves_interface_but_not_core() {
    // A contract-only edit moves the verification interface and leaves Core alone.
    assert_ne!(
        verify_digest(CONTRACT_BODY_A),
        verify_digest(CONTRACT_C),
        "a changed contract must move the verification interface digest"
    );
    assert_eq!(
        prism::dump("core-hash", CONTRACT_BODY_A).unwrap(),
        prism::dump("core-hash", CONTRACT_C).unwrap(),
        "a contract-only edit must not move the Core hash"
    );
}

#[test]
fn body_change_moves_core_but_not_interface() {
    // A runtime-body-only edit moves Core and leaves the verification interface.
    assert_ne!(
        prism::dump("core-hash", CONTRACT_BODY_A).unwrap(),
        prism::dump("core-hash", CONTRACT_BODY_B).unwrap(),
        "a changed body must move the Core hash"
    );
    assert_eq!(
        verify_digest(CONTRACT_BODY_A),
        verify_digest(CONTRACT_BODY_B),
        "a body-only edit must not move the verification interface digest"
    );
}

#[test]
fn interface_is_deterministic() {
    assert_eq!(
        verify_digest(CONTRACT_BODY_A),
        verify_digest(CONTRACT_BODY_A)
    );
}

// -- Verification-condition generation: `dump smt` -----------------------------

#[test]
fn dump_smt_emits_deterministic_obligations() {
    let src = "fn clamp(x: Int, lo: Int, hi: Int): Int\n  \
               requires lo <= hi\n  \
               ensures |r| lo <= r\n  \
               = if x < lo then lo else if x > hi then hi else x\n";
    let out = prism::dump("smt", src).expect("dump smt");
    assert_eq!(
        out,
        prism::dump("smt", src).unwrap(),
        "obligation bytes must be deterministic"
    );
    assert!(out.contains("clamp #0"), "names the obligation:\n{out}");
    assert!(out.contains("(set-logic QF_LIA)"));
    assert!(out.contains("(check-sat)"));
}
