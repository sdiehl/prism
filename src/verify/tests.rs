use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

use crate::store::disk::Store;
use crate::verify::certificate::{
    CertObligation, CertTrust, ClosureStatus, Completeness, SmtCertificate,
};
use crate::verify::logic::{Contract, FuncDecl, FuncId, LogicExpr, LogicSort, Obligation, VarId};
use crate::verify::ranking::{self, RankKind, RankStatus};
use crate::verify::response::{parse, SolverStatus};
use crate::verify::result::{
    ModelBinding, ResultStatus, SmtResult, SolverId, Trust, TRUST_PROOF_CHECKED,
};
use crate::verify::run::VerifyOptions;
use crate::verify::store as verify_store;
use crate::verify::vc::VcStatus;
use crate::verify::wf::{self, WfError};
use crate::verify::{normalize, query, run, smtlib, solver, vc};

fn var(i: u32) -> LogicExpr {
    LogicExpr::var(VarId(i))
}

/// `x >= 0 && x < 10  =>  x < 20`, over one `Int` variable.
fn sample() -> Obligation {
    Obligation {
        vars: vec![LogicSort::Int],
        funcs: vec![],
        assumptions: vec![
            LogicExpr::ge(var(0), LogicExpr::int(0)),
            LogicExpr::lt(var(0), LogicExpr::int(10)),
        ],
        goal: LogicExpr::lt(var(0), LogicExpr::int(20)),
    }
}

#[test]
fn wf_accepts_well_sorted() {
    assert_eq!(wf::check(&sample()), Ok(()));
}

#[test]
fn wf_rejects_non_bool_goal() {
    let ob = Obligation {
        vars: vec![],
        funcs: vec![],
        assumptions: vec![],
        goal: LogicExpr::int(3),
    };
    assert_eq!(wf::check(&ob), Err(WfError::GoalNotBool(LogicSort::Int)));
}

#[test]
fn wf_rejects_unknown_var() {
    let ob = Obligation {
        vars: vec![],
        funcs: vec![],
        assumptions: vec![],
        goal: LogicExpr::eq(var(0), var(0)),
    };
    assert_eq!(wf::check(&ob), Err(WfError::UnknownVar(VarId(0))));
}

#[test]
fn wf_rejects_int_argument_to_boolean_operator() {
    // `not(1)` is ill-sorted: `not` wants `Bool`.
    let ob = Obligation {
        vars: vec![],
        funcs: vec![],
        assumptions: vec![],
        goal: LogicExpr::not(LogicExpr::int(1)),
    };
    assert!(matches!(wf::check(&ob), Err(WfError::Sort { .. })));
}

#[test]
fn smtlib_encodes_canonical_bytes() {
    let ob = sample();
    assert_eq!(wf::check(&ob), Ok(()));
    let expected = "\
(set-logic QF_LIA)
(declare-const x0 Int)
(assert (>= x0 0))
(assert (< x0 10))
(assert (not (< x0 20)))
(check-sat)
";
    assert_eq!(smtlib::encode(&ob), expected);
}

#[test]
fn smtlib_negative_literal_and_uninterpreted_function() {
    // `f(x0) >= -3  =>  f(x0) > -4`, exercising QF_UFLIA, `(- k)`, and `(f0 x0)`.
    let fx = LogicExpr::func(FuncId(0), vec![var(0)]);
    let ob = Obligation {
        vars: vec![LogicSort::Int],
        funcs: vec![FuncDecl {
            params: vec![LogicSort::Int],
            result: LogicSort::Int,
        }],
        assumptions: vec![LogicExpr::ge(fx.clone(), LogicExpr::int(-3))],
        goal: LogicExpr::gt(fx, LogicExpr::int(-4)),
    };
    assert_eq!(wf::check(&ob), Ok(()));
    let expected = "\
(set-logic QF_UFLIA)
(declare-const x0 Int)
(declare-fun f0 (Int) Int)
(assert (>= (f0 x0) (- 3)))
(assert (not (> (f0 x0) (- 4))))
(check-sat)
";
    assert_eq!(smtlib::encode(&ob), expected);
}

fn goal_only(goal: LogicExpr, vars: Vec<LogicSort>) -> Obligation {
    Obligation {
        vars,
        funcs: vec![],
        assumptions: vec![],
        goal,
    }
}

#[test]
fn normalize_is_alpha_and_unused_invariant() {
    // `v < 5` over one Int, declared two different ways.
    let a = goal_only(
        LogicExpr::lt(var(0), LogicExpr::int(5)),
        vec![LogicSort::Int],
    );
    // Same logic, but the used variable is `var1` behind an unused `Bool` `var0`.
    let b = goal_only(
        LogicExpr::lt(var(1), LogicExpr::int(5)),
        vec![LogicSort::Bool, LogicSort::Int],
    );
    assert_eq!(wf::check(&a), Ok(()));
    assert_eq!(wf::check(&b), Ok(()));
    assert_eq!(
        smtlib::encode(&normalize::normalize(&a)),
        smtlib::encode(&normalize::normalize(&b))
    );
    assert_eq!(
        normalize::structural_digest(&a),
        normalize::structural_digest(&b)
    );
}

#[test]
fn digest_moves_on_operator_change() {
    let lt = goal_only(
        LogicExpr::lt(var(0), LogicExpr::int(5)),
        vec![LogicSort::Int],
    );
    let le = goal_only(
        LogicExpr::le(var(0), LogicExpr::int(5)),
        vec![LogicSort::Int],
    );
    assert_ne!(
        normalize::structural_digest(&lt),
        normalize::structural_digest(&le)
    );
}

#[test]
fn digest_moves_on_literal_change() {
    let five = goal_only(
        LogicExpr::lt(var(0), LogicExpr::int(5)),
        vec![LogicSort::Int],
    );
    let six = goal_only(
        LogicExpr::lt(var(0), LogicExpr::int(6)),
        vec![LogicSort::Int],
    );
    assert_ne!(
        normalize::structural_digest(&five),
        normalize::structural_digest(&six)
    );
}

#[test]
fn query_build_is_stable_and_inspectable() {
    let q = query::SmtQuery::build(&sample());
    assert_eq!(q.logic, "QF_LIA");
    assert_eq!(q.digest.len(), 64);
    assert!(q
        .render()
        .starts_with("prism-smt-query-v1\nlogic QF_LIA\ndigest "));
    // Building the same obligation twice is byte-identical.
    assert_eq!(q.digest, query::SmtQuery::build(&sample()).digest);
}

#[test]
fn response_parser_classifies_solver_output() {
    use crate::verify::response::ResponseError;
    assert_eq!(parse("unsat\n"), Ok(SolverStatus::Unsat));
    assert_eq!(
        parse("sat\n(\n  (define-fun x0 () Int 0)\n)\n"),
        Ok(SolverStatus::Sat)
    );
    assert_eq!(parse("unknown\n"), Ok(SolverStatus::Unknown));
    assert_eq!(parse("   \n"), Err(ResponseError::Empty));
    assert_eq!(parse("sat\nunsat\n"), Err(ResponseError::Contradictory));
    assert_eq!(parse("banana\n"), Err(ResponseError::Unrecognized));
    assert!(matches!(
        parse("(error \"line 1: unknown sort\")\n"),
        Err(ResponseError::Solver(_))
    ));
}

// -- Contracts (the internal representation) ----------------------------------

/// `clamp`-shaped: params (x, lo, hi) at `VarId` 0..3, `requires lo <= hi`,
/// result binder at `VarId` 3, `ensures lo <= r && r <= hi`. `x` is declared but,
/// as in real clamp contracts, unconstrained by the postcondition.
fn sample_contract() -> Contract {
    let (lo, hi, r) = (var(1), var(2), var(3));
    Contract {
        params: vec![LogicSort::Int, LogicSort::Int, LogicSort::Int],
        requires: vec![LogicExpr::le(lo.clone(), hi.clone())],
        result: LogicSort::Int,
        ensures: vec![LogicExpr::and(vec![
            LogicExpr::le(lo, r.clone()),
            LogicExpr::le(r, hi),
        ])],
    }
}

#[test]
fn wf_accepts_well_formed_contract() {
    assert_eq!(wf::check_contract(&sample_contract()), Ok(()));
}

#[test]
fn wf_rejects_result_reference_in_requires() {
    // The result binder (VarId 1 here) is not in scope in `requires`.
    let c = Contract {
        params: vec![LogicSort::Int],
        requires: vec![LogicExpr::ge(var(1), LogicExpr::int(0))],
        result: LogicSort::Int,
        ensures: vec![],
    };
    assert_eq!(wf::check_contract(&c), Err(WfError::UnknownVar(VarId(1))));
}

#[test]
fn wf_rejects_non_bool_ensures() {
    let c = Contract {
        params: vec![],
        requires: vec![],
        result: LogicSort::Int,
        // `ensures` clause is the result value itself, an Int, not a Bool.
        ensures: vec![var(0)],
    };
    assert_eq!(
        wf::check_contract(&c),
        Err(WfError::EnsuresNotBool(LogicSort::Int))
    );
}

#[test]
fn contract_digest_is_stable_and_moves_on_clause_change() {
    let a = sample_contract();
    assert_eq!(
        normalize::contract_digest(&a),
        normalize::contract_digest(&sample_contract())
    );
    // Loosen a postcondition (`<=` becomes `<`): the digest must move.
    let mut b = sample_contract();
    b.ensures = vec![LogicExpr::lt(var(1), var(3))];
    assert_ne!(
        normalize::contract_digest(&a),
        normalize::contract_digest(&b)
    );
}

// -- z3 solver-accept gate -----------------------------------------------------

/// Locate a z3 binary: `PRISM_Z3` if set, else `z3` on `PATH`, confirmed by a
/// successful `--version`. `None` means the gate is skipped (no solver present).
fn z3_exe() -> Option<String> {
    let exe = std::env::var("PRISM_Z3").unwrap_or_else(|_| "z3".to_string());
    let ok = Command::new(&exe)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success());
    ok.then_some(exe)
}

/// Run one canonical SMT-LIB script through z3 over stdin and parse its status
/// through the same response parser the out-of-process adapter uses.
fn z3_status(exe: &str, script: &str) -> SolverStatus {
    let mut child = Command::new(exe)
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn z3");
    child
        .stdin
        .take()
        .expect("z3 stdin")
        .write_all(script.as_bytes())
        .expect("write z3 stdin");
    let out = child.wait_with_output().expect("z3 output");
    let text = String::from_utf8_lossy(&out.stdout);
    parse(&text).unwrap_or_else(|e| panic!("z3 output not parseable: {text:?} ({e:?})"))
}

/// Portable-fragment corpus: each obligation paired with the status z3 must
/// return for its encoded script. `Unsat` = the obligation is valid (its negation
/// is unsatisfiable); `Sat` = a counterexample exists.
fn solver_corpus() -> Vec<(&'static str, Obligation, SolverStatus)> {
    let bool0 = || var(0);
    vec![
        // Linear integer arithmetic: 0 <= x < 10 => x < 20. Valid.
        ("lia_bounds", sample(), SolverStatus::Unsat),
        // Weakening that does not hold: x < 20 => x < 10. Counterexample x = 15.
        (
            "lia_counterexample",
            Obligation {
                vars: vec![LogicSort::Int],
                funcs: vec![],
                assumptions: vec![LogicExpr::lt(var(0), LogicExpr::int(20))],
                goal: LogicExpr::lt(var(0), LogicExpr::int(10)),
            },
            SolverStatus::Sat,
        ),
        // Boolean structure: p || !p is a tautology. Valid.
        (
            "bool_excluded_middle",
            goal_only(
                LogicExpr::or(vec![bool0(), LogicExpr::not(bool0())]),
                vec![LogicSort::Bool],
            ),
            SolverStatus::Unsat,
        ),
        // Equality congruence over LIA: a = b => a + 1 = b + 1. Valid.
        (
            "eq_congruence",
            Obligation {
                vars: vec![LogicSort::Int, LogicSort::Int],
                funcs: vec![],
                assumptions: vec![LogicExpr::eq(var(0), var(1))],
                goal: LogicExpr::eq(
                    LogicExpr::add(vec![var(0), LogicExpr::int(1)]),
                    LogicExpr::add(vec![var(1), LogicExpr::int(1)]),
                ),
            },
            SolverStatus::Unsat,
        ),
        // Uninterpreted function reflexivity: f(x) = f(x). Valid (QF_UFLIA).
        (
            "uf_reflexivity",
            Obligation {
                vars: vec![LogicSort::Int],
                funcs: vec![FuncDecl {
                    params: vec![LogicSort::Int],
                    result: LogicSort::Int,
                }],
                assumptions: vec![],
                goal: LogicExpr::eq(
                    LogicExpr::func(FuncId(0), vec![var(0)]),
                    LogicExpr::func(FuncId(0), vec![var(0)]),
                ),
            },
            SolverStatus::Unsat,
        ),
    ]
}

#[test]
fn z3_discharges_portable_fragment_corpus() {
    let Some(exe) = z3_exe() else {
        eprintln!("skipping z3_discharges_portable_fragment_corpus: no z3 on PATH or PRISM_Z3");
        return;
    };
    for (name, ob, expected) in solver_corpus() {
        assert_eq!(wf::check(&ob), Ok(()), "{name} is ill-formed");
        let script = smtlib::encode(&normalize::normalize(&ob));
        assert_eq!(z3_status(&exe, &script), expected, "z3 disagreed on {name}");
    }
}

// -- prism-smt-query-v1 compatibility fixture ----------------------------------

/// The committed query artifact bytes for `sample()`. Rebuilding the same
/// obligation must reproduce them exactly, pinning the schema, canonical SMT-LIB,
/// and digest across releases. Re-bless with `PRISM_BLESS_SMT=1`.
#[test]
fn query_v1_compat_fixture() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/smt/sample.query"
    );
    let got = query::SmtQuery::build(&sample()).render();
    if std::env::var("PRISM_BLESS_SMT").is_ok() {
        std::fs::write(path, &got).expect("write smt fixture");
    }
    let want = std::fs::read_to_string(path)
        .expect("missing tests/fixtures/smt/sample.query; bless with PRISM_BLESS_SMT=1");
    assert_eq!(
        got, want,
        "prism-smt-query-v1 bytes drifted from the fixture"
    );
}

// -- VC generation -------------------------------------------------------------

fn parse_prog(src: &str) -> crate::syntax::ast::Program {
    crate::parse::parse(src)
        .expect("test program parses")
        .program
}

#[test]
fn vc_generates_postconditions_and_flags_unsupported_bodies() {
    // `clamp` is in the scalar fragment: one obligation per `ensures` clause.
    // `viac`'s body calls a runtime function, so it is pending, not rejected.
    let prog = parse_prog(
        "\
fn clamp(x: Int, lo: Int, hi: Int): Int
  requires lo <= hi
  ensures |r| lo <= r
  ensures |r| r <= hi
  = if x < lo then lo else if x > hi then hi else x

fn dbl(y: Int): Int = y + y

fn viac(x: Int): Int
  ensures |r| r >= 0
  = dbl(x)
",
    );
    let vcs = vc::generate(&prog).expect("VC generation");
    let clamp = vcs
        .iter()
        .find(|f| f.name == "clamp")
        .expect("clamp present");
    match &clamp.status {
        VcStatus::Obligations(obs) => assert_eq!(obs.len(), 2, "one obligation per ensures"),
        VcStatus::Pending(r) => panic!("clamp should be eligible, got pending: {r}"),
    }
    let viac = vcs.iter().find(|f| f.name == "viac").expect("viac present");
    assert!(
        matches!(viac.status, VcStatus::Pending(_)),
        "a runtime call in the body is pending, not an obligation"
    );
}

// -- External discharge, gated on a present z3 ---------------------------------

#[test]
fn verify_discharges_valid_and_refutes_invalid() {
    let Some(exe) = z3_exe() else {
        eprintln!("skipping verify_discharges_valid_and_refutes_invalid: no z3");
        return;
    };
    // `inc` provably meets both postconditions; `bad` does not (`r > 100` has a
    // counterexample under `x >= 0`).
    let prog = parse_prog(
        "\
fn inc(x: Int): Int
  requires x >= 0
  ensures |r| r > x
  ensures |r| r >= 0
  = x + 1

fn bad(x: Int): Int
  requires x >= 0
  ensures |r| r > 100
  = x + 1
",
    );
    let report = run::run(&prog, &exe).expect("verify runs");
    let out = report.render();
    assert!(out.contains("inc: verified"), "inc must verify:\n{out}");
    assert!(
        out.contains("bad: counterexample"),
        "bad must be refuted:\n{out}"
    );
    assert!(!report.all_clear(), "a refuted contract is not all-clear");
}

#[test]
fn missing_solver_is_reported_not_silently_accepted() {
    let prog = parse_prog("fn inc(x: Int): Int\n  ensures |r| r > x\n  = x + 1\n");
    let report = run::run(&prog, "prism_no_such_solver_exe").expect("verify runs");
    assert!(report.render().contains("not found"));
    assert!(
        !report.all_clear(),
        "a missing solver never yields all-clear"
    );
}

// -- Termination ranking -------------------------------------------------------

/// The ranking analysis of one function by name.
fn ranking_for(src: &str, name: &str) -> RankStatus {
    ranking::generate(&parse_prog(src))
        .into_iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no ranking analysis for `{name}`"))
        .status
}

const COUNTDOWN: &str = "\
total fn count(n: Int): Int
  requires n >= 0
  decreases n
  = if n == 0 then 0 else count(n - 1)
";

#[test]
fn ranking_covers_entry_and_every_recursive_edge() {
    // Two self-calls guarded by nested conditions: each is a recursive SCC edge and
    // gets a nonnegativity and a decrease obligation, plus one entry obligation.
    let src = "\
total fn twostep(n: Int): Int
  requires n >= 0
  decreases n
  = if n == 0 then 0 else if n == 1 then 1 else twostep(n - 1) + twostep(n - 2)
";
    let RankStatus::Obligations { edges, obligations } = ranking_for(src, "twostep") else {
        panic!("twostep should produce ranking obligations");
    };
    assert_eq!(edges, 2, "both self-calls are recursive edges");
    assert_eq!(
        obligations.len(),
        5,
        "1 entry + 2 edges x (nonneg + decrease)"
    );
    assert_eq!(obligations[0].kind, RankKind::EntryNonneg);
    let kinds: Vec<&RankKind> = obligations.iter().map(|o| &o.kind).collect();
    assert!(kinds.contains(&&RankKind::EdgeDecrease(0)));
    assert!(kinds.contains(&&RankKind::EdgeDecrease(1)));
    // Every edge obligation carries the edge's path condition as an assumption
    // (both `n != 0` and `n != 1` guard the recursive calls).
    for o in &obligations {
        if matches!(o.kind, RankKind::EdgeDecrease(_) | RankKind::EdgeNonneg(_)) {
            assert!(
                o.ob.assumptions.len() >= 3,
                "an edge obligation assumes the precondition and both path conditions"
            );
        }
    }
    // Each generated obligation is well-sorted (reusing the contract WF checker).
    for o in &obligations {
        assert_eq!(wf::check(&o.ob), Ok(()));
    }
}

#[test]
fn ranking_emits_call_site_precondition() {
    // A recursive `total fn` calling a contracted helper must discharge the helper's
    // precondition at the call site, so consuming the helper's totality is sound.
    let src = "\
total fn needs_pos(x: Int): Int
  requires x >= 1
  = x

total fn callpre(n: Int): Int
  requires n >= 0
  decreases n
  = if n == 0 then 0 else needs_pos(n) + callpre(n - 1)
";
    let RankStatus::Obligations { obligations, .. } = ranking_for(src, "callpre") else {
        panic!("callpre should produce ranking obligations");
    };
    assert!(
        obligations
            .iter()
            .any(|o| matches!(&o.kind, RankKind::CallPrecondition(c) if c == "needs_pos")),
        "the call to `needs_pos` under its precondition creates a call-site obligation"
    );
}

#[test]
fn ranking_pending_on_measure_outside_fragment() {
    // A nonlinear measure is outside the linear-integer fragment, so the function is
    // reported pending with a precise reason, never "non-total".
    let src = "\
total fn f(n: Int): Int
  requires n >= 0
  decreases n * n
  = if n == 0 then 0 else f(n - 1)
";
    match ranking_for(src, "f") {
        RankStatus::Pending(reason) => assert!(reason.contains("measure")),
        RankStatus::Obligations { .. } => panic!("a nonlinear measure must stay pending"),
    }
}

#[test]
fn ranking_pends_mutual_recursion() {
    // Mutual recursion needs one SCC-wide measure; neither member may verify on its
    // own (each shows zero self-edges), so both stay pending. This guards against an
    // unsound "verified with zero decrease obligations".
    let src = "\
total fn ping(n: Int): Int
  requires n >= 0
  decreases n
  = if n == 0 then 0 else pong(n - 1)

total fn pong(n: Int): Int
  requires n >= 0
  decreases n
  = if n == 0 then 0 else ping(n - 1)
";
    for name in ["ping", "pong"] {
        match ranking_for(src, name) {
            RankStatus::Pending(reason) => assert!(reason.contains("mutual"), "{name}: {reason}"),
            RankStatus::Obligations { .. } => {
                panic!("{name}: mutual recursion must stay pending, never verify with zero edges")
            }
        }
    }
}

#[test]
fn ranking_pends_higher_order_body() {
    // A call to a higher-order parameter could hide a recursive call, so the measure
    // stays pending rather than being verified with zero recursive edges.
    let src = "\
total fn apply_ho(f: Int, n: Int): Int
  requires n >= 0
  decreases n
  = if n == 0 then 0 else f(n)
";
    match ranking_for(src, "apply_ho") {
        RankStatus::Pending(reason) => assert!(reason.contains("higher-order")),
        RankStatus::Obligations { .. } => {
            panic!("a call to a higher-order parameter must stay pending")
        }
    }
}

#[test]
fn z3_verifies_decreasing_and_refutes_nondecreasing() {
    let Some(exe) = z3_exe() else {
        eprintln!("skipping z3_verifies_decreasing_and_refutes_nondecreasing: no z3");
        return;
    };
    let src = "\
total fn count(n: Int): Int
  requires n >= 0
  decreases n
  = if n == 0 then 0 else count(n - 1)

total fn bad(n: Int): Int
  requires n >= 0
  decreases n
  = if n == 0 then 0 else bad(n + 1)
";
    let report = run::run(&parse_prog(src), &exe).expect("verify runs");
    let out = report.render();
    assert!(
        out.contains("count: verified (3 ranking obligations)"),
        "a decreasing measure verifies via z3:\n{out}"
    );
    // A `sat` is a failed ranking argument and leaves totality pending; it is never
    // reported as a proof of divergence ("non-total").
    assert!(
        out.contains("bad: pending: failed ranking argument"),
        "a non-decreasing measure is a failed ranking argument:\n{out}"
    );
    assert!(!out.contains("non-total"), "never claims non-total:\n{out}");
    assert!(
        !report.all_clear(),
        "a failed ranking measure is not all-clear"
    );
}

#[test]
fn z3_keeps_termination_and_partial_correctness_distinct() {
    let Some(exe) = z3_exe() else {
        eprintln!("skipping z3_keeps_termination_and_partial_correctness_distinct: no z3");
        return;
    };
    // `id_nonneg` closes both its contract and its ranking measure, so total
    // correctness is derived. `term_only` has no postcondition contract, so its
    // verified termination never becomes a derived total-correctness claim.
    let src = "\
total fn id_nonneg(n: Int): Int
  requires n >= 0
  ensures |r| r >= 0
  decreases n
  = n

total fn term_only(n: Int): Int
  requires n >= 0
  decreases n
  = if n == 0 then 0 else term_only(n - 1)
";
    let report = run::run(&parse_prog(src), &exe).expect("verify runs");
    let out = report.render();
    assert!(report.all_clear(), "both functions verify:\n{out}");
    assert!(out.contains("total correctness (derived"), "{out}");
    let derived = out
        .split("total correctness (derived")
        .nth(1)
        .expect("derived section present");
    assert!(derived.contains("id_nonneg"), "{out}");
    assert!(
        !derived.contains("term_only"),
        "termination alone does not derive total correctness:\n{out}"
    );
}

/// The committed ranking obligation bytes for `COUNTDOWN`: rebuilding the same
/// program must reproduce them exactly, pinning the schema, canonical SMT-LIB, and
/// per-obligation digests across releases. Re-bless with `PRISM_BLESS_SMT=1`.
#[test]
fn ranking_query_v1_compat_fixture() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/smt/ranking_countdown.smt"
    );
    let got = ranking::render_smt(&parse_prog(COUNTDOWN));
    if std::env::var("PRISM_BLESS_SMT").is_ok() {
        std::fs::write(path, &got).expect("write ranking fixture");
    }
    let want = std::fs::read_to_string(path)
        .expect("missing tests/fixtures/smt/ranking_countdown.smt; bless with PRISM_BLESS_SMT=1");
    assert_eq!(
        got, want,
        "ranking obligation bytes drifted from the fixture"
    );
}

// -- Content-addressed evidence: receipts, certificates, and closure -----------

static STORE_NONCE: AtomicU64 = AtomicU64::new(0);

/// A temporary content-addressed store, removed on drop.
struct StoreGuard {
    store: Store,
    dir: PathBuf,
}

impl Drop for StoreGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

fn temp_store(tag: &str) -> StoreGuard {
    let mut dir = std::env::temp_dir();
    let n = STORE_NONCE.fetch_add(1, Ordering::Relaxed);
    dir.push(format!(
        "prism-verify-store-{tag}-{}-{n}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("create scratch store");
    let store = Store::open_or_create(&dir).expect("open store");
    StoreGuard { store, dir }
}

fn z3_id() -> SolverId {
    SolverId {
        family: "z3".to_string(),
        version: "z3 4.13.0".to_string(),
        flags: vec!["-in".to_string()],
    }
}

fn hexq(byte: &str) -> String {
    byte.repeat(32)
}

fn unsat_receipt(query_digest: &str, solver: &SolverId) -> SmtResult {
    SmtResult::oracle(
        query_digest.to_string(),
        ResultStatus::Unsat,
        solver.clone(),
        vec![],
    )
}

fn leaf_cert(subject: &str, query_digest: &str, receipts: Vec<String>) -> SmtCertificate {
    SmtCertificate {
        subject: subject.to_string(),
        obligations: vec![CertObligation {
            query_digest: query_digest.to_string(),
            receipts,
        }],
        dependencies: vec![],
        assumptions: vec![],
        completeness: Completeness::Complete,
        trust: CertTrust::SolverOracle,
    }
}

#[test]
fn result_codec_round_trips_and_binds_query_and_solver() {
    let r = unsat_receipt(&hexq("aa"), &z3_id());
    assert_eq!(SmtResult::decode(&r.encode()).unwrap(), r);
    assert!(r.matches_query(&hexq("aa")));
    assert!(!r.matches_query(&hexq("bb")));
    assert!(r.is_reusable_evidence());
    // A foreign scheme and trailing bytes are rejected, never misdecoded. The
    // bytes are a length-4 string "nope", which decodes cleanly but is not SCHEMA.
    assert_eq!(
        SmtResult::decode(&[4, b'n', b'o', b'p', b'e']),
        Err(crate::store::CodecError::Scheme)
    );
    let mut trailing = r.encode();
    trailing.push(0);
    assert_eq!(
        SmtResult::decode(&trailing),
        Err(crate::store::CodecError::TrailingBytes)
    );
}

#[test]
fn receipt_identity_moves_with_solver_version_not_query() {
    let v1 = unsat_receipt(&hexq("aa"), &z3_id());
    let mut solver2 = z3_id();
    solver2.version = "z3 4.14.0".to_string();
    let v2 = unsat_receipt(&hexq("aa"), &solver2);
    // A version change moves the receipt identity ...
    assert_ne!(v1.digest(), v2.digest());
    // ... but the query it answers is unchanged.
    assert_eq!(v1.query_digest, v2.query_digest);
}

#[test]
fn only_unsat_solver_oracle_is_reusable_evidence() {
    let q = hexq("aa");
    let sat = SmtResult::oracle(q.clone(), ResultStatus::Sat, z3_id(), vec![]);
    let unknown = SmtResult::oracle(q.clone(), ResultStatus::Unknown, z3_id(), vec![]);
    let timeout = SmtResult::oracle(q.clone(), ResultStatus::Timeout, z3_id(), vec![]);
    assert!(!sat.is_reusable_evidence());
    assert!(!unknown.is_reusable_evidence());
    assert!(!timeout.is_reusable_evidence());
    // Even an `unsat` under a reserved trust class is not reusable.
    let reserved = SmtResult {
        query_digest: q,
        status: ResultStatus::Unsat,
        trust: Trust::Reserved(TRUST_PROOF_CHECKED),
        solver: z3_id(),
        model: vec![],
    };
    assert!(!reserved.is_reusable_evidence());
}

#[test]
fn unsat_receipt_names_solver_and_is_never_proof_checked() {
    let r = unsat_receipt(&hexq("aa"), &z3_id());
    let line = r.render();
    assert!(line.contains("solver-oracle"), "{line}");
    assert!(line.contains("z3"), "{line}");
    assert!(!line.contains("proof-checked"), "{line}");
    // The proof-checked rung is reserved: recognized, but reported untrusted.
    let label = Trust::Reserved(TRUST_PROOF_CHECKED).label();
    assert!(label.contains("proof-checked"));
    assert!(label.contains("reserved"));
}

#[test]
fn certificate_codec_round_trips() {
    let cert = leaf_cert(&hexq("cc"), &hexq("aa"), vec![hexq("dd")]);
    assert_eq!(SmtCertificate::decode(&cert.encode()).unwrap(), cert);
    let mut trailing = cert.encode();
    trailing.push(7);
    assert_eq!(
        SmtCertificate::decode(&trailing),
        Err(crate::store::CodecError::TrailingBytes)
    );
}

#[test]
fn receipt_for_one_query_cannot_replay_against_another() {
    let g = temp_store("replay");
    let solver = z3_id();
    let (qa, qb) = (hexq("aa"), hexq("bb"));
    let ra = unsat_receipt(&qa, &solver);
    verify_store::put_result(&g.store, &ra).unwrap();
    // A certificate that points obligation `qb` at the receipt built for `qa`
    // fails closed: the receipt is bound to a different query.
    let cert = leaf_cert(&hexq("cc"), &qb, vec![ra.digest()]);
    verify_store::put_certificate(&g.store, &cert).unwrap();
    assert!(matches!(
        verify_store::verify_closure(&g.store, &cert),
        ClosureStatus::FailedClosed(_)
    ));
}

#[test]
fn closure_fails_closed_on_non_unsat_receipt() {
    let g = temp_store("non-unsat");
    let q = hexq("aa");
    let sat = SmtResult::oracle(q.clone(), ResultStatus::Sat, z3_id(), vec![]);
    verify_store::put_result(&g.store, &sat).unwrap();
    let cert = leaf_cert(&hexq("cc"), &q, vec![sat.digest()]);
    verify_store::put_certificate(&g.store, &cert).unwrap();
    assert!(matches!(
        verify_store::verify_closure(&g.store, &cert),
        ClosureStatus::FailedClosed(_)
    ));
}

#[test]
fn closure_fails_closed_on_missing_receipt() {
    let g = temp_store("missing-receipt");
    let q = hexq("aa");
    // The receipt digest names an object never stored.
    let cert = leaf_cert(&hexq("cc"), &q, vec![hexq("ee")]);
    verify_store::put_certificate(&g.store, &cert).unwrap();
    assert!(matches!(
        verify_store::verify_closure(&g.store, &cert),
        ClosureStatus::FailedClosed(_)
    ));
}

#[test]
fn closure_fails_closed_on_empty_obligation() {
    let g = temp_store("empty-ob");
    let cert = leaf_cert(&hexq("cc"), &hexq("aa"), vec![]);
    assert!(matches!(
        verify_store::verify_closure(&g.store, &cert),
        ClosureStatus::FailedClosed(_)
    ));
}

#[test]
fn closure_fails_closed_on_trusted_assumption() {
    let g = temp_store("assumption");
    let q = hexq("aa");
    let r = unsat_receipt(&q, &z3_id());
    verify_store::put_result(&g.store, &r).unwrap();
    let mut cert = leaf_cert(&hexq("cc"), &q, vec![r.digest()]);
    cert.assumptions = vec![hexq("ff")];
    verify_store::put_certificate(&g.store, &cert).unwrap();
    assert!(matches!(
        verify_store::verify_closure(&g.store, &cert),
        ClosureStatus::FailedClosed(_)
    ));
}

#[test]
fn complete_certificate_dependency_closure_and_cone_invalidation() {
    let g = temp_store("cone");
    let solver = z3_id();
    // Callee `g`: a self-contained leaf certificate.
    let qg = hexq("a1");
    let rg = unsat_receipt(&qg, &solver);
    let cert_g = leaf_cert(&hexq("c1"), &qg, vec![rg.digest()]);
    // Caller `f`: its own obligation plus a dependency on `g`'s certificate.
    let qf = hexq("a2");
    let rf = unsat_receipt(&qf, &solver);
    let mut cert_f = leaf_cert(&hexq("c2"), &qf, vec![rf.digest()]);
    cert_f.dependencies = vec![cert_g.digest()];
    // Unrelated `h`: no dependency on `g`.
    let qh = hexq("a3");
    let rh = unsat_receipt(&qh, &solver);
    let cert_h = leaf_cert(&hexq("c3"), &qh, vec![rh.digest()]);

    // Store f's and h's receipts and certs, but NOT g's certificate yet: f depends
    // on a callee contract that is absent (a stale/changed callee).
    verify_store::put_result(&g.store, &rf).unwrap();
    verify_store::put_result(&g.store, &rh).unwrap();
    verify_store::put_certificate(&g.store, &cert_f).unwrap();
    verify_store::put_certificate(&g.store, &cert_h).unwrap();

    // Exactly the dependency cone is invalidated: `f` fails closed, `h` is fine.
    assert!(matches!(
        verify_store::verify_closure(&g.store, &cert_f),
        ClosureStatus::FailedClosed(_)
    ));
    assert_eq!(
        verify_store::verify_closure(&g.store, &cert_h),
        ClosureStatus::Verified
    );

    // Supplying the callee certificate and its receipt closes `f`'s cone.
    verify_store::put_result(&g.store, &rg).unwrap();
    verify_store::put_certificate(&g.store, &cert_g).unwrap();
    assert_eq!(
        verify_store::verify_closure(&g.store, &cert_f),
        ClosureStatus::Verified
    );
}

#[test]
fn closure_fails_closed_on_pending_dependency() {
    let g = temp_store("pending-dep");
    let solver = z3_id();
    let qf = hexq("a2");
    let rf = unsat_receipt(&qf, &solver);
    // A dependency certificate that is honestly pending.
    let mut dep = leaf_cert(&hexq("c1"), &hexq("a1"), vec![]);
    dep.completeness = Completeness::Pending;
    let mut cert_f = leaf_cert(&hexq("c2"), &qf, vec![rf.digest()]);
    cert_f.dependencies = vec![dep.digest()];
    verify_store::put_result(&g.store, &rf).unwrap();
    verify_store::put_certificate(&g.store, &dep).unwrap();
    verify_store::put_certificate(&g.store, &cert_f).unwrap();
    // The pending dependency is itself incomplete, and it fails the parent closed.
    assert!(matches!(
        verify_store::verify_closure(&g.store, &dep),
        ClosureStatus::Incomplete(_)
    ));
    assert!(matches!(
        verify_store::verify_closure(&g.store, &cert_f),
        ClosureStatus::FailedClosed(_)
    ));
}

#[test]
fn reusable_unsat_serves_exact_query_and_solver_only() {
    let g = temp_store("reuse");
    let solver = z3_id();
    let q = hexq("aa");
    let r = unsat_receipt(&q, &solver);
    verify_store::put_result(&g.store, &r).unwrap();
    // The exact query and solver identity reuse the recorded pass.
    assert_eq!(
        verify_store::reusable_unsat(&g.store, &q, &solver).unwrap(),
        Some(r)
    );
    // A different query, or a different solver identity, is a cold miss.
    assert_eq!(
        verify_store::reusable_unsat(&g.store, &hexq("bb"), &solver).unwrap(),
        None
    );
    let mut other = solver;
    other.version = "z3 9.9.9".to_string();
    assert_eq!(
        verify_store::reusable_unsat(&g.store, &q, &other).unwrap(),
        None
    );
}

#[test]
fn sat_receipt_carries_its_model_across_the_codec() {
    let sat = SmtResult::oracle(
        hexq("aa"),
        ResultStatus::Sat,
        z3_id(),
        vec![ModelBinding {
            name: "x0".to_string(),
            value: "15".to_string(),
        }],
    );
    assert_eq!(sat.model.len(), 1);
    assert_eq!(SmtResult::decode(&sat.encode()).unwrap(), sat);
}

// -- prism-smt-result-v1 / prism-smt-certificate-v1 compatibility fixtures -----

fn fixture_solver() -> SolverId {
    SolverId {
        family: "z3".to_string(),
        version: "z3 version 4.13.0 - 64 bit".to_string(),
        flags: vec!["-in".to_string()],
    }
}

fn fixture_result() -> SmtResult {
    SmtResult::oracle(
        query::SmtQuery::build(&sample()).digest,
        ResultStatus::Unsat,
        fixture_solver(),
        vec![],
    )
}

fn fixture_certificate() -> SmtCertificate {
    leaf_cert(
        &normalize::contract_digest(&sample_contract()),
        &query::SmtQuery::build(&sample()).digest,
        vec![fixture_result().digest()],
    )
}

/// The committed `prism-smt-result-v1` bytes: rebuilding the same receipt must
/// reproduce them exactly, pinning the wire schema across releases. Re-bless with
/// `PRISM_BLESS_SMT=1`.
#[test]
fn result_v1_compat_fixture() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/smt/sample.result"
    );
    let got = fixture_result().encode();
    if std::env::var("PRISM_BLESS_SMT").is_ok() {
        std::fs::write(path, &got).expect("write result fixture");
    }
    let want = std::fs::read(path)
        .expect("missing tests/fixtures/smt/sample.result; bless with PRISM_BLESS_SMT=1");
    assert_eq!(
        got, want,
        "prism-smt-result-v1 bytes drifted from the fixture"
    );
    assert_eq!(SmtResult::decode(&want).unwrap(), fixture_result());
}

/// The committed `prism-smt-certificate-v1` bytes. Re-bless with `PRISM_BLESS_SMT=1`.
#[test]
fn certificate_v1_compat_fixture() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/smt/sample.certificate"
    );
    let got = fixture_certificate().encode();
    if std::env::var("PRISM_BLESS_SMT").is_ok() {
        std::fs::write(path, &got).expect("write certificate fixture");
    }
    let want = std::fs::read(path)
        .expect("missing tests/fixtures/smt/sample.certificate; bless with PRISM_BLESS_SMT=1");
    assert_eq!(
        got, want,
        "prism-smt-certificate-v1 bytes drifted from the fixture"
    );
    assert_eq!(
        SmtCertificate::decode(&want).unwrap(),
        fixture_certificate()
    );
}

// -- z3-gated end-to-end store integration -------------------------------------

#[test]
fn z3_verify_mints_stores_and_reuses_certificates() {
    let Some(exe) = z3_exe() else {
        eprintln!("skipping z3_verify_mints_stores_and_reuses_certificates: no z3");
        return;
    };
    let g = temp_store("e2e");
    let prog = parse_prog(
        "\
fn inc(x: Int): Int
  requires x >= 0
  ensures |r| r > x
  ensures |r| r >= 0
  = x + 1
",
    );
    let opts = VerifyOptions {
        solvers: vec![exe.clone()],
        require_agreement: false,
        timeout: None,
    };
    let report = run::run_with(&prog, &opts, Some(&g.store)).expect("verify runs");
    assert!(report.all_clear(), "inc verifies:\n{}", report.render());
    assert!(
        report.render().contains("certificate"),
        "the report names the stored certificate:\n{}",
        report.render()
    );

    let pinned = solver::pin(&exe, None).expect("z3 pins");
    let digests = report.certificate_digests();
    assert!(
        !digests.is_empty(),
        "a verified function stores a certificate"
    );
    for cert_digest in digests {
        let cert = verify_store::load_certificate(&g.store, &cert_digest)
            .expect("store readable")
            .expect("certificate present and self-addressed");
        assert_eq!(
            verify_store::verify_closure(&g.store, &cert),
            ClosureStatus::Verified,
            "the stored certificate's closure holds"
        );
        // Every discharged obligation is now reusable evidence under the same solver.
        for ob in &cert.obligations {
            assert!(
                verify_store::reusable_unsat(&g.store, &ob.query_digest, &pinned.id())
                    .unwrap()
                    .is_some(),
                "a stored unsat is reusable evidence"
            );
        }
    }
}

// -- cvc5 adapter and cross-solver agreement (gated on a present cvc5) ----------

/// Locate a cvc5 binary: `PRISM_CVC5` if set, else `cvc5` on `PATH`, confirmed by a
/// successful `--version`. `None` means the gate is skipped (cvc5 not installed).
fn cvc5_exe() -> Option<String> {
    let exe = std::env::var("PRISM_CVC5").unwrap_or_else(|_| "cvc5".to_string());
    let ok = Command::new(&exe)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success());
    ok.then_some(exe)
}

const CONTRACT_PROG: &str = "\
fn inc(x: Int): Int
  requires x >= 0
  ensures |r| r > x
  ensures |r| r >= 0
  = x + 1

fn bad(x: Int): Int
  requires x >= 0
  ensures |r| r > 100
  = x + 1
";

#[test]
fn cvc5_discharges_valid_and_refutes_invalid() {
    let Some(exe) = cvc5_exe() else {
        eprintln!("skipping cvc5_discharges_valid_and_refutes_invalid: no cvc5");
        return;
    };
    let report = run::run(&parse_prog(CONTRACT_PROG), &exe).expect("verify runs");
    let out = report.render();
    assert!(
        out.contains("inc: verified"),
        "inc must verify via cvc5:\n{out}"
    );
    assert!(
        out.contains("bad: counterexample"),
        "bad must be refuted via cvc5:\n{out}"
    );
    assert!(!report.all_clear());
}

#[test]
fn z3_and_cvc5_agree_on_a_valid_contract() {
    let (Some(z3), Some(cvc5)) = (z3_exe(), cvc5_exe()) else {
        eprintln!("skipping z3_and_cvc5_agree_on_a_valid_contract: need both z3 and cvc5");
        return;
    };
    let prog = parse_prog(
        "\
fn inc(x: Int): Int
  requires x >= 0
  ensures |r| r > x
  = x + 1
",
    );
    let opts = VerifyOptions {
        solvers: vec![z3, cvc5],
        require_agreement: true,
        timeout: None,
    };
    let report = run::run_with(&prog, &opts, None).expect("verify runs");
    assert!(
        report.all_clear(),
        "both solvers agree the contract holds:\n{}",
        report.render()
    );
}
