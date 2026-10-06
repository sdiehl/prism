// A handler's `finally` clause is typed in the scope outside the handler,
// against `Unit`, at the handler's residual row. It binds nothing, so neither
// the `return` clause's binder nor an operation clause's continuation is in
// scope, and its answer is discarded, so a body of any other type is refused
// rather than silently dropped.
//
// Three further gates keep the clause's exactly-once promise: every operation
// clause of such a handler resumes at most once, the cleanup itself performs no
// operation that never resumes, and a handler carries at most one such clause.
//
// At run time the clause runs exactly once each time its handler is left: after
// the `return` clause on the normal path, or from the clause body that dropped
// the continuation on the abandoned one, innermost handler first.

use std::io::Cursor;
use std::path::Path;
use std::process::{Command, Stdio};

use prism::eval::Rv;
use prism::{
    check_on, check_validated_on_in, default_roots, interpret, record_on_with_args, replay_on,
    with_prelude, Config,
};

const SCOPE_UNBOUND: &str = "E2000";
const TYPE_MISMATCH: &str = "E1022";
const CLAUSE_RESUMES_TWICE: &str = "E6088";
const CLEANUP_ABORTS: &str = "E6089";
const DUPLICATE_CLEANUP: &str = "E6090";

const WELL_TYPED: &str = include_str!("../fixtures/language/finally/well_typed.pr");

// A pure bracket: a handler with no operation clauses may carry the clause, so a
// scoped resource has one spelling whether or not it owns an effect.
const PURE_BRACKET: &str = include_str!("../fixtures/language/finally/pure_bracket.pr");

const SEES_RETURN_BINDER: &str = include_str!("../fixtures/language/finally/sees_return_binder.pr");

const SEES_CONTINUATION: &str = include_str!("../fixtures/language/finally/sees_continuation.pr");

const ANSWERS_INT: &str = include_str!("../fixtures/language/finally/answers_int.pr");

const RESUMES_TWICE: &str = include_str!("../fixtures/language/finally/resumes_twice.pr");

const ONCE_CLAUSES: &str = include_str!("../fixtures/language/finally/once_clauses.pr");

const CLEANUP_QUITS: &str = include_str!("../fixtures/language/finally/cleanup_quits.pr");

const CLEANUP_QUITS_THROUGH_A_CALL: &str =
    include_str!("../fixtures/language/finally/cleanup_quits_through_a_call.pr");

const TWO_CLEANUPS: &str = include_str!("../fixtures/language/finally/two_cleanups.pr");

fn refusal(src: &str) -> prism::Error {
    check_validated_on_in(
        &with_prelude(src),
        &default_roots(Path::new(".")),
        &Config::default(),
    )
    .expect_err("the program is refused")
}

fn code_of(src: &str) -> String {
    refusal(src).code().to_string()
}

// The gates' diagnostics are pinned whole: the code and the complete message.
fn assert_refused(src: &str, code: &str, message: &str) {
    let err = refusal(src);
    assert_eq!(err.code().to_string(), code);
    let text = err.to_string();
    assert!(text.contains(message), "{text}");
}

#[test]
fn cleanup_clause_typechecks_at_unit_in_the_outer_scope() {
    check_on(&with_prelude(WELL_TYPED), &default_roots(Path::new("."))).expect("well typed");
}

#[test]
fn a_handler_with_no_operation_clauses_may_carry_cleanup() {
    check_on(&with_prelude(PURE_BRACKET), &default_roots(Path::new("."))).expect("well typed");
}

#[test]
fn cleanup_clause_cannot_see_the_return_binder() {
    assert_eq!(code_of(SEES_RETURN_BINDER), SCOPE_UNBOUND);
}

#[test]
fn cleanup_clause_cannot_see_a_continuation() {
    assert_eq!(code_of(SEES_CONTINUATION), SCOPE_UNBOUND);
}

#[test]
fn cleanup_clause_must_answer_unit() {
    assert_eq!(code_of(ANSWERS_INT), TYPE_MISMATCH);
}

#[test]
fn a_clause_that_may_resume_twice_is_refused_beside_a_cleanup_clause() {
    assert_refused(
        RESUMES_TWICE,
        CLAUSE_RESUMES_TWICE,
        "handler clause for `ask` may resume more than once; a handler with a `finally` \
         clause is left exactly once, so each of its clauses resumes at most once",
    );
}

// `once`, a bare single tail resume, and `never` all sit at or below `Once`.
#[test]
fn clauses_that_resume_at_most_once_are_accepted_beside_a_cleanup_clause() {
    check_on(&with_prelude(ONCE_CLAUSES), &default_roots(Path::new("."))).expect("well typed");
}

#[test]
fn a_cleanup_clause_may_not_perform_a_never_operation() {
    assert_refused(
        CLEANUP_QUITS,
        CLEANUP_ABORTS,
        "`finally` clause performs `quit` of effect `Quit`, which never resumes; a cleanup \
         clause runs to completion",
    );
}

// A call whose signature row names the effect stands for every operation the
// effect declares, so the never-resuming one is found through it too.
#[test]
fn a_cleanup_clause_may_not_call_into_a_never_operation() {
    assert_eq!(code_of(CLEANUP_QUITS_THROUGH_A_CALL), CLEANUP_ABORTS);
}

#[test]
fn a_second_cleanup_clause_is_refused() {
    assert_refused(
        TWO_CLEANUPS,
        DUPLICATE_CLEANUP,
        "duplicate `finally` clause; a handler has at most one",
    );
}

const ABANDONED: &str = include_str!("../fixtures/language/finally/abandoned.pr");

const RESUMED_ACROSS: &str = include_str!("../fixtures/language/finally/resumed_across.pr");

const NESTED: &str = include_str!("../fixtures/language/finally/nested.pr");

const RETURN_ABORTS: &str = include_str!("../fixtures/language/finally/return_aborts.pr");

const MASKED: &str = include_str!("../fixtures/language/finally/masked.pr");

const REENTERED: &str = include_str!("../fixtures/language/finally/reentered.pr");

const UNHANDLED: &str = "tests/fixtures/language/finally/unhandled.pr";

const REPLAYED: &str = include_str!("../fixtures/language/finally/replayed.pr");

fn printed(src: &str) -> Vec<String> {
    let run = interpret(&with_prelude(src)).expect("the program runs");
    run.out.iter().map(Rv::show).collect()
}

#[test]
fn cleanup_runs_once_after_the_return_clause() {
    assert_eq!(printed(WELL_TYPED), ["cleanup", "42"]);
}

#[test]
fn cleanup_runs_once_when_the_body_is_abandoned() {
    assert_eq!(printed(ABANDONED), ["cleanup", "7"]);
}

// An operation answered outside the handler crosses its cleanup on the way out;
// resuming reinstates the handler, which is then left once, on its normal path.
#[test]
fn cleanup_runs_once_when_a_crossing_operation_is_resumed() {
    assert_eq!(printed(RESUMED_ACROSS), ["cleanup", "42"]);
}

#[test]
fn nested_cleanups_abandoned_together_run_innermost_first() {
    assert_eq!(
        printed(NESTED),
        ["leave inner", "leave middle", "leave outer", "0"]
    );
}

#[test]
fn a_return_clause_that_aborts_still_runs_its_own_cleanup() {
    assert_eq!(printed(RETURN_ABORTS), ["returning 1", "cleanup", "7"]);
}

// The mask carries the operation past the inner handler to one that drops the
// continuation, and the handler it skipped is still left through its cleanup.
#[test]
fn a_masked_operation_leaves_the_skipped_handlers_cleanup_pending() {
    assert_eq!(printed(MASKED), ["inner cleanup", "7"]);
}

// A handler outside the cleanup's own may resume more than once; each time the
// segment runs to its `return` clause the handler is left again.
#[test]
fn a_handler_entered_twice_is_left_twice() {
    assert_eq!(printed(REENTERED), ["cleanup", "cleanup", "5"]);
}

// An operation no handler catches is a machine fault, not an exit: the run is
// over and nothing pending runs, the same rule the native runtime's abort keeps.
#[test]
fn an_operation_no_handler_catches_faults_without_cleanup() {
    let out = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("run")
        .arg(UNHANDLED)
        .stdin(Stdio::null())
        .output()
        .expect("run prism");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("unhandled effect `quit`"),
        "the run faults on the operation: {stderr}"
    );
    assert!(!stdout.contains("cleanup"), "no cleanup ran: {stdout}");
}

// The cleanup's own effects are ordinary recorded events and the trigger that
// runs it is not an observation, so a replay serves the recorded read and runs
// the cleanup exactly once, as the recorded run did.
#[test]
fn a_replayed_run_runs_an_abandoned_cleanup_once() {
    let src = with_prelude(REPLAYED);
    let roots = default_roots(Path::new("."));
    let cfg = Config::from_env();
    let mut recorded = Vec::new();
    let (_, trace, _) = record_on_with_args(
        &src,
        &roots,
        &mut recorded,
        &mut Cursor::new(Vec::new()),
        &cfg,
        vec!["alpha".into(), "beta".into()],
    )
    .expect("record");
    let mut replayed = Vec::new();
    replay_on(&src, &roots, &mut replayed, &trace, &cfg).expect("replay");
    let recorded = String::from_utf8(recorded).expect("utf8");
    assert_eq!(
        recorded.matches("cleanup with 2 arguments").count(),
        1,
        "{recorded}"
    );
    assert_eq!(String::from_utf8(replayed).expect("utf8"), recorded);
}
