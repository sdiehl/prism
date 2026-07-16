use prism::Error;

const HOLE_PROGRAM: &str = "fn main() : Int ! {} = ?todo";

#[test]
fn batch_frontend_refuses_typed_holes() {
    let error = prism::check(HOLE_PROGRAM).expect_err("batch checking must refuse typed holes");
    let Error::Type(error) = error else {
        panic!("expected a type error, got {error}");
    };
    assert_eq!(error.code(), Some(prism::TYPED_HOLE.as_str()));
    assert_eq!(
        error.hole_report().map(|report| report.name.as_str()),
        Some("todo")
    );
    insta::assert_snapshot!(error.to_string(), @"typed hole `?todo`: expected Int with effects {}; candidates: none; 132 binding(s) in scope");
}

#[test]
fn code_generation_frontend_refuses_typed_holes() {
    let error = prism::core_ir(HOLE_PROGRAM).expect_err("code generation must refuse holes");
    assert_eq!(error.code(), prism::TYPED_HOLE);
}

#[test]
fn deferred_interpreter_fault_names_only_the_hole_and_span() {
    let error = prism::interpret_deferred_holes(HOLE_PROGRAM)
        .expect_err("evaluation must halt when it reaches the hole");
    let Error::RuntimeEvaluation(fault) = error else {
        panic!("expected a runtime fault, got {error}");
    };
    let start = HOLE_PROGRAM.find("?todo").expect("hole offset");
    let span = marginalia::Span::new(start, start + "?todo".len());
    assert_eq!(fault, prism::typed_hole_fault("todo", span));
}

#[test]
fn deferred_hole_that_is_not_reached_does_not_affect_execution() {
    let source = "fn main() : Int ! {} = if false then ?todo else 7";
    let run = prism::interpret_deferred_holes(source).expect("unreached hole must not fault");
    assert_eq!(run.value.show(), "7");
}

#[test]
fn deferred_hole_fault_is_pinned_in_the_observation_trace() {
    let roots = prism::default_roots(std::path::Path::new("."));
    let mut out = Vec::new();
    let mut input = std::io::Cursor::new(Vec::<u8>::new());
    let run = prism::observe_run_on_deferred_holes(
        HOLE_PROGRAM,
        &roots,
        &mut out,
        &mut input,
        &prism::Config::default(),
        Vec::new(),
    )
    .expect("deferred observed run compiles");
    let start = HOLE_PROGRAM.find("?todo").expect("hole offset");
    let span = marginalia::Span::new(start, start + "?todo".len());
    let fault = prism::typed_hole_fault("todo", span);
    assert_eq!(
        run.canonical_trace.observations,
        vec![prism::Observation::Fault(fault.clone())]
    );
    assert_eq!(run.fault.as_deref(), Some(fault.as_str()));
    let encoded = run.canonical_trace.to_json().expect("trace serializes");
    assert_eq!(
        prism::ObservationTrace::from_json(&encoded).expect("trace validates"),
        run.canonical_trace
    );
}
