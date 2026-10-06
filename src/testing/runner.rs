//! Test runner: resolve, discover/check, select, then execute each selected test
//! serially in logical-ID order, each in a fresh interpreter world.
//!
//! Per test the runner synthesizes a private harness entry that calls the test
//! under a `Fail` handler and yields an `Int` sentinel (0 pass, 1 `fail()`), runs
//! it in test mode, and classifies the outcome: pass, `fail()`, runtime fault,
//! unhandled effect, or explicit exit. Output is captured per test, hidden on a
//! pass, shown on a failure (and on a pass under `--show-output`). Compilation
//! succeeded and all selected tests passing is the only zero-exit condition.

// Both write traits are in scope: `io::Write` for the byte sinks (stdout, the
// event buffer) and `fmt::Write` (anonymously, to avoid the name clash) so
// `writeln!` can render the `--list` output into a `String`.
use std::fmt::Write as _;
use std::io::{self, Cursor, Write};
use std::path::{Path, PathBuf};

use crate::cli::test::TestOptions;
use crate::cli::{enclosing_project, is_project, CmdError, CmdResult, TEST_WITHOUT_PATH};
use crate::error::Error;
use crate::eval::{Run, Rv};
use crate::names::bare_name;
use crate::{interpret_io_on_with_args, Config};

use super::discovery::{self, TestPlan, TestTarget};
use super::{decode_failure, events, junit, report, Failure, TEST_FAILURE_SCHEMA};

/// How a test finished. `None` kind is a pass; a `Some(kind)` is a failure of
/// that class.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OutcomeKind {
    /// The built-in `fail()` operation (or a structured test failure) fired.
    Fail,
    /// The evaluator faulted at runtime (a partial-function fault, a division by
    /// zero, and the like).
    Fault,
    /// A residual effect reached the runtime with no handler. The signature check rejects these at
    /// check time; this class exists so the runner still classifies one defensively.
    UnhandledEffect,
    /// The test called `exit(code)`; any exit, even zero, is a failure.
    Exit,
    /// The harness itself could not be built or run (a compile/harness fault),
    /// reported separately from a test failure.
    Infrastructure,
}

/// One test's classified result and its captured output.
#[derive(Clone, Debug)]
pub(crate) struct Outcome {
    pub kind: Option<OutcomeKind>,
    pub message: String,
    pub output: String,
    /// The structured failure payload, when the failure crossed the versioned
    /// test-ABI bridge rather than the payload-free `fail()`. Rendered into the
    /// `test_failed` event's structured fields; `None` keeps the payload-free bytes.
    pub failure: Option<Failure>,
    /// The `skip` pragma's reason when the test was not run. A skipped outcome
    /// has no failure kind and counts apart from a pass.
    pub skipped: Option<String>,
}

impl Outcome {
    const fn pass(output: String) -> Self {
        Self {
            kind: None,
            message: String::new(),
            output,
            failure: None,
            skipped: None,
        }
    }

    const fn skip(reason: String) -> Self {
        Self {
            kind: None,
            message: String::new(),
            output: String::new(),
            failure: None,
            skipped: Some(reason),
        }
    }

    const fn fail(kind: OutcomeKind, message: String, output: String) -> Self {
        Self {
            kind: Some(kind),
            message,
            output,
            failure: None,
            skipped: None,
        }
    }

    // A structured failure crossing the test-ABI bridge: always the `Fail` class,
    // carrying the decoded payload the event path renders in full.
    fn structured(failure: Failure, output: String) -> Self {
        Self {
            kind: Some(OutcomeKind::Fail),
            message: failure.message.clone(),
            output,
            failure: Some(failure),
            skipped: None,
        }
    }

    #[must_use]
    pub(crate) const fn passed(&self) -> bool {
        self.kind.is_none()
    }
}

/// Run the `prism test` command end to end.
///
/// # Errors
/// A dispatch error on a front-end/discovery failure, or a nonzero-summary error
/// when compilation succeeded but a selected test failed (or no test matched
/// under `--fail-if-no-tests`).
pub(crate) fn run(file: Option<&Path>, options: &TestOptions, cfg: &Config) -> CmdResult {
    // One test-mode config with a shared session for the whole command, so the
    // prelude and each module compile once and every per-test harness compile hits
    // the session cache instead of re-elaborating the prelude.
    let cfg = &discovery::test_config(cfg);
    let input = resolve_input(file)?;
    let plan = discover(&input, cfg).map_err(|e| (e, String::new(), input.display_name()))?;
    let selected = select(&plan, options);

    if options.list {
        list(&selected, options);
        return Ok(());
    }

    if selected.is_empty() {
        return no_match(options);
    }

    if options.no_run {
        // Selected targets are already checked (discovery ran the checker); there
        // is nothing left to compile without executing, so this is a clean stop.
        if !options.json {
            println!("compiled {} test(s); not run", selected.len());
        }
        return Ok(());
    }

    execute(&selected, options, cfg)
}

// The resolved test input: a project directory or a single file.
enum Input {
    Project(PathBuf),
    File(PathBuf),
}

impl Input {
    fn display_name(&self) -> String {
        match self {
            Self::Project(p) | Self::File(p) => p.display().to_string(),
        }
    }
}

fn resolve_input(file: Option<&Path>) -> Result<Input, CmdError> {
    match file {
        Some(path) if is_project(path) => Ok(Input::Project(path.to_path_buf())),
        Some(path) => Ok(Input::File(path.to_path_buf())),
        None => enclosing_project(TEST_WITHOUT_PATH).map(Input::Project),
    }
}

fn discover(input: &Input, cfg: &Config) -> Result<TestPlan, Error> {
    match input {
        Input::Project(dir) => discovery::discover_project(dir, cfg),
        Input::File(file) => discovery::discover_file(file, cfg),
    }
}

// Substring (default) or exact selection over logical IDs, narrowed to the tests
// carrying any requested `--tag`, preserving the logical-ID order the plan is
// already sorted into.
fn select<'a>(plan: &'a TestPlan, options: &TestOptions) -> Vec<&'a TestTarget> {
    plan.targets
        .iter()
        .filter(|t| match &options.filter {
            None => true,
            Some(f) if options.exact => t.descriptor.logical_id == *f,
            Some(f) => t.descriptor.logical_id.contains(f),
        })
        .filter(|t| {
            options.tags.is_empty()
                || options
                    .tags
                    .iter()
                    .any(|tag| t.descriptor.tags.contains(tag))
        })
        .collect()
}

fn list(selected: &[&TestTarget], options: &TestOptions) {
    let stdout = io::stdout();
    let mut out = stdout.lock();
    let _ = out.write_all(render_list(selected, options.json).as_bytes());
}

// The `--list` output as bytes: one logical ID per line (human), or the
// `suite_started`/`test_started`/`suite_finished` JSON frame (with every selected
// test counted as skipped, since listing runs nothing). The single renderer the
// CLI `list` and the testable `list_output` both use, so their bytes cannot drift.
fn render_list(selected: &[&TestTarget], json: bool) -> String {
    let mut out = String::new();
    if json {
        let _ = writeln!(out, "{}", events::suite_started(selected.len()));
        for t in selected {
            let _ = writeln!(out, "{}", events::test_started(&t.descriptor.logical_id));
        }
        let _ = writeln!(out, "{}", events::suite_finished(0, 0, selected.len(), 0));
    } else {
        for t in selected {
            let _ = writeln!(out, "{}", t.descriptor.logical_id);
        }
    }
    out
}

/// Discover and select tests, then render the `--list` output to a string without
/// printing. Tests assert the human and JSON list formats against this.
///
/// # Errors
/// Front-end/discovery errors surface as an `Err`.
pub(crate) fn list_output(
    file: Option<&Path>,
    options: &TestOptions,
    cfg: &Config,
) -> Result<String, Error> {
    let cfg = &discovery::test_config(cfg);
    let input = resolve_input(file).map_err(|(e, _, _)| e)?;
    let plan = discover(&input, cfg)?;
    Ok(render_list(&select(&plan, options), options.json))
}

/// Render a structured [`Failure`] to `prism-test-events-v1` bytes through the same
/// emit path the runner uses for a real failure (`emit_outcome`): `test_started`
/// then the structured `test_failed`. The conformance seam for the test-ABI bridge.
#[must_use]
pub(crate) fn structured_failure_events(id: &str, failure: &Failure) -> Vec<u8> {
    let outcome = Outcome::structured(failure.clone(), String::new());
    let mut out: Vec<u8> = Vec::new();
    let _ = events::emit_outcome(&mut out, id, &outcome, false);
    out
}

fn no_match(options: &TestOptions) -> CmdResult {
    if options.fail_if_no_tests {
        return Err((
            Error::ResolveCommand("no tests matched".into()),
            String::new(),
            String::new(),
        ));
    }
    if !options.json {
        eprintln!("warning: no tests matched");
    }
    Ok(())
}

// The suite tally. The four counts are disjoint and sum to the selected count,
// so a consumer may add them; a harness/infrastructure failure is counted apart
// from an ordinary test failure. Any nonzero `failed` or `infrastructure`
// determines the nonzero exit status.
#[derive(Default)]
pub(crate) struct Tally {
    pub passed: usize,
    pub failed: usize,
    pub skipped: usize,
    pub infrastructure: usize,
}

impl Tally {
    const fn record(&mut self, outcome: &Outcome) {
        if outcome.skipped.is_some() {
            self.skipped += 1;
            return;
        }
        match outcome.kind {
            None => self.passed += 1,
            Some(OutcomeKind::Infrastructure) => self.infrastructure += 1,
            Some(_) => self.failed += 1,
        }
    }

    const fn ok(&self) -> bool {
        self.failed == 0 && self.infrastructure == 0
    }
}

fn execute(selected: &[&TestTarget], options: &TestOptions, cfg: &Config) -> CmdResult {
    let stdout = io::stdout();
    let mut out = stdout.lock();
    if options.json {
        let _ = writeln!(out, "{}", events::suite_started(selected.len()));
    }

    let mut tally = Tally::default();
    let mut results = Vec::with_capacity(selected.len());
    for target in selected {
        let outcome = run_one(target, cfg);
        tally.record(&outcome);
        if options.json {
            let _ = events::emit_outcome(
                &mut out,
                &target.descriptor.logical_id,
                &outcome,
                options.show_output,
            );
        } else {
            let _ = report::line(
                &mut out,
                &target.descriptor.logical_id,
                &outcome,
                options.show_output,
            );
        }
        results.push((target.descriptor.logical_id.clone(), outcome));
    }

    if let Some(path) = &options.junit {
        std::fs::write(path, junit::render(&results)).map_err(|e| {
            (
                Error::ResolveCommand(format!("cannot write {}: {e}", path.display())),
                String::new(),
                String::new(),
            )
        })?;
    }

    if options.json {
        let _ = writeln!(
            out,
            "{}",
            events::suite_finished(
                tally.passed,
                tally.failed,
                tally.skipped,
                tally.infrastructure,
            )
        );
    } else {
        let _ = report::summary(&mut out, &tally);
    }

    if tally.ok() {
        Ok(())
    } else {
        let broken = tally.failed + tally.infrastructure;
        Err((
            Error::ResolveCommand(format!("{broken} test(s) failed")),
            String::new(),
            String::new(),
        ))
    }
}

// Map the internal outcome kind to the public status enum.
pub(crate) const fn public_status(outcome: &Outcome) -> super::TestStatus {
    if outcome.skipped.is_some() {
        return super::TestStatus::Skipped;
    }
    match outcome.kind {
        None => super::TestStatus::Passed,
        Some(OutcomeKind::Fail) => super::TestStatus::Failed,
        Some(OutcomeKind::Fault) => super::TestStatus::Fault,
        Some(OutcomeKind::UnhandledEffect) => super::TestStatus::UnhandledEffect,
        Some(OutcomeKind::Exit) => super::TestStatus::Exit,
        Some(OutcomeKind::Infrastructure) => super::TestStatus::Infrastructure,
    }
}

/// Discover, select, and run every matching test, returning each result in
/// logical-ID order without printing. The structured entry point tests drive.
///
/// # Errors
/// Front-end/discovery errors surface as an `Err`; a failing test does not (it
/// is a `Some(kind)` outcome in the returned list).
pub(crate) fn run_report(
    file: Option<&Path>,
    options: &TestOptions,
    cfg: &Config,
) -> Result<Vec<(String, Outcome)>, Error> {
    let cfg = &discovery::test_config(cfg);
    let input = resolve_input(file).map_err(|(e, _, _)| e)?;
    let plan = discover(&input, cfg)?;
    Ok(select(&plan, options)
        .into_iter()
        .map(|target| (target.descriptor.logical_id.clone(), run_one(target, cfg)))
        .collect())
}

/// Discover and select tests, then emit the `prism-test-events-v1` NDJSON to a
/// buffer, returning the exact bytes. Tests assert byte-stability against this.
///
/// # Errors
/// Front-end/discovery errors surface as an `Err`.
pub(crate) fn event_bytes(
    file: Option<&Path>,
    options: &TestOptions,
    cfg: &Config,
) -> Result<Vec<u8>, Error> {
    let cfg = &discovery::test_config(cfg);
    let input = resolve_input(file).map_err(|(e, _, _)| e)?;
    let plan = discover(&input, cfg)?;
    let selected = select(&plan, options);
    let mut out: Vec<u8> = Vec::new();
    let _ = writeln!(out, "{}", events::suite_started(selected.len()));
    let mut tally = Tally::default();
    for target in &selected {
        let outcome = run_one(target, cfg);
        tally.record(&outcome);
        let _ = events::emit_outcome(
            &mut out,
            &target.descriptor.logical_id,
            &outcome,
            options.show_output,
        );
    }
    let _ = writeln!(
        out,
        "{}",
        events::suite_finished(
            tally.passed,
            tally.failed,
            tally.skipped,
            tally.infrastructure,
        )
    );
    Ok(out)
}

// Run one test in a fresh world and classify the outcome.
fn run_one(target: &TestTarget, cfg: &Config) -> Outcome {
    if let Some(reason) = &target.descriptor.skip {
        return Outcome::skip(reason.clone());
    }
    let harness = synthesize(&target.full_src, &target.entry_name);
    let mut sink: Vec<u8> = Vec::new();
    let mut input = Cursor::new(Vec::new());
    let result = interpret_io_on_with_args(
        &harness,
        &target.roots,
        &mut sink,
        &mut input,
        cfg,
        Vec::new(),
    );
    let output = String::from_utf8_lossy(&sink).into_owned();
    match result {
        Ok(run) => classify(&run, output),
        Err(error) => Outcome::fail(error_kind(&error), error_message(&error), output),
    }
}

// Classify an interpreter-path error. A runtime fault (the only error a checked
// test body can raise at execution) is a `Fault`, or an `UnhandledEffect` when it
// names one defensively (the signature check rejects residual effects at check time, so this arm
// is a safety net). Any other error is a front-end failure of the synthesized
// harness itself, an infrastructure problem reported apart from a test failure.
fn error_kind(error: &Error) -> OutcomeKind {
    match error {
        Error::RuntimeEvaluation(m) | Error::RuntimeReplay(m) | Error::RuntimeDebugger(m) => {
            if m.contains("unhandled effect") {
                OutcomeKind::UnhandledEffect
            } else {
                OutcomeKind::Fault
            }
        }
        _ => OutcomeKind::Infrastructure,
    }
}

// Map a completed run to an outcome. The harness returns `Int(0)` on pass and
// `Int(1)` on `fail()`; an explicit `exit` unwinds past the handler's return
// clause, leaving `Run::exit` set (any code, even zero, is a failure).
fn classify(run: &Run, output: String) -> Outcome {
    if let Some(code) = run.exit {
        return Outcome::fail(
            OutcomeKind::Exit,
            format!("test called exit({code})"),
            output,
        );
    }
    match run.value {
        Rv::Int(0) => Outcome::pass(output),
        Rv::Int(1) => match take_failure_frame(&output) {
            Some((failure, rest)) => Outcome::structured(failure, rest),
            None => Outcome::fail(OutcomeKind::Fail, "test failed".into(), output),
        },
        _ => Outcome::fail(
            OutcomeKind::Infrastructure,
            "harness produced an unexpected result".into(),
            output,
        ),
    }
}

// Split a structured failure off a failing test's captured output. `Test.pr`
// writes the `prism-test-failure-v1` envelope, hex-encoded behind its schema tag,
// as the last line before `fail()` fires (`<schema>:<hex>`), so only a final line is honoured, and
// only when it decodes; anything else leaves the output and the bare failure as
// they were.
fn take_failure_frame(output: &str) -> Option<(Failure, String)> {
    let body = output.strip_suffix('\n')?;
    let start = body.rfind('\n').map_or(0, |i| i + 1);
    let hex = body[start..]
        .strip_prefix(TEST_FAILURE_SCHEMA.as_str())?
        .strip_prefix(':')?;
    let failure = decode_failure(&decode_hex(hex)?).ok()?;
    Some((failure, output[..start].to_string()))
}

fn decode_hex(hex: &str) -> Option<Vec<u8>> {
    if !hex.len().is_multiple_of(2) {
        return None;
    }
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(hex.get(i..i + 2)?, 16).ok())
        .collect()
}

// Build the harness source for one test: the compilation unit's full source plus
// a synthetic `main` that runs the one test under a non-resumable `Fail` handler
// and returns the pass/fail sentinel (`Int(0)` pass, `Int(1)` on `fail()`).
//
// The synthetic `main` is appended last. The checker keeps the last of two
// same-named top-level definitions, and the evaluator's global table does too, so
// this harness `main` shadows any user `main` in the unit; the user `main` never
// runs and its output never appears. A never-resumable `fail()` handler catches
// the built-in failure; a runtime fault surfaces as an interpreter error and an
// explicit exit leaves `Run::exit` set, both classified in `classify`.
fn synthesize(full_src: &str, entry_name: &str) -> String {
    let short = bare_name(entry_name);
    format!(
        "{full_src}\nfn main() =\n  handle {short}() with\n    never fail() => 1\n    return r => 0\n"
    )
}

fn error_message(error: &Error) -> String {
    match error {
        Error::RuntimeEvaluation(m) | Error::RuntimeReplay(m) | Error::RuntimeDebugger(m) => {
            m.clone()
        }
        other => other.to_string(),
    }
}
