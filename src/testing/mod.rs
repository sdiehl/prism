//! Language-integrated testing: `test fn` discovery, deterministic manifests,
//! harness construction, and the interpreter runner behind `prism test`.
//!
//! The compiler owns test identity, discovery,
//! harness generation, execution, and events; the stdlib assertion library
//! arrives later over the versioned test ABI. Production neutrality is the
//! release gate: test-only edits leave production interface hashes, Core
//! hashes, and emitted artifacts byte-identical (enforced by the
//! `BuildMode::Production` strip in `driver::front` and `driver::modules`).

use std::path::Path;

use crate::cli::test::TestOptions;
use crate::cli::CmdResult;

mod check;
mod discovery;
mod events;
mod failure;
mod manifest;
mod report;
mod runner;

pub use discovery::TestDescriptor;
pub use failure::{decode_failure, encode_failure, Failure};
pub use manifest::{decode_manifest, encode_manifest, ManifestError};

/// The versioned test manifest schema tag.
pub const TEST_MANIFEST_SCHEMA: &str = "prism-test-manifest-v1";

/// The versioned test event stream schema tag.
pub const TEST_EVENTS_SCHEMA: &str = "prism-test-events-v1";

/// The versioned structured-failure test-ABI schema tag. The wire envelope a
/// structured failure crosses from the stdlib assertion layer to the harness.
pub const TEST_FAILURE_SCHEMA: &str = "prism-test-failure-v1";

/// The effect names the test world observes: `Fail` is a test failure and
/// `IO` is the ambient output channel captured per test. This is the complete
/// initial effect contract; any other residual effect (a capability effect or a
/// user effect) is a compile-time rejection at the test declaration.
pub(crate) const TEST_WORLD_EFFECTS: &[&str] =
    &[crate::names::FAIL_EFFECT, crate::names::IO_EFFECT];

/// Run the `prism test` command end to end: resolve, discover/check, select,
/// execute/report.
///
/// # Errors
/// Compilation, discovery, or harness failures, and a nonzero summary when any
/// selected test fails.
pub fn test_cmd(file: Option<&Path>, options: &TestOptions, cfg: &crate::Config) -> CmdResult {
    runner::run(file, options, cfg)
}

/// A test's classified result, as public data for tests and tools: the logical
/// ID, the outcome status, and the captured output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TestResult {
    /// The test's logical ID.
    pub id: String,
    /// The outcome status.
    pub status: TestStatus,
    /// The captured output (always present; the reporter decides when to show it).
    pub output: String,
}

/// The public outcome classification, mirroring the runner's internal one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TestStatus {
    /// The test returned normally.
    Passed,
    /// The built-in `fail()` fired.
    Failed,
    /// The evaluator faulted at runtime.
    Fault,
    /// A residual effect reached the runtime with no handler.
    UnhandledEffect,
    /// The test called `exit(code)` (any code, even zero).
    Exit,
    /// The harness could not be built or run.
    Infrastructure,
}

/// Discover, select, and run tests for a project or a single file, returning
/// each result in logical-ID order. The structured entry point tests drive.
///
/// # Errors
/// Front-end or discovery errors; a failing test is a result, not an error.
pub fn run_results(
    file: Option<&Path>,
    options: &TestOptions,
    cfg: &crate::Config,
) -> Result<Vec<TestResult>, crate::Error> {
    Ok(runner::run_report(file, options, cfg)?
        .into_iter()
        .map(|(id, outcome)| TestResult {
            id,
            status: runner::public_status(outcome.kind),
            output: outcome.output,
        })
        .collect())
}

/// The `prism-test-events-v1` NDJSON bytes for a project or file. Byte-stable
/// across runs; tests assert this directly.
///
/// # Errors
/// Front-end or discovery errors.
pub fn event_bytes(
    file: Option<&Path>,
    options: &TestOptions,
    cfg: &crate::Config,
) -> Result<Vec<u8>, crate::Error> {
    runner::event_bytes(file, options, cfg)
}

/// The `prism-test-events-v1` NDJSON bytes a structured [`Failure`] renders to.
///
/// Runs through the same emit path the runner uses (`test_started` then the
/// structured `test_failed`). The seam the later stdlib assertion layer and its
/// conformance fixture exercise: a decoded failure payload converts to canonical
/// event bytes without a second event path.
#[must_use]
pub fn structured_failure_events(id: &str, failure: &Failure) -> Vec<u8> {
    runner::structured_failure_events(id, failure)
}

/// The `prism test --list` output for a project or file.
///
/// One logical ID per line (human) or the `prism-test-events-v1`
/// `suite_started`/`test_started`/`suite_finished` frame (JSON, selected by
/// `options.json`). The bytes the CLI prints, exposed so the list contract is
/// testable without capturing stdout.
///
/// # Errors
/// Front-end or discovery errors, an invalid test signature, or a duplicate ID.
pub fn list_output(
    file: Option<&Path>,
    options: &TestOptions,
    cfg: &crate::Config,
) -> Result<String, crate::Error> {
    runner::list_output(file, options, cfg)
}

/// The sorted descriptor set discovered for a project directory.
///
/// The stable inspection surface behind `prism test --list`, exposed for the
/// manifest and byte-stability tests. Diagnostic locations are populated but do
/// not enter the manifest's canonical bytes.
///
/// # Errors
/// Front-end errors, an invalid test signature, or a duplicate logical ID.
pub fn descriptors_for_project(
    dir: &Path,
    cfg: &crate::Config,
) -> Result<Vec<TestDescriptor>, crate::Error> {
    Ok(discovery::discover_project(dir, cfg)?.descriptors())
}

/// The sorted descriptor set discovered for a single source file.
///
/// # Errors
/// Front-end errors, an invalid test signature, or a duplicate logical ID.
pub fn descriptors_for_file(
    file: &Path,
    cfg: &crate::Config,
) -> Result<Vec<TestDescriptor>, crate::Error> {
    Ok(discovery::discover_file(file, cfg)?.descriptors())
}
