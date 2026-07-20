//! `prism test`: discover, select, and run `test fn` declarations.
//!
//! Thin CLI shell over `crate::testing` (discovery, manifest, harness,
//! runner, events).

use std::path::Path;

use super::CmdResult;

/// The `prism test` invocation options, mirrored from the CLI surface.
///
/// The booleans are independent CLI flags, not a state machine, so the flat set
/// is deliberate (the `Decl`/`DynFlags` precedent).
#[allow(clippy::struct_excessive_bools)]
#[derive(Clone, Debug, Default)]
pub struct TestOptions {
    /// Substring filter over logical test IDs.
    pub filter: Option<String>,
    /// Match the filter as a complete logical ID.
    pub exact: bool,
    /// Discover and print matching tests without running.
    pub list: bool,
    /// Compile the selected targets without executing.
    pub no_run: bool,
    /// Emit `prism-test-events-v1` newline-delimited JSON.
    pub json: bool,
    /// Show captured output for successful tests too.
    pub show_output: bool,
    /// Make an empty selection a command failure.
    pub fail_if_no_tests: bool,
}

/// Run the `prism test` command.
///
/// # Errors
/// Compilation, discovery, or harness failures, and a nonzero summary when any
/// selected test fails.
pub fn test_cmd(file: Option<&Path>, options: &TestOptions, cfg: &crate::Config) -> CmdResult {
    crate::testing::test_cmd(file, options, cfg)
}
