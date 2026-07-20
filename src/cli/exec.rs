//! The execution-control family: reproduce, step, pause, and resume runs.

use std::path::Path;

use crate::cli::render::{cut_position, cut_provenance, print_step_ruler};
use crate::cli::{file_name, read, resolve_input, CmdError, CmdResult};
use crate::driver::CutTarget;
use crate::error::Error;

// Reproduce a recorded run from a `.replay` trace.
pub fn replay(file: &Path, trace: &Path, cfg: &crate::Config) -> CmdResult {
    let (full, roots, name, _) = resolve_input(file, cfg)?;
    let trace_src = read(trace).map_err(|e| (e, String::new(), file_name(trace)))?;
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    let exit =
        crate::replay_on(&full, &roots, &mut out, &trace_src, cfg).map_err(|e| (e, full, name))?;
    drop(out);
    if let Some(code) = exit {
        std::process::exit(code);
    }
    Ok(())
}

// Reverse-step debugger over a `.replay` trace.
pub fn debug(file: &Path, trace: &Path, cfg: &crate::Config) -> CmdResult {
    let (full, roots, name, _) = resolve_input(file, cfg)?;
    let trace_src = read(trace).map_err(|e| (e, String::new(), file_name(trace)))?;
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let mut cmds = stdin.lock();
    let mut ui = stdout.lock();
    crate::debug_on(&full, &roots, &trace_src, &mut cmds, &mut ui, cfg)
        .map_err(|e| (e, full, name))?;
    Ok(())
}

// Run a program and print each observation with the machine step it fired at.
pub fn steps(file: &Path, json: bool, cfg: &crate::Config) -> CmdResult {
    let (full, roots, name, _) = resolve_input(file, cfg)?;
    let stdin = std::io::stdin();
    let mut input = stdin.lock();
    // Under `--json` the program's own stdout is captured rather than echoed, so
    // the emitted JSON is the whole stream a tool reads; the run still executes in
    // full (previews carry what it printed).
    let ruler = if json {
        let mut sink: Vec<u8> = Vec::new();
        crate::step_ruler_on(&full, &roots, &mut sink, &mut input, cfg)
    } else {
        let stdout = std::io::stdout();
        let mut sink = stdout.lock();
        crate::step_ruler_on(&full, &roots, &mut sink, &mut input, cfg)
    }
    .map_err(|e| (e, full.clone(), name.clone()))?;
    drop(input);
    if json {
        println!(
            "{}",
            serde_json::to_string_pretty(&ruler).expect("ruler is serializable")
        );
    } else {
        print_step_ruler(&ruler);
    }
    if let Some(code) = ruler.exit {
        std::process::exit(code);
    }
    Ok(())
}

// Pause a running program and snapshot it to a `kont` file. The pause point is
// named exactly one way: an opaque step budget (`--at`), the k-th entry to a
// definition (`--at-call`), or the k-th performance of a capability op
// (`--at-op`). The named cuts each reduce to an equivalent `--at N`, reported so
// the snapshot can be reproduced by step count.
pub fn suspend(
    file: &Path,
    at: Option<usize>,
    at_call: Option<&str>,
    at_op: Option<&str>,
    out: &Path,
    cfg: &crate::Config,
) -> CmdResult {
    match (at, at_call, at_op) {
        (Some(n), None, None) => suspend_at_step(file, n, out, cfg),
        (None, Some(spec), None) => {
            let (def, nth) = parse_nth(spec)?;
            suspend_at_named(file, &CutTarget::Call { def, nth }, out, cfg)
        }
        (None, None, Some(spec)) => {
            let (op, nth) = parse_nth(spec)?;
            suspend_at_named(file, &CutTarget::Op { op, nth }, out, cfg)
        }
        _ => Err(suspend_arg_error(
            "`prism exec suspend` needs exactly one of --at, --at-call, or --at-op",
        )),
    }
}

// The `--at N` arm: pause after `at` machine steps.
fn suspend_at_step(file: &Path, at: usize, out: &Path, cfg: &crate::Config) -> CmdResult {
    let (full, roots, name, _) = resolve_input(file, cfg)?;
    let stdout = std::io::stdout();
    let stdin = std::io::stdin();
    let mut sink = stdout.lock();
    let mut input = stdin.lock();
    let result = crate::suspend_on(&full, &roots, &mut sink, &mut input, at, cfg)
        .map_err(|e| (e, full.clone(), name.clone()))?;
    drop(sink);
    drop(input);
    match result {
        crate::SuspendResult::Suspended { bytes, cut } => {
            std::fs::write(out, &bytes)
                .map_err(|e| (Error::Io(e), full, out.display().to_string()))?;
            eprintln!(
                "suspended after {at} steps to {} ({} bytes); {}",
                out.display(),
                bytes.len(),
                cut_position(&cut)
            );
            Ok(())
        }
        crate::SuspendResult::Done(exit) => {
            // The budget was past the program's length: it simply ran.
            eprintln!("program completed in fewer than {at} steps; nothing suspended");
            if let Some(code) = exit {
                std::process::exit(code);
            }
            Ok(())
        }
    }
}

// The `--at-call` / `--at-op` arm: pause at a named program point. The report
// names the def stack and the equivalent `--at N` that reproduces the snapshot.
fn suspend_at_named(file: &Path, target: &CutTarget, out: &Path, cfg: &crate::Config) -> CmdResult {
    let (full, roots, name, _) = resolve_input(file, cfg)?;
    let stdout = std::io::stdout();
    let stdin = std::io::stdin();
    let mut sink = stdout.lock();
    let mut input = stdin.lock();
    let result = crate::suspend_at_cut_on(&full, &roots, &mut sink, &mut input, target, cfg)
        .map_err(|e| (e, full.clone(), name.clone()))?;
    drop(sink);
    drop(input);
    match result {
        crate::SuspendAtCut::Suspended { bytes, cut, report } => {
            std::fs::write(out, &bytes)
                .map_err(|e| (Error::Io(e), full, out.display().to_string()))?;
            eprintln!(
                "suspended at {} to {} ({} bytes); {}",
                cut_provenance(report.equiv_at, &report.def_stack),
                out.display(),
                bytes.len(),
                cut_position(&cut)
            );
            eprintln!("  reproduce with `--at {}`", report.equiv_at);
            Ok(())
        }
        crate::SuspendAtCut::Done(exit) => {
            eprintln!(
                "program completed before {}; nothing suspended",
                target.describe()
            );
            if let Some(code) = exit {
                std::process::exit(code);
            }
            Ok(())
        }
    }
}

// Parse a `NAME[:K]` cut spec into its name and 1-based count (default 1). The
// count rides after the last colon; op labels (`Console.print`) and qualified
// definition names carry a `.`, never a `:`, so splitting on the last colon is
// unambiguous.
fn parse_nth(spec: &str) -> Result<(String, usize), CmdError> {
    let (name, nth) = match spec.rsplit_once(':') {
        Some((name, count)) => {
            let nth = count.parse::<usize>().map_err(|_| {
                suspend_arg_error(&format!("cut count `{count}` in `{spec}` is not a number"))
            })?;
            (name, nth)
        }
        None => (spec, 1),
    };
    if name.is_empty() {
        return Err(suspend_arg_error("a cut needs a definition or op name"));
    }
    if nth == 0 {
        return Err(suspend_arg_error(
            "a cut count is 1-based; `:0` is not a target",
        ));
    }
    Ok((name.to_string(), nth))
}

fn suspend_arg_error(msg: &str) -> CmdError {
    (
        Error::ResolveCommand(msg.to_string()),
        String::new(),
        "suspend".to_string(),
    )
}

// Resume a program from a `kont` snapshot, running it to completion.
pub fn resume(file: &Path, snapshot: &Path, cfg: &crate::Config) -> CmdResult {
    let (full, roots, name, _) = resolve_input(file, cfg)?;
    let bytes =
        std::fs::read(snapshot).map_err(|e| (Error::Io(e), String::new(), file_name(snapshot)))?;
    let stdout = std::io::stdout();
    let stdin = std::io::stdin();
    let mut sink = stdout.lock();
    let mut input = stdin.lock();
    let exit = crate::resume_on(&full, &roots, &bytes, &mut sink, &mut input, cfg)
        .map_err(|e| (e, full, name))?;
    drop(sink);
    drop(input);
    if let Some(code) = exit {
        std::process::exit(code);
    }
    Ok(())
}
