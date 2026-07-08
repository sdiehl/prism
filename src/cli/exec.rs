//! The execution-control family: reproduce, step, pause, and resume runs.

use std::path::Path;

use crate::cli::render::{cut_position, print_step_ruler};
use crate::cli::{file_name, read, resolve_input, CmdResult};
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

// Pause a running program at a step and snapshot it to a `kont` file.
pub fn suspend(file: &Path, at: usize, out: &Path, cfg: &crate::Config) -> CmdResult {
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
