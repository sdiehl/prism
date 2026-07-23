//! `prism run`: interpret a single program, or every example under a directory.

use std::ffi::OsStr;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use clap::ValueEnum;

use crate::cli::{render_cli_error, resolve_input, CmdError, CmdResult};
use crate::error::Error;

const DEFAULT_EXAMPLE_ATTEMPTS: usize = 1;
const EXAMPLE_ATTEMPTS_KEY: &str = "attempts=";
const EXAMPLE_DIRECTIVE_PREFIX: &str = "prism-example:";
const EXAMPLE_INPUT_EXTENSION: &str = "in";
const PRISM_SOURCE_EXTENSION: &str = "pr";

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub enum ExampleStdin {
    /// Use a same-basename `.in` file when present, otherwise empty stdin
    Fixture,
    /// Always run with empty stdin, ignoring any same-basename `.in` file
    Empty,
}

#[derive(Debug)]
struct ExampleSpec {
    stdin: ExampleStdin,
    attempts: usize,
}

pub fn run_file_cmd(
    file: &Path,
    record: Option<&Path>,
    lineage: Option<&Path>,
    durable: Option<&Path>,
    args: Vec<String>,
    cfg: &crate::Config,
    defer_holes: bool,
) -> Result<Option<i32>, CmdError> {
    let (full, roots, name, _) = resolve_input(file, cfg)?;
    // Stream `print` to the terminal and read from real stdin so the CLI behaves
    // like a normal program. `exit(n)` maps to a real process exit in the caller,
    // skipping the `=> value` trailer.
    let stdout = io::stdout();
    let stdin = io::stdin();
    let mut out = stdout.lock();
    let mut input = stdin.lock();
    if defer_holes && record.is_some() {
        return Err((
            Error::ResolveCommand("`--defer-holes` cannot be combined with `--record`".into()),
            full,
            name,
        ));
    }
    if durable.is_some() && record.is_some() {
        return Err((
            Error::ResolveCommand("`--durable` cannot be combined with `--record`".into()),
            full,
            name,
        ));
    }
    // `--durable PATH` persists each observation to a crash-safe log and resumes a
    // prior crashed run from it: the committed prefix is replayed with no real IO,
    // then new observations stream live and are appended. Re-running the same
    // command after a crash continues byte-identically.
    if let Some(durable_path) = durable {
        let run = crate::durable_run_on(
            &full,
            &roots,
            &mut out,
            &mut input,
            cfg,
            args,
            durable_path,
            None,
        )
        .map_err(|e| (e, full.clone(), name.clone()))?;
        drop(out);
        drop(input);
        eprintln!(
            "durable run: {} observations committed to {} ({} replayed from the prior run)",
            run.committed,
            durable_path.display(),
            run.replayed
        );
        return Ok(run.exit);
    }
    // `--lineage` (which clap already gated on `--record`) records the run, writes
    // its trace, and writes the sidecar that explains that trace.
    if let (Some(record_path), Some(lineage_path)) = (record, lineage) {
        let recorded = crate::record_run_on(&full, &roots, &mut out, &mut input, cfg, args.clone())
            .map_err(|e| (e, full.clone(), name.clone()))?;
        drop(out);
        drop(input);
        crate::debug::durable::write_atomic(record_path, &recorded.trace).map_err(|e| {
            (
                Error::Io(e),
                full.clone(),
                record_path.display().to_string(),
            )
        })?;
        // Compute the trace's relation to its sidecar (relative path plus a digest of
        // the trace bytes) now, while both paths are in hand, so the sidecar's trace
        // node describes where its durable trace lives and `lineage verify` can find
        // and check it from the graph alone.
        let replay =
            crate::lineage::replay_relation(lineage_path, record_path, recorded.trace.as_bytes());
        let run_lineage = crate::lineage::RunLineage::collect(crate::lineage::RunLineageInput {
            request: crate::lineage::BuildRequest::run(file),
            source: &full,
            roots: &roots,
            cfg,
            backend: crate::lineage::BACKEND_INTERPRETER,
            argv: args,
            events: &recorded.events,
            observations: &recorded.canonical_trace,
            stdout: &recorded.term,
            replay: Some(replay),
        })
        .map_err(|e| (e, full.clone(), name.clone()))?;
        crate::lineage::write_run_sidecar(lineage_path, &run_lineage)
            .map_err(|e| (e, full, lineage_path.display().to_string()))?;
        eprintln!(
            "recorded {} observations to {} and run lineage to {}",
            recorded.observations,
            record_path.display(),
            lineage_path.display()
        );
        return Ok(recorded.exit);
    }
    if let Some(path) = record {
        let (exit, trace, n_obs) =
            crate::record_on_with_args(&full, &roots, &mut out, &mut input, cfg, args)
                .map_err(|e| (e, full.clone(), name.clone()))?;
        drop(out);
        drop(input);
        crate::debug::durable::write_atomic(path, &trace)
            .map_err(|e| (Error::Io(e), full, path.display().to_string()))?;
        eprintln!("recorded {n_obs} observations to {}", path.display());
        return Ok(exit);
    }
    let run = if defer_holes {
        crate::interpret_io_on_with_args_deferred_holes(
            &full, &roots, &mut out, &mut input, cfg, args,
        )
    } else {
        crate::interpret_io_on_with_args(&full, &roots, &mut out, &mut input, cfg, args)
    }
    .map_err(|e| (e, full, name))?;
    drop(out);
    drop(input);
    if run.exit.is_none() {
        println!("=> {}", run.value.show());
    }
    Ok(run.exit)
}

pub(crate) fn collect_prism_sources(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), io::Error> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            // A directory with a manifest is a project, not a set of standalone
            // examples: its modules import each other (and dependencies), so
            // compiling them file-by-file fails resolution by construction.
            // Projects run through the project pipeline; the sweep skips them.
            if path.join(crate::project::MANIFEST).is_file() {
                continue;
            }
            collect_prism_sources(&path, out)?;
        } else if file_type.is_file()
            && path.extension().and_then(OsStr::to_str) == Some(PRISM_SOURCE_EXTENSION)
        {
            out.push(path);
        }
    }
    Ok(())
}

pub(crate) fn example_sources(dir: &Path) -> Result<Vec<PathBuf>, CmdError> {
    let mut sources = Vec::new();
    collect_prism_sources(dir, &mut sources)
        .map_err(|e| (Error::Io(e), String::new(), dir.display().to_string()))?;
    sources.sort();
    if sources.is_empty() {
        return Err((
            Error::ResolveCommand(format!(
                "no .{PRISM_SOURCE_EXTENSION} files found under {}",
                dir.display()
            )),
            String::new(),
            dir.display().to_string(),
        ));
    }
    Ok(sources)
}

fn example_spec(file: &Path, default_stdin: ExampleStdin) -> Result<ExampleSpec, String> {
    let src = fs::read_to_string(file).map_err(|e| format!("{}: {e}", file.display()))?;
    let mut spec = ExampleSpec {
        stdin: default_stdin,
        attempts: DEFAULT_EXAMPLE_ATTEMPTS,
    };
    for line in src.lines() {
        let trimmed = line.trim_start();
        if trimmed.is_empty() {
            continue;
        }
        let Some(comment) = trimmed.strip_prefix("--") else {
            break;
        };
        let comment = comment.trim_start();
        let Some(rest) = comment.strip_prefix(EXAMPLE_DIRECTIVE_PREFIX) else {
            continue;
        };
        for item in rest.split(',').map(str::trim).filter(|s| !s.is_empty()) {
            if let Some(value) = item.strip_prefix(EXAMPLE_ATTEMPTS_KEY) {
                spec.attempts = value
                    .parse::<usize>()
                    .ok()
                    .filter(|attempts| *attempts > 0)
                    .ok_or_else(|| {
                        format!("{}: invalid example attempts `{value}`", file.display())
                    })?;
            }
        }
    }
    Ok(spec)
}

fn example_input(file: &Path, stdin: ExampleStdin) -> Result<Vec<u8>, String> {
    match stdin {
        ExampleStdin::Empty => Ok(Vec::new()),
        ExampleStdin::Fixture => {
            let input_path = file.with_extension(EXAMPLE_INPUT_EXTENSION);
            if input_path.exists() {
                fs::read(&input_path).map_err(|e| format!("{}: {e}", input_path.display()))
            } else {
                Ok(Vec::new())
            }
        }
    }
}

fn run_example_once(
    file: &Path,
    cfg: &crate::Config,
    stdin: ExampleStdin,
) -> Result<Option<i32>, String> {
    let (full, roots, name, _) =
        resolve_input(file, cfg).map_err(|(e, src, name)| render_cli_error(&e, &src, &name))?;
    let mut out = io::sink();
    let input_bytes = example_input(file, stdin)?;
    let mut input = io::Cursor::new(input_bytes);
    crate::interpret_io_on_with_args(&full, &roots, &mut out, &mut input, cfg, Vec::new())
        .map(|run| run.exit)
        .map_err(|e| render_cli_error(&e, &full, &name))
}

pub(crate) fn run_example_file(
    file: &Path,
    cfg: &crate::Config,
    default_stdin: ExampleStdin,
) -> Result<Option<i32>, String> {
    let spec = example_spec(file, default_stdin)?;
    let mut last_error = None;
    for _ in 0..spec.attempts {
        match run_example_once(file, cfg, spec.stdin) {
            Ok(exit) => return Ok(exit),
            Err(msg) => last_error = Some(msg),
        }
    }
    Err(last_error.unwrap_or_else(|| format!("{}: no example attempts ran", file.display())))
}

pub fn run_examples_cmd(dir: &Path, cfg: &crate::Config, stdin: ExampleStdin) -> CmdResult {
    let sources = example_sources(dir)?;
    let mut failures = Vec::new();
    for file in &sources {
        match run_example_file(file, cfg, stdin) {
            Ok(None | Some(0)) => println!("ok {}", file.display()),
            Ok(Some(code)) => {
                println!("FAIL {}", file.display());
                failures.push(format!("{} exited with status {code}", file.display()));
            }
            Err(msg) => {
                println!("FAIL {}", file.display());
                failures.push(format!("{}:\n{msg}", file.display()));
            }
        }
    }
    if failures.is_empty() {
        println!("examples: {} passed", sources.len());
        return Ok(());
    }
    for failure in &failures {
        eprintln!("{failure}");
    }
    Err((
        Error::RuntimeEvaluation(format!(
            "{} of {} examples failed",
            failures.len(),
            sources.len()
        )),
        String::new(),
        dir.display().to_string(),
    ))
}
