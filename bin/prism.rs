#![allow(clippy::multiple_crate_versions)]

use std::io::Read as _;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use clap::{Parser, Subcommand};
use prism::error::Error;

// A CLI argument struct is the canonical exception to `struct_excessive_bools`:
// the `--no-<pass>` flags and `--mlir` are independent on/off switches, exactly
// what clap models as bool fields, not a state machine.
#[allow(clippy::struct_excessive_bools)]
#[derive(Parser, Debug)]
#[command(
    name = "prism",
    version,
    about = "A modern typed functional language with a call-by-push-value core that lowers to LLVM",
    args_conflicts_with_subcommands = true
)]
struct Cli {
    #[command(subcommand)]
    cmd: Option<Cmd>,
    /// A `.pr` file or project to compile; no path starts the REPL
    file: Option<PathBuf>,
    /// Output path for the compiled binary
    #[arg(short, long)]
    out: Option<PathBuf>,
    /// Use the MLIR backend instead of LLVM
    #[arg(long)]
    mlir: bool,
    /// Core optimizer level (0-2; bare -O is highest)
    #[arg(
        short = 'O',
        long = "opt",
        value_name = "LEVEL",
        global = true,
        num_args = 0..=1,
        default_missing_value = "2"
    )]
    opt: Option<String>,
    /// Explicit pass list, overriding -O (see docs)
    #[arg(long = "passes", value_name = "SPEC", global = true)]
    passes: Option<String>,
    /// C-compiler optimization level for the emitted code (0-3, s, z)
    #[arg(long = "backend-opt", value_name = "LEVEL", global = true)]
    backend_opt: Option<String>,
    /// Default cooperative scheduler policy (cooperative or lifo)
    #[arg(long = "scheduler", value_name = "POLICY", global = true)]
    scheduler: Option<String>,
    /// Disable the newtype-erasure pass
    #[arg(long, global = true)]
    no_erase_newtypes: bool,
    /// Disable the dictionary-specialization pass
    #[arg(long, global = true)]
    no_specialize: bool,
    /// Disable the simplifier pass
    #[arg(long, global = true)]
    no_simplify: bool,
    /// Disable the inliner pass
    #[arg(long, global = true)]
    no_inline: bool,
    /// Disable the scalar-CSE pass
    #[arg(long, global = true)]
    no_cse: bool,
    /// Disable the native effect driver
    #[arg(long, global = true)]
    no_native_effects: bool,
    /// Disable the free-monad trampoline
    #[arg(long, global = true)]
    no_trampoline: bool,
    /// Run Core Lint between optimization passes
    #[arg(long, global = true)]
    core_lint: bool,
    /// Print per-pass rewrite counts to stderr
    #[arg(long, global = true)]
    opt_stats: bool,
    /// Dump Core after each pass to SINK (stdout, stderr, or a directory)
    #[arg(long = "dump-core", value_name = "SINK", global = true)]
    dump_core: Option<String>,
}

#[derive(Subcommand, Debug)]
enum Cmd {
    /// Type-check and run in the interpreter
    Run {
        file: PathBuf,
        /// Capture the run's trace to a `.replay` file
        #[arg(long, value_name = "PATH")]
        record: Option<PathBuf>,
    },
    /// Reproduce a recorded run from a `.replay` trace
    Replay {
        /// The program the trace was recorded against
        file: PathBuf,
        /// The `.replay` trace file to reproduce
        trace: PathBuf,
    },
    /// Reverse-step debugger over a `.replay` trace
    Debug {
        /// The program the trace was recorded against
        file: PathBuf,
        /// The `.replay` trace file to step through
        trace: PathBuf,
    },
    /// Compile the enclosing project to a native binary
    Build {
        /// Where to start the search for the project's `prism.toml`
        #[arg(default_value = ".")]
        path: PathBuf,
        /// Output path for the compiled binary
        #[arg(short, long)]
        out: Option<PathBuf>,
        /// Use the MLIR backend instead of LLVM
        #[arg(long)]
        mlir: bool,
    },
    /// Remove the build-artifact directory (`target/`)
    Clean {
        /// Where to start the search for the project's `prism.toml`
        #[arg(default_value = ".")]
        path: PathBuf,
    },
    /// Type-check and print inferred signatures
    Check { file: PathBuf },
    /// Print one pipeline phase artifact
    ///
    /// PHASE is one of: tokens, ast, types, core, core-json, core-hash, shape,
    /// dupes, namespace, stdlib-hash, fbip, lowered, tier, llvm, mlir.
    Dump { phase: String, file: PathBuf },
    /// Behavior diff by content hash
    Diff {
        /// The old revision (a `.pr` file, directory, or `prism.toml`)
        old: PathBuf,
        /// The new revision (a `.pr` file, directory, or `prism.toml`)
        new: PathBuf,
    },
    /// Attest two backends emit identical output
    Attest { file: PathBuf },
    /// Query the definition dependency graph
    Query {
        /// callers | dependents | deps | uses-type
        kind: String,
        /// The definition name to query (a type name for `uses-type`)
        name: String,
        /// Source file to query (the prelude is included)
        file: PathBuf,
    },
    /// Print every pipeline phase for a program
    Report { file: PathBuf },
    /// Start the interactive shell
    Repl {
        /// Skip the startup banner
        #[arg(long)]
        no_banner: bool,
    },
    /// Format source files in place
    Fmt {
        /// Files or directories to format; `-` for stdin, default current dir
        files: Vec<PathBuf>,
        /// Check only: exit 1 if any file is not canonical, write nothing
        #[arg(long)]
        check: bool,
    },
    /// Generate Markdown API docs from doc comments
    Docs {
        /// Project directory, `prism.toml`, or `.pr` file to document
        #[arg(default_value = ".")]
        path: PathBuf,
        /// Output directory (default: `<project>/target/docs`)
        #[arg(short, long)]
        out: Option<PathBuf>,
        /// Document the embedded standard library instead of `path`
        #[arg(long)]
        stdlib: bool,
        /// Run the doctests (`prism` blocks in doc comments) instead of writing
        #[arg(long)]
        test: bool,
        /// Rewrite stale/empty `output` expectation blocks with the actual output
        /// (implies `--test`); exits nonzero if anything was rewritten
        #[arg(long, visible_alias = "bless")]
        accept: bool,
        /// Check only: exit 1 if any committed page is out of date, write nothing
        #[arg(long)]
        check: bool,
        /// Open the generated index after writing
        #[arg(long)]
        open: bool,
    },
    /// Reseat stable-block rung digests
    Wire {
        /// Recompute and rewrite the goldens in place (required; a bare `wire` is a
        /// no-op guard against an accidental rewrite)
        #[arg(long)]
        accept: bool,
        /// The `.pr` file whose `stable` blocks to reseat
        file: PathBuf,
    },
    /// Add a dependency, pinning its resolved root hash
    Add {
        /// The git reference or content-hash pin to depend on
        target: String,
    },
    /// Explain why a hash is in the build closure
    Why {
        /// The dependency name or content hash to explain
        target: String,
    },
    /// Materialize a namespace to a canonical `.pr` file
    Export {
        /// The project directory, `prism.toml`, or `.pr` file to export
        file: PathBuf,
        /// Output directory for the `.pr` projection and its manifest
        #[arg(short, long)]
        out: Option<PathBuf>,
    },
    /// Sign and log a name -> root pointer at a tag
    Publish {
        /// The project directory, `prism.toml`, or `.pr` file to publish
        file: PathBuf,
        /// The git tag this release is cut at (an opaque label, never a range)
        #[arg(long)]
        tag: String,
        /// The published name (default: the package name, or the file stem)
        #[arg(long)]
        name: Option<String>,
    },
    /// Re-verify published roots against the store
    Audit {
        /// Accept an unsigned (dev-mode) index instead of failing on it
        #[arg(long)]
        allow_unsigned: bool,
    },
    /// mdbook preprocessor for `prism` code blocks
    #[command(hide = true)]
    Mdbook {
        /// mdbook passes `supports <renderer>` here; the book JSON otherwise
        /// arrives on stdin.
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        rest: Vec<String>,
    },
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    if cli.opt.is_some() && cli.passes.is_some() {
        eprintln!("error: `--passes` and `-O` are mutually exclusive");
        return ExitCode::FAILURE;
    }
    // Start from the environment-implied config, then let explicit flags win. The
    // resolved value threads through every compile call, replacing the old set of
    // process-global knobs.
    let mut cfg = prism::Config::from_env();
    if let Some(s) = &cli.opt {
        let Some(level) = prism::OptLevel::parse(s) else {
            eprintln!("invalid optimization level `-O{s}` (expected 0, 1, or 2)");
            return ExitCode::FAILURE;
        };
        cfg.opt = level;
    }
    if let Some(s) = &cli.passes {
        match prism::PassSpec::parse(s) {
            Ok(spec) => cfg.passes = Some(spec),
            Err(e) => {
                eprintln!("error: invalid pass specification: {e}");
                return ExitCode::FAILURE;
            }
        }
    }
    if let Some(s) = &cli.backend_opt {
        if !prism::valid_backend_opt(s) {
            eprintln!(
                "invalid backend optimization level `--backend-opt {s}` (expected {})",
                prism::BACKEND_OPT_LEVELS.join(", ")
            );
            return ExitCode::FAILURE;
        }
        cfg.backend_opt.clone_from(s);
    }
    if let Some(s) = &cli.scheduler {
        let Some(sched) = prism::Scheduler::parse(s) else {
            eprintln!("invalid scheduler `--scheduler {s}` (expected cooperative, fifo, or lifo)");
            return ExitCode::FAILURE;
        };
        cfg.scheduler = sched;
    }
    cfg.disabled.extend(
        [
            (cli.no_erase_newtypes, prism::CorePass::EraseNewtypes),
            (cli.no_specialize, prism::CorePass::Specialize),
            (cli.no_simplify, prism::CorePass::Simplify),
            (cli.no_inline, prism::CorePass::Inline),
            (cli.no_cse, prism::CorePass::Cse),
        ]
        .into_iter()
        .filter_map(|(off, pass)| off.then_some(pass)),
    );
    // Behavior toggles: the env baseline (via `from_env`) stands unless a flag
    // overrides it, the same "explicit flag wins" rule as `-O`/`--scheduler`.
    if cli.no_native_effects {
        cfg.flags.native_effects = false;
    }
    if cli.no_trampoline {
        cfg.flags.trampoline = false;
    }
    if cli.core_lint {
        cfg.flags.core_lint = true;
    }
    if cli.opt_stats {
        cfg.flags.opt_stats = true;
    }
    if let Some(sink) = cli.dump_core {
        cfg.flags.dump_core = Some(sink.into());
    }
    let result = match (cli.cmd, cli.file) {
        (Some(cmd), _) => dispatch(cmd, &cfg),
        // Bare `prism <path>` compiles to a native binary (rustc-style: the
        // output is named after the source); with no path, the REPL opens.
        (None, Some(file)) => build_input(&file, cli.out, cli.mlir, &cfg),
        (None, None) => {
            prism::repl::repl(true);
            return ExitCode::SUCCESS;
        }
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err((e, src, name)) => {
            eprint!("{}", e.render(&src, &name));
            ExitCode::FAILURE
        }
    }
}

fn read(file: &Path) -> Result<String, Error> {
    std::fs::read_to_string(file).map_err(Error::Io)
}

// Imports resolve relative to the entry file's directory.
fn base_of(file: &Path) -> PathBuf {
    file.parent()
        .filter(|p| !p.as_os_str().is_empty())
        .map_or_else(|| PathBuf::from("."), Path::to_path_buf)
}

// A resolved CLI input: source with prelude prepended, the module search path
// (project source root, any path dependencies, then the embedded stdlib), a
// display name for diagnostics, and the default binary name a bare build would
// write.
type Resolved = (String, Vec<prism::Root>, String, PathBuf);

// Resolve a CLI argument into the source to compile, the module-resolution base,
// a display name, and the default binary name a bare build would write. A
// directory or a `prism.toml` is a project: the entry comes from the manifest,
// modules resolve from the project's `src/`, and the default binary is the
// package name. A `.pr` file is a single-file program whose imports resolve
// relative to its own directory and whose default binary is its stem.
fn resolve_input(arg: &Path) -> Result<Resolved, (Error, String, String)> {
    let is_project = arg.is_dir() || arg.file_name().is_some_and(|n| n == "prism.toml");
    if is_project {
        let project = prism::project::load_project(arg)
            .map_err(|e| (e, String::new(), arg.display().to_string()))?;
        let src =
            read(&project.entry).map_err(|e| (e, String::new(), file_name(&project.entry)))?;
        // A project may replace the built-in prelude with its own (`[package]
        // prelude`); otherwise the built-in one is prepended as usual.
        let full = match &project.prelude {
            Some(p) => {
                let prelude = read(p).map_err(|e| (e, String::new(), file_name(p)))?;
                prism::with_custom_prelude(&prelude, &src)
            }
            None => prism::with_prelude(&src),
        };
        // A project build lands in `target/` at the package root (rustc-style),
        // keeping artifacts out of the source tree.
        let out = project.root.join("target").join(&project.name);
        let roots = prism::project_roots(&project.src_dir, &project.dep_src_dirs);
        Ok((full, roots, file_name(&project.entry), out))
    } else {
        let src = read(arg).map_err(|e| (e, String::new(), file_name(arg)))?;
        let full = prism::with_prelude(&src);
        // `factorial.pr` -> `factorial`; an extensionless arg falls back to `a.out`.
        let out = arg
            .file_stem()
            .map_or_else(|| PathBuf::from("a.out"), PathBuf::from);
        Ok((
            full,
            prism::default_roots(&base_of(arg)),
            file_name(arg),
            out,
        ))
    }
}

// Compile `arg` to a native binary, the shared body of bare `prism <file>` and
// `prism build`. `out` overrides the default name (source stem for a file, the
// package name for a project).
fn build_input(
    arg: &Path,
    out: Option<PathBuf>,
    mlir: bool,
    cfg: &prism::Config,
) -> Result<(), (Error, String, String)> {
    let (full, roots, name, default_out) = resolve_input(arg)?;
    let out = out.unwrap_or(default_out);
    // Codegen writes intermediates (`.bc`, `.ll`) beside the binary, so the
    // output directory must exist first (the default `target/` may not yet).
    if let Some(dir) = out.parent().filter(|d| !d.as_os_str().is_empty()) {
        std::fs::create_dir_all(dir).map_err(|e| (Error::Io(e), full.clone(), name.clone()))?;
    }
    // Report the modules entering the build, one per line, before compiling.
    // Best-effort: a resolution failure here is swallowed so the real build below
    // produces the authoritative diagnostic.
    if let Ok(modules) = prism::source_modules(&full, &roots) {
        for m in &modules {
            println!("  compiling {m}");
        }
    }
    build_dispatch(mlir, &full, &roots, &out, cfg).map_err(|e| (e, full, name))?;
    println!("wrote {}", out.display());
    Ok(())
}

// `prism clean`: wipe the `target/` build-artifact directory, cargo-clean style.
// In a project it is the `target/` at the package root (the nearest enclosing
// `prism.toml`); otherwise the one under `path`. A missing `target/` is success.
fn clean_cmd(path: &Path) -> Result<(), (Error, String, String)> {
    let start = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let root = prism::project::find_manifest(&start)
        .and_then(|m| m.parent().map(Path::to_path_buf))
        .unwrap_or(start);
    let target = root.join("target");
    match std::fs::remove_dir_all(&target) {
        Ok(()) => println!("removed {}", target.display()),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            println!("nothing to clean ({} absent)", target.display());
        }
        Err(e) => return Err((Error::Io(e), String::new(), target.display().to_string())),
    }
    Ok(())
}

fn dispatch(cmd: Cmd, cfg: &prism::Config) -> Result<(), (Error, String, String)> {
    match cmd {
        Cmd::Run { file, record } => {
            let (full, roots, name, _) = resolve_input(&file)?;
            // Stream `print` to the terminal and read from real stdin so the CLI
            // behaves like a normal program. `exit(n)` maps to a real process
            // exit with that code, skipping the `=> value` trailer.
            let stdout = std::io::stdout();
            let stdin = std::io::stdin();
            let mut out = stdout.lock();
            let mut input = stdin.lock();
            // `--record`: capture the observation trace and write it out; the run
            // still streams live to the terminal.
            if let Some(path) = record {
                let (exit, trace, n_obs) =
                    prism::record_on(&full, &roots, &mut out, &mut input, cfg)
                        .map_err(|e| (e, full.clone(), name.clone()))?;
                drop(out);
                drop(input);
                std::fs::write(&path, &trace)
                    .map_err(|e| (Error::Io(e), full, path.display().to_string()))?;
                eprintln!("recorded {n_obs} observations to {}", path.display());
                if let Some(code) = exit {
                    std::process::exit(code);
                }
                return Ok(());
            }
            let run = prism::interpret_io_on(&full, &roots, &mut out, &mut input, cfg)
                .map_err(|e| (e, full, name))?;
            drop(out);
            drop(input);
            if let Some(code) = run.exit {
                std::process::exit(code);
            }
            println!("=> {}", run.value.show());
            Ok(())
        }
        Cmd::Replay { file, trace } => {
            let (full, roots, name, _) = resolve_input(&file)?;
            let trace_src = read(&trace).map_err(|e| (e, String::new(), file_name(&trace)))?;
            let stdout = std::io::stdout();
            let mut out = stdout.lock();
            let exit = prism::replay_on(&full, &roots, &mut out, &trace_src, cfg)
                .map_err(|e| (e, full, name))?;
            drop(out);
            if let Some(code) = exit {
                std::process::exit(code);
            }
            Ok(())
        }
        Cmd::Debug { file, trace } => {
            let (full, roots, name, _) = resolve_input(&file)?;
            let trace_src = read(&trace).map_err(|e| (e, String::new(), file_name(&trace)))?;
            let stdin = std::io::stdin();
            let stdout = std::io::stdout();
            let mut cmds = stdin.lock();
            let mut ui = stdout.lock();
            prism::debug_on(&full, &roots, &trace_src, &mut cmds, &mut ui, cfg)
                .map_err(|e| (e, full, name))?;
            Ok(())
        }
        Cmd::Build { path, out, mlir } => {
            // `build` is the project verb: locate the nearest enclosing
            // `prism.toml` and compile it. A single file compiles via
            // `prism <file.pr>`. Canonicalize first so the default `.` has real
            // parent components to walk up through.
            let start = path.canonicalize().unwrap_or(path);
            let manifest = prism::project::find_manifest(&start).ok_or_else(|| {
                (
                    Error::Resolve(
                        "no prism.toml found: `prism build` compiles a project; \
                         compile a single file with `prism <file.pr>`"
                            .into(),
                    ),
                    String::new(),
                    start.display().to_string(),
                )
            })?;
            build_input(&manifest, out, mlir, cfg)
        }
        Cmd::Clean { path } => clean_cmd(&path),
        Cmd::Check { file } => {
            let (full, roots, name, _) = resolve_input(&file)?;
            let checked = prism::check_on(&full, &roots).map_err(|e| (e, full, name))?;
            for d in &checked.decls {
                println!("{} : {}", d.name, d.ty.show());
            }
            Ok(())
        }
        Cmd::Dump { phase, file } => {
            let (full, roots, name, _) = resolve_input(&file)?;
            let out = prism::dump_on(&phase, &full, &roots, cfg).map_err(|e| (e, full, name))?;
            println!("{out}");
            Ok(())
        }
        Cmd::Attest { file } => {
            let (full, roots, name, _) = resolve_input(&file)?;
            let out = prism::attest_on(&full, &roots, cfg).map_err(|e| (e, full, name))?;
            print!("{out}");
            Ok(())
        }
        Cmd::Diff { old, new } => {
            let (old_full, _, old_name, _) = resolve_input(&old)?;
            let (new_full, roots, new_name, _) = resolve_input(&new)?;
            let out = prism::diff_on(&old_full, &new_full, &roots, cfg)
                .map_err(|e| (e, new_full, format!("{old_name} -> {new_name}")))?;
            print!("{out}");
            Ok(())
        }
        Cmd::Query { kind, name, file } => {
            let (full, roots, disp, _) = resolve_input(&file)?;
            let out =
                prism::query_on(&kind, &name, &full, &roots, cfg).map_err(|e| (e, full, disp))?;
            print!("{out}");
            Ok(())
        }
        Cmd::Report { file } => {
            let (full, roots, _name, _) = resolve_input(&file)?;
            print!("{}", prism::report_on(&full, &roots, cfg));
            Ok(())
        }
        Cmd::Repl { no_banner } => {
            prism::repl::repl(!no_banner);
            Ok(())
        }
        Cmd::Fmt { files, check } => fmt_cmd(&files, check),
        Cmd::Wire { accept, file } => wire_cmd(accept, &file),
        Cmd::Docs {
            path,
            out,
            stdlib,
            test,
            accept,
            check,
            open,
        } => docs_cmd(&path, out, stdlib, test, accept, check, open),
        Cmd::Add { target } => pkg_report(prism::pkg::cmd::add(&target, cfg), &target),
        Cmd::Why { target } => pkg_report(prism::pkg::cmd::why(&target, cfg), &target),
        Cmd::Export { file, out } => {
            let (full, roots, _name, default_out) = resolve_input(&file)?;
            let user_src = user_source(&file)?;
            let stem = out_stem(&default_out);
            let out_dir = out.unwrap_or_else(|| PathBuf::from("target").join("export"));
            pkg_report(
                prism::pkg::export::export_cmd(&user_src, &full, &roots, &out_dir, &stem),
                &file.display().to_string(),
            )
        }
        Cmd::Publish { file, tag, name } => {
            let (full, roots, _disp, default_out) = resolve_input(&file)?;
            let pkg_name = name.unwrap_or_else(|| out_stem(&default_out));
            pkg_report(
                prism::pkg::trust::publish_cmd(&full, &roots, &pkg_name, &tag, cfg),
                &file.display().to_string(),
            )
        }
        Cmd::Audit { allow_unsigned } => audit_cli(cfg, allow_unsigned),
        Cmd::Mdbook { rest } => mdbook_cmd(&rest),
    }
}

// Print a package-command summary, mapping its error into the dispatch tuple.
// The raw user source of an export/publish input, without the prelude that
// `resolve_input` prepends: the entry file of a project, or the file itself. Kept
// separate because `export` writes this text back out and must not materialize the
// prelude into it.
fn user_source(arg: &Path) -> Result<String, (Error, String, String)> {
    let is_project = arg.is_dir() || arg.file_name().is_some_and(|n| n == "prism.toml");
    if is_project {
        let project = prism::project::load_project(arg)
            .map_err(|e| (e, String::new(), arg.display().to_string()))?;
        read(&project.entry).map_err(|e| (e, String::new(), file_name(&project.entry)))
    } else {
        read(arg).map_err(|e| (e, String::new(), file_name(arg)))
    }
}

// The namespace stem/name of an input, taken from the default output name
// `resolve_input` computes (the package name for a project, the file stem for a
// single file).
fn out_stem(default_out: &Path) -> String {
    default_out.file_name().map_or_else(
        || "namespace".to_string(),
        |s| s.to_string_lossy().into_owned(),
    )
}

// `prism audit`: render the report and set the exit code from its verdict.
fn audit_cli(cfg: &prism::Config, allow_unsigned: bool) -> Result<(), (Error, String, String)> {
    let report = prism::pkg::trust::audit_cmd(cfg, allow_unsigned)
        .map_err(|e| (e, String::new(), "audit".to_string()))?;
    print!("{}", report.render());
    if report.ok() {
        Ok(())
    } else {
        Err((
            Error::Resolve("audit failed".into()),
            String::new(),
            "audit".to_string(),
        ))
    }
}

fn pkg_report(result: Result<String, Error>, arg: &str) -> Result<(), (Error, String, String)> {
    match result {
        Ok(report) => {
            print!("{report}");
            if !report.ends_with('\n') {
                println!();
            }
            Ok(())
        }
        Err(e) => Err((e, String::new(), arg.to_string())),
    }
}

// The mdbook preprocessor entry point. `prism mdbook supports <renderer>` exits 0
// (every renderer is supported); otherwise the `[context, book]` JSON arrives on
// stdin and the rewritten book JSON is written to stdout. Failures (a block that
// should type-check but does not) print to stderr, and `PRISM_MDBOOK_STRICT` makes
// them fail the build.
fn mdbook_cmd(args: &[String]) -> Result<(), (Error, String, String)> {
    if args.first().map(String::as_str) == Some("supports") {
        return Ok(());
    }
    let mut input = String::new();
    std::io::stdin()
        .read_to_string(&mut input)
        .map_err(|e| (Error::Io(e), String::new(), "<stdin>".into()))?;
    let (book, warnings) =
        prism::preprocess_book(&input).map_err(|e| (e, String::new(), "<mdbook>".into()))?;
    for w in &warnings {
        eprintln!("prism mdbook: {w}");
    }
    print!("{book}");
    if !warnings.is_empty() && std::env::var_os("PRISM_MDBOOK_STRICT").is_some() {
        return Err((
            Error::Codegen(format!(
                "{} doc block(s) did not type-check",
                warnings.len()
            )),
            String::new(),
            String::new(),
        ));
    }
    Ok(())
}

// The modules to document, the roots that resolve their imports, the base to run
// doctests from, the default output directory, and the index title.
type DocsInput = (
    Vec<prism::ModuleSource>,
    Vec<prism::Root>,
    PathBuf,
    PathBuf,
    String,
);

// `prism docs [PATH] [--out DIR] [--stdlib] [--test] [--check] [--open]`.
// Documents the project/dir/file at PATH (or the embedded stdlib with `--stdlib`)
// as one Markdown page per module. `--test` runs the doctests instead of writing;
// `--check` verifies committed pages are current (the `fmt --check` contract);
// otherwise the pages are written under DIR (default `<project>/target/docs`).
#[allow(clippy::fn_params_excessive_bools)]
fn docs_cmd(
    path: &Path,
    out: Option<PathBuf>,
    stdlib: bool,
    test: bool,
    accept: bool,
    check: bool,
    open: bool,
) -> Result<(), (Error, String, String)> {
    // `--accept` (`--bless`) rewrites the inline `output` expectation blocks, so
    // it always runs the doctests.
    let test = test || accept;
    let (generated, roots, base, default_out, expect_files) = if stdlib {
        let g = prism::stdlib_pages().map_err(|e| (e, String::new(), "<stdlib>".into()))?;
        (
            g,
            prism::default_roots(Path::new(".")),
            PathBuf::from("."),
            PathBuf::from("target").join("docs"),
            prism::stdlib_expect_files(),
        )
    } else {
        let (modules, roots, base, default_out, title) = resolve_docs_input(path)?;
        let files = prism::project_expect_files(&modules, &base);
        let g = prism::project_pages(modules, &roots, &title)
            .map_err(|e| (e, String::new(), file_name(path)))?;
        (g, roots, base, default_out, files)
    };

    if test {
        let report = generated.test(&roots, &base);
        for (origin, msg) in &report.failures {
            eprintln!("FAIL {origin}: {msg}");
        }
        println!(
            "doctests: {} passed, {} failed, {} ignored",
            report.passed,
            report.failures.len(),
            report.ignored
        );
        let expect = prism::accept(&expect_files, &roots, &base, accept);
        return expect_result(report.failures.is_empty(), accept, &expect);
    }

    let dir = out.unwrap_or(default_out);
    if check {
        let mut stale = Vec::new();
        for page in &generated.pages {
            let p = dir.join(format!("{}.md", page.slug));
            if std::fs::read_to_string(&p).unwrap_or_default() != page.markdown {
                stale.push(p.display().to_string());
            }
        }
        if !stale.is_empty() {
            for s in &stale {
                eprintln!("{s}: out of date");
            }
            return Err((
                Error::Codegen("docs are out of date; run `prism docs`".into()),
                String::new(),
                String::new(),
            ));
        }
        return Ok(());
    }

    std::fs::create_dir_all(&dir)
        .map_err(|e| (Error::Io(e), String::new(), dir.display().to_string()))?;
    for page in &generated.pages {
        let p = dir.join(format!("{}.md", page.slug));
        std::fs::write(&p, &page.markdown)
            .map_err(|e| (Error::Io(e), String::new(), p.display().to_string()))?;
        println!("  {}", p.display());
    }
    println!("wrote {} pages to {}", generated.pages.len(), dir.display());
    if open {
        open_path(&dir.join("index.md"));
    }
    Ok(())
}

// Report an expect pass loudly (like `just snap`) and turn it into an exit code.
// In accept mode a rewrite is a nonzero exit so CI can never silently bless; in
// check mode a mismatch or run failure is nonzero. `doctests_ok` folds in the
// ordinary compile/run doctest result.
fn expect_result(
    doctests_ok: bool,
    accept: bool,
    expect: &prism::ExpectReport,
) -> Result<(), (Error, String, String)> {
    for origin in &expect.rewritten {
        eprintln!("blessed {origin}");
    }
    for (origin, msg) in &expect.failures {
        eprintln!("FAIL {origin}: {msg}");
    }
    println!(
        "expect: {} checked, {} rewritten, {} failed",
        expect.checked,
        expect.rewritten.len(),
        expect.failures.len()
    );
    let ok = doctests_ok && expect.failures.is_empty() && (!accept || expect.rewritten.is_empty());
    if ok {
        Ok(())
    } else {
        Err((
            Error::Codegen("doctest failures".into()),
            String::new(),
            String::new(),
        ))
    }
}

// Resolve a docs PATH into modules + roots. A `prism.toml` (or a directory under
// one) is a project: its `src/` modules, resolved against the project roots. A
// plain directory documents every `.pr` file beneath it. A single `.pr` file is
// one module. The dotted module name is the source path relative to the source
// root.
fn resolve_docs_input(path: &Path) -> Result<DocsInput, (Error, String, String)> {
    let manifest = if path.file_name().is_some_and(|n| n == "prism.toml") {
        Some(path.to_path_buf())
    } else if path.is_dir() {
        prism::project::find_manifest(&path.canonicalize().unwrap_or_else(|_| path.to_path_buf()))
    } else {
        None
    };

    if manifest.is_some() {
        let project = prism::project::load_project(path)
            .map_err(|e| (e, String::new(), path.display().to_string()))?;
        let files = glob_pr(&project.src_dir);
        let modules = read_modules(&project.src_dir, &files, &project.root)?;
        let roots = prism::project_roots(&project.src_dir, &project.dep_src_dirs);
        let out = project.root.join("target").join("docs");
        Ok((modules, roots, project.root.clone(), out, project.name))
    } else if path.is_dir() {
        let files = glob_pr(path);
        let modules = read_modules(path, &files, path)?;
        let roots = prism::default_roots(path);
        let out = path.join("target").join("docs");
        let title = dir_title(path);
        Ok((modules, roots, path.to_path_buf(), out, title))
    } else {
        let base = base_of(path);
        let modules = read_modules(&base, std::slice::from_ref(&path.to_path_buf()), &base)?;
        let roots = prism::default_roots(&base);
        let out = base.join("target").join("docs");
        let title = path.file_stem().map_or_else(
            || "Documentation".into(),
            |s| s.to_string_lossy().into_owned(),
        );
        Ok((modules, roots, base, out, title))
    }
}

fn read_modules(
    src_root: &Path,
    files: &[PathBuf],
    provenance_root: &Path,
) -> Result<Vec<prism::ModuleSource>, (Error, String, String)> {
    let mut mods = Vec::new();
    for f in files {
        let source = read(f).map_err(|e| (e, String::new(), file_name(f)))?;
        let dotted = dotted_of(src_root, f);
        let source_path = f
            .strip_prefix(provenance_root)
            .unwrap_or(f)
            .display()
            .to_string();
        mods.push(prism::ModuleSource {
            dotted: dotted.clone(),
            title: dotted,
            source,
            source_path,
            is_prelude: false,
        });
    }
    Ok(mods)
}

// A file's dotted module name: its path relative to the source root with the
// `.pr` dropped and separators turned into dots (`src/Data/List.pr` -> `Data.List`).
fn dotted_of(src_root: &Path, file: &Path) -> String {
    let rel = file
        .strip_prefix(src_root)
        .unwrap_or(file)
        .with_extension("");
    let parts: Vec<String> = rel
        .components()
        .filter_map(|c| match c {
            std::path::Component::Normal(s) => Some(s.to_string_lossy().into_owned()),
            _ => None,
        })
        .collect();
    if parts.is_empty() {
        file.file_stem()
            .map_or_else(String::new, |s| s.to_string_lossy().into_owned())
    } else {
        parts.join(".")
    }
}

fn dir_title(path: &Path) -> String {
    path.canonicalize()
        .ok()
        .as_deref()
        .and_then(Path::file_name)
        .or_else(|| path.file_name())
        .map_or_else(
            || "Documentation".into(),
            |n| n.to_string_lossy().into_owned(),
        )
}

// Open a path with the platform's default handler, best-effort.
fn open_path(p: &Path) {
    let mut cmd = if cfg!(target_os = "macos") {
        Command::new("open")
    } else if cfg!(target_os = "windows") {
        let mut c = Command::new("cmd");
        c.args(["/C", "start", ""]);
        c
    } else {
        Command::new("xdg-open")
    };
    if let Err(e) = cmd.arg(p).spawn() {
        eprintln!("could not open {}: {e}", p.display());
    }
}

// Every `.pr` file under `root`, recursively, skipping any build artifacts in a
// `target/` directory. A bad glob pattern yields nothing rather than erroring.
fn glob_pr(root: &Path) -> Vec<PathBuf> {
    let pattern = format!("{}/**/*.pr", root.display());
    let Ok(paths) = glob::glob(&pattern) else {
        return Vec::new();
    };
    paths
        .filter_map(Result::ok)
        // Skip build artifacts (`target`) and dotfile directories (`.git`,
        // editor caches, etc.) that sit BELOW the requested root: a stray
        // `.pr` under one is not part of the project's own source. Only components
        // beneath `root` are inspected, so a project whose own path has a
        // `.`-prefixed or `target` ancestor (e.g. under `~/.config`) is still
        // formatted rather than silently skipped.
        .filter(|p| {
            let rel = p.strip_prefix(root).unwrap_or(p.as_path());
            !rel.components().any(|c| match c {
                std::path::Component::Normal(s) => {
                    s == "target" || s.to_str().is_some_and(|n| n.starts_with('.'))
                }
                _ => false,
            })
        })
        .collect()
}

// `prism fmt [paths..] [--check]`. With no path, the current directory is
// walked, as is any directory path. Explicitly named files must parse. Files
// reached by walking are skipped with a notice if they do not, so one
// unparseable fixture cannot fail a whole-tree run.
// Reseat the wire goldens of a single file's `stable` blocks. Without `--accept`
// it is a deliberate no-op, so an accidental `prism wire foo.pr` never rewrites.
fn wire_cmd(accept: bool, file: &Path) -> Result<(), (Error, String, String)> {
    let name = file_name(file);
    let src = read(file).map_err(|e| (e, String::new(), name.clone()))?;
    if !accept {
        eprintln!(
            "wire: pass --accept to reseat the goldens in {}",
            file.display()
        );
        return Ok(());
    }
    let reseated = prism::format_wire_accept(&src).map_err(|e| (e, src.clone(), name.clone()))?;
    if reseated == src {
        eprintln!("{}: goldens already current", file.display());
        return Ok(());
    }
    std::fs::write(file, &reseated).map_err(|e| (Error::Io(e), String::new(), name))?;
    eprintln!("{}: goldens reseated", file.display());
    Ok(())
}

fn fmt_cmd(paths: &[PathBuf], check: bool) -> Result<(), (Error, String, String)> {
    if paths.len() == 1 && paths[0].as_os_str() == "-" {
        return fmt_stdin();
    }
    let mut targets: Vec<(PathBuf, bool)> = Vec::new();
    if paths.is_empty() {
        targets.extend(glob_pr(Path::new(".")).into_iter().map(|p| (p, false)));
    } else {
        for p in paths {
            if p.is_dir() {
                targets.extend(glob_pr(p).into_iter().map(|q| (q, false)));
            } else {
                targets.push((p.clone(), true));
            }
        }
    }
    targets.sort();
    targets.dedup();

    let mut needs_fmt = false;
    for (path, strict) in targets {
        let src = read(&path).map_err(|e| (e, String::new(), file_name(&path)))?;
        let formatted = match prism::format(&src) {
            Ok(f) => f,
            Err(e) if strict => return Err((e, src, file_name(&path))),
            Err(_) => {
                eprintln!("{}: skipped (does not parse)", path.display());
                continue;
            }
        };
        if formatted == src {
            continue;
        }
        if check {
            eprintln!("{}: not formatted", path.display());
            needs_fmt = true;
        } else {
            std::fs::write(&path, &formatted)
                .map_err(|e| (Error::Io(e), String::new(), file_name(&path)))?;
        }
    }
    if needs_fmt {
        Err((
            Error::Codegen("some files need formatting".into()),
            String::new(),
            String::new(),
        ))
    } else {
        Ok(())
    }
}

// Editor format-on-save filter: read source on stdin, write the canonical form
// to stdout. Any parse error is fatal so an editor never overwrites a buffer
// with a half-formatted result.
fn fmt_stdin() -> Result<(), (Error, String, String)> {
    let mut src = String::new();
    std::io::stdin()
        .read_to_string(&mut src)
        .map_err(|e| (Error::Io(e), String::new(), "<stdin>".into()))?;
    let formatted = prism::format(&src).map_err(|e| (e, src.clone(), "<stdin>".into()))?;
    print!("{formatted}");
    Ok(())
}

fn build_dispatch(
    mlir: bool,
    src: &str,
    roots: &[prism::Root],
    out: &Path,
    cfg: &prism::Config,
) -> Result<(), Error> {
    if mlir {
        #[cfg(feature = "mlir")]
        return prism::build_mlir_on(src, roots, out, cfg);
        #[cfg(not(feature = "mlir"))]
        {
            let _ = (roots, cfg);
            return Err(Error::Codegen(
                "rebuild with --features mlir to use the MLIR backend".into(),
            ));
        }
    }
    prism::build_on(src, roots, out, cfg)
}

fn file_name(p: &Path) -> String {
    p.to_string_lossy().into_owned()
}
