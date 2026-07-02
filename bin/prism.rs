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
    /// A `.pr` file to compile to a native binary named after it (a directory or
    /// `prism.toml` compiles the whole project). With no path the REPL starts.
    /// Override the output with `-o`; interpret instead with `prism run`.
    file: Option<PathBuf>,
    /// Output path for the compiled binary (default: the source file's stem, or
    /// `target/<package name>` for a project)
    #[arg(short, long)]
    out: Option<PathBuf>,
    /// Lower through the MLIR backend instead of the textual LLVM emitter
    #[arg(long)]
    mlir: bool,
    /// Optimization level: `-O0` none (representation only), `-O1` (default)
    /// dictionary specialization, `-O2` all of `-O1` (room for more). Bare `-O`
    /// is the highest. Applies to building, running, and `dump core`.
    #[arg(
        short = 'O',
        long = "opt",
        value_name = "LEVEL",
        global = true,
        num_args = 0..=1,
        default_missing_value = "2"
    )]
    opt: Option<String>,
    /// Run an explicit ordered pass list, overriding `-O` (mutually exclusive
    /// with it). Syntax `[pre:<names>][;late:<names>]`, names comma-separated;
    /// a bare list is the pre stage. Pre passes: `EraseNewtypes`, `Specialize`;
    /// late pass: `Simplify`. Example:
    /// `--passes 'pre:EraseNewtypes,Specialize;late:Simplify'`.
    #[arg(long = "passes", value_name = "SPEC", global = true)]
    passes: Option<String>,
    /// LLVM-backend optimization level handed to the C compiler as `-O<LEVEL>`:
    /// `0`, `1`, `2` (default), `3`, or `s`/`z` for size. This tunes clang's own
    /// pipeline over the emitted bitcode and is distinct from `-O`, which tunes
    /// Prism's Core optimizer. Also settable via `PRISM_BACKEND_OPT`. Pick the
    /// compiler with `PRISM_CC` (default `clang`) and pass it arbitrary extra
    /// flags with `PRISM_CC_FLAGS` (e.g. `-march=native`, `-g`).
    #[arg(long = "backend-opt", value_name = "LEVEL", global = true)]
    backend_opt: Option<String>,
    /// Which cooperative scheduler the policy-neutral `run_cooperative` entry binds
    /// to: `cooperative` (FIFO round-robin, the default) or `lifo` (depth-first).
    /// Only `run_cooperative` is retargeted; `run_async`/`run_lifo` name a concrete
    /// policy and are never rewritten, so this picks the default wrap, never the
    /// semantics. Also settable via `PRISM_SCHEDULER`.
    #[arg(long = "scheduler", value_name = "POLICY", global = true)]
    scheduler: Option<String>,
    /// Turn off the newtype-erasure pass everywhere in the pipeline (composes
    /// with both `-O` and `--passes`). Both backends rely on it; disabling it is
    /// your choice.
    #[arg(long, global = true)]
    no_erase_newtypes: bool,
    /// Turn off the dictionary-specialization pass everywhere in the pipeline
    /// (the flag form of `PRISM_NO_SPECIALIZE`).
    #[arg(long, global = true)]
    no_specialize: bool,
    /// Turn off the gentle simplifier pass everywhere in the pipeline.
    #[arg(long, global = true)]
    no_simplify: bool,
    /// Turn off the inliner pass everywhere in the pipeline.
    #[arg(long, global = true)]
    no_inline: bool,
    /// Turn off the scalar-CSE pass everywhere in the pipeline.
    #[arg(long, global = true)]
    no_cse: bool,
    /// Drop the constant-stack native effect driver, forcing eligible handlers
    /// onto the mutually-recursive thunk driver (the flag form of
    /// `PRISM_NATIVE_EFFECTS=0`). Default on.
    #[arg(long, global = true)]
    no_native_effects: bool,
    /// Drop the whole-program free-monad trampoline (the flag form of
    /// `PRISM_TRAMPOLINE=0`). Default on.
    #[arg(long, global = true)]
    no_trampoline: bool,
    /// Run Core Lint between optimization passes, aborting on ill-formed Core (the
    /// flag form of `PRISM_CORE_LINT`).
    #[arg(long, global = true)]
    core_lint: bool,
    /// Dump per-pass rewrite tick counts to stderr (the flag form of
    /// `PRISM_OPT_STATS`).
    #[arg(long, global = true)]
    opt_stats: bool,
    /// Dump Core after each optimization pass to SINK: `stdout`, `stderr`, or a
    /// base directory (the flag form of `PRISM_DUMP_CORE`).
    #[arg(long = "dump-core", value_name = "SINK", global = true)]
    dump_core: Option<String>,
}

#[derive(Subcommand, Debug)]
enum Cmd {
    /// Type-check and run a program in the interpreter
    Run { file: PathBuf },
    /// Compile the enclosing project (the nearest `prism.toml`) to a native
    /// executable; fails outside a project. Compile a single file with
    /// `prism <file.pr>`.
    Build {
        /// Where to start the search for the project's `prism.toml` (default: the
        /// current directory)
        #[arg(default_value = ".")]
        path: PathBuf,
        /// Output path for the compiled binary (default: `target/<package name>`)
        #[arg(short, long)]
        out: Option<PathBuf>,
        /// Lower through the MLIR backend instead of the textual LLVM emitter
        #[arg(long)]
        mlir: bool,
    },
    /// Remove the build-artifact directory (`target/`). In a project it is the
    /// one at the package root; otherwise the one under the given path.
    Clean {
        /// Where to start the search for the project's `prism.toml` (default: the
        /// current directory)
        #[arg(default_value = ".")]
        path: PathBuf,
    },
    /// Type-check and print inferred signatures and effects
    Check { file: PathBuf },
    /// Print one pipeline artifact: tokens, ast, types, core, core-json, core-hash,
    /// shape, dupes, namespace, stdlib-hash, fbip, lowered, llvm, mlir
    Dump { phase: String, file: PathBuf },
    /// Query the definition dependency graph: `callers` (direct), `dependents`
    /// (the transitive closure a change would affect), `deps` (transitive
    /// dependencies), or `uses-type` (definitions whose type mentions a type)
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
    /// Format source files in place; with no path, every `.pr` file under the
    /// current directory is formatted recursively; `-` filters stdin to stdout
    Fmt {
        /// Files or directories to format; `-` for stdin, default current dir
        files: Vec<PathBuf>,
        /// Check only: exit 1 if any file is not canonical, write nothing
        #[arg(long)]
        check: bool,
    },
    /// Generate Markdown API docs (one page per module) from `-- |` doc
    /// comments, with signatures taken from the typechecker
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
        /// Check only: exit 1 if any committed page is out of date, write nothing
        #[arg(long)]
        check: bool,
        /// Open the generated index after writing
        #[arg(long)]
        open: bool,
    },
    /// mdbook preprocessor: classify and live-check `prism` code blocks. Invoked
    /// by mdbook via `[preprocessor.prism]`, not directly.
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
        Cmd::Run { file } => {
            let (full, roots, name, _) = resolve_input(&file)?;
            // Stream `print` to the terminal and read from real stdin so the CLI
            // behaves like a normal program. `exit(n)` maps to a real process
            // exit with that code, skipping the `=> value` trailer.
            let stdout = std::io::stdout();
            let stdin = std::io::stdin();
            let mut out = stdout.lock();
            let mut input = stdin.lock();
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
        Cmd::Docs {
            path,
            out,
            stdlib,
            test,
            check,
            open,
        } => docs_cmd(&path, out, stdlib, test, check, open),
        Cmd::Mdbook { rest } => mdbook_cmd(&rest),
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
    check: bool,
    open: bool,
) -> Result<(), (Error, String, String)> {
    let (generated, roots, base, default_out) = if stdlib {
        let g = prism::stdlib_pages().map_err(|e| (e, String::new(), "<stdlib>".into()))?;
        (
            g,
            prism::default_roots(Path::new(".")),
            PathBuf::from("."),
            PathBuf::from("target").join("docs"),
        )
    } else {
        let (modules, roots, base, default_out, title) = resolve_docs_input(path)?;
        let g = prism::project_pages(modules, &roots, &title)
            .map_err(|e| (e, String::new(), file_name(path)))?;
        (g, roots, base, default_out)
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
        return if report.failures.is_empty() {
            Ok(())
        } else {
            Err((
                Error::Codegen("doctest failures".into()),
                String::new(),
                String::new(),
            ))
        };
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
    }
    println!("wrote {} pages to {}", generated.pages.len(), dir.display());
    if open {
        open_path(&dir.join("index.md"));
    }
    Ok(())
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
