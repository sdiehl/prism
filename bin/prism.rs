#![allow(clippy::multiple_crate_versions)]

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use prism::error::Error;

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
    /// the project's package name)
    #[arg(short, long)]
    out: Option<PathBuf>,
    /// Lower through the MLIR backend instead of the textual LLVM emitter
    #[arg(long)]
    mlir: bool,
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
        /// Output path for the compiled binary (default: the project's package name)
        #[arg(short, long)]
        out: Option<PathBuf>,
        /// Lower through the MLIR backend instead of the textual LLVM emitter
        #[arg(long)]
        mlir: bool,
    },
    /// Type-check and print inferred signatures and effects
    Check { file: PathBuf },
    /// Print one pipeline artifact: tokens, ast, types, core, fbip, lowered, llvm, mlir
    Dump { phase: String, file: PathBuf },
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
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    let result = match (cli.cmd, cli.file) {
        (Some(cmd), _) => dispatch(cmd),
        // Bare `prism <path>` compiles to a native binary (rustc-style: the
        // output is named after the source); with no path, the REPL opens.
        (None, Some(file)) => build_input(&file, cli.out, cli.mlir),
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

// A resolved CLI input: source with prelude prepended, the module-resolution
// base, a display name for diagnostics, and the default binary name a bare build
// would write.
type Resolved = (String, PathBuf, String, PathBuf);

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
        let out = PathBuf::from(&project.name);
        Ok((full, project.src_dir, file_name(&project.entry), out))
    } else {
        let src = read(arg).map_err(|e| (e, String::new(), file_name(arg)))?;
        let full = prism::with_prelude(&src);
        // `factorial.pr` -> `factorial`; an extensionless arg falls back to `a.out`.
        let out = arg
            .file_stem()
            .map_or_else(|| PathBuf::from("a.out"), PathBuf::from);
        Ok((full, base_of(arg), file_name(arg), out))
    }
}

// Compile `arg` to a native binary, the shared body of bare `prism <file>` and
// `prism build`. `out` overrides the default name (source stem for a file, the
// package name for a project).
fn build_input(
    arg: &Path,
    out: Option<PathBuf>,
    mlir: bool,
) -> Result<(), (Error, String, String)> {
    let (full, base, name, default_out) = resolve_input(arg)?;
    let out = out.unwrap_or(default_out);
    build_dispatch(mlir, &full, &base, &out).map_err(|e| (e, full, name))?;
    println!("wrote {}", out.display());
    Ok(())
}

fn dispatch(cmd: Cmd) -> Result<(), (Error, String, String)> {
    match cmd {
        Cmd::Run { file } => {
            let (full, base, name, _) = resolve_input(&file)?;
            // Stream `print` to the terminal and read from real stdin so the CLI
            // behaves like a normal program. `exit(n)` maps to a real process
            // exit with that code, skipping the `=> value` trailer.
            let stdout = std::io::stdout();
            let stdin = std::io::stdin();
            let mut out = stdout.lock();
            let mut input = stdin.lock();
            let run = prism::interpret_io_at(&full, &base, &mut out, &mut input)
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
            build_input(&manifest, out, mlir)
        }
        Cmd::Check { file } => {
            let (full, base, name, _) = resolve_input(&file)?;
            let checked = prism::check_at(&full, &base).map_err(|e| (e, full, name))?;
            for d in &checked.decls {
                println!("{} : {}", d.name, d.ty.show());
            }
            Ok(())
        }
        Cmd::Dump { phase, file } => {
            let (full, base, name, _) = resolve_input(&file)?;
            let out = prism::dump_at(&phase, &full, &base).map_err(|e| (e, full, name))?;
            println!("{out}");
            Ok(())
        }
        Cmd::Report { file } => {
            let (full, base, _name, _) = resolve_input(&file)?;
            print!("{}", prism::report_at(&full, &base));
            Ok(())
        }
        Cmd::Repl { no_banner } => {
            prism::repl::repl(!no_banner);
            Ok(())
        }
        Cmd::Fmt { files, check } => fmt_cmd(&files, check),
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
        .filter(|p| !p.components().any(|c| c.as_os_str() == "target"))
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
    use std::io::Read as _;
    let mut src = String::new();
    std::io::stdin()
        .read_to_string(&mut src)
        .map_err(|e| (Error::Io(e), String::new(), "<stdin>".into()))?;
    let formatted = prism::format(&src).map_err(|e| (e, src.clone(), "<stdin>".into()))?;
    print!("{formatted}");
    Ok(())
}

fn build_dispatch(mlir: bool, src: &str, base: &Path, out: &Path) -> Result<(), Error> {
    if mlir {
        #[cfg(feature = "mlir")]
        return prism::build_mlir_at(src, base, out);
        #[cfg(not(feature = "mlir"))]
        {
            let _ = base;
            return Err(Error::Codegen(
                "rebuild with --features mlir to use the MLIR backend".into(),
            ));
        }
    }
    prism::build_at(src, base, out)
}

fn file_name(p: &Path) -> String {
    p.to_string_lossy().into_owned()
}
