//! Command-line command bodies.
//!
//! The `prism` binary parses clap into the command enums and dispatches into these
//! modules; everything below the argument parsing lives here so the binary stays a
//! thin parse-and-route shell. These functions are binary-internal tooling rather
//! than a documented public library API, so the doc-completeness lints that target
//! real library surfaces are turned off for the whole module tree.
#![allow(
    clippy::missing_errors_doc,
    clippy::missing_panics_doc,
    clippy::must_use_candidate
)]

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use crate::error::Error;
use crate::pkg::lock::Lock;
use crate::store::disk::resolve_store_path;

pub mod check_world;
pub mod docs;
pub mod exec;
pub mod fmt;
pub mod lineage;
pub mod pkg;
pub mod render;
pub mod run;
pub mod store;

pub use run::ExampleStdin;

// The dispatch error tuple: the error, the source it was raised against (for a
// span-annotated render), and a display name. Every command body threads it.
pub type CmdError = (Error, String, String);
pub type CmdResult = Result<(), CmdError>;

const PRISM_MANIFEST: &str = "prism.toml";

pub fn read(file: &Path) -> Result<String, Error> {
    std::fs::read_to_string(file).map_err(Error::Io)
}

// Imports resolve relative to the entry file's directory.
pub fn base_of(file: &Path) -> PathBuf {
    file.parent()
        .filter(|p| !p.as_os_str().is_empty())
        .map_or_else(|| PathBuf::from("."), Path::to_path_buf)
}

pub fn file_name(p: &Path) -> String {
    p.to_string_lossy().into_owned()
}

pub fn render_cli_error(e: &Error, src: &str, name: &str) -> String {
    match e {
        Error::Runtime(msg) => format!("fatal: {msg}\n"),
        _ => e.render(src, name),
    }
}

// A resolved CLI input: source with prelude prepended, the module search path
// (project source root, any path dependencies, then the embedded stdlib), a
// display name for diagnostics, and the default binary name a bare build would
// write.
pub type Resolved = (String, Vec<crate::Root>, String, PathBuf);

// Resolve a CLI argument into the source to compile, the module-resolution base,
// a display name, and the default binary name a bare build would write. A
// directory or a `prism.toml` is a project: the entry comes from the manifest,
// modules resolve from the project's `src/`, and the default binary is the
// package name. A `.pr` file is a single-file program whose imports resolve
// relative to its own directory and whose default binary is its stem.
pub fn resolve_input(arg: &Path, cfg: &crate::Config) -> Result<Resolved, CmdError> {
    let is_project = arg.is_dir() || arg.file_name().is_some_and(|n| n == PRISM_MANIFEST);
    if is_project {
        let project = crate::project::load_project(arg)
            .map_err(|e| (e, String::new(), arg.display().to_string()))?;
        let src =
            read(&project.entry).map_err(|e| (e, String::new(), file_name(&project.entry)))?;
        // A project may replace the built-in prelude with its own (`[package]
        // prelude`); otherwise the built-in one is prepended as usual.
        let full = match &project.prelude {
            Some(p) => {
                let prelude = read(p).map_err(|e| (e, String::new(), file_name(p)))?;
                crate::with_custom_prelude(&prelude, &src)
            }
            None => crate::with_prelude(&src),
        };
        // A project build lands in `target/` at the package root (rustc-style),
        // keeping artifacts out of the source tree.
        let out = project.root.join("target").join(&project.name);
        let lock =
            read_lock(&project.root).map_err(|e| (e, full.clone(), file_name(&project.entry)))?;
        let store_root = resolve_store_path(cfg.flags.store_path.as_deref());
        let package_roots =
            crate::pkg::package_source_roots(&lock, &project.dependencies, &store_root, &cfg.flags)
                .map_err(|e| (e, full.clone(), file_name(&project.entry)))?;
        let std_root = crate::pkg::stdlib_source_root(&lock, &store_root)
            .map_err(|e| (e, full.clone(), file_name(&project.entry)))?;
        let roots = crate::project_roots_with_packages_and_std(
            &project.src_dir,
            &project.dep_src_dirs,
            package_roots,
            std_root,
        );
        Ok((full, roots, file_name(&project.entry), out))
    } else {
        let src = read(arg).map_err(|e| (e, String::new(), file_name(arg)))?;
        let full = crate::with_prelude(&src);
        // `factorial.pr` -> `factorial`; an extensionless arg falls back to `a.out`.
        let out = arg
            .file_stem()
            .map_or_else(|| PathBuf::from("a.out"), PathBuf::from);
        Ok((
            full,
            crate::default_roots(&base_of(arg)),
            file_name(arg),
            out,
        ))
    }
}

fn read_lock(project_root: &Path) -> Result<Lock, Error> {
    match fs::read_to_string(project_root.join("prism.lock")) {
        Ok(text) => {
            let lock = Lock::parse(&text)?;
            lock.validate_current_scheme()?;
            Ok(lock)
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(Lock::default()),
        Err(e) => Err(Error::Io(e)),
    }
}

// Compile `arg` to a native binary, the shared body of bare `prism <file>` and
// `prism build`. `out` overrides the default name (source stem for a file, the
// package name for a project).
pub fn build_input(arg: &Path, out: Option<PathBuf>, mlir: bool, cfg: &crate::Config) -> CmdResult {
    let lineage_request = project_lineage_request(arg)?;
    let (full, roots, name, default_out) = resolve_input(arg, cfg)?;
    let out = out.unwrap_or(default_out);
    // Codegen writes intermediates (`.bc`, `.ll`) beside the binary, so the
    // output directory must exist first (the default `target/` may not yet).
    if let Some(dir) = out.parent().filter(|d| !d.as_os_str().is_empty()) {
        std::fs::create_dir_all(dir).map_err(|e| (Error::Io(e), full.clone(), name.clone()))?;
    }
    // Report the modules entering the build, one per line, before compiling.
    // Best-effort: a resolution failure here is swallowed so the real build below
    // produces the authoritative diagnostic.
    if let Ok(modules) = crate::source_modules(&full, &roots) {
        for m in &modules {
            println!("  compiling {m}");
        }
    }
    let report = build_dispatch(mlir, &full, &roots, &out, cfg)
        .map_err(|e| (e, full.clone(), name.clone()))?;
    if let Some(request) = lineage_request {
        let mut artifacts = vec![("native-binary", out.clone())];
        let bitcode = out.with_extension("bc");
        if bitcode.exists() {
            artifacts.push(("llvm-bitcode", bitcode));
        }
        let lineage = crate::lineage::BuildLineage::collect(crate::lineage::BuildLineageInput {
            request,
            source: &full,
            roots: &roots,
            cfg,
            backend: crate::lineage::backend_name(mlir),
            artifacts,
            cache: report.store,
            diagnostics: Vec::new(),
        })
        .map_err(|e| (e, full.clone(), name.clone()))?;
        let sidecar = crate::lineage::write_sidecar(&out, &lineage)
            .map_err(|e| (e, full.clone(), name.clone()))?;
        println!("wrote {}", sidecar.display());
    }
    println!("wrote {}", out.display());
    Ok(())
}

fn project_lineage_request(arg: &Path) -> Result<Option<crate::lineage::BuildRequest>, CmdError> {
    let is_project = arg.is_dir() || arg.file_name().is_some_and(|n| n == PRISM_MANIFEST);
    if !is_project {
        return Ok(None);
    }
    let project = crate::project::load_project(arg)
        .map_err(|e| (e, String::new(), arg.display().to_string()))?;
    Ok(Some(crate::lineage::BuildRequest::project(
        &project.root.join("prism.toml"),
        &project.entry,
    )))
}

fn build_dispatch(
    mlir: bool,
    src: &str,
    roots: &[crate::Root],
    out: &Path,
    cfg: &crate::Config,
) -> Result<crate::NativeBuildReport, Error> {
    if mlir {
        #[cfg(feature = "mlir")]
        {
            crate::build_mlir_on(src, roots, out, cfg)?;
            return Ok(crate::NativeBuildReport::default());
        }
        #[cfg(not(feature = "mlir"))]
        {
            let _ = (roots, cfg);
            return Err(Error::Codegen(
                "rebuild with --features mlir to use the MLIR backend".into(),
            ));
        }
    }
    crate::build_on_report(src, roots, out, cfg)
}

// `prism clean`: wipe the `target/` build-artifact directory, cargo-clean style.
// In a project it is the `target/` at the package root (the nearest enclosing
// `prism.toml`); otherwise the one under `path`. A missing `target/` is success.
pub fn clean_cmd(path: &Path) -> CmdResult {
    let start = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let root = crate::project::find_manifest(&start)
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

// `prism check [FILE]`: with an explicit path, type-check exactly that file or
// project input; with no path, find the enclosing project and check its manifest
// entry. Success is quiet and reported by exit status.
pub fn check_cmd(file: Option<&Path>, cfg: &crate::Config) -> CmdResult {
    let input = if let Some(path) = file {
        path.to_path_buf()
    } else {
        let start = Path::new(".")
            .canonicalize()
            .unwrap_or_else(|_| PathBuf::from("."));
        crate::project::find_manifest(&start).ok_or_else(|| {
            (
                Error::Resolve(
                    "no prism.toml found: `prism check` without FILE checks the enclosing \
                     project; pass a `.pr` file to check a single source"
                        .into(),
                ),
                String::new(),
                start.display().to_string(),
            )
        })?
    };
    let (full, roots, name, _) = resolve_input(&input, cfg)?;
    crate::check_on_in(&full, &roots, cfg).map_err(|e| (e, full, name))?;
    Ok(())
}

// `prism dump PHASE FILE`: print one pipeline-phase artifact.
pub fn dump_cmd(phase: &str, file: &Path, cfg: &crate::Config) -> CmdResult {
    let (full, roots, name, _) = resolve_input(file, cfg)?;
    let out = crate::dump_on(phase, &full, &roots, cfg).map_err(|e| (e, full, name))?;
    println!("{out}");
    Ok(())
}

// `prism report FILE`: print every pipeline phase for a program.
pub fn report_cmd(file: &Path, cfg: &crate::Config) -> CmdResult {
    let (full, roots, _name, _) = resolve_input(file, cfg)?;
    print!("{}", crate::report_on(&full, &roots, cfg));
    Ok(())
}

// The raw user source of an export/publish input, without the prelude that
// `resolve_input` prepends: the entry file of a project, or the file itself. Kept
// separate because `export` writes this text back out and must not materialize the
// prelude into it.
pub fn user_source(arg: &Path) -> Result<String, CmdError> {
    let is_project = arg.is_dir() || arg.file_name().is_some_and(|n| n == PRISM_MANIFEST);
    if is_project {
        let project = crate::project::load_project(arg)
            .map_err(|e| (e, String::new(), arg.display().to_string()))?;
        read(&project.entry).map_err(|e| (e, String::new(), file_name(&project.entry)))
    } else {
        read(arg).map_err(|e| (e, String::new(), file_name(arg)))
    }
}

// The namespace stem/name of an input, taken from the default output name
// `resolve_input` computes (the package name for a project, the file stem for a
// single file).
pub fn out_stem(default_out: &Path) -> String {
    default_out.file_name().map_or_else(
        || "namespace".to_string(),
        |s| s.to_string_lossy().into_owned(),
    )
}

// Print a package-command summary, mapping its error into the dispatch tuple.
pub fn pkg_report(result: Result<String, Error>, arg: &str) -> CmdResult {
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

// Every `.pr` file under `root`, recursively, skipping any build artifacts in a
// `target/` directory. A bad glob pattern yields nothing rather than erroring.
pub fn glob_pr(root: &Path) -> Vec<PathBuf> {
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
