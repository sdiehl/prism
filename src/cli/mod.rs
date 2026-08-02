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
use std::time::{Duration, Instant};

use crate::driver::stable_lock;
use crate::error::Error;
use crate::pkg::lock::Lock;
use crate::project::MANIFEST as PRISM_MANIFEST;
use crate::store::disk::{resolve_store_path, Store};
use crate::syntax::reflect::parse_unit;
use crate::verify::run::VerifyOptions;

pub mod bootstrap;
pub mod check_world;
pub mod docs;
pub mod exec;
pub mod explain;
pub mod fmt;
pub mod holes;
pub mod index;
pub mod lineage;
pub mod patch;
pub mod pkg;
pub mod render;
pub mod run;
pub mod store;
pub mod test;
pub mod type_query;

pub use run::ExampleStdin;

// The dispatch error tuple: the error, the source it was raised against (for a
// span-annotated render), and a display name. Every command body threads it.
pub type CmdError = (Error, String, String);
pub type CmdResult = Result<(), CmdError>;

/// The leading relative-root component `glob` normalizes out of the paths it
/// yields, so a root spelled `./src` comes back as `src/...`.
const CURRENT_DIR: &str = ".";
const WATCH_SNAPSHOT_SCHEMA: &[u8] = b"prism-project-watch-snapshot-v1";
const WATCH_POLL_INTERVAL: Duration = Duration::from_millis(100);
const WATCH_HASH_PREFIX: usize = 12;

struct BuildObservation {
    path: PathBuf,
    report: crate::NativeBuildReport,
    modules: Option<crate::ModuleCheckReport>,
    graph: Option<crate::ModuleGraph>,
    module_time: Duration,
    pipeline_time: Duration,
    total_time: Duration,
}

#[derive(Default)]
struct WatchHistory {
    graph: Option<crate::ModuleGraph>,
    definition_hashes: Option<crate::core::Hashes>,
}

// A CLI path argument names a project when it is a directory or points directly
// at a `prism.toml`; otherwise it is a single-file program.
pub(crate) fn is_project(arg: &Path) -> bool {
    arg.is_dir() || arg.file_name().is_some_and(|n| n == PRISM_MANIFEST)
}

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
        Error::RuntimeEvaluation(msg) | Error::RuntimeReplay(msg) | Error::RuntimeDebugger(msg) => {
            format!("fatal: {msg}\n")
        }
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
    if is_project(arg) {
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
    built_input(arg, out, mlir, cfg).map(|_| ())
}

/// Compile a project, then retain the command's [`crate::CompilerSession`] and
/// rebuild whenever its source snapshot changes.
///
/// The watcher deliberately polls content rather than modification times:
/// atomic-save renames, timestamp granularity, and clocks cannot hide an edit,
/// while generated files under `target/` are excluded by [`glob_pr`]. A failed
/// build is reported and the loop stays alive so the next editor save can repair
/// it. Process termination remains the ordinary terminal interrupt.
pub fn watch_build_input(
    arg: &Path,
    out: Option<&Path>,
    mlir: bool,
    cfg: &crate::Config,
) -> CmdResult {
    let mut snapshot = watch_state(arg, cfg);
    let mut history = WatchHistory::default();
    report_watch_build(
        watch_build_once(arg, out, mlir, cfg),
        cfg.flags.verbose,
        &mut history,
    );
    eprintln!("watching {} for changes", arg.display());
    loop {
        std::thread::sleep(WATCH_POLL_INTERVAL);
        let next = watch_state(arg, cfg);
        if next == snapshot {
            continue;
        }
        snapshot = next;
        eprintln!("change detected; rebuilding");
        report_watch_build(
            watch_build_once(arg, out, mlir, cfg),
            cfg.flags.verbose,
            &mut history,
        );
    }
}

fn watch_build_once(
    arg: &Path,
    out: Option<&Path>,
    mlir: bool,
    cfg: &crate::Config,
) -> (Result<BuildObservation, CmdError>, Duration) {
    // A timing sink de-duplicates phase rows within one compile. Watch mode is
    // many compiles in one process, so each rebuild needs a fresh sink while the
    // compiler session itself remains shared and resident.
    let mut rebuild_cfg = cfg.clone();
    if cfg.timing.is_some() {
        rebuild_cfg.timing = Some(crate::TimingSink::new());
    }
    let started = Instant::now();
    let result = built_input_observed(arg, out.map(Path::to_path_buf), mlir, &rebuild_cfg, true);
    (result, started.elapsed())
}

fn report_watch_build(
    (result, failed_time): (Result<BuildObservation, CmdError>, Duration),
    verbose: bool,
    history: &mut WatchHistory,
) {
    match result {
        Ok(observation) => {
            if verbose {
                report_watch_units(&observation, history);
                report_watch_merkle(&observation, history);
                eprintln!(
                    "watch timing: modules={} pipeline={} total={} cache(linked={}, bitcode={})",
                    display_duration(observation.module_time),
                    display_duration(observation.pipeline_time),
                    display_duration(observation.total_time),
                    observation.report.cache.label(),
                    observation.report.bitcode_cache.label(),
                );
            }
            if let Some(graph) = observation.graph {
                history.graph = Some(graph);
            }
            if let Some(hashes) = observation.report.definition_hashes {
                history.definition_hashes = Some(hashes);
            }
        }
        Err((error, source, name)) => {
            eprint!("{}", render_cli_error(&error, &source, &name));
            if verbose {
                eprintln!(
                    "watch timing: failed after {}",
                    display_duration(failed_time)
                );
            }
        }
    }
}

fn report_watch_units(observation: &BuildObservation, history: &WatchHistory) {
    let decisions = observation
        .modules
        .as_ref()
        .map(|report| {
            report
                .decisions
                .iter()
                .map(|decision| (decision.module.as_str(), decision))
                .collect::<std::collections::BTreeMap<_, _>>()
        })
        .unwrap_or_default();
    let Some(current) = observation.graph.as_ref() else {
        eprintln!("watch units: graph unavailable");
        return;
    };
    let Some(previous) = history.graph.as_ref() else {
        eprintln!(
            "watch units: baseline contains {} units",
            current.nodes.len()
        );
        for node in &current.nodes {
            eprintln!(
                "  unit {} initial; {}",
                node.name,
                display_query_decision(decisions.get(node.name.as_str()).copied())
            );
        }
        return;
    };
    let Ok(mut closure) = current.invalidation_closure(previous) else {
        eprintln!("watch units: invalidation closure unavailable");
        return;
    };
    let direct = closure
        .iter()
        .filter(|item| matches!(item.cause, crate::ModuleInvalidationCause::InputChanged))
        .count();
    closure.sort_by(|left, right| {
        let left_impacted = !matches!(left.cause, crate::ModuleInvalidationCause::InputChanged);
        let right_impacted = !matches!(right.cause, crate::ModuleInvalidationCause::InputChanged);
        left_impacted
            .cmp(&right_impacted)
            .then_with(|| left.name.cmp(&right.name))
    });
    eprintln!("watch units: changed={direct} closure={}", closure.len());
    if closure.is_empty() {
        eprintln!("  no imported compilation unit changed");
        return;
    }
    for item in closure {
        let cause = match item.cause {
            crate::ModuleInvalidationCause::InputChanged => "input changed".to_string(),
            crate::ModuleInvalidationCause::DependencyChanged { dependencies } => {
                format!("impacted by {}", dependencies.join(", "))
            }
        };
        eprintln!(
            "  unit {} {cause}; {}",
            item.name,
            display_query_decision(decisions.get(item.name.as_str()).copied())
        );
    }
}

fn display_query_decision(decision: Option<&crate::driver::ModuleQueryDecision>) -> String {
    let Some(decision) = decision else {
        return "query=not reported (removed, shipped, or whole-program fallback)".to_string();
    };
    if decision.reused {
        "query=reused".to_string()
    } else {
        format!("query=recompiled ({})", decision.reasons.join("; "))
    }
}

fn report_watch_merkle(observation: &BuildObservation, history: &WatchHistory) {
    match (
        history.definition_hashes.as_ref(),
        observation.report.definition_hashes.as_ref(),
    ) {
        (Some(previous), Some(current)) => {
            let changes = definition_hash_changes(previous, current);
            eprintln!("watch merkle impact: {} definitions", changes.len());
            for change in changes {
                eprintln!("  definition {change}");
            }
        }
        (None, Some(current)) => {
            eprintln!("watch merkle baseline: {} definitions", current.len());
        }
        (Some(_), None) if observation.report.cache == crate::NativeCacheStatus::Hit => {
            eprintln!("watch merkle impact: 0 definitions (linked artifact reused)");
        }
        _ => {
            eprintln!(
                "watch merkle impact: unavailable (frontend skipped or backend has no hash report)"
            );
        }
    }
}

fn definition_hash_changes(
    previous: &crate::core::Hashes,
    current: &crate::core::Hashes,
) -> Vec<String> {
    let normalize = |hashes: &crate::core::Hashes| {
        hashes
            .iter()
            .map(|(name, digest)| (name.to_string(), digest.to_string()))
            .collect::<std::collections::BTreeMap<_, _>>()
    };
    let previous = normalize(previous);
    let current = normalize(current);
    let definitions = previous
        .keys()
        .chain(current.keys())
        .cloned()
        .collect::<std::collections::BTreeSet<_>>();
    definitions
        .into_iter()
        .filter_map(|name| match (previous.get(&name), current.get(&name)) {
            (Some(old), Some(new)) if old != new => Some(format!(
                "{name} {} -> {}",
                hash_prefix(old),
                hash_prefix(new)
            )),
            (None, Some(new)) => Some(format!("{name} added {}", hash_prefix(new))),
            (Some(old), None) => Some(format!("{name} removed {}", hash_prefix(old))),
            _ => None,
        })
        .collect()
}

fn hash_prefix(hash: &str) -> &str {
    &hash[..hash.len().min(WATCH_HASH_PREFIX)]
}

fn display_duration(duration: Duration) -> String {
    format!("{:.2}ms", duration.as_secs_f64() * 1_000.0)
}

// A probe error is itself a stable state. This matters while a manifest is
// temporarily malformed during an editor save: report one failed rebuild, wait
// quietly while the same bytes remain, and resume as soon as the project loads
// again.
fn watch_state(arg: &Path, cfg: &crate::Config) -> String {
    match watch_snapshot(arg, cfg) {
        Ok(snapshot) => format!("ok:{snapshot}"),
        Err((error, source, name)) => {
            let rendered = render_cli_error(&error, &source, &name);
            let manifest = if arg.is_dir() {
                arg.join(PRISM_MANIFEST)
            } else {
                arg.to_path_buf()
            };
            let mut hasher = blake3::Hasher::new();
            watch_field(&mut hasher, rendered.as_bytes());
            if let Ok(bytes) = fs::read(manifest) {
                watch_field(&mut hasher, &bytes);
            }
            format!("error:{}", hasher.finalize().to_hex())
        }
    }
}

fn watch_snapshot(arg: &Path, cfg: &crate::Config) -> Result<String, CmdError> {
    let project = crate::project::load_project(arg)
        .map_err(|error| (error, String::new(), arg.display().to_string()))?;
    let mut paths = vec![
        project.root.join(PRISM_MANIFEST),
        project.root.join("prism.lock"),
        project.entry,
    ];
    if let Some(prelude) = project.prelude {
        paths.push(prelude);
    }
    paths.extend(glob_pr(&project.src_dir));
    for dependency_root in &project.dep_src_dirs {
        paths.extend(glob_pr(dependency_root));
        if let Some(manifest) = crate::project::find_manifest(dependency_root) {
            paths.push(manifest);
        }
    }
    paths.sort();
    paths.dedup();

    let mut hasher = blake3::Hasher::new();
    watch_field(&mut hasher, WATCH_SNAPSHOT_SCHEMA);
    watch_field(
        &mut hasher,
        cfg.artifact_identity_for("watch").fingerprint().as_bytes(),
    );
    for path in paths {
        watch_field(&mut hasher, path.as_os_str().as_encoded_bytes());
        match fs::read(&path) {
            Ok(bytes) => {
                watch_field(&mut hasher, &[1]);
                watch_field(&mut hasher, &bytes);
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                watch_field(&mut hasher, &[0]);
            }
            Err(error) => {
                return Err((Error::Io(error), String::new(), path.display().to_string()));
            }
        }
    }
    Ok(hasher.finalize().to_hex().to_string())
}

fn watch_field(hasher: &mut blake3::Hasher, bytes: &[u8]) {
    hasher.update(&(bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

/// [`build_input`], returning the path of the binary it wrote so a caller
/// (`prism run` in a project) can execute it.
pub fn built_input(
    arg: &Path,
    out: Option<PathBuf>,
    mlir: bool,
    cfg: &crate::Config,
) -> Result<PathBuf, CmdError> {
    built_input_observed(arg, out, mlir, cfg, false).map(|observation| observation.path)
}

fn built_input_observed(
    arg: &Path,
    out: Option<PathBuf>,
    mlir: bool,
    cfg: &crate::Config,
    observe_watch: bool,
) -> Result<BuildObservation, CmdError> {
    let total_started = Instant::now();
    let lineage_request = project_lineage_request(arg)?;
    let (full, roots, name, default_out) = resolve_input(arg, cfg)?;
    let project = is_project(arg);
    // Enforce a committed stable-lock manifest beside a single source before
    // building it, the same gate `prism check` applies. Absent manifest is a
    // no-op, so an unlocked family builds unchanged.
    if !project {
        stable_lock::enforce(arg, &full, &roots).map_err(|e| (e, full.clone(), name.clone()))?;
    }
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
    let module_started = Instant::now();
    let modules = project
        .then(|| crate::check_modules_on(&full, &roots, cfg))
        .transpose()
        .map_err(|e| (e, full.clone(), name.clone()))?;
    let module_time = module_started.elapsed();
    // Building this graph requires another parse/load walk, so it is strictly
    // verbose-watch instrumentation rather than overhead on ordinary builds.
    let graph = (observe_watch && project && cfg.flags.verbose)
        .then(|| crate::module_graph(&full, &roots).ok())
        .flatten();
    let pipeline_started = Instant::now();
    let report = build_dispatch(mlir, &full, &roots, &out, cfg)
        .map_err(|e| (e, full.clone(), name.clone()))?;
    let pipeline_time = pipeline_started.elapsed();
    if cfg.flags.explain_cache {
        eprintln!(
            "compiler cache: linked={} bitcode={} reason={}",
            report.cache.label(),
            report.bitcode_cache.label(),
            report.cache_explanation()
        );
    }
    if let Some(request) = lineage_request {
        // The native binary is the durable build output and the only artifact
        // recorded here. The `.bc` intermediate is deliberately excluded:
        // codegen writes it beside the binary only on a bitcode-cache miss (a
        // warm build links from the cache and leaves no `.bc`), so recording it
        // would make the lineage graph depend on cache state rather than on the
        // inputs, breaking the determinism contract that identical inputs
        // produce identical lineage.
        let artifacts = vec![("native-binary", out.clone())];
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
    Ok(BuildObservation {
        path: out,
        report,
        modules,
        graph,
        module_time,
        pipeline_time,
        total_time: total_started.elapsed(),
    })
}

fn project_lineage_request(arg: &Path) -> Result<Option<crate::lineage::BuildRequest>, CmdError> {
    if !is_project(arg) {
        return Ok(None);
    }
    let project = crate::project::load_project(arg)
        .map_err(|e| (e, String::new(), arg.display().to_string()))?;
    Ok(Some(crate::lineage::BuildRequest::project(
        &project.root.join(PRISM_MANIFEST),
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
            return Err(Error::CodegenBackend(
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

// The input a `check` names: the explicit path, or the enclosing project's
// manifest when none is given. Shared by the plain verdict and the typed-hole
// query so both resolve a bare `prism check` the same way.
pub fn check_input(file: Option<&Path>) -> Result<PathBuf, CmdError> {
    if let Some(path) = file {
        return Ok(path.to_path_buf());
    }
    let start = Path::new(CURRENT_DIR)
        .canonicalize()
        .unwrap_or_else(|_| PathBuf::from(CURRENT_DIR));
    crate::project::find_manifest(&start).ok_or_else(|| {
        (
            Error::ResolveCommand(
                "no prism.toml found: `prism check` without FILE checks the enclosing \
                 project; pass a `.pr` file to check a single source"
                    .into(),
            ),
            String::new(),
            start.display().to_string(),
        )
    })
}

// `prism check [FILE]`: with an explicit path, type-check exactly that file or
// project input; with no path, find the enclosing project and check its manifest
// entry. Success is quiet and reported by exit status.
pub fn check_cmd(file: Option<&Path>, cfg: &crate::Config) -> CmdResult {
    let input = check_input(file)?;
    let (full, roots, name, _) = resolve_input(&input, cfg)?;
    // The warm no-op cutoff: this exact source tree, configuration, mode, and
    // stable-lock manifest already passed a warning-free validated check, so the
    // warm run returns the identical (empty) success with no parse or resolve.
    // Only warning-free passes are ever recorded, so a run that would print
    // diagnostics always re-runs; a failing check is never cached.
    let lock_manifest = (!is_project(&input))
        .then(|| std::fs::read(stable_lock::manifest_path(&input)).ok())
        .flatten();
    let verdict_cache =
        crate::driver::CheckVerdictCache::for_check(&full, &roots, lock_manifest.as_deref(), cfg)
            .map_err(|e| (e, full.clone(), name.clone()))?;
    if let Some(cache) = &verdict_cache {
        if cache.hit().map_err(|e| (e, full.clone(), name.clone()))? {
            return Ok(());
        }
    }
    // A committed stable-lock manifest beside a single source is enforced here, so
    // a locked migration whose generated behavior drifted fails the check. Absent
    // manifest is a no-op, so an unlocked family is not checked.
    if !is_project(&input) {
        stable_lock::enforce(&input, &full, &roots).map_err(|e| (e, full.clone(), name.clone()))?;
    }
    // The public verdict validates (fip / replayable / effect reconciliation),
    // so `prism check` agrees with `prism build`. The type-only surface stays
    // available to `dump` / `report` / snapshots via `check_on_in`.
    let checked =
        crate::check_validated_on_in(&full, &roots, cfg).map_err(|e| (e, full.clone(), name))?;
    if checked.warnings.is_empty() {
        if let Some(cache) = &verdict_cache {
            // Best-effort: a failed record leaves the check's verdict untouched.
            let _ = cache.record();
        }
    }
    Ok(())
}

// `prism verify FILE [--solver z3] [--solvers z3,cvc5 --require-agreement]`:
// discharge the file's function contracts through one or more external solvers,
// print honest per-function receipts, and record content-addressed evidence
// (receipts and dependency-closed certificates) in the store.
pub fn verify_cmd(
    file: &Path,
    solver: &str,
    solvers: &[String],
    require_agreement: bool,
    cfg: &crate::Config,
) -> CmdResult {
    let (full, roots, name, _) = resolve_input(file, cfg)?;
    // A verdict about a program that does not type check is meaningless, so the
    // same front-end check `dump` and `report` run gates the report: a lex, parse,
    // module, or type error is raised here and nothing is ever printed as verified.
    crate::check_on_in(&full, &roots, cfg).map_err(|e| (e, full.clone(), name.clone()))?;
    let parsed = parse_unit(&full).map_err(|e| (e, full.clone(), name.clone()))?;
    let program = crate::resolve::resolve_modules_in(parsed, &roots)
        .map_err(|e| (e, full.clone(), name.clone()))?;
    // An explicit `--solvers` list wins; otherwise the single `--solver`.
    let solver_list = if solvers.is_empty() {
        vec![solver.to_string()]
    } else {
        solvers.to_vec()
    };
    let opts = VerifyOptions {
        solvers: solver_list,
        require_agreement,
        timeout: cfg.flags.solver_timeout_ms.map(Duration::from_millis),
    };
    // Evidence rides the same content-addressed store the compiler uses; it is a
    // cache, so a store that cannot be opened just means no recorded evidence.
    let store_root = resolve_store_path(cfg.flags.store_path.as_deref());
    let store = Store::open_or_create(&store_root).ok();
    let report = crate::verify::run::run_with(&program, &opts, store.as_ref())
        .map_err(|e| (Error::from(e), full.clone(), name.clone()))?;
    print!("{}", report.render());
    if report.all_clear() {
        Ok(())
    } else {
        Err((Error::CodegenVerification(report.summary()), full, name))
    }
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
    if is_project(arg) {
        let project = crate::project::load_project(arg)
            .map_err(|e| (e, String::new(), arg.display().to_string()))?;
        read(&project.entry).map_err(|e| (e, String::new(), file_name(&project.entry)))
    } else {
        read(arg).map_err(|e| (e, String::new(), file_name(arg)))
    }
}

// The source file a patch commit is allowed to replace: the manifest entry for a
// project input, or the explicit `.pr` file itself.
pub fn user_entry_path(arg: &Path) -> Result<PathBuf, CmdError> {
    let is_project = arg.is_dir() || arg.file_name().is_some_and(|n| n == PRISM_MANIFEST);
    if is_project {
        let project = crate::project::load_project(arg)
            .map_err(|e| (e, String::new(), arg.display().to_string()))?;
        Ok(project.entry)
    } else {
        Ok(arg.to_path_buf())
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
// A returned path always begins with `root` as the caller spelled it, since
// callers strip it back off to recover a module name from what lies beneath.
pub fn glob_pr(root: &Path) -> Vec<PathBuf> {
    // `glob` drops a leading `./`, so match on the spelling it will answer with
    // and put the caller's back on. Stripping `.` alone would leave no root to
    // glob at all, so that one is used as it stands.
    let base = root
        .strip_prefix(CURRENT_DIR)
        .ok()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(root);
    let pattern = format!("{}/**/*.pr", base.display());
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
            let rel = p.strip_prefix(base).unwrap_or(p.as_path());
            !rel.components().any(|c| match c {
                std::path::Component::Normal(s) => {
                    s == "target" || s.to_str().is_some_and(|n| n.starts_with('.'))
                }
                _ => false,
            })
        })
        .map(|p| {
            p.strip_prefix(base)
                .map_or_else(|_| p.clone(), |rel| root.join(rel))
        })
        .collect()
}

#[cfg(test)]
mod glob_tests {
    use std::path::Path;

    use super::glob_pr;

    // Callers recover a module name by stripping the root back off, so a hit
    // that has lost the root's spelling silently renames every module under it.
    #[test]
    fn a_hit_keeps_the_root_spelling_it_was_asked_for() {
        let hits = glob_pr(Path::new("./tests/cases/run"));
        assert!(!hits.is_empty(), "the run corpus is not empty");
        assert!(
            hits.iter().all(|p| p.starts_with("./tests/cases/run")),
            "{hits:?}"
        );
    }
}

#[cfg(test)]
mod watch_tests {
    use std::fs;

    use super::{definition_hash_changes, watch_snapshot, PRISM_MANIFEST};

    #[test]
    fn project_watch_snapshot_tracks_existing_added_and_removed_sources() {
        let root =
            std::env::temp_dir().join(format!("prism-watch-snapshot-{}", std::process::id()));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("src")).unwrap();
        fs::write(
            root.join(PRISM_MANIFEST),
            "[package]\nname = \"watch-test\"\n\n[bin]\nentry = \"src/main.pr\"\n",
        )
        .unwrap();
        fs::write(root.join("src/main.pr"), "fn main() : Int = 1\n").unwrap();

        let config = crate::Config::default();
        let initial = watch_snapshot(&root, &config).unwrap();
        fs::write(root.join("src/main.pr"), "fn main() : Int = 2\n").unwrap();
        let edited = watch_snapshot(&root, &config).unwrap();
        assert_ne!(edited, initial);

        let added_path = root.join("src/Added.pr");
        fs::write(&added_path, "pub fn value() : Int = 3\n").unwrap();
        let added = watch_snapshot(&root, &config).unwrap();
        assert_ne!(added, edited);

        fs::remove_file(added_path).unwrap();
        assert_eq!(watch_snapshot(&root, &config).unwrap(), edited);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn definition_hash_changes_reports_merkle_cone_by_name() {
        let previous = crate::core::Hashes::from([
            ("callee".into(), "aaaaaaaaaaaaaaaa".into()),
            ("caller".into(), "bbbbbbbbbbbbbbbb".into()),
            ("removed".into(), "cccccccccccccccc".into()),
        ]);
        let current = crate::core::Hashes::from([
            ("callee".into(), "dddddddddddddddd".into()),
            ("caller".into(), "eeeeeeeeeeeeeeee".into()),
            ("added".into(), "ffffffffffffffff".into()),
        ]);

        assert_eq!(
            definition_hash_changes(&previous, &current),
            vec![
                "added added ffffffffffff",
                "callee aaaaaaaaaaaa -> dddddddddddd",
                "caller bbbbbbbbbbbb -> eeeeeeeeeeee",
                "removed removed cccccccccccc",
            ]
        );
    }
}
