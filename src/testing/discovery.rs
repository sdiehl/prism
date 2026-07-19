//! Test discovery: enumerate project-owned modules and integration roots, check
//! their `test fn` declarations (the signature rules), assign stable logical IDs,
//! and build the deterministic descriptor set the manifest and runner consume.
//!
//! Discovery compiles each unit module as its own entry so a unit test reaches
//! its module's private declarations; each `tests/*.pr` module is compiled as a
//! package consumer, so an integration test reaches only the public API. Both go
//! through the ordinary checker under `BuildMode::Test`, which retains the test
//! supplements the production strip removes.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use crate::core::fbip::borrow_sigs;
use crate::core::{fip_annots, hash_program, Digest};
use crate::driver::BuildMode;
use crate::error::Error;
use crate::resolve::Root;

use super::check::{self, TestSignature};

/// One discovered runnable test, with everything the manifest and the runner
/// need. `diagnostic_location` is side metadata and is deliberately excluded
/// from the manifest's canonical bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TestDescriptor {
    /// Stable selectable identity: `<canonical-module>::<name>` for a unit test,
    /// `integration::<relative-module>::<name>` for an integration test.
    pub logical_id: String,
    /// The defining module identity (`<canonical-module>` or
    /// `integration::<relative-module>`).
    pub defining_module_id: String,
    /// The canonical, module-qualified definition symbol.
    pub definition_id: String,
    /// Content hash of the checked test definition's Core body.
    pub test_core_digest: String,
    /// Digest over the test's compilation dependency closure.
    pub dependency_closure_digest: String,
    /// Diagnostic-only source location (file path). Never enters canonical bytes.
    pub diagnostic_location: String,
}

/// A discovered test target ready to run: its descriptor plus the resolved
/// source and roots the runner recompiles a fresh world from.
#[derive(Clone, Debug)]
pub(crate) struct TestTarget {
    pub descriptor: TestDescriptor,
    /// The full (prelude-prepended) source of the compilation unit this test
    /// lives in.
    pub full_src: String,
    /// The module search path the unit compiles under.
    pub roots: Vec<Root>,
    /// The bare (entry-local) canonical name of the test function, used to
    /// synthesize the per-test harness entry.
    pub entry_name: String,
}

/// The whole discovered plan: every runnable target, sorted by logical ID.
#[derive(Clone, Debug)]
pub(crate) struct TestPlan {
    pub targets: Vec<TestTarget>,
}

impl TestPlan {
    /// The descriptors, in logical-ID order.
    #[must_use]
    pub(crate) fn descriptors(&self) -> Vec<TestDescriptor> {
        self.targets.iter().map(|t| t.descriptor.clone()).collect()
    }
}

/// Discover every runnable test for a project rooted at `dir`.
///
/// Enumerates all project-owned `*.pr` modules under the source root (including
/// modules unreachable from the entry point) plus every `tests/*.pr` integration
/// module.
///
/// # Errors
/// Front-end errors, an invalid test signature, or a duplicate logical ID.
pub(crate) fn discover_project(dir: &Path, cfg: &crate::Config) -> Result<TestPlan, Error> {
    let cfg = &test_config(cfg);
    let project = crate::project::load_project(dir)?;
    let roots = crate::project_roots(&project.src_dir, &project.dep_src_dirs);
    let tests_dir = project.root.join("tests");
    let mut targets = Vec::new();

    // Unit tests: every module file under the source root, compiled as its own
    // entry so private siblings are in scope. Files under `tests/` are excluded
    // here even when it nests under the source root (a `src = "."` layout), so an
    // integration module is never also discovered as a unit module.
    for file in module_files(&project.src_dir) {
        if file.starts_with(&tests_dir) {
            continue;
        }
        let module = module_name_of(&project.src_dir, &file);
        let source = crate::cli::read(&file)?;
        let full = prelude_for(&project, &source)?;
        discover_unit(&full, &roots, &module, &file, cfg, &mut targets)?;
    }

    // Integration tests: every `tests/*.pr`, compiled as a package consumer that
    // sees the project through its public API only. The project source root is on
    // the search path so `import <Module>` resolves the public surface.
    for file in module_files(&tests_dir) {
        let relative = module_name_of(&tests_dir, &file);
        let module = format!("integration::{relative}");
        let source = crate::cli::read(&file)?;
        let full = prelude_for(&project, &source)?;
        discover_unit(&full, &roots, &module, &file, cfg, &mut targets)?;
    }

    finish(targets)
}

/// Discover the tests in a single source file.
///
/// # Errors
/// Front-end errors, an invalid test signature, or a duplicate logical ID.
pub(crate) fn discover_file(file: &Path, cfg: &crate::Config) -> Result<TestPlan, Error> {
    let cfg = &test_config(cfg);
    let source = crate::cli::read(file)?;
    let full = crate::with_prelude(&source);
    let roots = crate::default_roots(&crate::cli::base_of(file));
    let module = module_stem(file);
    let mut targets = Vec::new();
    discover_unit(&full, &roots, &module, file, cfg, &mut targets)?;
    finish(targets)
}

// Check one compilation unit under test mode and append its runnable tests. One
// front-end pass yields the program (test membership + canonical names), the
// checked view (the signature rules), and the elaborated Core (per-test digests).
fn discover_unit(
    full_src: &str,
    roots: &[Root],
    module: &str,
    file: &Path,
    cfg: &crate::Config,
    out: &mut Vec<TestTarget>,
) -> Result<(), Error> {
    if let Some(name) = check::duplicate_test_name(full_src) {
        return Err(Error::ResolveCommand(format!(
            "test `{}` is declared more than once in {}",
            crate::names::bare_name(&name),
            file.display()
        )));
    }
    let (program, checked, core) = crate::driver::frontend(full_src, roots, cfg)?;
    let signatures = check::signatures_from(&program, &checked).map_err(Error::Type)?;
    if signatures.is_empty() {
        return Ok(());
    }
    let hashes = hash_program(
        &core,
        &crate::driver::hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program)),
    );
    let digests: BTreeMap<String, Digest> = hashes
        .into_iter()
        .map(|(sym, digest)| (sym.as_str().to_string(), digest))
        .collect();
    let closure = crate::core::hash_root(&digests).into_string();
    let location = file.display().to_string();
    for TestSignature { name } in signatures {
        let logical_id = format!("{module}::{}", crate::names::bare_name(&name));
        let definition_id = crate::names::private(module, crate::names::bare_name(&name));
        let test_core_digest = digests
            .get(name.as_str())
            .map(|d| d.as_str().to_string())
            .unwrap_or_default();
        out.push(TestTarget {
            descriptor: TestDescriptor {
                logical_id,
                defining_module_id: module.to_string(),
                definition_id,
                test_core_digest,
                dependency_closure_digest: closure.clone(),
                diagnostic_location: location.clone(),
            },
            full_src: full_src.to_string(),
            roots: roots.to_vec(),
            entry_name: name,
        });
    }
    Ok(())
}

// Sort by logical ID and reject a duplicate deterministically (the first
// colliding pair, in sorted order).
fn finish(mut targets: Vec<TestTarget>) -> Result<TestPlan, Error> {
    targets.sort_by(|a, b| a.descriptor.logical_id.cmp(&b.descriptor.logical_id));
    for pair in targets.windows(2) {
        if pair[0].descriptor.logical_id == pair[1].descriptor.logical_id {
            return Err(Error::ResolveCommand(format!(
                "duplicate test id `{}`",
                pair[0].descriptor.logical_id
            )));
        }
    }
    Ok(TestPlan { targets })
}

/// A test-mode config derived from `cfg`: `BuildMode::Test` (so test declarations
/// survive), warnings quieted (the non-resumable `fail` handler emits a perf note
/// that must never reach a reporter's stream), and a shared compiler session so
/// the prelude and each module compile once and every later per-test harness
/// compile hits the cache. Built once per command and threaded through discovery
/// and execution.
pub(crate) fn test_config(cfg: &crate::Config) -> crate::Config {
    let mut cfg = cfg.clone();
    cfg.mode = BuildMode::Test;
    cfg.flags.quiet = true;
    if cfg.session.is_none() {
        cfg.session = Some(crate::CompilerSession::new());
    }
    cfg
}

fn prelude_for(project: &crate::project::Project, source: &str) -> Result<String, Error> {
    match &project.prelude {
        Some(path) => {
            let prelude = crate::cli::read(path)?;
            Ok(crate::with_custom_prelude(&prelude, source))
        }
        None => Ok(crate::with_prelude(source)),
    }
}

// Every `*.pr` under `dir`, sorted, excluding build output and hidden
// directories (mirrors the CLI's project glob). A missing directory yields none.
fn module_files(dir: &Path) -> Vec<PathBuf> {
    if !dir.is_dir() {
        return Vec::new();
    }
    let mut files = crate::cli::glob_pr(dir);
    files.sort();
    files
}

// The dotted module name of a file relative to a base directory: `src/Foo/Bar.pr`
// under `src` is `Foo.Bar`.
fn module_name_of(base: &Path, file: &Path) -> String {
    let relative = file.strip_prefix(base).unwrap_or(file);
    let mut parts: Vec<String> = relative
        .components()
        .filter_map(|c| match c {
            std::path::Component::Normal(s) => s.to_str().map(ToString::to_string),
            _ => None,
        })
        .collect();
    if let Some(last) = parts.last_mut() {
        if let Some(stem) = Path::new(last).file_stem().and_then(|s| s.to_str()) {
            *last = stem.to_string();
        }
    }
    parts.join(".")
}

fn module_stem(file: &Path) -> String {
    file.file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("<file>")
        .to_string()
}
