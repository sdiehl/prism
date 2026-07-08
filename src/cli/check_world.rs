//! `prism pkg check-world`: check a package universe against its committed gates.
//!
//! Type-check a package universe, run its committed gates, and report
//! digest-addressed inputs. The machine-readable report is a set of typed
//! `Serialize` structs (below); its keys are emitted in the same sorted order the
//! previous hand-built `serde_json::Map` produced, so the byte stream is unchanged.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

use serde::{Serialize, Serializer};
use serde_json::Value;

use crate::cli::docs::resolve_docs_input;
use crate::cli::lineage::verify_run_sidecar;
use crate::cli::run::{example_sources, run_example_file, ExampleStdin};
use crate::cli::{read, resolve_input, CmdResult};
use crate::error::Error;
use crate::lineage::{
    BuildLineage, BuildLineageInput, BuildRequest, RequestKind, LINEAGE_EXTENSION, LINEAGE_FORMAT,
};

const PRISM_MANIFEST: &str = "prism.toml";
const CHECK_WORLD_FORMAT: &str = "prism-check-world-v1";
const CHECK_WORLD_BACKEND: &str = "check";
const CHECK_WORLD_COMPATIBLE: &str = "compatible";
const CHECK_WORLD_INCOMPATIBLE: &str = "incompatible";
const CHECK_WORLD_SCOPE: &str = "typecheck-only";
const CHECK_WORLD_CHECK_TYPECHECK: &str = "typecheck";
const CHECK_WORLD_CHECK_DOCTESTS: &str = "doctests";
const CHECK_WORLD_CHECK_REPLAY: &str = "replay";
const CHECK_WORLD_CHECK_NATIVE: &str = "native";
const CHECK_WORLD_CHECK_PASSED: &str = "passed";
const CHECK_WORLD_CHECK_NOT_RUN: &str = "not-run";
const CHECK_WORLD_CHECK_FAILED: &str = "failed";
// Per-package gate names, used to label the human-output gates line. The JSON
// report names the same gates from the `GatesReport` struct's own field names.
const GATE_CHECK: &str = "check";
const GATE_EXAMPLE: &str = "example";
const GATE_DOCS: &str = "docs";
const GATE_USAGE: &str = "usage";
const GATE_ROOT: &str = "root";
const GATE_DEPENDENCY: &str = "dependency";
// The committed-artifact conventions a package gate looks for, each a directory
// beneath the package root.
const PACKAGE_EXAMPLES_DIR: &str = "examples";
const PACKAGE_REPLAY_DIR: &str = "replay";
const PACKAGE_DOCS_DIR: &str = "docs";
// The usage gate golden: a package may commit `usage-summary.md` at its root, the
// human-readable markdown projection of the usage summary, regenerated the way the
// tier manifest golden is (`dump usage-summary-md`). Shared with `pkg accept-usage`.
pub(crate) const PACKAGE_USAGE_SUMMARY: &str = "usage-summary.md";
pub(crate) const USAGE_SUMMARY_PHASE: &str = "usage-summary-md";
// The whole-program lowering-tier phase. The usage summary is headed by this same
// tier (both read the one canonical `effect_strategy`), so the usage gate surfaces
// it as a scalar in the report without parsing the markdown back.
const TIER_PHASE: &str = "tier";
const GIT_DIR: &str = ".git";
const TARGET_DIR: &str = "target";
const COMPILER_INPUT_ROWS: &[&str] = &["source-root", "stdlib-root", "package-root"];

// A gate outcome. Passed/NotRun/Failed are the only three values a gate reports;
// the enum replaces the `&'static str` triple so `PackageGates::failed` compares
// variants rather than string literals. It serializes to, and displays as, the
// same three strings the report has always used.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum GateStatus {
    Passed,
    NotRun,
    Failed,
}

impl GateStatus {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Passed => CHECK_WORLD_CHECK_PASSED,
            Self::NotRun => CHECK_WORLD_CHECK_NOT_RUN,
            Self::Failed => CHECK_WORLD_CHECK_FAILED,
        }
    }
}

impl fmt::Display for GateStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

// One source of truth (`as_str`) for both the human rendering and the JSON, so the
// serialized string can never drift from the displayed one.
impl Serialize for GateStatus {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_str())
    }
}

// A package's per-package check-world facts: its build lineage, the status of each
// gate, its public API surface, and (against a baseline) which public definitions
// moved. `root` and `dependency` are filled once the whole universe is known.
struct PackageReport {
    name: String,
    lineage: BuildLineage,
    gates: PackageGates,
    public_api: Vec<crate::PublicDef>,
    public_api_changes: Option<PublicApiChanges>,
}

struct PackageGates {
    check: GateStatus,
    example: GateStatus,
    doctests: GateStatus,
    replay: GateStatus,
    docs: GateStatus,
    // Report-only by default: `usage` is regenerated and its drift reported, but it
    // is excluded from `failed()`, so a drifted usage summary fails strict mode only
    // under the opt-in `--strict-usage` flag. `usage_drift` names the first differing
    // line when `usage` is `Failed`; `usage_tier` is the whole-program lowering tier
    // the summary is headed by, present whenever the summary was regenerated.
    usage: GateStatus,
    usage_drift: Option<String>,
    usage_tier: Option<String>,
    root: GateStatus,
    dependency: GateStatus,
}

impl PackageGates {
    // A gate is a hard failure only when it ran and did not pass; a not-run gate
    // (the package commits no such artifact) never fails strict mode. `usage` is
    // intentionally absent: it is report-only by default and fails strict mode only
    // under the opt-in `--strict-usage` flag, handled separately at the call site.
    fn failed(&self) -> bool {
        [
            self.check,
            self.example,
            self.doctests,
            self.replay,
            self.docs,
            self.root,
            self.dependency,
        ]
        .contains(&GateStatus::Failed)
    }
}

// The public-surface definitions that moved, were added, or were removed relative
// to a baseline report, named (never keyed on path).
#[derive(Default)]
struct PublicApiChanges {
    moved: Vec<(String, String, String)>,
    added: Vec<String>,
    removed: Vec<String>,
}

impl PublicApiChanges {
    const fn any(&self) -> bool {
        !self.moved.is_empty() || !self.added.is_empty() || !self.removed.is_empty()
    }
}

pub fn check_world_cmd(
    path: &Path,
    json_output: bool,
    strict: bool,
    strict_usage: bool,
    baseline: Option<&Path>,
    cfg: &crate::Config,
) -> CmdResult {
    let manifests = world_manifests(path)?;
    if manifests.is_empty() {
        return Err((
            Error::Resolve(format!(
                "no package projects found under `{}`",
                path.display()
            )),
            String::new(),
            path.display().to_string(),
        ));
    }
    let baseline = load_baseline(baseline)?;

    let mut reports = Vec::new();
    for manifest in manifests {
        let project = crate::project::load_project(&manifest)
            .map_err(|e| (e, String::new(), manifest.display().to_string()))?;
        let package_dir = manifest
            .parent()
            .map_or_else(|| PathBuf::from("."), Path::to_path_buf);
        let (full, roots, name, _) = resolve_input(&manifest, cfg)?;
        crate::check_on(&full, &roots).map_err(|e| (e, full.clone(), name.clone()))?;
        let lineage = BuildLineage::collect(BuildLineageInput {
            request: BuildRequest {
                kind: RequestKind::CheckWorld,
                path: manifest.display().to_string(),
                entry: project.entry.display().to_string(),
            },
            source: &full,
            roots: &roots,
            cfg,
            backend: CHECK_WORLD_BACKEND,
            artifacts: Vec::new(),
            cache: None,
            diagnostics: Vec::new(),
        })
        .map_err(|e| (e, full.clone(), name.clone()))?;
        let entry_src = read(&project.entry).unwrap_or_default();
        let public_api = crate::public_surface(&entry_src, &full, &roots).unwrap_or_default();
        let public_api_changes = baseline
            .as_ref()
            .map(|b| diff_public_api(b, &project.name, &public_api));
        let usage = usage_gate(&package_dir, &full, &roots, cfg);
        let gates = PackageGates {
            check: GateStatus::Passed,
            example: example_gate(&package_dir, cfg),
            doctests: doctest_gate(&manifest),
            replay: replay_gate(&package_dir, cfg),
            docs: docs_gate(&package_dir),
            usage: usage.status,
            usage_drift: usage.drift,
            usage_tier: usage.tier,
            // Filled from the whole-universe compatibility below.
            root: GateStatus::Passed,
            dependency: GateStatus::Passed,
        };
        reports.push(PackageReport {
            name: project.name,
            lineage,
            gates,
            public_api,
            public_api_changes,
        });
    }

    let compatibility = CheckWorldCompatibility::from_reports(&reports);
    for report in &mut reports {
        report.gates.root = compatibility.root_status(report);
        report.gates.dependency = compatibility.dependency_status(report);
    }

    let gate_failed = reports.iter().any(|report| report.gates.failed());
    // Usage stays report-only unless `--strict-usage` opts it into strict mode; then
    // a drifted (failed) summary fails strict the way the hard gates do. A missing
    // summary is never fatal: missing means the package did not opt in.
    let usage_failed = strict_usage
        && reports
            .iter()
            .any(|report| report.gates.usage == GateStatus::Failed);
    if json_output {
        println!("{}", check_world_json(path, &reports)?);
    } else {
        print_check_world_human(path, &reports);
    }
    if strict && (!compatibility.is_compatible() || gate_failed || usage_failed) {
        return Err((
            Error::Resolve("check-world found an incompatible package universe".into()),
            String::new(),
            path.display().to_string(),
        ));
    }
    Ok(())
}

// Read a prior `--json` report for the public-surface diff, or `None` when no
// baseline was given.
fn load_baseline(baseline: Option<&Path>) -> Result<Option<Value>, (Error, String, String)> {
    let Some(path) = baseline else {
        return Ok(None);
    };
    let text = read(path).map_err(|e| (e, String::new(), path.display().to_string()))?;
    let value = serde_json::from_str::<Value>(&text).map_err(|e| {
        (
            Error::Resolve(e.to_string()),
            String::new(),
            path.display().to_string(),
        )
    })?;
    Ok(Some(value))
}

// The example gate: run every program under the package's `examples/` directory
// through the compiler-owned runner. A package with no such directory is not-run.
fn example_gate(package_dir: &Path, cfg: &crate::Config) -> GateStatus {
    let dir = package_dir.join(PACKAGE_EXAMPLES_DIR);
    if !dir.is_dir() {
        return GateStatus::NotRun;
    }
    let Ok(sources) = example_sources(&dir) else {
        return GateStatus::NotRun;
    };
    for file in &sources {
        match run_example_file(file, cfg, ExampleStdin::Fixture) {
            Ok(None | Some(0)) => {}
            _ => return GateStatus::Failed,
        }
    }
    GateStatus::Passed
}

// The doctest gate: run the doctests in the package's doc comments through the docs
// machinery. A package with no doctests is not-run.
fn doctest_gate(manifest: &Path) -> GateStatus {
    let Ok((modules, roots, base, _, title)) = resolve_docs_input(manifest) else {
        return GateStatus::NotRun;
    };
    let Ok(generated) = crate::project_pages(modules, &roots, &title) else {
        return GateStatus::NotRun;
    };
    if generated.example_count() == 0 {
        return GateStatus::NotRun;
    }
    if generated.test(&roots, &base).failures.is_empty() {
        GateStatus::Passed
    } else {
        GateStatus::Failed
    }
}

// The replay gate: verify every run sidecar committed under the package's
// `replay/` directory by replaying its trace. A package with none is not-run.
fn replay_gate(package_dir: &Path, cfg: &crate::Config) -> GateStatus {
    let dir = package_dir.join(PACKAGE_REPLAY_DIR);
    if !dir.is_dir() {
        return GateStatus::NotRun;
    }
    let sidecars = lineage_sidecars_in(&dir);
    if sidecars.is_empty() {
        return GateStatus::NotRun;
    }
    for sidecar in &sidecars {
        if verify_run_sidecar(sidecar, cfg).is_err() {
            return GateStatus::Failed;
        }
    }
    GateStatus::Passed
}

// The docs-manifest gate: if the package commits a docs manifest under `docs/`,
// rehash the pages it names against the committed pages. A package with none is
// not-run. Root/compiler drift is a `prism docs --verify-manifest` concern (it
// recomputes identity from source); the world gate checks page integrity, which is
// stable across unrelated stdlib and compiler churn.
fn docs_gate(package_dir: &Path) -> GateStatus {
    let docs_dir = package_dir.join(PACKAGE_DOCS_DIR);
    let manifest_path = crate::lineage::docs_manifest_path(&docs_dir);
    if !manifest_path.is_file() {
        return GateStatus::NotRun;
    }
    let Ok(graph) = crate::lineage::read_lineage(&manifest_path) else {
        return GateStatus::Failed;
    };
    if crate::lineage::verify(&graph, &docs_dir).is_err() {
        return GateStatus::Failed;
    }
    GateStatus::Passed
}

// The outcome of the per-package usage gate: the gate status, the first differing
// line when it drifted, and the whole-program lowering tier the summary is headed by
// (present whenever the summary was regenerated, whether or not it matched).
struct UsageGate {
    status: GateStatus,
    drift: Option<String>,
    tier: Option<String>,
}

// The usage gate: if the package commits a `usage-summary.md` golden at its root,
// regenerate the markdown usage summary from source through the `dump
// usage-summary-md` machinery and compare it, line for line, against the golden. A
// package with no golden is not-run; a source that no longer regenerates is a
// failure. The comparison ignores a trailing newline, so a golden produced verbatim
// with `prism dump usage-summary-md <pkg> > usage-summary.md` matches with no
// post-processing. Report-only by default (see `PackageGates::failed`);
// `--strict-usage` promotes a drift to a strict failure at the call site.
fn usage_gate(
    package_dir: &Path,
    full: &str,
    roots: &[crate::Root],
    cfg: &crate::Config,
) -> UsageGate {
    let golden_path = package_dir.join(PACKAGE_USAGE_SUMMARY);
    let Ok(committed) = read(&golden_path) else {
        return UsageGate {
            status: GateStatus::NotRun,
            drift: None,
            tier: None,
        };
    };
    let Ok(regenerated) = crate::dump_on(USAGE_SUMMARY_PHASE, full, roots, cfg) else {
        return UsageGate {
            status: GateStatus::Failed,
            drift: Some("could not regenerate usage summary from source".to_string()),
            tier: None,
        };
    };
    let tier = crate::dump_on(TIER_PHASE, full, roots, cfg)
        .ok()
        .map(|t| t.trim().to_string());
    let committed = committed.trim_end_matches('\n');
    let regenerated = regenerated.trim_end_matches('\n');
    if committed == regenerated {
        UsageGate {
            status: GateStatus::Passed,
            drift: None,
            tier,
        }
    } else {
        UsageGate {
            status: GateStatus::Failed,
            drift: Some(first_diff_line(committed, regenerated)),
            tier,
        }
    }
}

// Name the first line at which the committed golden and the regenerated summary
// diverge (1-indexed), quoting both sides so a reader can see the drift without a
// separate diff. A pure length difference past the shorter side is named too.
fn first_diff_line(committed: &str, regenerated: &str) -> String {
    let mut old = committed.lines();
    let mut new = regenerated.lines();
    let mut line = 0usize;
    loop {
        line += 1;
        match (old.next(), new.next()) {
            (Some(a), Some(b)) if a == b => {}
            (Some(a), Some(b)) => {
                return format!("line {line}: committed {a:?} != regenerated {b:?}");
            }
            (Some(a), None) => return format!("line {line}: committed {a:?} != regenerated <eof>"),
            (None, Some(b)) => return format!("line {line}: committed <eof> != regenerated {b:?}"),
            (None, None) => return format!("differ past line {}", line - 1),
        }
    }
}

// The `.plineage` run sidecars directly under `dir`, sorted for determinism.
fn lineage_sidecars_in(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    if let Ok(entries) = fs::read_dir(dir) {
        for entry in entries.flatten() {
            let p = entry.path();
            if p.extension().and_then(OsStr::to_str) == Some(LINEAGE_EXTENSION) {
                out.push(p);
            }
        }
    }
    out.sort();
    out
}

// Diff a package's current public surface against the same package's surface in a
// baseline report, naming the definitions whose hash moved, appeared, or vanished.
fn diff_public_api(baseline: &Value, name: &str, current: &[crate::PublicDef]) -> PublicApiChanges {
    let mut prior: BTreeMap<String, String> = BTreeMap::new();
    if let Some(packages) = baseline["packages"].as_object() {
        for package in packages.values() {
            if package["name"].as_str() == Some(name) {
                if let Some(defs) = package["public_api"].as_array() {
                    for def in defs {
                        if let (Some(n), Some(h)) = (def["name"].as_str(), def["hash"].as_str()) {
                            prior.insert(n.to_string(), h.to_string());
                        }
                    }
                }
            }
        }
    }
    let mut changes = PublicApiChanges::default();
    let mut seen = BTreeSet::new();
    for def in current {
        seen.insert(def.name.clone());
        match prior.get(&def.name) {
            Some(old) if *old != def.hash => {
                changes
                    .moved
                    .push((def.name.clone(), old.clone(), def.hash.clone()));
            }
            Some(_) => {}
            None => changes.added.push(def.name.clone()),
        }
    }
    for name in prior.keys() {
        if !seen.contains(name) {
            changes.removed.push(name.clone());
        }
    }
    changes
}

fn world_manifests(path: &Path) -> Result<Vec<PathBuf>, (Error, String, String)> {
    if path.is_file() {
        if path.file_name().is_some_and(|name| name == PRISM_MANIFEST) {
            return Ok(vec![path.to_path_buf()]);
        }
        return Err((
            Error::Resolve(format!(
                "`{}` is not a package universe or prism.toml",
                path.display()
            )),
            String::new(),
            path.display().to_string(),
        ));
    }
    if path.join(PRISM_MANIFEST).is_file() {
        return Ok(vec![path.join(PRISM_MANIFEST)]);
    }

    let mut manifests = Vec::new();
    collect_world_manifests(path, &mut manifests)?;
    manifests.sort();
    Ok(manifests)
}

fn collect_world_manifests(
    dir: &Path,
    manifests: &mut Vec<PathBuf>,
) -> Result<(), (Error, String, String)> {
    let entries =
        fs::read_dir(dir).map_err(|e| (Error::Io(e), String::new(), dir.display().to_string()))?;
    for entry in entries {
        let entry = entry.map_err(|e| (Error::Io(e), String::new(), dir.display().to_string()))?;
        let path = entry.path();
        let file_name = entry.file_name();
        if file_name == OsStr::new(GIT_DIR) || file_name == OsStr::new(TARGET_DIR) {
            continue;
        }
        let file_type = entry
            .file_type()
            .map_err(|e| (Error::Io(e), String::new(), path.display().to_string()))?;
        if !file_type.is_dir() {
            continue;
        }
        let manifest = path.join(PRISM_MANIFEST);
        if manifest.is_file() {
            manifests.push(manifest);
        } else {
            collect_world_manifests(&path, manifests)?;
        }
    }
    Ok(())
}

// ---- Typed JSON report ----
//
// Every object below declares its fields in the alphabetical order the previous
// hand-built `serde_json::Map` (a `BTreeMap`) emitted them in, so the pretty output
// is byte-identical. `Option` fields that were conditionally inserted carry
// `skip_serializing_if` so an absent value is omitted exactly as before.

#[derive(Serialize)]
struct CheckWorldJson<'a> {
    compatibility: CompatibilityReport<'a>,
    format: &'static str,
    lineage_format: &'static str,
    packages: BTreeMap<String, PackageEntry<'a>>,
    root: String,
    validation: ValidationReport,
}

#[derive(Serialize)]
struct PackageEntry<'a> {
    gates: GatesReport<'a>,
    // The build lineage's own JSON object, embedded verbatim (owned by the lineage
    // subsystem); serde serializes a `Value` as-is.
    lineage: Value,
    name: &'a str,
    public_api: Vec<PublicApiRow<'a>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    public_api_changes: Option<ChangesReport<'a>>,
}

#[derive(Serialize)]
struct GatesReport<'a> {
    check: GateStatus,
    dependency: GateStatus,
    docs: GateStatus,
    doctests: GateStatus,
    example: GateStatus,
    replay: GateStatus,
    root: GateStatus,
    usage: GateStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    usage_drift: Option<&'a str>,
    // The dump phase the gate regenerates and compares through, so a report reader
    // knows which artifact format the committed golden is checked under.
    usage_format: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    usage_tier: Option<&'a str>,
}

#[derive(Serialize)]
struct PublicApiRow<'a> {
    hash: &'a str,
    name: &'a str,
    scheme: &'a str,
}

#[derive(Serialize)]
struct ChangesReport<'a> {
    added: &'a [String],
    changed: bool,
    moved: Vec<MovedRow<'a>>,
    removed: &'a [String],
}

#[derive(Serialize)]
struct MovedRow<'a> {
    name: &'a str,
    new: &'a str,
    old: &'a str,
}

#[derive(Serialize)]
struct ValidationReport {
    checks: BTreeMap<&'static str, GateStatus>,
    scope: &'static str,
}

#[derive(Serialize)]
struct CompatibilityReport<'a> {
    compiler_surfaces: &'a [String],
    dependencies_by_identity: &'a BTreeMap<String, Vec<String>>,
    dependency_root_conflicts: &'a BTreeMap<String, Vec<String>>,
    duplicate_packages: &'a BTreeMap<String, Vec<String>>,
    package_count: usize,
    packages_by_name: &'a BTreeMap<String, Vec<String>>,
    problems: &'a [String],
    stdlib_roots: &'a [String],
    unique_package_names: usize,
    verdict: &'static str,
}

impl<'a> GatesReport<'a> {
    fn of(gates: &'a PackageGates) -> Self {
        GatesReport {
            check: gates.check,
            dependency: gates.dependency,
            docs: gates.docs,
            doctests: gates.doctests,
            example: gates.example,
            replay: gates.replay,
            root: gates.root,
            usage: gates.usage,
            usage_drift: gates.usage_drift.as_deref(),
            usage_format: USAGE_SUMMARY_PHASE,
            usage_tier: gates.usage_tier.as_deref(),
        }
    }
}

fn public_api_rows(defs: &[crate::PublicDef]) -> Vec<PublicApiRow<'_>> {
    defs.iter()
        .map(|def| PublicApiRow {
            hash: &def.hash,
            name: &def.name,
            scheme: def.scheme,
        })
        .collect()
}

fn changes_report(changes: &PublicApiChanges) -> ChangesReport<'_> {
    ChangesReport {
        added: &changes.added,
        changed: changes.any(),
        moved: changes
            .moved
            .iter()
            .map(|(name, old, new)| MovedRow { name, new, old })
            .collect(),
        removed: &changes.removed,
    }
}

fn validation_report() -> ValidationReport {
    let mut checks = BTreeMap::new();
    checks.insert(CHECK_WORLD_CHECK_TYPECHECK, GateStatus::Passed);
    checks.insert(CHECK_WORLD_CHECK_DOCTESTS, GateStatus::NotRun);
    checks.insert(CHECK_WORLD_CHECK_REPLAY, GateStatus::NotRun);
    checks.insert(CHECK_WORLD_CHECK_NATIVE, GateStatus::NotRun);
    ValidationReport {
        checks,
        scope: CHECK_WORLD_SCOPE,
    }
}

fn check_world_json(
    path: &Path,
    reports: &[PackageReport],
) -> Result<String, (Error, String, String)> {
    let mut packages = BTreeMap::new();
    for report in reports {
        packages.insert(
            report.lineage.source.root.clone(),
            PackageEntry {
                gates: GatesReport::of(&report.gates),
                lineage: report.lineage.to_json(),
                name: &report.name,
                public_api: public_api_rows(&report.public_api),
                public_api_changes: report.public_api_changes.as_ref().map(changes_report),
            },
        );
    }
    let compatibility = CheckWorldCompatibility::from_reports(reports);
    let value = CheckWorldJson {
        compatibility: compatibility.to_report(),
        format: CHECK_WORLD_FORMAT,
        lineage_format: LINEAGE_FORMAT,
        packages,
        root: path.display().to_string(),
        validation: validation_report(),
    };
    serde_json::to_string_pretty(&value).map_err(|e| {
        (
            Error::Resolve(e.to_string()),
            String::new(),
            path.display().to_string(),
        )
    })
}

fn print_check_world_human(path: &Path, reports: &[PackageReport]) {
    let compatibility = CheckWorldCompatibility::from_reports(reports);
    println!("checked {} package(s) in {}", reports.len(), path.display());
    println!("validation: {CHECK_WORLD_SCOPE}");
    println!("  {CHECK_WORLD_CHECK_TYPECHECK}: {CHECK_WORLD_CHECK_PASSED}");
    println!("  {CHECK_WORLD_CHECK_DOCTESTS}: {CHECK_WORLD_CHECK_NOT_RUN}");
    println!("  {CHECK_WORLD_CHECK_REPLAY}: {CHECK_WORLD_CHECK_NOT_RUN}");
    println!("  {CHECK_WORLD_CHECK_NATIVE}: {CHECK_WORLD_CHECK_NOT_RUN}");
    println!("compatibility: {}", compatibility.verdict());
    for problem in &compatibility.problems {
        println!("  problem: {problem}");
    }
    for report in reports {
        let lineage = &report.lineage;
        println!(
            "  {}: {}:{}",
            report.name, lineage.source.scheme, lineage.source.root
        );
        let g = &report.gates;
        println!(
            "    gates: {GATE_CHECK}={} {GATE_EXAMPLE}={} {CHECK_WORLD_CHECK_DOCTESTS}={} \
             {CHECK_WORLD_CHECK_REPLAY}={} {GATE_DOCS}={} {GATE_USAGE}={} {GATE_ROOT}={} \
             {GATE_DEPENDENCY}={}",
            g.check, g.example, g.doctests, g.replay, g.docs, g.usage, g.root, g.dependency
        );
        if let Some(drift) = &g.usage_drift {
            println!("    {GATE_USAGE} drift: {drift}");
        }
        println!(
            "    stdlib: {}:{}",
            lineage.stdlib.scheme, lineage.stdlib.root
        );
        for package in &lineage.packages {
            let dep_name = package.name.as_deref().unwrap_or("<anonymous>");
            println!(
                "    package {dep_name}: {}:{}",
                package.scheme, package.root
            );
        }
        if let Some(changes) = &report.public_api_changes {
            for (name, old, new) in &changes.moved {
                println!("    public-api moved {name}: {old} -> {new}");
            }
            for name in &changes.added {
                println!("    public-api added {name}");
            }
            for name in &changes.removed {
                println!("    public-api removed {name}");
            }
        }
    }
}

#[derive(Debug)]
struct CheckWorldCompatibility {
    packages_by_name: BTreeMap<String, Vec<String>>,
    stdlib_roots: Vec<String>,
    compiler_surfaces: Vec<String>,
    dependencies_by_identity: BTreeMap<String, Vec<String>>,
    duplicate_packages: BTreeMap<String, Vec<String>>,
    dependency_root_conflicts: BTreeMap<String, Vec<String>>,
    problems: Vec<String>,
}

impl CheckWorldCompatibility {
    fn from_reports(reports: &[PackageReport]) -> Self {
        let mut packages_by_name = BTreeMap::<String, BTreeSet<String>>::new();
        let mut stdlib_roots = BTreeSet::new();
        let mut compiler_surfaces = BTreeSet::new();
        let mut dependencies_by_identity = BTreeMap::<String, BTreeSet<String>>::new();

        for report in reports {
            let lineage = &report.lineage;
            packages_by_name
                .entry(report.name.clone())
                .or_default()
                .insert(lineage.source.descriptor());
            stdlib_roots.insert(lineage.stdlib.descriptor());
            compiler_surfaces.insert(compiler_surface(&lineage.compiler));
            for package in &lineage.packages {
                dependencies_by_identity
                    .entry(package_identity(package))
                    .or_default()
                    .insert(package.descriptor());
            }
        }

        let packages_by_name = map_sets(packages_by_name);
        let dependencies_by_identity = map_sets(dependencies_by_identity);
        let duplicate_packages = conflicts(&packages_by_name);
        let dependency_root_conflicts = conflicts(&dependencies_by_identity);
        let stdlib_roots = set_values(stdlib_roots);
        let compiler_surfaces = set_values(compiler_surfaces);
        let mut problems = Vec::new();

        if stdlib_roots.len() > 1 {
            problems.push(format!(
                "package universe uses {} distinct Std roots",
                stdlib_roots.len()
            ));
        }
        if compiler_surfaces.len() > 1 {
            problems.push(format!(
                "package universe uses {} distinct compiler surfaces",
                compiler_surfaces.len()
            ));
        }
        for (name, roots) in &duplicate_packages {
            problems.push(format!(
                "package name `{name}` has {} distinct source roots",
                roots.len()
            ));
        }
        for (identity, roots) in &dependency_root_conflicts {
            problems.push(format!(
                "dependency `{identity}` resolves to {} distinct roots",
                roots.len()
            ));
        }

        Self {
            packages_by_name,
            stdlib_roots,
            compiler_surfaces,
            dependencies_by_identity,
            duplicate_packages,
            dependency_root_conflicts,
            problems,
        }
    }

    const fn verdict(&self) -> &'static str {
        if self.problems.is_empty() {
            CHECK_WORLD_COMPATIBLE
        } else {
            CHECK_WORLD_INCOMPATIBLE
        }
    }

    const fn is_compatible(&self) -> bool {
        self.problems.is_empty()
    }

    // The root gate fails when this package's own source root collides with another
    // package of the same name, or the universe disagrees on the Std root or the
    // compiler surface (a world-level drift every package shares).
    fn root_status(&self, report: &PackageReport) -> GateStatus {
        let duplicated = self.duplicate_packages.contains_key(&report.name);
        if duplicated || self.stdlib_roots.len() > 1 || self.compiler_surfaces.len() > 1 {
            GateStatus::Failed
        } else {
            GateStatus::Passed
        }
    }

    // The dependency gate fails when any dependency this package resolves also
    // resolves to a different root elsewhere in the universe.
    fn dependency_status(&self, report: &PackageReport) -> GateStatus {
        let conflicted = report.lineage.packages.iter().any(|dep| {
            self.dependency_root_conflicts
                .contains_key(&package_identity(dep))
        });
        if conflicted {
            GateStatus::Failed
        } else {
            GateStatus::Passed
        }
    }

    fn to_report(&self) -> CompatibilityReport<'_> {
        CompatibilityReport {
            compiler_surfaces: &self.compiler_surfaces,
            dependencies_by_identity: &self.dependencies_by_identity,
            dependency_root_conflicts: &self.dependency_root_conflicts,
            duplicate_packages: &self.duplicate_packages,
            package_count: self.packages_by_name.values().map(Vec::len).sum(),
            packages_by_name: &self.packages_by_name,
            problems: &self.problems,
            stdlib_roots: &self.stdlib_roots,
            unique_package_names: self.packages_by_name.len(),
            verdict: self.verdict(),
        }
    }
}

fn compiler_surface(identity: &crate::driver::ArtifactIdentity) -> String {
    identity
        .rows()
        .into_iter()
        .filter(|(key, _)| !COMPILER_INPUT_ROWS.contains(key))
        .map(|(key, value)| format!("{key}={value}"))
        .collect::<Vec<_>>()
        .join(";")
}

fn package_identity(package: &crate::lineage::LineageRoot) -> String {
    match (&package.name, &package.origin) {
        (Some(name), Some(origin)) => format!("{origin}/{name}"),
        (Some(name), None) => name.clone(),
        _ => package.descriptor(),
    }
}

fn set_values(values: BTreeSet<String>) -> Vec<String> {
    values.into_iter().collect()
}

fn map_sets(values: BTreeMap<String, BTreeSet<String>>) -> BTreeMap<String, Vec<String>> {
    values
        .into_iter()
        .map(|(key, set)| (key, set_values(set)))
        .collect()
}

fn conflicts(values: &BTreeMap<String, Vec<String>>) -> BTreeMap<String, Vec<String>> {
    values
        .iter()
        .filter(|(_, roots)| roots.len() > 1)
        .map(|(key, roots)| (key.clone(), roots.clone()))
        .collect()
}
