//! Lineage inspection: render a sidecar, explain an output, verify one, and the
//! `prism diff` dispatch between Git project revisions, source revisions, and
//! `.plineage` sidecars.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::fmt::Write as _;
use std::fs;
use std::io::{self, IsTerminal};
use std::path::{Path, PathBuf};
use std::process::{self, Command};

use crate::cli::{base_of, resolve_input, CmdResult, PRISM_MANIFEST};
use crate::driver::{ModuleCheckReport, SOURCE_EXT};
use crate::error::Error;
use crate::lineage::{
    FactLedger, FactOutcome, FactScope, QueryFact, QueryKind, Variant, LINEAGE_EXTENSION,
    LINEAGE_FORMAT, LINEAGE_GRAPH_FORMAT,
};
use crate::parse::parse;
use crate::store::cert::CertStatus;
use crate::store::disk::{resolve_store_path, Store};
use anstyle::{AnsiColor, Color, Style};

// `prism diff` is the project-shaped default: without paths, compare Git HEAD
// to the working tree of the nearest project. `prism diff OLD NEW` remains the
// explicit form for source revisions and lineage sidecars.
pub fn diff_cmd(
    old: Option<&Path>,
    new: Option<&Path>,
    json: bool,
    cfg: &crate::Config,
) -> CmdResult {
    match (old, new) {
        (None, None) => git_project_diff_cmd(json, cfg),
        (Some(old), Some(new)) => explicit_diff_cmd(old, new, json, cfg),
        _ => Err((
            Error::ResolveLineage("`prism diff` accepts either no paths or OLD NEW".into()),
            String::new(),
            "diff".into(),
        )),
    }
}

// `prism diff OLD NEW`: one verb over two revisions or two lineage sidecars. Two
// `.plineage` sidecars diff by logical key (absorbing the old `lineage --diff`);
// two source revisions diff by Core hash. Mixing the two is a pointed error.
fn explicit_diff_cmd(old: &Path, new: &Path, json: bool, cfg: &crate::Config) -> CmdResult {
    match (is_lineage_sidecar(old), is_lineage_sidecar(new)) {
        (true, true) => lineage_diff_cmd(old, new, json),
        (false, false) => {
            let (old_full, old_roots, old_name, _) = resolve_input(old, cfg)?;
            let (new_full, new_roots, new_name, _) = resolve_input(new, cfg)?;
            if json {
                let d = crate::driver::source_diff_on_roots(
                    &old_full, &new_full, &old_roots, &new_roots, cfg,
                )
                .map_err(|e| (e, new_full, format!("{old_name} -> {new_name}")))?;
                let text = serde_json::to_string_pretty(&d).map_err(|e| {
                    (
                        Error::ResolveLineage(e.to_string()),
                        String::new(),
                        String::new(),
                    )
                })?;
                println!("{text}");
            } else {
                let out =
                    crate::driver::diff_on_roots(&old_full, &new_full, &old_roots, &new_roots, cfg)
                        .map_err(|e| (e, new_full, format!("{old_name} -> {new_name}")))?;
                print!("{out}");
            }
            Ok(())
        }
        _ => Err((
            Error::ResolveLineage(
                "`prism diff` compares two source revisions or two `.plineage` sidecars; \
                 one argument is a lineage sidecar and the other is not"
                    .into(),
            ),
            String::new(),
            format!("{} -> {}", old.display(), new.display()),
        )),
    }
}

#[derive(Debug)]
struct GitChange {
    old: Option<PathBuf>,
    new: Option<PathBuf>,
}

// `prism diff` with no paths compares the project at Git HEAD to the working
// tree. Git supplies the baseline for changed `.pr` files; all unchanged source
// files stay in memory from the working tree, which is equivalent and avoids a
// temporary checkout. Staged changes are included by diffing against HEAD.
fn git_project_diff_cmd(json: bool, cfg: &crate::Config) -> CmdResult {
    let start = Path::new(".")
        .canonicalize()
        .unwrap_or_else(|_| PathBuf::from("."));
    let manifest = crate::project::find_manifest(&start).ok_or_else(|| {
        (
            Error::ResolveLineage(
                "no prism.toml found: `prism diff` without OLD NEW diffs the enclosing project"
                    .into(),
            ),
            String::new(),
            start.display().to_string(),
        )
    })?;
    let project = crate::project::load_project(&manifest)
        .map_err(|e| (e, String::new(), manifest.display().to_string()))?;
    let changes = git_changes(&project.root)
        .map_err(|e| (e, String::new(), project.root.display().to_string()))?;
    let (new_full, new_roots, new_name, _) = resolve_input(&manifest, cfg)?;
    let old_entry = git_baseline_file(&project.root, &project.entry, &changes)
        .map_err(|e| (e, String::new(), project.entry.display().to_string()))?;
    let old_full = match &project.prelude {
        Some(path) => {
            let prelude = git_baseline_file(&project.root, path, &changes)
                .map_err(|e| (e, String::new(), path.display().to_string()))?;
            crate::with_custom_prelude(&prelude, &old_entry)
        }
        None => crate::with_prelude(&old_entry),
    };
    let mut old_roots = new_roots.clone();
    let old_modules = git_baseline_modules(&project, &changes)
        .map_err(|e| (e, old_full.clone(), project.src_dir.display().to_string()))?;
    let Some(root) = old_roots.first_mut() else {
        return Err((
            Error::InternalInvariant("a project source search path has no project root".into()),
            old_full,
            new_name,
        ));
    };
    *root = crate::Root::source_bundle(
        format!("Git HEAD ({})", project.src_dir.display()),
        old_modules,
    );

    if json {
        let diff =
            crate::driver::source_diff_on_roots(&old_full, &new_full, &old_roots, &new_roots, cfg)
                .map_err(|e| (e, new_full, new_name))?;
        let text = serde_json::to_string_pretty(&diff).map_err(|e| {
            (
                Error::ResolveLineage(e.to_string()),
                String::new(),
                String::new(),
            )
        })?;
        println!("{text}");
    } else {
        let diff =
            crate::driver::source_diff_on_roots(&old_full, &new_full, &old_roots, &new_roots, cfg)
                .map_err(|e| (e, new_full, new_name))?;
        print!("{}", crate::driver::render_source_diff(&diff));
        let surface = surface_definition_diff(&project.root, &changes, &diff)
            .map_err(|e| (e, String::new(), project.root.display().to_string()))?;
        if !surface.is_empty() {
            println!("surface:");
            print!("{surface}");
        }
    }
    Ok(())
}

// The semantic summary says what moved and its blast radius. The surface view
// then shows only those changed definitions, not a noisy file-level patch.
fn surface_definition_diff(
    root: &Path,
    changes: &[GitChange],
    diff: &crate::driver::SourceDiff,
) -> Result<String, Error> {
    let names: BTreeMap<String, String> = diff
        .behavioral
        .iter()
        .map(|change| (bare_name(&change.name), change.name.clone()))
        .chain(
            diff.added
                .iter()
                .map(|change| (bare_name(&change.name), change.name.clone())),
        )
        .chain(
            diff.removed
                .iter()
                .map(|change| (bare_name(&change.name), change.name.clone())),
        )
        .collect();
    if names.is_empty() {
        return Ok(String::new());
    }

    let mut rendered = BTreeSet::new();
    let mut out = String::new();
    for change in changes {
        let old = change
            .old
            .as_deref()
            .map(|path| git_head_file(root, path))
            .transpose()?
            .unwrap_or_default();
        let new = change
            .new
            .as_deref()
            .map(|path| fs::read_to_string(root.join(path)).map_err(Error::Io))
            .transpose()?
            .unwrap_or_default();
        let old_defs = surface_definitions(&old)?;
        let new_defs = surface_definitions(&new)?;
        for (bare, name) in &names {
            let old_def = old_defs.get(bare).map(String::as_str).unwrap_or_default();
            let new_def = new_defs.get(bare).map(String::as_str).unwrap_or_default();
            if old_def.is_empty() && new_def.is_empty() {
                continue;
            }
            if old_def != new_def && rendered.insert(name.clone()) {
                render_definition_delta(&mut out, name, old_def, new_def);
            }
        }
    }
    Ok(out)
}

fn surface_definitions(src: &str) -> Result<BTreeMap<String, String>, Error> {
    let parsed = parse(src)?;
    Ok(parsed
        .program
        .fns
        .iter()
        .filter_map(|decl| {
            src.get(decl.span.start..decl.span.end)
                .map(|text| (decl.name.clone(), text.trim().to_string()))
        })
        .collect())
}

fn bare_name(name: &str) -> String {
    name.rsplit_once('.')
        .map_or(name, |(_, tail)| tail)
        .to_string()
}

fn render_definition_delta(out: &mut String, name: &str, old: &str, new: &str) {
    writeln!(out, "  {name}").unwrap();
    for line in old.lines() {
        writeln!(out, "    {}", paint(AnsiColor::Red, '-', line)).unwrap();
    }
    for line in new.lines() {
        writeln!(out, "    {}", paint(AnsiColor::Green, '+', line)).unwrap();
    }
}

fn paint(color: AnsiColor, marker: char, line: &str) -> String {
    let text = format!("{marker} {line}");
    if io::stdout().is_terminal() {
        let style = Style::new().fg_color(Some(Color::Ansi(color)));
        format!("{}{}{}", style.render(), text, style.render_reset())
    } else {
        text
    }
}

fn git_changes(root: &Path) -> Result<Vec<GitChange>, Error> {
    let repo_root = git_repo_root(root)?;
    let project_path = root.strip_prefix(&repo_root).map_err(|_| {
        Error::ResolveLineage(format!(
            "project root `{}` is outside Git root `{}`",
            root.display(),
            repo_root.display()
        ))
    })?;
    let project_path_text = project_path.to_str().ok_or_else(|| {
        Error::ResolveLineage(format!(
            "project path `{}` is not UTF-8",
            project_path.display()
        ))
    })?;
    let pathspec = if project_path.as_os_str().is_empty() {
        "."
    } else {
        project_path_text
    };
    let output = git_output(
        &repo_root,
        vec![
            "diff",
            "HEAD",
            "--name-status",
            "-z",
            "--find-renames",
            "--",
            pathspec,
        ],
    )?;
    let fields: Vec<&[u8]> = output
        .split(|b| *b == 0)
        .filter(|field| !field.is_empty())
        .collect();
    let mut changes = Vec::new();
    let mut i = 0;
    while i < fields.len() {
        let status = std::str::from_utf8(fields[i])
            .map_err(|_| Error::ResolveLineage("Git returned a non-UTF-8 diff status".into()))?;
        i += 1;
        let renamed = status.starts_with('R') || status.starts_with('C');
        let paths = if renamed { 2 } else { 1 };
        if i + paths > fields.len() {
            return Err(Error::ResolveLineage(
                "malformed NUL-delimited Git diff output".into(),
            ));
        }
        let path = |field: &[u8]| -> Result<PathBuf, Error> {
            String::from_utf8(field.to_vec())
                .map(PathBuf::from)
                .map_err(|_| Error::ResolveLineage("Git diff path is not UTF-8".into()))
                .and_then(|path| {
                    if project_path.as_os_str().is_empty() {
                        Ok(path)
                    } else {
                        path.strip_prefix(project_path)
                            .map(Path::to_path_buf)
                            .map_err(|_| {
                                Error::ResolveLineage(format!(
                                    "Git returned `{}` outside project `{project_path_text}`",
                                    path.display()
                                ))
                            })
                    }
                })
        };
        let (old, new) = match status.chars().next() {
            Some('A') => (None, Some(path(fields[i])?)),
            Some('D') => (Some(path(fields[i])?), None),
            Some('M' | 'T') => {
                let path = path(fields[i])?;
                (Some(path.clone()), Some(path))
            }
            Some('R' | 'C') => (Some(path(fields[i])?), Some(path(fields[i + 1])?)),
            Some('U') => {
                return Err(Error::ResolveLineage(
                    "cannot diff a project with unmerged `.pr` files; resolve the Git conflict first"
                        .into(),
                ));
            }
            _ => {
                return Err(Error::ResolveLineage(format!(
                    "unsupported Git diff status `{status}`"
                )));
            }
        };
        i += paths;
        if old.as_ref().is_some_and(|path| is_pr_file(path))
            || new.as_ref().is_some_and(|path| is_pr_file(path))
        {
            changes.push(GitChange { old, new });
        }
    }
    Ok(changes)
}

fn git_baseline_file(root: &Path, path: &Path, changes: &[GitChange]) -> Result<String, Error> {
    let relative = path.strip_prefix(root).map_err(|_| {
        Error::ResolveLineage(format!(
            "project file `{}` is outside project root `{}`",
            path.display(),
            root.display()
        ))
    })?;
    for change in changes {
        if change.new.as_deref() == Some(relative) {
            return change
                .old
                .as_deref()
                .map_or_else(|| Ok(String::new()), |old| git_head_file(root, old));
        }
        if change.new.is_none() && change.old.as_deref() == Some(relative) {
            return git_head_file(root, relative);
        }
    }
    fs::read_to_string(path).map_err(Error::Io)
}

fn git_baseline_modules(
    project: &crate::project::Project,
    changes: &[GitChange],
) -> Result<BTreeMap<String, String>, Error> {
    let mut modules = project_modules(&project.src_dir)?;
    for change in changes {
        if let Some(new) = &change.new {
            if let Some(module) = source_module_path(&project.src_dir, &project.root.join(new))? {
                modules.remove(&module);
            }
        }
        if let Some(old) = &change.old {
            if let Some(module) = source_module_path(&project.src_dir, &project.root.join(old))? {
                modules.insert(module, git_head_file(&project.root, old)?);
            }
        }
    }
    Ok(modules)
}

fn project_modules(src_dir: &Path) -> Result<BTreeMap<String, String>, Error> {
    let mut modules = BTreeMap::new();
    collect_project_modules(src_dir, src_dir, &mut modules)?;
    Ok(modules)
}

fn collect_project_modules(
    src_dir: &Path,
    dir: &Path,
    modules: &mut BTreeMap<String, String>,
) -> Result<(), Error> {
    for entry in fs::read_dir(dir).map_err(Error::Io)? {
        let path = entry.map_err(Error::Io)?.path();
        if path.is_dir() {
            collect_project_modules(src_dir, &path, modules)?;
        } else if let Some(module) = source_module_path(src_dir, &path)? {
            modules.insert(module, fs::read_to_string(path).map_err(Error::Io)?);
        }
    }
    Ok(())
}

fn source_module_path(src_dir: &Path, path: &Path) -> Result<Option<String>, Error> {
    if !is_pr_file(path) || !path.starts_with(src_dir) {
        return Ok(None);
    }
    let relative = path.strip_prefix(src_dir).map_err(|_| {
        Error::InternalInvariant(format!(
            "source `{}` was accepted under `{}` but could not be relativized",
            path.display(),
            src_dir.display()
        ))
    })?;
    let stem = relative.with_extension("");
    let mut names = Vec::new();
    for component in stem.components() {
        let Some(name) = component.as_os_str().to_str() else {
            return Err(Error::ResolveLineage(format!(
                "Prism module path `{}` is not UTF-8",
                path.display()
            )));
        };
        names.push(name);
    }
    Ok(Some(names.join(".")))
}

fn is_pr_file(path: &Path) -> bool {
    path.extension().and_then(OsStr::to_str) == Some(SOURCE_EXT)
}

fn git_head_file(root: &Path, path: &Path) -> Result<String, Error> {
    let repo_root = git_repo_root(root)?;
    let project_path = root.strip_prefix(&repo_root).map_err(|_| {
        Error::ResolveLineage(format!(
            "project root `{}` is outside Git root `{}`",
            root.display(),
            repo_root.display()
        ))
    })?;
    let spec = format!(
        "HEAD:{}",
        project_path.join(path).to_string_lossy().replace('\\', "/")
    );
    let output = git_output(&repo_root, ["show", "--no-textconv", &spec])?;
    String::from_utf8(output)
        .map_err(|_| Error::ResolveLineage(format!("Git file `{}` is not UTF-8", path.display())))
}

fn git_repo_root(root: &Path) -> Result<PathBuf, Error> {
    let output = git_output(root, ["rev-parse", "--show-toplevel"])?;
    let path = String::from_utf8(output)
        .map_err(|_| Error::ResolveLineage("Git root path is not UTF-8".into()))?;
    Ok(PathBuf::from(path.trim()))
}

fn git_output<'a>(root: &Path, args: impl IntoIterator<Item = &'a str>) -> Result<Vec<u8>, Error> {
    let output = Command::new("git")
        .args(args)
        .current_dir(root)
        .output()
        .map_err(|e| Error::ResolveLineage(format!("could not run Git: {e}")))?;
    if output.status.success() {
        Ok(output.stdout)
    } else {
        Err(Error::ResolveLineage(format!(
            "Git diff failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        )))
    }
}

// A path is a lineage sidecar if it carries the `.plineage` extension or its own
// bytes declare a lineage format field. The format peek reads the path itself, not
// the sibling sidecar `read_lineage` would resolve, so a `.pr` source with a stray
// `.plineage` neighbor still diffs as source.
pub fn is_lineage_sidecar(path: &Path) -> bool {
    if path.extension().and_then(OsStr::to_str) == Some(LINEAGE_EXTENSION) {
        return true;
    }
    fs::read_to_string(path)
        .ok()
        .and_then(|text| serde_json::from_str::<serde_json::Value>(&text).ok())
        .and_then(|value| {
            value
                .get("format")
                .and_then(serde_json::Value::as_str)
                .map(str::to_owned)
        })
        .is_some_and(|format| format == LINEAGE_FORMAT || format == LINEAGE_GRAPH_FORMAT)
}

// `lineage verify SIDECAR [--certify OUT]`: rehash the recorded artifacts. A world
// timeline carries no on-disk artifacts to rehash; its ids are self-certifying
// content hashes, so verification is the structural graph invariants, and
// re-derivation (re-running the wasm) is not implemented. A `--certify` path mints a
// `lineage-verified` certificate over the sidecar digest on a clean rehash.
pub fn verify_rehash_cmd(file: &Path, certify: Option<&Path>) -> CmdResult {
    let graph = crate::lineage::read_lineage(file)
        .map_err(|e| (e, String::new(), file.display().to_string()))?;
    if graph.variant == Variant::World {
        if certify.is_some() {
            return Err((
                Error::ResolveLineage(
                    "lineage verify --certify: a world timeline verifies structurally \
                     (self-certifying ids), not by a byte rehash, so it carries no \
                     lineage-verified certificate"
                        .into(),
                ),
                String::new(),
                file.display().to_string(),
            ));
        }
        let report = crate::lineage::verify_world(&graph)
            .map_err(|e| (e, String::new(), file.display().to_string()))?;
        println!(
            "world timelines verify structurally (self-certifying ids); \
             re-derivation is not implemented"
        );
        println!(
            "  well-formed: {} law(s), {} state(s), {} fork(s)",
            report.laws, report.states, report.forks
        );
        return Ok(());
    }
    let sidecar = crate::lineage::sidecar_of(file);
    let base = sidecar.parent().unwrap_or_else(|| Path::new("."));
    let report = crate::lineage::verify(&graph, base)
        .map_err(|e| (e, String::new(), file.display().to_string()))?;
    println!(
        "lineage verified: {} file(s) rehash to the recorded digests",
        report.checked
    );
    if report.skipped > 0 {
        println!(
            "  ({} append/removal write(s) recorded but not rehashable)",
            report.skipped
        );
    }
    if let Some(out) = certify {
        let bytes = fs::read(&sidecar)
            .map_err(|e| (Error::Io(e), String::new(), sidecar.display().to_string()))?;
        let cert = crate::lineage::mint_lineage_cert(&graph, &report, &bytes);
        write_certificate(out, &cert)?;
    }
    Ok(())
}

// `prism lineage why-recompiled [FILE]`: explain each durable module-query
// decision from the persisted previous/current fact-graph diff. When the source
// files are gone, the stored graphs alone still explain the last recording.
pub fn why_recompiled_cmd(file: Option<&Path>, cfg: &crate::Config) -> CmdResult {
    let input = if let Some(path) = file {
        path.to_path_buf()
    } else {
        let start = Path::new(".")
            .canonicalize()
            .unwrap_or_else(|_| PathBuf::from("."));
        crate::project::find_manifest(&start).ok_or_else(|| {
            (
                Error::ResolveCommand(
                    "no prism.toml found: pass a `.pr` file or run inside a project".into(),
                ),
                String::new(),
                start.display().to_string(),
            )
        })?
    };
    let (full, roots, name, _) = match resolve_input(&input, cfg) {
        Ok(resolved) => resolved,
        Err(err) => {
            let offline = offline_fact_lines(&input, cfg)
                .map_err(|e| (e, String::new(), input.display().to_string()))?;
            let Some(lines) = offline else {
                return Err(err);
            };
            for line in lines {
                println!("{line}");
            }
            return Ok(());
        }
    };
    let session = cfg.session.clone().unwrap_or_default();
    let mut explain_cfg = cfg.clone();
    explain_cfg.session = Some(session.clone());
    let report = crate::check_modules_on(&full, &roots, &explain_cfg)
        .map_err(|error| (error, full.clone(), name.clone()))?;
    let fact_lines = module_fact_lines(&roots, &report, cfg)
        .map_err(|error| (error, full.clone(), name.clone()))?;
    match fact_lines {
        Some(lines) => {
            for line in lines {
                println!("{line}");
            }
        }
        // Without a durable store there is no ledger; the in-memory decisions
        // carry the same derivation for this command alone.
        None => {
            for decision in report.decisions {
                if decision.reused {
                    println!("reused {}", decision.module);
                } else {
                    println!(
                        "recompiled {}: {}",
                        decision.module,
                        decision.reasons.join("; ")
                    );
                }
            }
        }
    }
    #[cfg(feature = "native")]
    crate::driver::explain_downstream_queries(&full, &roots, &explain_cfg)
        .map_err(|error| (error, full.clone(), name.clone()))?;
    let downstream = session.decisions();
    if let Some(lines) = downstream_fact_lines(&roots, &downstream, cfg)
        .map_err(|error| (error, full.clone(), name.clone()))?
    {
        for line in lines {
            println!("{line}");
        }
    } else {
        for decision in downstream {
            if decision.reused {
                println!("reused {} {}", decision.kind.tag(), decision.identity);
            } else {
                println!(
                    "recompiled {} {}: {}",
                    decision.kind.tag(),
                    decision.identity,
                    decision.reasons.join("; ")
                );
            }
        }
    }
    Ok(())
}

// The durable store the fact ledger lives in, when the compiler cache is on.
fn fact_store(cfg: &crate::Config) -> Result<Option<Store>, Error> {
    if !cfg.flags.compiler_cache || cfg.flags.store {
        return Ok(None);
    }
    Store::open_or_create(resolve_store_path(cfg.flags.store_path.as_deref()))
        .map(Some)
        .map_err(Error::Io)
}

// One explanation line per fact, from the previous/current graph alignment.
fn fact_line(fact: &QueryFact) -> String {
    let subject = if fact.kind == QueryKind::Module {
        fact.identity.clone()
    } else {
        format!("{} {}", fact.kind.tag(), fact.identity)
    };
    if fact.outcome == FactOutcome::Hit {
        format!("reused {subject}")
    } else if fact.reasons.is_empty() {
        format!("recompiled {subject}")
    } else {
        format!("recompiled {subject}: {}", fact.reasons.join("; "))
    }
}

// Explanation lines for the module queries this command ran, read back from the
// persisted previous/current fact-graph diff. `None` when no store is enabled.
fn module_fact_lines(
    roots: &[crate::Root],
    report: &ModuleCheckReport,
    cfg: &crate::Config,
) -> Result<Option<Vec<String>>, Error> {
    let Some(store) = fact_store(cfg)? else {
        return Ok(None);
    };
    let ledger = FactLedger::load(&store, &FactScope::of_roots(roots))?;
    let touched: BTreeSet<&str> = report
        .decisions
        .iter()
        .map(|decision| decision.module.as_str())
        .collect();
    let lines = ledger
        .diff()
        .entries
        .iter()
        .filter(|entry| {
            entry.kind == QueryKind::Module && touched.contains(entry.identity.as_str())
        })
        .filter_map(|entry| entry.current.as_ref().map(fact_line))
        .collect();
    Ok(Some(lines))
}

fn downstream_fact_lines(
    roots: &[crate::Root],
    decisions: &[crate::driver::QueryDecision],
    cfg: &crate::Config,
) -> Result<Option<Vec<String>>, Error> {
    let Some(store) = fact_store(cfg)? else {
        return Ok(None);
    };
    let touched = decisions
        .iter()
        .map(|decision| (decision.kind, decision.identity.clone()))
        .collect::<BTreeSet<_>>();
    let ledger = FactLedger::load(&store, &FactScope::of_roots(roots))?;
    Ok(Some(
        ledger
            .diff()
            .entries
            .iter()
            .filter(|entry| touched.contains(&(entry.kind, entry.identity.clone())))
            .filter_map(|entry| entry.current.as_ref().map(fact_line))
            .collect(),
    ))
}

// The offline arm of `why-recompiled`: when the input file is gone, the scope's
// persisted fact graphs still explain the last recorded decisions. `None` when
// the input exists (the failure was something else), the input names a project
// manifest (its roots cannot be reconstructed without it), no store is enabled,
// or nothing was ever recorded for the scope.
fn offline_fact_lines(input: &Path, cfg: &crate::Config) -> Result<Option<Vec<String>>, Error> {
    if input.exists() || input.file_name().is_some_and(|name| name == PRISM_MANIFEST) {
        return Ok(None);
    }
    let Some(store) = fact_store(cfg)? else {
        return Ok(None);
    };
    let roots = crate::default_roots(&base_of(input));
    let ledger = FactLedger::load(&store, &FactScope::of_roots(&roots))?;
    if ledger.current.is_empty() {
        return Ok(None);
    }
    Ok(Some(
        ledger
            .diff()
            .entries
            .iter()
            .filter_map(|entry| entry.current.as_ref().map(fact_line))
            .collect(),
    ))
}

pub fn lineage_cmd(file: &Path, json: bool) -> CmdResult {
    let graph = crate::lineage::read_lineage(file)
        .map_err(|e| (e, String::new(), file.display().to_string()))?;
    if json {
        let text = graph.to_json_string().map_err(|e| {
            (
                Error::ResolveLineage(e.to_string()),
                String::new(),
                file.display().to_string(),
            )
        })?;
        println!("{text}");
    } else {
        print!("{}", crate::lineage::render_human(&graph));
    }
    Ok(())
}

// `lineage why`: explain one output by walking the sidecar backward. Pure graph
// work, so it explains an old run even after its source files have moved.
pub fn why_output_cmd(sidecar: &Path, output: &str, json: bool) -> CmdResult {
    let graph = crate::lineage::read_lineage(sidecar)
        .map_err(|e| (e, String::new(), sidecar.display().to_string()))?;
    // A world timeline is walked by state hash, not by output selector; the same
    // `why` verb serves both, dispatching on the sidecar's variant.
    if graph.variant == Variant::World {
        return why_world_cmd(sidecar, &graph, output, json);
    }
    let explanation = crate::lineage::why_output(&graph, output)
        .map_err(|e| (e, String::new(), sidecar.display().to_string()))?;
    if json {
        // The terminal and JSON renderings consume the same answer object, so they
        // cannot drift.
        let text = serde_json::to_string_pretty(&explanation).map_err(|e| {
            (
                Error::ResolveLineage(e.to_string()),
                String::new(),
                sidecar.display().to_string(),
            )
        })?;
        println!("{text}");
    } else {
        print!("{}", crate::lineage::render_explanation(&explanation));
    }
    Ok(())
}

// `lineage why <state-hash> world.plineage`: walk a world state back through its
// predecessors, the law it stepped under, and any fork points crossed. Pure graph
// work over self-certifying ids, so it explains an exported timeline offline.
fn why_world_cmd(
    sidecar: &Path,
    graph: &crate::lineage::LineageGraph,
    state: &str,
    json: bool,
) -> CmdResult {
    let explanation = crate::lineage::why_world_state(graph, state)
        .map_err(|e| (e, String::new(), sidecar.display().to_string()))?;
    if json {
        let text = serde_json::to_string_pretty(&explanation).map_err(|e| {
            (
                Error::ResolveLineage(e.to_string()),
                String::new(),
                sidecar.display().to_string(),
            )
        })?;
        println!("{text}");
    } else {
        print!("{}", crate::lineage::render_world_explanation(&explanation));
    }
    Ok(())
}

// The `.plineage` arm of `prism diff`: align two sidecars by logical key. Exits
// nonzero when anything moved, was added, or was removed, so it can gate CI; a
// clean diff exits zero. Either way it prints a one-line verdict first.
fn lineage_diff_cmd(old: &Path, new: &Path, json: bool) -> CmdResult {
    let old_graph = crate::lineage::read_lineage(old)
        .map_err(|e| (e, String::new(), old.display().to_string()))?;
    let new_graph = crate::lineage::read_lineage(new)
        .map_err(|e| (e, String::new(), new.display().to_string()))?;
    let diff = crate::lineage::diff(&old_graph, &new_graph);
    if json {
        let text = serde_json::to_string_pretty(&diff).map_err(|e| {
            (
                Error::ResolveLineage(e.to_string()),
                String::new(),
                "lineage".into(),
            )
        })?;
        println!("{text}");
    } else {
        print!("{}", crate::lineage::render_diff(&diff));
    }
    if diff.changed() {
        process::exit(1);
    }
    Ok(())
}

// `lineage verify SIDECAR --replay`: close the record/verify loop by replay. The
// program and trace are resolved from the sidecar's request and its sibling
// `.replay`; a fresh replay recomputes the trace and stdout digests, and the input
// files are rehashed from disk. Any disagreement is a named error. Shared by the
// `lineage verify` command and the check-world replay gate.
pub fn verify_run_sidecar(
    sidecar: &Path,
    cfg: &crate::Config,
) -> Result<crate::lineage::RunVerification, (Error, String, String)> {
    let path = crate::lineage::sidecar_of(sidecar);
    let graph = crate::lineage::read_lineage(&path)
        .map_err(|e| (e, String::new(), path.display().to_string()))?;
    let base = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .map_or_else(|| PathBuf::from("."), Path::to_path_buf);
    let entry = crate::lineage::run_entry(&graph)
        .map_err(|e| (e, String::new(), path.display().to_string()))?;
    let program = base.join(&entry);
    // Resolve the durable trace from the graph's own self-description (verifying its
    // digest), falling back to the sibling `.replay` only for pre-relation sidecars.
    let trace_path = crate::lineage::resolve_replay_file(&graph, &path, &base)
        .map_err(|e| (e, String::new(), path.display().to_string()))?;
    let trace_src = crate::cli::read(&trace_path).map_err(|e| {
        (
            e,
            String::new(),
            format!("{}: replay trace not found", trace_path.display()),
        )
    })?;
    let (full, roots, name, _) = resolve_input(&program, cfg)?;
    // Replay into a buffer: verification recomputes digests, it does not reproduce
    // the run's output to the terminal.
    let mut sink: Vec<u8> = Vec::new();
    let replayed = crate::replay_run_on(&full, &roots, &mut sink, &trace_src, cfg)
        .map_err(|e| (e, full, name))?;
    let digest = replayed.canonical_trace.trace_digest();
    crate::lineage::verify_run_replay(&graph, &digest, replayed.term.as_bytes(), &base)
        .map_err(|e| (e, String::new(), path.display().to_string()))
}

pub fn verify_lineage_cmd(
    sidecar: &Path,
    certify: Option<&Path>,
    cfg: &crate::Config,
) -> CmdResult {
    let verified = verify_run_sidecar(sidecar, cfg)?;
    println!(
        "lineage verify: replay matches the sidecar ({} trace event(s), {} stdout byte(s), \
         {} input file(s) rehashed)",
        verified.trace_events, verified.stdout_bytes, verified.input_files
    );
    if verified.written_files > 0 || verified.skipped_writes > 0 {
        println!(
            "  ({} written file(s) rehashed, {} append/removal write(s) skipped)",
            verified.written_files, verified.skipped_writes
        );
    }
    // Only a passed replay reaches here, so a `--certify` path mints a
    // `replay-verified` certificate over the sidecar's own digest.
    if let Some(out) = certify {
        let path = crate::lineage::sidecar_of(sidecar);
        let graph = crate::lineage::read_lineage(&path)
            .map_err(|e| (e, String::new(), path.display().to_string()))?;
        let bytes = fs::read(&path)
            .map_err(|e| (Error::Io(e), String::new(), path.display().to_string()))?;
        let cert = crate::lineage::mint_replay_cert(&graph, &verified, &bytes)
            .map_err(|e| (e, String::new(), path.display().to_string()))?;
        write_certificate(out, &cert)?;
    }
    Ok(())
}

// Write a minted certificate and name where it landed. Certificates are a few
// hundred bytes; a filesystem error is the only failure.
fn write_certificate(out: &Path, cert: &[u8]) -> CmdResult {
    fs::write(out, cert).map_err(|e| (Error::Io(e), String::new(), out.display().to_string()))?;
    println!("  certificate written to {}", out.display());
    Ok(())
}

// `lineage check-cert CERT SIDECAR`: validate a minted certificate against the
// sidecar it names. Recomputes the sidecar digest and checks the certificate's
// bindings (scheme, subject digest, claim recognition) rather than re-running the
// verification, matching the parity-certificate discipline. A tampered sidecar, a
// foreign scheme, or a corrupt certificate is a named failure with a nonzero exit;
// an unrecognized claim is recognized-but-untrusted, also nonzero, never a silent
// pass; a recognized claim whose binding holds exits zero.
pub fn check_cert_cmd(cert: &Path, sidecar: &Path) -> CmdResult {
    let cert_bytes =
        fs::read(cert).map_err(|e| (Error::Io(e), String::new(), cert.display().to_string()))?;
    let sidecar_path = crate::lineage::sidecar_of(sidecar);
    let sidecar_bytes = fs::read(&sidecar_path).map_err(|e| {
        (
            Error::Io(e),
            String::new(),
            sidecar_path.display().to_string(),
        )
    })?;
    match crate::lineage::check_cert(&cert_bytes, &sidecar_bytes) {
        CertStatus::Verified(desc) => {
            println!("certificate ok: {desc}");
            Ok(())
        }
        CertStatus::Unverifiable(desc) => {
            eprintln!("certificate untrusted: {desc}");
            process::exit(1);
        }
        CertStatus::Failed(reason) => Err((
            Error::ResolveLineage(format!("certificate check failed: {reason}")),
            String::new(),
            cert.display().to_string(),
        )),
        CertStatus::Absent => Err((
            Error::ResolveLineage("certificate check failed: no certificate bytes".into()),
            String::new(),
            cert.display().to_string(),
        )),
    }
}
