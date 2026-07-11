//! `prism docs` and the mdbook preprocessor: generate Markdown API docs from doc
//! comments, run doctests, and verify committed docs manifests.

use std::io::Read as _;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::cli::{base_of, file_name, glob_pr, read, resolve_input, CmdResult};
use crate::error::Error;

const DOCS_BACKEND: &str = "docs";

// The mdbook preprocessor entry point. `prism mdbook supports <renderer>` exits 0
// (every renderer is supported); otherwise the `[context, book]` JSON arrives on
// stdin and the rewritten book JSON is written to stdout. Failures (a block that
// should type-check but does not) print to stderr, and `PRISM_MDBOOK_STRICT` makes
// them fail the build.
pub fn mdbook_cmd(args: &[String]) -> CmdResult {
    if args.first().map(String::as_str) == Some("supports") {
        return Ok(());
    }
    let mut input = String::new();
    std::io::stdin()
        .read_to_string(&mut input)
        .map_err(|e| (Error::Io(e), String::new(), "<stdin>".into()))?;
    let (book, warnings) =
        crate::preprocess_book(&input).map_err(|e| (e, String::new(), "<mdbook>".into()))?;
    for w in &warnings {
        eprintln!("prism mdbook: {w}");
    }
    print!("{book}");
    if !warnings.is_empty() && std::env::var_os("PRISM_MDBOOK_STRICT").is_some() {
        return Err((
            Error::CodegenDocs(format!(
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
    Vec<crate::ModuleSource>,
    Vec<crate::Root>,
    PathBuf,
    PathBuf,
    String,
);

// `prism docs [PATH] [--out DIR] [--stdlib] [--test] [--check] [--open]`.
// Documents the project/dir/file at PATH (or the embedded stdlib with `--stdlib`)
// as one Markdown page per module. `--test` runs the doctests instead of writing;
// `--check` verifies committed pages are current (the `fmt --check` contract);
// otherwise the pages are written under DIR (default `<project>/target/docs`).
#[allow(clippy::fn_params_excessive_bools, clippy::too_many_arguments)]
pub fn docs_cmd(
    path: &Path,
    out: Option<PathBuf>,
    stdlib: bool,
    test: bool,
    accept: bool,
    check: bool,
    verify_manifest: bool,
    open: bool,
    cfg: &crate::Config,
) -> CmdResult {
    // `--accept` (`--bless`) rewrites the inline `output` expectation blocks, so
    // it always runs the doctests.
    let test = test || accept;
    let (generated, roots, base, default_out, expect_files) = if stdlib {
        let g = crate::stdlib_pages().map_err(|e| (e, String::new(), "<stdlib>".into()))?;
        (
            g,
            crate::default_roots(Path::new(".")),
            PathBuf::from("."),
            PathBuf::from("target").join("docs"),
            crate::stdlib_expect_files(),
        )
    } else {
        let (modules, roots, base, default_out, title) = resolve_docs_input(path)?;
        let files = crate::project_expect_files(&modules, &base);
        let g = crate::project_pages(modules, &roots, &title)
            .map_err(|e| (e, String::new(), file_name(path)))?;
        (g, roots, base, default_out, files)
    };

    // The identity a manifest records: the same source root and search path the build
    // and check-world use for this project/file (the stdlib book path carries no
    // package identity, so it emits no manifest). Best-effort: a bare directory
    // that is not a package has no build identity, so it simply gets no manifest.
    let manifest_identity = if stdlib {
        None
    } else {
        resolve_input(path, cfg)
            .ok()
            .map(|(full, id_roots, _, _)| (full, id_roots))
    };

    if verify_manifest {
        let dir = out.unwrap_or(default_out);
        return verify_docs_manifest_cmd(path, &dir, manifest_identity.as_ref(), cfg);
    }

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
        let expect = crate::accept(&expect_files, &roots, &base, accept);
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
                Error::CodegenDocs("docs are out of date; run `prism docs`".into()),
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
    if let Some((full, id_roots)) = &manifest_identity {
        let manifest = write_docs_manifest_for(path, &generated, full, id_roots, &base, &dir, cfg)?;
        println!("  {}", manifest.display());
    }
    if open {
        open_path(&dir.join("index.md"));
    }
    Ok(())
}

// Build and write the docs manifest beside the generated pages: the same source
// and search-path identity the build carries, the pages' digests, and the output
// of every doctest that ran. `prism docs` is the one manifest writer.
fn write_docs_manifest_for(
    path: &Path,
    generated: &crate::Generated,
    full: &str,
    id_roots: &[crate::Root],
    base: &Path,
    dir: &Path,
    cfg: &crate::Config,
) -> Result<PathBuf, (Error, String, String)> {
    let pages = generated
        .pages
        .iter()
        .map(|page| crate::lineage::DocsPageInput {
            path: format!("{}.md", page.slug),
            bytes: page.markdown.clone().into_bytes(),
        })
        .collect();
    let doctests = generated
        .ran_doctests(id_roots, base)
        .into_iter()
        .map(|(location, output)| crate::lineage::DoctestInput { location, output })
        .collect();
    let docs = crate::lineage::DocsLineage::collect(crate::lineage::DocsLineageInput {
        request: crate::lineage::BuildRequest::docs(path, path),
        source: full,
        roots: id_roots,
        cfg,
        backend: DOCS_BACKEND,
        pages,
        doctests,
    })
    .map_err(|e| (e, String::new(), path.display().to_string()))?;
    crate::lineage::write_docs_manifest(dir, &docs)
        .map_err(|e| (e, String::new(), dir.display().to_string()))
}

// Verify a committed docs manifest: rehash the pages it names against the output
// directory, then confirm the roots it recorded still match the current source.
fn verify_docs_manifest_cmd(
    path: &Path,
    dir: &Path,
    identity: Option<&(String, Vec<crate::Root>)>,
    cfg: &crate::Config,
) -> CmdResult {
    let manifest = crate::lineage::docs_manifest_path(dir);
    let graph = crate::lineage::read_lineage(&manifest)
        .map_err(|e| (e, String::new(), manifest.display().to_string()))?;
    let report = crate::lineage::verify(&graph, dir)
        .map_err(|e| (e, String::new(), manifest.display().to_string()))?;
    if let Some((full, id_roots)) = identity {
        crate::lineage::verify_manifest_identity(&graph, full, id_roots, cfg, DOCS_BACKEND)
            .map_err(|e| (e, String::new(), path.display().to_string()))?;
    }
    println!(
        "docs manifest ok: {} page(s) verified in {}",
        report.checked,
        dir.display()
    );
    Ok(())
}

// Report an expect pass loudly (like `just snap`) and turn it into an exit code.
// In accept mode a rewrite is a nonzero exit so CI can never silently bless; in
// check mode a mismatch or run failure is nonzero. `doctests_ok` folds in the
// ordinary compile/run doctest result.
fn expect_result(doctests_ok: bool, accept: bool, expect: &crate::ExpectReport) -> CmdResult {
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
            Error::CodegenDocs("doctest failures".into()),
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
pub(crate) fn resolve_docs_input(path: &Path) -> Result<DocsInput, (Error, String, String)> {
    let manifest = if path.file_name().is_some_and(|n| n == "prism.toml") {
        Some(path.to_path_buf())
    } else if path.is_dir() {
        crate::project::find_manifest(&path.canonicalize().unwrap_or_else(|_| path.to_path_buf()))
    } else {
        None
    };

    if manifest.is_some() {
        let project = crate::project::load_project(path)
            .map_err(|e| (e, String::new(), path.display().to_string()))?;
        let files = glob_pr(&project.src_dir);
        let modules = read_modules(&project.src_dir, &files, &project.root)?;
        let roots = crate::project_roots(&project.src_dir, &project.dep_src_dirs);
        let out = project.root.join("target").join("docs");
        Ok((modules, roots, project.root.clone(), out, project.name))
    } else if path.is_dir() {
        let files = glob_pr(path);
        let modules = read_modules(path, &files, path)?;
        let roots = crate::default_roots(path);
        let out = path.join("target").join("docs");
        let title = dir_title(path);
        Ok((modules, roots, path.to_path_buf(), out, title))
    } else {
        let base = base_of(path);
        let modules = read_modules(&base, std::slice::from_ref(&path.to_path_buf()), &base)?;
        let roots = crate::default_roots(&base);
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
) -> Result<Vec<crate::ModuleSource>, (Error, String, String)> {
    let mut mods = Vec::new();
    for f in files {
        let source = read(f).map_err(|e| (e, String::new(), file_name(f)))?;
        let dotted = dotted_of(src_root, f);
        let source_path = f
            .strip_prefix(provenance_root)
            .unwrap_or(f)
            .display()
            .to_string();
        mods.push(crate::ModuleSource {
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
