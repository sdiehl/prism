//! `prism index`: write the whole-codebase index a program viewer reads.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use crate::cli::docs::resolve_docs_input;
use crate::cli::{file_name, CmdError, CmdResult};
use crate::error::Error;
use crate::index::{build, diff, Index, IndexInput, TestLayer};

// The default artifact name, in `target/` beside the `docs/` the doc generator
// writes.
const INDEX_FILE: &str = "index.json";

/// The switches `prism index` accepts, named rather than positional: four bare
/// bools at the call site read as an opaque `true, false, false, true`.
#[derive(Debug, Clone, Copy, Default)]
pub struct IndexOpts {
    /// Index the embedded standard library instead of PATH.
    pub stdlib: bool,
    /// Compile every project module through an import, entry included.
    pub as_library: bool,
    /// Omit definition source text from the artifact.
    pub no_source: bool,
    /// Write the artifact, or verify a committed copy without writing.
    pub mode: IndexMode,
}

/// What `prism index` does with the artifact it builds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum IndexMode {
    /// Write the artifact to the output file.
    #[default]
    Write,
    /// Verify a committed copy is current and write nothing, the
    /// `prism docs --check` contract.
    Check,
}

// `prism index [PATH] [--out FILE] [--stdlib] [--no-source] [--check]`.
// Indexes the project/dir/file at PATH (or the embedded standard library with
// `--stdlib`) into one JSON artifact. `--check` verifies a committed copy is
// current and writes nothing, the `prism docs --check` contract.
pub fn index_cmd(
    path: &Path,
    out: Option<PathBuf>,
    opts: IndexOpts,
    cfg: &crate::Config,
) -> CmdResult {
    let (index, default_dir) = if opts.stdlib {
        (build_stdlib(!opts.no_source)?, PathBuf::from("target"))
    } else {
        build_project(path, !opts.no_source, opts.as_library, cfg)?
    };
    let json = index.to_json().map_err(|e| {
        (
            Error::CodegenDump(e.to_string()),
            String::new(),
            String::new(),
        )
    })?;
    let file = out.unwrap_or_else(|| default_dir.join(INDEX_FILE));

    if opts.mode == IndexMode::Check {
        if std::fs::read_to_string(&file).unwrap_or_default() == json {
            return Ok(());
        }
        return Err((
            Error::CodegenDump(format!(
                "{}: out of date; run `prism index`",
                file.display()
            )),
            String::new(),
            String::new(),
        ));
    }

    if let Some(dir) = file.parent().filter(|d| !d.as_os_str().is_empty()) {
        std::fs::create_dir_all(dir)
            .map_err(|e| (Error::Io(e), String::new(), dir.display().to_string()))?;
    }
    std::fs::write(&file, &json)
        .map_err(|e| (Error::Io(e), String::new(), file.display().to_string()))?;
    report(&index, &file);
    Ok(())
}

// The standard library index. Every stdlib module is imported by the driver
// program and none is compiled at the root, so there is no entry module: only the
// prelude's declarations are addressed by bare name, which `is_prelude` already
// says.
fn build_stdlib(embed_source: bool) -> Result<Index, CmdError> {
    let modules = crate::stdlib_modules();
    let roots = vec![crate::Root::Embedded(crate::stdlib::STDLIB)];
    build(IndexInput {
        modules: &modules,
        source: &crate::driver::stdlib_driver_src(),
        roots: &roots,
        entry: None,
        title: "Standard Library".into(),
        embed_source,
    })
    .map_err(|e| (e, String::new(), "<stdlib>".into()))
}

// A project, directory, or single-file index, returning it and the directory its
// default output lands in.
//
// The modules and their search path come from the same resolution the doc
// generator uses, so the two surfaces always describe the same module set; the
// merged source comes from the build's own input resolution, so the addresses are
// the ones a build would compute.
fn build_project(
    path: &Path,
    embed_source: bool,
    as_library: bool,
    cfg: &crate::Config,
) -> Result<(Index, PathBuf), CmdError> {
    let (modules, roots, base, _, title, _) = resolve_docs_input(path)?;
    // Documentation combines several packages in one namespace. Indexing a
    // project's binary entry at the compiler root would make its declarations
    // bare (`render`) while another package imports them qualified
    // (`Typst.render`). Library mode compiles every project module through an
    // import, making the identities agree at that join.
    let entry = (!as_library)
        .then(|| entry_dotted(path, &modules, &base))
        .flatten();
    let source = merged_source(path, &modules, entry.as_deref(), cfg)?;
    let index = build(IndexInput {
        modules: &modules,
        source: &source,
        roots: &roots,
        entry: entry.as_deref(),
        title,
        embed_source,
    })
    .map_err(|e| (e, source.clone(), file_name(path)))?;
    Ok((index, base.join("target")))
}

/// Join existing index artifacts into one cross-unit reference universe.
pub fn merge_cmd(inputs: &[PathBuf], title: String, out: Option<PathBuf>) -> CmdResult {
    let mut indexes = Vec::new();
    for file in inputs {
        let text = std::fs::read_to_string(file)
            .map_err(|e| (Error::Io(e), String::new(), file.display().to_string()))?;
        indexes.push(Index::from_json(&text).map_err(|e| {
            (
                Error::CodegenDump(e),
                String::new(),
                file.display().to_string(),
            )
        })?);
    }
    let index = Index::merge(title, indexes)
        .map_err(|e| (Error::CodegenDump(e), String::new(), String::new()))?;
    let json = index.to_json().map_err(|e| {
        (
            Error::CodegenDump(e.to_string()),
            String::new(),
            String::new(),
        )
    })?;
    let file = out.unwrap_or_else(|| PathBuf::from("target").join(INDEX_FILE));
    if let Some(dir) = file.parent().filter(|d| !d.as_os_str().is_empty()) {
        std::fs::create_dir_all(dir)
            .map_err(|e| (Error::Io(e), String::new(), dir.display().to_string()))?;
    }
    std::fs::write(&file, json)
        .map_err(|e| (Error::Io(e), String::new(), file.display().to_string()))?;
    report(&index, &file);
    Ok(())
}

// The merged program the addresses are taken over: the build's own input, plus one
// import per indexed module the entry does not already reach.
//
// Every listed module has to reach the compiled program or it carries no address
// at all, and "the entry's import closure" is the wrong set: a library package's
// modules are not reachable from its `[bin]` entry, and they are most of the code
// a reviewer wants to read. The extra imports are qualified-only, so they bring no
// name into unqualified scope, and one that duplicates an import the entry already
// makes is a no-op. The entry itself stays at the root, so its own definitions are
// addressed exactly as a build addresses them (bare names, `main` wrapped in its
// world handler) rather than as an imported module's would be.
fn merged_source(
    path: &Path,
    modules: &[crate::ModuleSource],
    entry: Option<&str>,
    cfg: &crate::Config,
) -> Result<String, CmdError> {
    let imports = modules
        .iter()
        .filter(|m| !m.is_prelude && Some(m.dotted.as_str()) != entry && importable(&m.dotted))
        .fold(String::new(), |mut imports, m| {
            writeln!(imports, "import {}", m.dotted).expect("writing to a String cannot fail");
            imports
        });
    match entry {
        Some(_) => {
            let (full, _, _, _) = crate::cli::resolve_input(path, cfg)?;
            Ok(format!("{full}\n{imports}"))
        }
        // A plain directory is not a project and has no entry module, so it is
        // indexed through a synthesized driver over its modules alone, the same
        // shape `--stdlib` uses.
        None => Ok(crate::with_prelude(&imports)),
    }
}

// Whether a dotted module name is one `import` can actually say: every segment
// an uppercase identifier, which is what the grammar demands of a module path.
// A `.pr` file under a lowercase directory (`benches/lexbench.pr` indexed from
// a repository root) has no importable name at all. Skipping its import is not
// skipping the module — it is still indexed, it just cannot be reached by the
// driver, so its definitions carry no address, the honest state [`Def::hash`]
// documents. Synthesizing the import anyway would hand the front end a line
// that cannot parse and fail the whole index over text the author never wrote.
fn importable(dotted: &str) -> bool {
    !dotted.is_empty()
        && dotted.split('.').all(|segment| {
            let mut chars = segment.chars();
            chars.next().is_some_and(|c| c.is_ascii_uppercase())
                && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        })
}

// The dotted name of the module compiled at the root, whose declarations are
// addressed by bare name. Getting it wrong would leave the entry module's
// definitions unaddressed, so it is matched by resolved path rather than by name:
// `resolve_docs_input` records each module's path relative to `base`, and the
// entry is one of them.
fn entry_dotted(path: &Path, modules: &[crate::ModuleSource], base: &Path) -> Option<String> {
    let entry = crate::cli::user_entry_path(path).ok()?;
    let entry = entry.canonicalize().ok()?;
    modules
        .iter()
        .find(|m| base.join(&m.source_path).canonicalize().ok() == Some(entry.clone()))
        .map(|m| m.dotted.clone())
}

// `prism index --diff OLD NEW [--out FILE]`. Compares two committed artifacts and
// writes the diff (or prints its summary when no `--out` is given).
//
// Two artifacts, no compiler: the comparison is between content addresses a
// compiler already computed, which is what lets it separate the definitions an
// author edited from the ones that merely re-hashed underneath them.
pub fn diff_cmd(old: &Path, new: &Path, out: Option<PathBuf>) -> CmdResult {
    let read = |p: &Path| -> Result<Index, CmdError> {
        let text = std::fs::read_to_string(p)
            .map_err(|e| (Error::Io(e), String::new(), p.display().to_string()))?;
        Index::from_json(&text).map_err(|e| {
            (
                Error::CodegenDump(e),
                String::new(),
                p.display().to_string(),
            )
        })
    };
    let report = diff::diff(&read(old)?, &read(new)?)
        .map_err(|e| (Error::CodegenDump(e), String::new(), String::new()))?;
    let Some(file) = out else {
        println!("{}", report.summary());
        for e in report.entries.iter().filter(|e| e.status.is_authored()) {
            let moved = e
                .old_id
                .as_ref()
                .map_or(String::new(), |from| format!("  (was {from})"));
            println!("  {:<9} {}{moved}", format!("{:?}", e.status), e.id);
        }
        return Ok(());
    };
    let json = report.to_json().map_err(|e| {
        (
            Error::CodegenDump(e.to_string()),
            String::new(),
            String::new(),
        )
    })?;
    if let Some(dir) = file.parent().filter(|d| !d.as_os_str().is_empty()) {
        std::fs::create_dir_all(dir)
            .map_err(|e| (Error::Io(e), String::new(), dir.display().to_string()))?;
    }
    std::fs::write(&file, &json)
        .map_err(|e| (Error::Io(e), String::new(), file.display().to_string()))?;
    println!("wrote {} ({})", file.display(), report.summary());
    Ok(())
}

// How many broken-module warnings are spelled out before the rest are counted.
const SHOWN: usize = 5;

fn report(index: &Index, file: &Path) {
    println!(
        "wrote {} ({} modules, {} definitions, {} edges)",
        file.display(),
        index.modules.len(),
        index.defs.len(),
        index.edges.len()
    );
    // A missing test layer is reported, never silent: an absent `tests` edge set
    // must not read as "this code has no tests".
    if let TestLayer::Unavailable(why) = &index.envelope.tests {
        eprintln!("prism index: test layer unavailable ({why})");
    }
    // Likewise a module that did not parse: its declarations are absent from the
    // definition layer, and silence would read as "an empty module". Capped the
    // way a viewer relation row is: a few broken files in a project deserve a
    // line each, while a compiler repository's own negative fixture corpus is
    // dozens of files that exist *because* they do not parse, and a wall of
    // warnings buries the one that matters. The true count is always printed,
    // and every diagnostic is in the artifact (`modules[].error`).
    let broken: Vec<_> = index.modules.iter().filter(|m| m.error.is_some()).collect();
    for m in broken.iter().take(SHOWN) {
        let why = m.error.as_deref().unwrap_or_default();
        eprintln!(
            "prism index: {}: not indexed, does not parse ({why})",
            m.path
        );
    }
    if broken.len() > SHOWN {
        eprintln!(
            "prism index: ... and {} more modules that do not parse; each is named with \
             its diagnostic in the artifact",
            broken.len() - SHOWN
        );
    }
}

#[cfg(test)]
mod tests {
    use super::importable;

    #[test]
    fn only_uppercase_dotted_paths_are_importable() {
        assert!(importable("Data.List"));
        assert!(importable("M"));
        assert!(importable("Syntax.Lex2"));
        assert!(!importable("benches.lexbench"));
        assert!(!importable("lib.std.Replay"));
        assert!(!importable(""));
        assert!(!importable("Data..List"));
    }
}
