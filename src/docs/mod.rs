//! `prism docs`: generate Markdown API documentation for a Prism project.
//!
//! A general tool: it renders one Markdown page per module of a project (or
//! single file) into `target/docs`, with signatures taken from the typechecker's
//! inferred types and prose from `-- |` doc comments (see `extract`). Runnable
//! ```` ```prism ```` blocks in those comments are doctests, compiled and
//! optionally run by `prism docs --test` (see `doctest`), keeping the
//! documentation in sync with the code.
//!
//! The standard library is the first consumer: [`stdlib_pages`] documents the
//! embedded prelude and `Data.*`/`Replay`/`Concurrent` modules, and the book
//! build redirects that output into the mdbook source. Any other project is
//! documented through [`project_pages`].

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use crate::core::Digest;
use crate::driver::{stdlib_driver_src, with_prelude, PRELUDE};
use crate::error::Error;
use crate::parse::{parse, ParseResult};
use crate::resolve::{resolve_modules_in, Root};
use crate::stdlib::STDLIB;
use crate::syntax::desugar::desugar;
use crate::types::{check_allow_holes, Checked};

mod accept;
mod doctest;
mod extract;
mod mdbook;
mod render;
mod typespans;

pub use accept::{accept, ExpectFile, ExpectReport};
pub use doctest::Report;
pub use mdbook::preprocess_book;
pub(crate) use typespans::extract as extract_typespans;
pub use typespans::{TypeSpan, TypeSpans, TYPESPANS_FORMAT};

/// One generated documentation page.
#[derive(Debug)]
pub struct DocPage {
    /// File stem under the output directory (e.g. `data-list`, `index`).
    pub slug: String,
    /// Page title / book heading.
    pub title: String,
    /// The dotted module path (empty for the index page).
    pub module: String,
    /// The rendered Markdown.
    pub markdown: String,
}

/// A module to document, supplied by a caller for [`project_pages`]: its dotted
/// name, page title, source text, and repo-relative path (for provenance).
#[derive(Clone, Debug)]
pub struct ModuleSource {
    pub dotted: String,
    pub title: String,
    pub source: String,
    pub source_path: String,
    pub is_prelude: bool,
}

/// The output of a documentation run: the rendered pages plus the doctests
/// harvested from them.
#[derive(Debug)]
pub struct Generated {
    pub pages: Vec<DocPage>,
    examples: Vec<doctest::Example>,
}

impl Generated {
    /// Compile (and run where applicable) every harvested doctest against the
    /// same explicit module search path.
    #[must_use]
    pub fn test(&self, roots: &[Root], base: &Path) -> Report {
        doctest::run(&self.examples, roots, base)
    }

    /// How many doctests were harvested.
    #[must_use]
    pub const fn example_count(&self) -> usize {
        self.examples.len()
    }

    /// The `(source location, observable output)` of every doctest that ran, for
    /// the docs manifest. Only runnable examples that executed contribute.
    #[must_use]
    pub fn ran_doctests(&self, roots: &[Root], base: &Path) -> Vec<(String, String)> {
        doctest::ran_outputs(&self.examples, roots, base)
    }
}

// A module ready to render: like `ModuleSource` but with its output slug fixed.
struct ModSpec {
    dotted: String,
    title: String,
    slug: String,
    src: String,
    source_path: String,
    is_prelude: bool,
}

impl ModSpec {
    fn from_source(m: ModuleSource) -> Self {
        let slug = slug_of(&m.dotted);
        Self {
            dotted: m.dotted,
            title: m.title,
            slug,
            src: m.source,
            source_path: m.source_path,
            is_prelude: m.is_prelude,
        }
    }
}

fn slug_of(dotted: &str) -> String {
    dotted.to_lowercase().replace('.', "-")
}

// Bypass the driver's warning emission so a docs run stays quiet, and skip the
// surface lints (they target user source, not a whole library).
fn check_quiet(src: &str, roots: &[Root]) -> Result<Checked, Error> {
    // Hole-tolerant on purpose: a documentation example may carry a typed hole
    // (`?name`) to teach the hole report itself. It type-checks with the hole
    // retained (and its tooltip shows the inferred type); running it is the
    // author's problem, which is what `no_run` is for.
    let ParseResult { program, .. } = parse(src)?;
    let program = resolve_modules_in(program, roots)?;
    let program = desugar(program)?;
    Ok(check_allow_holes(&program)?)
}

// Render a set of modules into pages plus their harvested doctests, prepending an
// index page that links every module.
fn render_all(
    specs: &[ModSpec],
    sigs: &BTreeMap<String, String>,
    index_title: &str,
    index_blurb: &str,
    anchor: Option<&str>,
    hashes: &BTreeMap<String, Digest>,
    inst_hashes: &BTreeMap<String, Digest>,
) -> Result<Generated, Error> {
    let mut pages = Vec::new();
    let mut examples = Vec::new();
    let mut index_entries: Vec<(String, String, String)> = Vec::new();

    for spec in specs {
        let ParseResult { program, trivia } = parse(&spec.src)?;
        let (markdown, summary, exs) =
            render::page(spec, &program, &trivia, sigs, hashes, inst_hashes);
        examples.extend(exs);
        index_entries.push((spec.slug.clone(), spec.title.clone(), summary));
        pages.push(DocPage {
            slug: spec.slug.clone(),
            title: spec.title.clone(),
            module: spec.dotted.clone(),
            markdown,
        });
    }

    pages.insert(
        0,
        DocPage {
            slug: "index".into(),
            title: index_title.to_string(),
            module: String::new(),
            markdown: render::index(index_title, index_blurb, anchor, &index_entries),
        },
    );
    Ok(Generated { pages, examples })
}

// ---------------------------------------------------------------------------
// Standard library (the first consumer): the embedded prelude and modules.
// ---------------------------------------------------------------------------

const STDLIB_BLURB: &str =
    "Prism's standard library is ordinary Prism source, not compiler built-ins. \
A small always-on Base supplies the core types, the type-class tower, and the common data modules \
in unqualified scope; everything else is opt-in via explicit import. The pages below are generated \
from the module sources, with signatures taken from the typechecker.";

// The on-disk source path of an embedded stdlib module, derived from its dotted
// name (`Data.List` -> `lib/std/Data/List.pr`) so it cannot drift from `STDLIB`.
fn source_path_of(dotted: &str) -> String {
    format!("lib/std/{}.pr", dotted.replace('.', "/"))
}

/// The embedded stdlib source files eligible for expect-block rewriting: the
/// prelude and every `Data.*`/`Replay`/`Concurrent` module, paired with the
/// repo-relative path `--accept` writes back to.
#[must_use]
pub fn stdlib_expect_files() -> Vec<ExpectFile> {
    stdlib_specs()
        .into_iter()
        .map(|spec| ExpectFile {
            path: std::path::PathBuf::from(spec.source_path),
            source: spec.src,
            module: spec.dotted,
        })
        .collect()
}

/// The expect-block source files for a documented project: each module's
/// on-disk path (resolved under `base`) and its source.
#[must_use]
pub fn project_expect_files(modules: &[ModuleSource], base: &Path) -> Vec<ExpectFile> {
    modules
        .iter()
        .map(|m| ExpectFile {
            path: base.join(&m.source_path),
            source: m.source.clone(),
            module: m.dotted.clone(),
        })
        .collect()
}

fn stdlib_specs() -> Vec<ModSpec> {
    let mut v = vec![ModSpec {
        dotted: doctest::PRELUDE_DOTTED.into(),
        title: "Base".into(),
        slug: "base".into(),
        src: PRELUDE.to_string(),
        source_path: "lib/prelude.pr".into(),
        is_prelude: true,
    }];
    let mut rest = Vec::new();
    for (name, src) in STDLIB {
        rest.push(ModSpec {
            dotted: (*name).into(),
            title: (*name).into(),
            slug: slug_of(name),
            src: (*src).to_string(),
            source_path: source_path_of(name),
            is_prelude: false,
        });
    }
    // Prefixed modules grouped and lexicographic first (`Control.*`, then
    // `Data.*`), then the bare modules lexicographic, so the reference reads in a
    // predictable order rather than the embed-registration order.
    rest.sort_by(|a, b| {
        (!a.dotted.contains('.'), &a.dotted).cmp(&(!b.dotted.contains('.'), &b.dotted))
    });
    v.extend(rest);
    v
}

// Type-check the whole embedded stdlib once, indexing every top-level signature
// by name (names are unique across the stdlib, since it all compiles in one
// scope). The prelude globs in the `Data.*` modules already; import the two it
// does not so their declarations are inferred too.
fn stdlib_sigs() -> Result<BTreeMap<String, String>, Error> {
    let driver = stdlib_driver_src();
    let checked = check_quiet(&driver, &[Root::Embedded(STDLIB)])?;
    Ok(checked
        .decls
        .iter()
        .map(|d| (d.name.clone(), d.ty.show()))
        .collect())
}

/// Generate the Standard Library Reference: the index, then one page per module.
///
/// # Errors
/// Fails if the embedded stdlib does not parse or type-check (a compiler bug).
pub fn stdlib_pages() -> Result<Generated, Error> {
    let sigs = stdlib_sigs()?;
    // One hash of the whole library feeds both surfaces: the full-length root
    // shown on the index page, and the short per-definition badges on the module
    // pages (behavior hashes for functions, shape digests for types/effects).
    let h = crate::driver::stdlib_hash()?;
    // Plain CommonMark, no raw HTML or click-to-copy machinery. The `## Merkle
    // root` heading mirrors the `## Modules` heading the index renderer emits, so
    // the two sections read symmetrically.
    let anchor = format!(
        "## Merkle root\n\n\
         - **Scheme**: `{scheme}`\n\
         - **Hash**: `{root}`\n\
         - **Compiler version**: Prism v{version}",
        scheme = h.scheme,
        root = h.root,
        version = h.version
    );
    // Values, datatype/effect shapes, and class digests all key by distinct-cased
    // names, so they share one lookup. Instances are lowercase like values (a
    // `showBool` value and a `showBool` instance coexist), so they are kept
    // separate and consulted only for instance entries.
    let mut hashes: BTreeMap<String, Digest> = h
        .defs
        .iter()
        .map(|(k, v)| (k.as_str().to_string(), v.clone()))
        .collect();
    hashes.extend(h.shapes);
    hashes.extend(h.classes);
    let inst_hashes = h.instances;
    render_all(
        &stdlib_specs(),
        &sigs,
        "Standard Library",
        STDLIB_BLURB,
        Some(&anchor),
        &hashes,
        &inst_hashes,
    )
}

// ---------------------------------------------------------------------------
// General projects.
// ---------------------------------------------------------------------------

const PROJECT_BLURB: &str = "API documentation generated from the project's source by `prism docs`. \
Function and value signatures are the typechecker's inferred types; prose comes from `-- |` doc comments.";

// Infer each module's own signatures by type-checking it against the project's
// roots with the prelude prepended, then keeping only the names it defines. A
// user module is not glob-imported by the prelude, so this does not double-define
// (unlike the self-referential stdlib, which uses `stdlib_sigs`).
fn project_sigs(
    modules: &[ModuleSource],
    roots: &[Root],
) -> Result<BTreeMap<String, String>, Error> {
    let mut sigs = BTreeMap::new();
    for m in modules {
        let ParseResult { program, .. } = parse(&m.source)?;
        let own: BTreeSet<String> = program.fns.iter().map(|d| d.name.clone()).collect();
        let checked = check_quiet(&with_prelude(&m.source), roots)?;
        for d in &checked.decls {
            if own.contains(&d.name) {
                // Key by the qualified name the renderer looks up first, so two
                // modules that share a bare name never collide in the map.
                sigs.insert(format!("{}.{}", m.dotted, d.name), d.ty.show());
            }
        }
    }
    Ok(sigs)
}

/// Generate documentation for an arbitrary project: one page per supplied
/// module, resolving imports and inferring signatures against `roots`.
///
/// # Errors
/// Fails if a module does not parse or type-check.
pub fn project_pages(
    modules: Vec<ModuleSource>,
    roots: &[Root],
    index_title: &str,
) -> Result<Generated, Error> {
    let sigs = project_sigs(&modules, roots)?;
    let specs: Vec<ModSpec> = modules.into_iter().map(ModSpec::from_source).collect();
    render_all(
        &specs,
        &sigs,
        index_title,
        PROJECT_BLURB,
        None,
        &BTreeMap::new(),
        &BTreeMap::new(),
    )
}
