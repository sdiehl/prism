//! `prism index` end to end: the CLI's artifact, its `--check` gate, and the
//! cross-module addressing a single-file library test cannot reach.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use prism::index::{EdgeKind, Index, Kind, TestLayer, Vis};

// A project laid out the way `prism index` will meet one in the wild: an entry
// module, an imported module with both an exported and a private definition, and
// tests beside the code they exercise.
const MANIFEST: &str = "[package]\nname = \"indexed\"\n\n[bin]\nentry = \"src/main.pr\"\n";
const MAIN: &str = "\
import Parser

fn main() = println(show(Parser.parse(\"7\")))
";
const PARSER: &str = "\
-- | Parsing helpers.

-- | Not exported: only `parse` and the inline test reach it.
fn normalize(n : Int) : Int = n + 1

-- | The module's one public entry point.
pub fn parse(s : String) : Int = normalize(1)

test fn parse_normalizes() =
  if parse(\"x\") == 2 then () else fail()
";
// A module nothing in the entry's import closure reaches: the shape of a library
// package's own surface, which is most of what a reviewer reads.
const LIBRARY: &str = "\
pub type Doc = Empty | Text(String)

pub fn render(d : Doc) : String =
  match d of
    Empty => \"\"
    Text(s) => s
";

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let count = COUNTER.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |duration| duration.as_nanos());
        let path = std::env::temp_dir().join(format!(
            "prism-index-{tag}-{}-{nanos}-{count}",
            std::process::id()
        ));
        fs::create_dir_all(path.join("src")).unwrap();
        Self { path }
    }

    // Write the fixture project and return its root.
    fn project(tag: &str) -> Self {
        let dir = Self::new(tag);
        fs::write(dir.path.join("prism.toml"), MANIFEST).unwrap();
        fs::write(dir.path.join("src/main.pr"), MAIN).unwrap();
        fs::write(dir.path.join("src/Parser.pr"), PARSER).unwrap();
        fs::write(dir.path.join("src/Library.pr"), LIBRARY).unwrap();
        dir
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn run(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_prism"))
        .args(args)
        .output()
        .unwrap()
}

fn succeed(output: &Output) {
    assert!(
        output.status.success(),
        "stderr:\n{}\nstdout:\n{}",
        String::from_utf8_lossy(&output.stderr),
        String::from_utf8_lossy(&output.stdout)
    );
}

fn index_project(dir: &Path, extra: &[&str]) -> Index {
    let out = dir.join("index.json");
    let mut args = vec![
        "index",
        dir.to_str().unwrap(),
        "--out",
        out.to_str().unwrap(),
    ];
    args.extend_from_slice(extra);
    let output = run(&args);
    succeed(&output);
    // The decoder is the consumer's contract, so the test reads the artifact the
    // way a viewer would rather than poking at raw JSON.
    Index::from_json(&fs::read_to_string(&out).unwrap()).expect("decode the artifact")
}

fn def<'a>(index: &'a Index, id: &str) -> &'a prism::index::Def {
    index.def(id).unwrap_or_else(|| {
        let ids: Vec<&str> = index.defs.iter().map(|d| d.id.as_str()).collect();
        panic!("no definition `{id}`; index has {ids:?}")
    })
}

fn targets<'a>(index: &'a Index, kind: EdgeKind, from: &str) -> Vec<&'a str> {
    index
        .edges
        .iter()
        .filter(|e| e.kind == kind && e.from == from)
        .map(|e| e.to.as_str())
        .collect()
}

// The addressing rule a single-module test cannot exercise: an imported module's
// definitions are named by module, and whether the name joins with `.` or `@`
// follows the `pub` marker, exactly as Core names them. Getting this wrong would
// leave a definition unaddressed, so it is pinned per visibility.
#[test]
fn imported_module_definitions_are_addressed_by_visibility() {
    let dir = TempDir::project("addressing");
    let index = index_project(&dir.path, &[]);

    let exported = def(&index, "Parser.parse");
    assert_eq!(exported.vis, Vis::Public);
    assert_eq!(exported.module, "Parser");
    assert_eq!(exported.name, "parse");
    assert!(exported.hash.is_some());

    let private = def(&index, "Parser@normalize");
    assert_eq!(private.vis, Vis::Private);
    assert!(private.hash.is_some());

    // The entry module is compiled at the root, so its definitions stay bare.
    assert_eq!(def(&index, "main").module, "main");

    // Cross-module navigation in both directions.
    assert!(targets(&index, EdgeKind::Calls, "main").contains(&"Parser.parse"));
    assert!(targets(&index, EdgeKind::Calls, "Parser.parse").contains(&"Parser@normalize"));
}

// The set a build compiles is not the set a reader reads. A module outside the
// entry's import closure — a library package's whole surface — must still be
// addressed, or the index would be empty of exactly the code someone opened it to
// review.
#[test]
fn a_module_the_entry_never_imports_is_still_addressed() {
    let dir = TempDir::project("library");
    let index = index_project(&dir.path, &[]);

    for id in ["Library.Doc", "Library.render"] {
        let def = def(&index, id);
        assert!(
            def.hash.is_some(),
            "`{id}` is outside the entry's imports but must still be addressed"
        );
    }
    assert_eq!(def(&index, "Library.Doc").kind, Kind::Type);
    // And its relationships resolve, not just its address.
    assert!(targets(&index, EdgeKind::UsesType, "Library.render").contains(&"Library.Doc"));
    // Nothing reaches it, so it has no callers; that is a fact about the code, and
    // the reason the reader wanted to see the module in the first place.
    assert!(!index
        .edges
        .iter()
        .any(|e| e.kind == EdgeKind::Calls && e.to == "Library.render"));
}

// A test lives beside the code it covers, and "which tests exercise this?" has to
// reach a private helper the test only touches transitively.
#[test]
fn tests_reach_what_they_exercise_transitively() {
    let dir = TempDir::project("tests");
    let index = index_project(&dir.path, &[]);
    assert_eq!(index.envelope.tests, TestLayer::Included);

    let test = def(&index, "Parser@parse_normalizes");
    assert_eq!(test.kind, Kind::Test);
    let covered = targets(&index, EdgeKind::Tests, "Parser@parse_normalizes");
    assert!(covered.contains(&"Parser.parse"), "direct: {covered:?}");
    assert!(
        covered.contains(&"Parser@normalize"),
        "through a helper: {covered:?}"
    );
}

// The artifact is self-contained by default so a viewer needs no filesystem
// access, and `--no-source` drops exactly that for a consumer holding the tree.
// Either way `span` must still index the module source.
#[test]
fn module_source_is_embedded_by_default_and_droppable() {
    let dir = TempDir::project("source");

    let full = index_project(&dir.path, &[]);
    let parser = full
        .modules
        .iter()
        .find(|m| m.dotted == "Parser")
        .expect("Parser module");
    let embedded = parser.source.as_deref().expect("embedded source");
    assert_eq!(embedded, PARSER);
    let parse = def(&full, "Parser.parse");
    assert_eq!(&embedded[parse.span.start..parse.span.end], parse.source);
    assert_eq!(
        parse.doc.as_deref(),
        Some("The module's one public entry point.")
    );
    assert_eq!(parser.doc.as_deref(), Some("Parsing helpers."));

    let lean = index_project(&dir.path, &["--no-source"]);
    assert!(lean.modules.iter().all(|m| m.source.is_none()));
    // Dropping the module text changes nothing else: the definitions and their
    // own slices are unaffected.
    assert_eq!(lean.defs, full.defs);
}

// `--check` is the CI gate, so it must pass on a current artifact, fail on a
// stale one, and write nothing either way.
#[test]
fn check_gates_a_committed_artifact_without_writing() {
    let dir = TempDir::project("check");
    let out = dir.path.join("index.json");
    let path = dir.path.to_str().unwrap();
    let out_arg = out.to_str().unwrap();

    succeed(&run(&["index", path, "--out", out_arg]));
    let written = fs::read_to_string(&out).unwrap();
    succeed(&run(&["index", path, "--out", out_arg, "--check"]));

    // Editing a body moves its hash, so the committed artifact goes stale.
    fs::write(
        dir.path.join("src/Parser.pr"),
        PARSER.replace("n + 1", "n + 2"),
    )
    .unwrap();
    let stale = run(&["index", path, "--out", out_arg, "--check"]);
    assert!(!stale.status.success());
    assert!(
        String::from_utf8_lossy(&stale.stderr).contains("out of date"),
        "stderr:\n{}",
        String::from_utf8_lossy(&stale.stderr)
    );
    assert_eq!(
        fs::read_to_string(&out).unwrap(),
        written,
        "--check must not write"
    );
}

// The standard library is the largest input the index has, and its addresses are
// published in the Standard Library Reference: the two are generated by different
// code paths, so a disagreement between them is exactly the drift worth pinning.
#[test]
fn stdlib_index_addresses_match_the_committed_reference_badges() {
    let dir = TempDir::new("stdlib");
    let out = dir.path.join("index.json");
    succeed(&run(&[
        "index",
        "--stdlib",
        "--out",
        out.to_str().unwrap(),
        "--no-source",
    ]));
    let index = Index::from_json(&fs::read_to_string(&out).unwrap()).unwrap();

    // Every stdlib module is imported by the driver program, so nothing is left
    // unaddressed except the kinds that have no address at all.
    let unaddressed: Vec<(&str, Kind)> = index
        .defs
        .iter()
        .filter(|d| d.hash.is_none())
        .map(|d| (d.id.as_str(), d.kind))
        .collect();
    assert!(
        unaddressed.iter().all(|(_, kind)| matches!(
            kind,
            Kind::Synonym | Kind::RowAlias | Kind::Pattern | Kind::Stable
        )),
        "unexpectedly unaddressed: {unaddressed:?}"
    );

    // The reference pages carry each definition's hash as an `h-<hex>` fence
    // token. Cross-check every one the index also knows.
    let stdlib_docs = Path::new(env!("CARGO_MANIFEST_DIR")).join("docs/src/stdlib");
    let mut checked = 0usize;
    for entry in fs::read_dir(&stdlib_docs).expect("read stdlib docs") {
        let page = entry.unwrap().path();
        if page.extension().and_then(|e| e.to_str()) != Some("md") {
            continue;
        }
        let text = fs::read_to_string(&page).unwrap();
        let mut name: Option<String> = None;
        for line in text.lines() {
            if let Some(heading) = line.strip_prefix("### `") {
                name = heading.strip_suffix("`").map(str::to_string);
            } else if let Some(hash) = line.split(",h-").nth(1) {
                let Some(name) = &name else { continue };
                // The page shows a bare name; the index may hold it under any
                // module, so match on the unqualified tail.
                let matched = index
                    .defs
                    .iter()
                    .any(|d| &d.name == name && d.hash.as_deref() == Some(hash));
                if matched {
                    checked += 1;
                    continue;
                }
                // A name the index knows, but under no matching hash, is drift.
                assert!(
                    index.defs.iter().all(|d| &d.name != name),
                    "`{name}` in {} carries hash {hash}, which no indexed definition of that name has",
                    page.display()
                );
            }
        }
    }
    assert!(
        checked > 100,
        "expected to cross-check many reference badges, only matched {checked}"
    );
}
