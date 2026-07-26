// The three identities a Prism source file carries, and the requirement that
// they stay distinct axes.
//
//   - Source identity: the exact bytes, comments and formatting included. The
//     compiler embeds its digest in every syntax artifact.
//   - Surface identity: the canonical semantic surface tree with source
//     positions erased. Computed here by `Syntax.Identity` from the published
//     artifact, so the property is stated in Prism over public data.
//   - Core identity: the elaborated subject, as the whole-program namespace
//     root and the per-definition Core hashes.
//
// The matrix below pins one edit per boundary between them: a comment edit and
// a layout edit move source identity alone; rewriting a call as a pipeline
// moves surface identity too, since it is a different tree; changing a literal
// moves all three. The negative directions are the point. Equal Core identity
// does not require equal surface or source identity, so a tool may not treat a
// syntax digest as a semantic one; and equal source bytes do not imply equal
// Core identity, because the same text elaborates differently under a different
// set of imported modules. That last case is the sharpest: two worlds, byte-
// identical program text, identical source and surface identity, different Core
// identity, different output.

use std::fs;
use std::path::{Path, PathBuf};

use prism::{
    default_roots, dump, interpret_io_on_with_args, namespace_root, with_prelude, Config, Root,
};

const FIXTURE_DIR: &str = "tests/fixtures/syntax";
const HARNESS: &str = "consumers/identity_report.pr";

// A digest is 32 bytes rendered as lowercase hex.
const DIGEST_HEX_LEN: usize = 64;

const BASE: &str = "\
-- the base program
fn double(x : Int) : Int = x * 2

fn main() : Int = double(10)
";

// One comment rewritten: different bytes, same tree, same subject.
const COMMENT: &str = "\
-- a different comment entirely
fn double(x : Int) : Int = x * 2

fn main() : Int = double(10)
";

// The same tokens over different lines: different bytes and different spans,
// still the same tree.
const LAYOUT: &str = "\
-- the base program
fn double(x : Int) : Int =
  x * 2

fn main() : Int =
  double(10)
";

// `double(10)` written as `10 |> double`: a different surface tree that
// desugars to the same call.
const SUGAR: &str = "\
-- the base program
fn double(x : Int) : Int = x * 2

fn main() : Int = 10 |> double
";

// One literal changed: a different subject.
const SEMANTIC: &str = "\
-- the base program
fn double(x : Int) : Int = x * 3

fn main() : Int = double(10)
";

// Whether an identity is expected to hold or move against the base program.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Rel {
    Holds,
    Moves,
}

use Rel::{Holds, Moves};

struct Row {
    edit: &'static str,
    src: &'static str,
    source: Rel,
    surface: Rel,
    core: Rel,
}

const MATRIX: [Row; 4] = [
    Row {
        edit: "comment-only",
        src: COMMENT,
        source: Moves,
        surface: Holds,
        core: Holds,
    },
    Row {
        edit: "formatting-only",
        src: LAYOUT,
        source: Moves,
        surface: Holds,
        core: Holds,
    },
    Row {
        edit: "call rewritten as a pipeline",
        src: SUGAR,
        source: Moves,
        surface: Moves,
        core: Holds,
    },
    Row {
        edit: "literal changed",
        src: SEMANTIC,
        source: Moves,
        surface: Moves,
        core: Moves,
    },
];

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE_DIR)
}

fn roots() -> Vec<Root> {
    default_roots(Path::new(env!("CARGO_MANIFEST_DIR")))
}

// Run the Prism identity consumer over one artifact from an explicit path and
// capture its single output line.
fn report(artifact: &str, mode: &str, label: &str, roots: &[Root]) -> String {
    let tmp = std::env::temp_dir().join(format!("prism_identity_{label}.surface-syntax.json"));
    fs::write(&tmp, artifact).expect("write artifact");

    let harness = fs::read_to_string(fixture_dir().join(HARNESS)).expect("harness source");
    let full = with_prelude(&harness);
    let cfg = Config::from_env();
    let args = vec![tmp.display().to_string(), mode.to_string()];
    let mut sink = Vec::new();
    interpret_io_on_with_args(&full, roots, &mut sink, &mut &b""[..], &cfg, args)
        .unwrap_or_else(|e| panic!("identity harness run: {e}"));
    let out = String::from_utf8(sink).expect("utf8 report");
    let out = out.trim().to_string();
    assert!(
        !out.starts_with("decode error") && !out.starts_with("encode error"),
        "identity consumer refused the artifact: {out}"
    );
    out
}

// The three identities of one program: source and surface computed in Prism from
// the artifact, Core taken from the compiler's own whole-program root.
fn identities(src: &str, label: &str) -> (String, String, String) {
    let artifact = dump("surface-syntax", src).expect("surface-syntax dump");
    let source = report(&artifact, "source", &format!("{label}_source"), &roots());
    let surface = report(&artifact, "surface", &format!("{label}_surface"), &roots());
    (
        source,
        surface,
        namespace_root(src, &roots()).expect("root"),
    )
}

fn check(edit: &str, axis: &str, rel: Rel, base: &str, other: &str) {
    match rel {
        Holds => assert_eq!(base, other, "{edit}: {axis} identity moved but must hold"),
        Moves => assert_ne!(base, other, "{edit}: {axis} identity held but must move"),
    }
}

// Every edit in the matrix moves exactly the identities it is supposed to move.
#[test]
fn identity_matrix() {
    let (base_source, base_surface, base_core) = identities(BASE, "base");

    for row in &MATRIX {
        let (source, surface, core) = identities(row.src, row.edit);
        check(row.edit, "source", row.source, &base_source, &source);
        check(row.edit, "surface", row.surface, &base_surface, &surface);
        check(row.edit, "core", row.core, &base_core, &core);
    }
}

// Source identity is the digest of the exact bytes, and surface identity is a
// canonical tree with no positions left in it: the erasure is what makes the two
// axes independent, so it is asserted rather than assumed.
#[test]
fn surface_identity_carries_no_positions() {
    let (source, surface, _) = identities(BASE, "shape");

    assert_eq!(
        source.len(),
        DIGEST_HEX_LEN,
        "source identity is not a digest"
    );
    assert!(
        source.chars().all(|c| c.is_ascii_hexdigit()),
        "source identity is not hex: {source}"
    );

    assert!(
        surface.starts_with('{') && surface.contains("\"items\""),
        "surface identity is not a canonical document: {surface}"
    );
    assert!(
        !surface.contains("\"span\""),
        "surface identity still carries source positions"
    );
    assert!(
        !surface.contains("\"compiler\"") && !surface.contains("\"source\""),
        "surface identity carries the source or the compiler stamp"
    );
}

// Two module worlds, one byte-identical program. Source and surface identity are
// equal because the bytes and the tree are equal; Core identity differs because
// the imported definition differs, and so does the result. Syntax identity is
// never evidence of behavior.
#[test]
fn identical_syntax_under_different_worlds_is_not_identical_core() {
    const MAIN: &str = "\
import Dep (f)

fn main() = println(\"{f(1)}\")
";
    const WORLDS: [(&str, &str); 2] = [
        ("increments", "pub fn f(x : Int) : Int = x + 1\n"),
        ("hundreds", "pub fn f(x : Int) : Int = x + 100\n"),
    ];

    let mut seen: Vec<(String, String, String, String)> = Vec::new();
    for (label, dep) in WORLDS {
        let dir = std::env::temp_dir().join(format!("prism_identity_world_{label}"));
        fs::create_dir_all(&dir).expect("world dir");
        fs::write(dir.join("Dep.pr"), dep).expect("write dep");
        let world = default_roots(&dir);

        let artifact = dump("surface-syntax", MAIN).expect("surface-syntax dump");
        let source = report(&artifact, "source", &format!("world_{label}_src"), &roots());
        let surface = report(
            &artifact,
            "surface",
            &format!("world_{label}_srf"),
            &roots(),
        );
        let core = namespace_root(MAIN, &world).expect("root");

        let full = with_prelude(MAIN);
        let cfg = Config::from_env();
        let mut sink = Vec::new();
        interpret_io_on_with_args(&full, &world, &mut sink, &mut &b""[..], &cfg, Vec::new())
            .unwrap_or_else(|e| panic!("world run: {e}"));
        let output = String::from_utf8(sink)
            .expect("utf8 output")
            .trim()
            .to_string();

        seen.push((source, surface, core, output));
    }

    let (a_source, a_surface, a_core, a_out) = &seen[0];
    let (b_source, b_surface, b_core, b_out) = &seen[1];

    assert_eq!(a_source, b_source, "identical bytes moved source identity");
    assert_eq!(
        a_surface, b_surface,
        "identical bytes moved surface identity"
    );
    assert_ne!(
        a_core, b_core,
        "a different dependency world kept Core identity"
    );
    assert_ne!(a_out, b_out, "a different dependency world kept the result");
}
