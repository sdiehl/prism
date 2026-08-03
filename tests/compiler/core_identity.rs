// The content-addressing differential: a Prism program recomputes every
// definition's `prism-core-hash-v2` hash from the published identity surface,
// and the result must equal what the compiler prints.
//
// `dump core-identity` is an observation of the identity surface, not a part of
// it. It renders the same pre-optimizer Core the hasher folds, tagged with the
// same node identifiers, plus the two facts Core does not carry (a definition's
// dictionary arity and its elaboration metadata), the recursive-group partition
// the hasher works in, and the content hashes of the definitions the exported
// group depends on. Nothing here may move a hash, so the corpus below asserts
// agreement against `dump core-hash` rather than against a golden file.
//
// The corpus is chosen for encoder coverage, not for size: every construct that
// the encoder spells specially appears at least once. Programs stay small
// because the reader parses JSON in Prism.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use prism::{default_roots, dump_on, interpret_io_on_with_args, with_prelude, Config, Error, Root};

const FIXTURE_DIR: &str = "tests/fixtures/syntax";
const HARNESS: &str = "consumers/core_identity_hash.pr";

const IDENTITY_PHASE: &str = "core-identity";
const HASH_PHASE: &str = "core-hash";

// A `dump core-hash` line is an abbreviated hash, two spaces, then the name.
const HASH_LINE_SEP: &str = "  ";

struct Case {
    name: &'static str,
    src: &'static str,
}

// Straight-line arithmetic and a call: `Bind`, `Prim`, `Call`, `Return`.
const ARITH: &str = "\
fn twice(n : Int) : Int = n + n

fn main() : Unit ! {IO} = println(show(twice(21)))
";

// Self recursion, so a group of one is genuinely cyclic and its own reference
// resolves to an intra-component index rather than to a dependency hash.
const RECURSION: &str = "\
fn down(n : Int) : Int =
  if n <= 0 then
    0
  else
    down(n - 1)

fn main() : Unit ! {IO} = println(show(down(5)))
";

// Mutual recursion: one component with two members, whose canonical order is
// decided by the encoding, not by the source order or the names.
const MUTUAL: &str = "\
fn ping(n : Int) : Int =
  if n <= 0 then
    1
  else
    pong(n - 1)

fn pong(n : Int) : Int =
  if n <= 0 then
    2
  else
    ping(n - 1)

fn main() : Unit ! {IO} = println(show(ping(4) + pong(3)))
";

// A datatype, constructor values, and constructor/wildcard patterns with their
// binder lists.
const DATA: &str = "\
type Shape = Circle(Int) | Rect(Int, Int) | Dot

fn area(s : Shape) : Int =
  match s of
    Circle(r) => r * r * 3
    Rect(w, h) => w * h
    Dot => 0

fn main() : Unit ! {IO} =
  println(show(area(Circle(2)) + area(Rect(3, 4)) + area(Dot)))
";

// Lambdas and thunks under a higher-order call, plus a tuple value.
const LAMBDA: &str = "\
fn apply_twice(f : (Int) -> Int, x : Int) : Int = f(f(x))

fn pair_up(n : Int) : (Int, Int) = (n, n + 1)

fn main() : Unit ! {IO} =
  let p = pair_up(apply_twice(\\(y) -> y * 3, 2))
  println(show(fst(p) + snd(p)))
";

// A user-declared effect and a handler with a return clause, whose operation
// names the hasher commits to verbatim and whose clauses it sorts. The
// declaration names are deliberately unlike anything the prelude declares:
// operations share one flat namespace with it, so a plausible name such as
// `ask` or `tell` would rebind a standard effect's operation program-wide.
const HANDLER: &str = "\
effect Oracle
  oracle_read() : Int
  oracle_note(Int) : Unit

fn consult() : Int ! {Oracle} =
  let a = oracle_read()
  oracle_note(a)
  a + oracle_read()

fn main() : Unit ! {IO} =
  let r = handle consult() with
    oracle_read() resume k => k(7)
    oracle_note(v) resume k => k(())
    return x => x
  println(show(r))
";

// Mutable variables, which elaborate to generated `get`/`set` operations. The
// hasher renumbers those by first occurrence so a rename cannot move a hash, and
// the reader has to perform the same renumbering from the exported verb and slot.
const MUTABLE: &str = "\
fn accumulate(n : Int) : Int =
  var acc := 0
  var i := 0
  while i < n do
    acc := acc + i
    i := i + 1
  acc

fn main() : Unit ! {IO} = println(show(accumulate(5)))
";

// Strings and floats: the token length prefix, and the bit pattern a float is
// committed by.
const SCALARS: &str = "\
fn label(x : Float) : String = concat(\"v=\", show(x))

fn main() : Unit ! {IO} =
  println(label(1.5))
  println(label(0.0 - 0.25))
";

const CORPUS: [Case; 8] = [
    Case {
        name: "arith",
        src: ARITH,
    },
    Case {
        name: "recursion",
        src: RECURSION,
    },
    Case {
        name: "mutual",
        src: MUTUAL,
    },
    Case {
        name: "data",
        src: DATA,
    },
    Case {
        name: "lambda",
        src: LAMBDA,
    },
    Case {
        name: "handler",
        src: HANDLER,
    },
    Case {
        name: "mutable",
        src: MUTABLE,
    },
    Case {
        name: "scalars",
        src: SCALARS,
    },
];

fn manifest() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

fn fixture(rel: &str) -> PathBuf {
    manifest().join(FIXTURE_DIR).join(rel)
}

fn roots() -> Vec<Root> {
    default_roots(manifest())
}

fn phase(name: &str, src: &str) -> Result<String, Error> {
    dump_on(name, &with_prelude(src), &roots(), &Config::default())
}

// Every `<hash>  <name>` line of a dump, as a map.
fn hash_lines(out: &str) -> BTreeMap<&str, &str> {
    out.lines()
        .filter_map(|l| l.split_once(HASH_LINE_SEP))
        .map(|(h, n)| (n.trim(), h.trim()))
        .collect()
}

// Run the Prism reader over one identity artifact and return its report.
fn recompute(artifact: &str, label: &str) -> String {
    let tmp = std::env::temp_dir().join(format!("prism_core_identity_{label}.json"));
    fs::write(&tmp, artifact).expect("write artifact");

    let harness = fs::read_to_string(fixture(HARNESS)).expect("harness source");
    let mut sink = Vec::new();
    interpret_io_on_with_args(
        &with_prelude(&harness),
        &roots(),
        &mut sink,
        &mut &b""[..],
        &Config::default(),
        vec![tmp.display().to_string()],
    )
    .unwrap_or_else(|e| panic!("{label}: hash reader run: {e}"));
    let out = String::from_utf8(sink).expect("utf8 report");
    assert!(
        !out.contains("error:"),
        "{label}: hash reader refused the artifact: {out}"
    );
    out
}

// The differential itself. For every program in the corpus, the hash the Prism
// reader derives from the published identity surface equals the hash the
// compiler derives from Core.
#[test]
fn prism_recomputes_every_core_hash() {
    for case in &CORPUS {
        let artifact = phase(IDENTITY_PHASE, case.src)
            .unwrap_or_else(|e| panic!("{}: core-identity dump: {e}", case.name));
        let compiler = phase(HASH_PHASE, case.src)
            .unwrap_or_else(|e| panic!("{}: core-hash dump: {e}", case.name));

        let reported = recompute(&artifact, case.name);
        let mine = hash_lines(&reported);
        let theirs = hash_lines(&compiler);
        assert!(
            !mine.is_empty(),
            "{}: the reader reported no definitions",
            case.name
        );

        for (name, hash) in &mine {
            let want = theirs.get(name).unwrap_or_else(|| {
                panic!("{}: the reader invented a definition {name}", case.name)
            });
            assert_eq!(
                hash, want,
                "{}: recomputed hash for {name} disagrees with the compiler",
                case.name
            );
        }
    }
}

// The user's own definitions are what the export carries, so the reader must
// account for all of them and for nothing from the prelude.
#[test]
fn the_export_is_exactly_the_user_program() {
    let artifact = phase(IDENTITY_PHASE, MUTUAL).expect("core-identity dump");
    let reported = recompute(&artifact, "mutual_coverage");
    let names: Vec<&str> = hash_lines(&reported).into_keys().collect();
    assert_eq!(names, vec!["main", "ping", "pong"]);
}

// The observation surface is not an observable. Publishing it may not perturb a
// single content hash, so the hashes of a program are identical whether or not
// the identity surface was dumped, and the dump itself is a pure function of the
// source.
#[test]
fn dumping_the_identity_surface_moves_no_hash() {
    let before = phase(HASH_PHASE, DATA).expect("core-hash dump");
    let once = phase(IDENTITY_PHASE, DATA).expect("core-identity dump");
    let twice = phase(IDENTITY_PHASE, DATA).expect("core-identity dump");
    let after = phase(HASH_PHASE, DATA).expect("core-hash dump");

    assert_eq!(once, twice, "the identity surface is not deterministic");
    assert_eq!(before, after, "observing the identity surface moved a hash");
}
