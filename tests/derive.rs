//! Structural deriving: `Hash`, `Serialize`, `Stable`, and `Arbitrary`.
//!
//! `Ord` deriving is covered by the snapshot corpus; these gate the four
//! derivations that landed with the wire work. The cross-backend cases assert
//! the acceptance bar that a derived value hash is byte-identical on the
//! interpreter and the native backend, produced by the same blake3 scheme.

use std::process::Command;

use prism::{build, interpret, with_prelude};

// Interpret a prelude-wrapped program, returning its terminal output.
fn run(src: &str) -> String {
    interpret(&with_prelude(src))
        .unwrap_or_else(|e| panic!("interpret failed: {e}"))
        .term
}

// The rendered error of a program expected not to type-check.
fn check_err(src: &str) -> String {
    match prism::check(&with_prelude(src)) {
        Ok(_) => panic!("expected a type error, but the program checked"),
        Err(e) => format!("{e}"),
    }
}

// Build the program natively and run it, returning stdout. Skips (returns the
// interpreter output) when no C compiler is reachable, so the suite still runs
// where the native backend cannot be exercised.
fn native_out(tag: &str, src: &str) -> String {
    let full = with_prelude(src);
    if Command::new("clang").arg("--version").output().is_err() {
        return interpret(&full).unwrap().term;
    }
    let bin = std::env::temp_dir().join(format!("prism_derive_{tag}_{}", std::process::id()));
    build(&full, &bin).expect("native build failed");
    let out = Command::new(&bin).output().expect("native run failed");
    let _ = std::fs::remove_file(&bin);
    String::from_utf8_lossy(&out.stdout).into_owned()
}

const HASH_SRC: &str = r"
type Color = Red | Green | Blue deriving (Eq, Hash)
type Point = P { x: Int, y: Int } deriving (Eq, Hash)
fn main() =
  println(hash(P { x = 1, y = 2 }))
  println(hash(P { x = 1, y = 2 }))
  println(hash(P { x = 1, y = 3 }))
  println(hash(Green))
";

#[test]
fn hash_is_structural_and_hex() {
    let out = run(HASH_SRC);
    let lines: Vec<&str> = out.lines().collect();
    // Every digest is 64 lowercase hex characters.
    for l in &lines {
        assert_eq!(l.len(), 64, "digest is not 64 hex chars: {l:?}");
        assert!(l.bytes().all(|b| b.is_ascii_hexdigit()), "non-hex: {l:?}");
    }
    // Structurally equal values hash equally; a different field differs.
    assert_eq!(lines[0], lines[1], "equal points must hash equally");
    assert_ne!(lines[0], lines[2], "a changed field must change the hash");
}

#[test]
fn hash_native_matches_interpreter() {
    assert_eq!(
        native_out("hash", HASH_SRC),
        run(HASH_SRC),
        "derived Hash must be byte-identical across backends"
    );
}

#[test]
fn stable_derives_when_every_component_is_stable() {
    let src = "import Wire (..)\n\
               type Rec = R { a: Int, b: String, c: Bool } deriving (Stable)\n\
               type Wrap(x) = W(x) deriving (Stable)\n\
               type Nested = N(Rec, Wrap(Int)) deriving (Stable)\n\
               fn main() = println(\"ok\")\n";
    assert_eq!(run(src), "ok\n");
}

#[test]
fn stable_rejects_a_non_stable_field_with_the_field_and_type() {
    let src = "import Wire (..)\n\
               type Config = C { retry: Int, on_fail: (Unit) -> Unit } deriving (Stable)\n\
               fn main() = println(\"x\")\n";
    let err = check_err(src);
    assert!(err.contains("cannot derive Stable for Config"), "{err}");
    assert!(
        err.contains("on_fail"),
        "diagnostic must name the field: {err}"
    );
    assert!(err.contains("(Unit) -> Unit"), "must name the type: {err}");
    assert!(err.contains("not Stable"), "{err}");
}

// The derived `Serialize` roundtrips end to end over the real wire library: a sum
// tags each constructor, and decode peels the tag and reads the fields in order,
// bottoming out in the library's primitive `Serialize(Int)` instance.
const SER_SRC: &str = r"
import Wire (..)

type Shape = Circle(Int) | Rect(Int, Int) deriving (Show, Serialize)

fn roundtrip(x : Shape) : Shape =
  match decode(encode(x)) of
    (v, _rest) => v

fn body() =
  println(show(roundtrip(Circle(7))))
  println(show(roundtrip(Rect(3, 4))))

fn main() = default(body, ())
";

#[test]
fn serialize_roundtrips_a_sum() {
    assert_eq!(run(SER_SRC), "Circle(7)\nRect(3, 4)\n");
}

const ARB_SRC: &str = r"
import Test (..)
import Quickcheck (..)

type Tree = Leaf | Node(Tree, Int, Tree) deriving (Show, Arbitrary)

fn one(seed : U64) : Tree = gen_at(arb_gen(), seed, 4)

fn main() =
  println(show(one(7u64)))
  println(show(one(99u64)))
  println(show(one(7u64)))
";

#[test]
fn arbitrary_is_deterministic_under_a_seed() {
    let out = run(ARB_SRC);
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(
        lines[0], lines[2],
        "same seed must reproduce the same value"
    );
    assert_ne!(lines[0], lines[1], "a different seed should differ");
}

#[test]
fn arbitrary_native_matches_interpreter() {
    assert_eq!(native_out("arb", ARB_SRC), run(ARB_SRC));
}

// The blake3 builtin the interpreter and native runtime share must agree on the
// empty string and a known vector, so a drift in either implementation is caught
// here rather than only through a derived instance.
#[test]
fn blake3_builtin_known_vectors() {
    let src = "fn main() =\n  println(blake3(\"\"))\n  println(blake3(\"abc\"))\n";
    let out = run(src);
    assert_eq!(
        out,
        "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262\n\
         6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85\n"
    );
    assert_eq!(
        native_out("b3", src),
        out,
        "blake3 must match across backends"
    );
}
