//! Structural deriving: `Hash`, `Serialize`, `Stable`, and `Arbitrary`.
//!
//! `Ord` deriving is covered by the snapshot corpus; these gate the four
//! wire-visible derivations. The cross-backend cases assert
//! the acceptance bar that a derived value hash is byte-identical on the
//! interpreter and the native backend, produced by the same blake3 scheme.

use std::process::Command;

use prism::error::Diag;
use prism::{build, interpret, with_prelude, Error, TypeError};

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

// The structured diagnostic of a program expected not to type-check, for the
// cases that assert on the code, the help, or the notes rather than the message.
fn check_diag(src: &str) -> Diag {
    match prism::check(&with_prelude(src)) {
        Ok(_) => panic!("expected a type error, but the program checked"),
        Err(Error::Type(TypeError::Kind(diag))) => *diag,
        Err(e) => panic!("expected a coded diagnostic, got: {e}"),
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
    let src = r#"import Wire (..)
type Rec = R { a: Int, b: String, c: Bool } deriving (Stable)
type Wrap(x) = W(x) deriving (Stable)
type Nested = N(Rec, Wrap(Int)) deriving (Stable)
fn main() = println("ok")
"#;
    assert_eq!(run(src), "ok\n");
}

#[test]
fn stable_rejects_a_non_stable_field_with_the_field_and_type() {
    let src = r#"import Wire (..)
type Config = C { retry: Int, on_fail: (Unit) -> Unit } deriving (Stable)
fn main() = println("x")
"#;
    let err = check_err(src);
    assert!(err.contains("cannot derive Stable for Config"), "{err}");
    assert!(
        err.contains("on_fail"),
        "diagnostic must name the field: {err}"
    );
    assert!(err.contains("(Unit) -> Unit"), "must name the type: {err}");
    assert!(err.contains("not Stable"), "{err}");
}

// The digest a derived `Stable` instance injects into `shape_digest_of` (and so
// stamps into every `wire_encode_stable` frame) is exactly the type's canonical
// shape digest. Encode at runtime, read the frame's digest back with
// `wire_open_value_any`, and it must equal `shape_digests_of` computed in Rust:
// the injected literal and the compiler's shape-digest computation are one value.
#[test]
fn stable_injected_digest_equals_canonical_shape_digest() {
    let src = r#"
import Wire (..)

type T = T(Int, String) deriving (Serialize, Stable)

fn main() =
  match wire_open_value_any(wire_encode_stable(T(7, "hi"))) of
    (dig, _body) => println(dig)
"#;
    let printed = run(src);
    let all = prism::shape_digests_of(&prism::with_prelude(
        "type T = T(Int, String)\nfn main() = println(\"ok\")\n",
    ))
    .expect("shape digests");
    assert_eq!(printed.trim(), &all["T"][..16]);
}

// A hand-written `Stable` instance is rejected: the shape digest is compiler-owned,
// so the only instance is the derived one, and a manual one could forge a frozen
// contract.
#[test]
fn stable_rejects_a_hand_written_instance() {
    let src = r#"import Wire (..)
type T = T(Int) deriving (Serialize)
instance stableT : Stable(T)
  fn shape_digest_of(_x) = "deadbeefdeadbeef"
fn main() = println("x")
"#;
    let err = check_err(src);
    assert!(
        err.contains("Stable") && err.contains("deriving (Stable)"),
        "manual Stable instance must be rejected pointing at deriving: {err}"
    );
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

// A type parameter no field mentions is a brand: it exists to keep two uses of
// one shape from being interchanged, and no derived method can ever reach a value
// of it. The derived context therefore omits it, so branding at a type with no
// `Show` or `Eq` instance of its own still compiles and runs.
const PHANTOM_SRC: &str = r#"
type Draft = Draft
type Final = Final

type Doc(phase) = D { text : String, revision : Int } deriving (Eq, Show)

fn drafted(t : String) : Doc(Draft) = D { text = t, revision = 0 }

fn published(d : Doc(Draft)) : Doc(Final) =
  D { text = d.text, revision = d.revision + 1 }

fn main() =
  let d = drafted("hi")
  println(show(d))
  println(show(published(d)))
  println(show(d == drafted("hi")))
  println(show(d == drafted("bye")))
"#;

#[test]
fn a_phantom_parameter_needs_no_instance() {
    assert_eq!(
        run(PHANTOM_SRC),
        "D { text = \"hi\", revision = 0 }\nD { text = \"hi\", revision = 1 }\ntrue\nfalse\n"
    );
}

// The other side of the same rule: a parameter a field does mention is reached by
// the derived method, so its instance is still required and its absence is still
// an error. The occurrence is nested (`List(a)`), proving the rule looks through
// type application rather than only at a bare parameter.
#[test]
fn an_occurring_parameter_still_demands_its_instance() {
    let src = r"
type Opaque = Opaque
type Bag(a) = Bag(List(a)) deriving (Show)
fn bagged() : Bag(Opaque) = Bag([Opaque])
fn main() = println(show(bagged()))
";
    let err = check_err(src);
    assert!(
        err.contains("Show") && err.contains("Opaque"),
        "a mentioned parameter must still require its instance: {err}"
    );
}

// `deriving (Lens)` with the optic library in scope: one lens value per field,
// named for its type and field, read and written through the library. `Tagged`
// carries a brand no field mentions, and a lens shows and compares nothing, so
// neither the lenses nor the derived `Show` demands anything of a brand type that
// has no instances at all.
const LENS_SRC: &str = r"
import Data.Optic (..)

type Point = Point { x: Int, y: Int } deriving (Lens, Show)

type Metric = Metric

type Tagged(brand) = Tagged { count: Int } deriving (Lens, Show)

fn hits() : Tagged(Metric) = Tagged { count = 1 }

fn main() =
  let p = Point { x = 1, y = 2 }
  println(show(view(point_x, p)))
  println(show(lens_set(point_y, p, 9)))
  println(show(over(tagged_count, \(n) -> n + 1, hits())))
";

#[test]
fn field_lenses_are_type_qualified_and_brand_free() {
    assert_eq!(
        run(LENS_SRC),
        "1\nPoint { x = 1, y = 9 }\nTagged { count = 2 }\n"
    );
}

// The accessor pair predates the optic library and costs no import, so a program
// that never mentions a lens value still derives `<f>_of` and `with_<f>` and never
// has to import anything.
#[test]
fn lens_accessors_need_no_optic_import() {
    let src = r"
type Point = Point { x: Int, y: Int } deriving (Lens)
fn main() =
  println(x_of(with_x(Point { x = 1, y = 2 }, 7)))
";
    assert_eq!(run(src), "7\n");
}

// A lens names one part inside one whole, so there has to be exactly one whole to
// take apart and its parts have to have names. Both rejections name the type.
#[test]
fn lens_rejects_a_type_that_is_not_one_record() {
    let many = check_err(
        r"
type Shape = Circle { r: Int } | Square { s: Int } deriving (Lens)
fn main() = println(1)
",
    );
    assert!(
        many.contains("cannot derive Lens for Shape") && many.contains("single record constructor"),
        "{many}"
    );
    let positional = check_err(
        r"
type Pair = Pair(Int, Int) deriving (Lens)
fn main() = println(1)
",
    );
    assert!(
        positional.contains("cannot derive Lens for Pair") && positional.contains("named fields"),
        "{positional}"
    );
}

// The accessor pair is named after the field alone, so two records sharing a
// field name would define `x_of` and `with_x` twice at two unrelated types. That
// is refused at the derive, where both types can be named, rather than becoming
// an unbuildable Core witness later. The report is the same whichever type is
// declared first: it names the one that claimed the name.
#[test]
fn lens_rejects_two_records_claiming_one_accessor() {
    let both = |first: &str, second: &str| {
        check_diag(&format!(
            "type {first} = {first} {{ x: Int }} deriving (Lens)
type {second} = {second} {{ x: Int }} deriving (Lens)
fn main() = println(1)
"
        ))
    };
    for diag in [both("Point", "Vec"), both("Vec", "Point")] {
        assert_eq!(diag.kind.code(), "E6072");
        let msg = diag.to_string();
        assert!(msg.contains("Point") && msg.contains("Vec"), "{msg}");
        assert!(
            msg.contains("x_of") && msg.contains("with_x"),
            "both accessor names belong in the report: {msg}"
        );
        let note = diag.notes.join(" ");
        assert!(
            note.contains("point_x") && note.contains("vec_x"),
            "the note must say the lens values are unaffected: {note}"
        );
        assert!(diag.help.is_some(), "the report offers no fix");
    }
}

// One type deriving lenses over two fields claims four accessor names and is not
// a collision with itself, and neither is a field name two types share when only
// one of them derives lenses.
#[test]
fn lens_accessor_names_collide_only_across_deriving_types() {
    let src = r"
type Point = Point { x: Int, y: Int } deriving (Lens)
type Vec = Vec { x: String }
fn main() = println(x_of(Point { x = 1, y = 2 }))
";
    assert_eq!(run(src), "1\n");
}

// A synthesized accessor may not take a name a top-level function already holds.
// `x_of` for field `x` would otherwise reach Core as two definitions of one name
// against the hand-written function, or, were the name a library one, silently
// resolve to whichever the merge kept. The derive is refused with a named
// diagnostic, whichever order the function and the type are written in.
#[test]
fn lens_rejects_accessor_that_shadows_a_function() {
    let clash = |fn_first: bool| {
        let func = "fn x_of(r) = 0";
        let ty = "type Point = Point { x: Int } deriving (Lens)";
        let src = if fn_first {
            format!("{func}\n{ty}\nfn main() = println(1)\n")
        } else {
            format!("{ty}\n{func}\nfn main() = println(1)\n")
        };
        check_diag(&src)
    };
    for diag in [clash(true), clash(false)] {
        assert_eq!(diag.kind.code(), "E6074");
        let msg = diag.to_string();
        assert!(
            msg.contains("Point") && msg.contains("x_of"),
            "the report names the type and the accessor: {msg}"
        );
        assert!(diag.help.is_some(), "the report offers no fix");
        assert!(
            !diag.notes.is_empty(),
            "the report explains the flat namespace"
        );
    }
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
        r"af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262
6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85
"
    );
    assert_eq!(
        native_out("b3", src),
        out,
        "blake3 must match across backends"
    );
}
