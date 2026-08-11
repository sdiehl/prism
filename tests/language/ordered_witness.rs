// The branded-witness ordering path. `with_ordering` hands its body a
// witness whose brand is a fresh, rigid, scope-local skolem, so a map built under
// one witness carries a brand that a second witness's brand cannot unify with.
// Mixing two witnesses' maps is therefore a compile-time type error, and the
// message names both brands. This checks that guarantee (and the positive case, so
// the brand is not so rigid it rejects consistent use) against the embedded
// `Data.Ordered` module.

use prism::{with_prelude, Error, TypeError};

// Two witnesses in scope at once (the inner one closes over the outer), inserting
// an outer-branded map through the inner witness. That is cross-witness mixing.
const CROSS: &str = r#"import Data.Ordered (..)
fn asc(a : Int, b : Int) : Int = a - b
fn inner(wa : OrdWitness(Int, ba)) : forall bb. (OrdWitness(Int, bb)) -> Int =
  \(wb) -> ord_size(wb, ord_insert(wb, 2, "x", ord_insert(wa, 1, "y", ord_empty(wa))))
fn nest(wa : OrdWitness(Int, ba)) : Int = with_ordering(asc, inner(wa))
fn main() = print(with_ordering(asc, nest))
"#;

// The same program with a single witness threaded consistently: this must check.
const CONSISTENT: &str = r#"import Data.Ordered (..)
fn asc(a : Int, b : Int) : Int = a - b
fn build(w : OrdWitness(Int, brand)) : Int =
  ord_size(w, ord_insert(w, 2, "b", ord_insert(w, 1, "a", ord_empty(w))))
fn main() = print(with_ordering(asc, build))
"#;

// A raw map can infer any phantom brand, so branding the witness alone is not
// enough. The ordered-map wrapper must reject a tree built outside the witness
// API even when its brand variable could otherwise unify.
const RAW_MAP_BYPASS: &str = r#"import Data.Ordered (..)
import Data.Map (..)
fn asc(a : Int, b : Int) : Int = a - b
fn attempt_lookup(w : OrdWitness(Int, brand)) : Option(String) =
  ord_lookup(w, 1, map_insert(1, "forged", map_empty))
fn main() = print(with_ordering(asc, attempt_lookup))
"#;

#[test]
fn cross_witness_mixing_is_rejected() {
    let err = prism::check(with_prelude(CROSS).as_str())
        .expect_err("mixing two ordering witnesses must be a type error");
    assert!(
        matches!(err, Error::Type(TypeError::Kind(_))),
        "expected a type error, got: {err}"
    );
    let msg = err.to_string();
    // A brand mismatch naming both witnesses directly. Since a call's
    // instantiated result unifies with its expected type before the arguments
    // are checked, the disagreement surfaces at the witness argument itself
    // (`OrdWitness(Int, ba)` vs `OrdWitness(Int, bb)`) rather than one level
    // out at the `Map` those calls would have produced.
    assert!(
        msg.contains("type mismatch")
            && msg.contains("OrdWitness(Int, bb)")
            && msg.contains("OrdWitness(Int, ba)"),
        "expected a brand mismatch naming both witnesses, got: {msg}"
    );
}

#[test]
fn one_witness_threaded_consistently_checks() {
    prism::check(with_prelude(CONSISTENT).as_str())
        .expect("a single witness used consistently must type-check");
}

#[test]
fn raw_map_cannot_enter_the_witness_api() {
    let err = prism::check(with_prelude(RAW_MAP_BYPASS).as_str())
        .expect_err("a raw map must not masquerade as a witness-built map");
    let msg = err.to_string();
    assert!(
        msg.contains("type mismatch")
            && msg.contains("Map(Int, String")
            && msg.contains("OrderedMap(Int, String"),
        "expected a raw/ordered map mismatch, got: {msg}"
    );
}

#[test]
fn stdlib_invariant_constructors_are_hidden() {
    let cases = [
        ("Data.Vec", "MkVec"),
        ("Data.FlatArray", "FloatArr"),
        ("Data.IntMap", "IMLeaf"),
        ("Data.UnionFind.Payload", "Ufp"),
        ("Data.Frozen", "Frz"),
        ("Data.Tensor", "MkTensor"),
        ("Data.Ordered", "OrdBy"),
    ];
    for (module, ctor) in cases {
        let src = format!("import {module} ({ctor})\nfn main() = print(0)");
        let err = prism::check(with_prelude(&src).as_str())
            .expect_err("stdlib invariant constructor must be hidden");
        let msg = err.to_string();
        assert!(
            msg.contains(&format!("does not export `{ctor}`")),
            "expected hidden-constructor error for {module}.{ctor}, got: {msg}"
        );
    }
}
