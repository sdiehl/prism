// The branded-witness ordering path. `with_ordering` hands its body a
// witness whose brand is a fresh, rigid, scope-local skolem, so a map built under
// one witness carries a brand that a second witness's brand cannot unify with.
// Mixing two witnesses' maps is therefore a compile-time type error, and the
// message names both brands. This pins that guarantee (and the positive case, so
// the brand is not so rigid it rejects consistent use) against the embedded
// `Data.Ordered` module.

use prism::{with_prelude, Error, TypeError};

// Two witnesses in scope at once (the inner one closes over the outer), inserting
// an outer-branded map through the inner witness. That is cross-witness mixing.
const CROSS: &str = "import Data.Ordered (..)\n\
    fn asc(a : Int, b : Int) : Int = a - b\n\
    fn inner(wa : OrdWitness(Int, ba)) : forall bb. (OrdWitness(Int, bb)) -> Int =\n  \
      \\(wb) -> ord_size(wb, ord_insert(wb, 2, \"x\", ord_insert(wa, 1, \"y\", ord_empty(wa))))\n\
    fn nest(wa : OrdWitness(Int, ba)) : Int = with_ordering(asc, inner(wa))\n\
    fn main() = print(with_ordering(asc, nest))\n";

// The same program with a single witness threaded consistently: this must check.
const CONSISTENT: &str = "import Data.Ordered (..)\n\
    fn asc(a : Int, b : Int) : Int = a - b\n\
    fn build(w : OrdWitness(Int, brand)) : Int =\n  \
      ord_size(w, ord_insert(w, 2, \"b\", ord_insert(w, 1, \"a\", ord_empty(w))))\n\
    fn main() = print(with_ordering(asc, build))\n";

#[test]
fn cross_witness_mixing_is_rejected() {
    let err = prism::check(with_prelude(CROSS).as_str())
        .expect_err("mixing two ordering witnesses must be a type error");
    assert!(
        matches!(err, Error::Type(TypeError::Other { .. })),
        "expected a type error, got: {err}"
    );
    let msg = err.to_string();
    // A brand mismatch: two `Map` types agreeing on key and value but differing in
    // the third (brand) parameter, naming both witnesses' brands.
    assert!(
        msg.contains("type mismatch")
            && msg.contains("Map(Int, String, bb)")
            && msg.contains("Map(Int, String, ba)"),
        "expected a brand mismatch naming both witnesses, got: {msg}"
    );
}

#[test]
fn one_witness_threaded_consistently_checks() {
    prism::check(with_prelude(CONSISTENT).as_str())
        .expect("a single witness used consistently must type-check");
}
