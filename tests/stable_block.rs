//! The `stable` block: its desugaring into frozen rung
//! types and the version ladder, the frozen-rung-edit compile error, and
//! formatter round-trip.
//!
//! The generated roundtrip law (upgrade after downgrade is the identity on the
//! safe subset) runs as a committed property test in
//! `tests/cases/run/stable_ladder.pr`; here we gate the surface and the golden.

use prism::{format, with_prelude, Error, TypeError};

// A minimal stable block: `Order` is the current rung, `Order.V1` its frozen
// predecessor, with one additive field defaulted on upgrade.
const BLOCK: &str = "\
import Wire (..)

stable Order {
  V1 = { id: Int, qty: Int, sym: String },
  V2 = { ..V1, tif: Int = 0 }
}
";

fn dump_core(src: &str) -> String {
    prism::dump("core", &with_prelude(src)).unwrap_or_else(|e| panic!("dump failed: {e}"))
}

fn line_of(src: &str, byte: usize) -> usize {
    src[..byte].matches('\n').count() + 1
}

// The block desugars to the frozen rung type, the bare current type, and the
// adjacent up/down ladder as plain functions.
#[test]
fn desugars_to_rung_types_and_ladder() {
    let core = dump_core(BLOCK);
    assert!(
        core.contains("upgrade_Order_V1_V2"),
        "the generated total upgrade must be present:\n{core}"
    );
    assert!(
        core.contains("downgrade_Order_V2_V1"),
        "the generated partial downgrade must be present:\n{core}"
    );
    // The frozen predecessor is a real rung type the ladder converts through.
    assert!(
        core.contains("Order.V1"),
        "the frozen rung type `Order.V1` must be minted:\n{core}"
    );
}

// Editing a shipped rung in place moves its committed shape digest, which is a
// compile error carrying the frozen-format message and a caret at the rung.
#[test]
fn frozen_rung_edit_is_a_compile_error() {
    // A sealed V1 whose committed digest does not match its shape: exactly the
    // state a rung reaches when its fields are edited after it shipped.
    let edited = "\
import Wire (..)

stable Order {
  V1 = { id: Int, qty: Int, sym: String } frozen \"0000000000000000\",
  V2 = { ..V1, tif: Int = 0 }
}
";
    let full = with_prelude(edited);
    let err = prism::check(&full).expect_err("a drifted frozen rung must be rejected");
    assert!(
        matches!(err, Error::Type(TypeError::Other { .. })),
        "expected a type error, got: {err}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("frozen format `Order.V1` changed shape") && msg.contains("wire --accept"),
        "the rejection must be the frozen-format message with a reseat hint, got: {msg}"
    );
    // The caret lands on the edited V1 rung, not a later use.
    let span = err.primary_span().expect("the frozen error carries a span");
    let want = line_of(&full, full.find("V1 = ").expect("V1 rung present"));
    assert_eq!(
        line_of(&full, span.start),
        want,
        "the error must point at the edited rung: {err}"
    );
}

// A never-shipped rung (no `frozen` badge) is not gated: the block compiles, and
// `prism wire --accept` is what seals it.
#[test]
fn unsealed_rung_is_not_gated() {
    prism::check(&with_prelude(BLOCK)).expect("an unsealed block compiles");
}

// The block round-trips through the parser and formats idempotently, badge and
// all.
#[test]
fn formats_idempotently() {
    let sealed = "\
import Wire (..)

stable Order {
  V1 = { id: Int, qty: Int, sym: String } frozen \"377ee9c637d0924c\",
  V2 = { ..V1, tif: Int = 0 }
}
";
    let once = format(sealed).expect("the block formats");
    let twice = format(&once).expect("the formatted block re-formats");
    assert_eq!(
        once, twice,
        "format must be idempotent:\n{once}\n---\n{twice}"
    );
    assert!(
        once.contains("frozen \"377ee9c637d0924c\""),
        "the per-rung golden must survive formatting:\n{once}"
    );
}
