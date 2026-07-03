// The native sort kernel (`prism_sort_prim`) switches on a small-int kind tag
// that the elaborator emits from `names::SORT_PRIM_INSTANCES`. Nothing but a
// comment ties that table to the C `switch`, so a drifted tag would silently
// misorder one element type. This gate pins the correspondence end to end: for
// each primitive `Ord`, sort a list whose order DEPENDS on the tag (a signed
// negative, an unsigned value with the high bit set, a float needing the IEEE
// total-order transform, a bignum past i64) and diff the native binary against
// the interpreter, whose `SortPrim` ignores the tag and orders by runtime value.
// A wrong tag makes native disagree with the interpreter; a silently dropped
// specialization is caught by the `sort_prim` assertion on the lowered core.

use std::path::Path;
use std::process::Command;
use std::{env, fs};

mod common;
use common::require_cc;

// Each case: a label naming the kind under test and a `main` that prints the
// sorted list. The literals are chosen so the tag actually matters.
const CASES: &[(&str, &str)] = &[
    // Integer: bignum-aware merge (tag 0); a fixed-width tag would unbox the
    // bignum pointer as an integer. Negatives and a value past i64.
    (
        "Integer",
        "fn main() = println(sort([3, 0 - 1, 2, 100000000000000000000]))",
    ),
    // I64: signed radix (tag 1); an unsigned tag sorts -1 as a huge value.
    (
        "I64",
        "fn main() = println(sort([to_i64(3), to_i64(0 - 1), to_i64(2)]))",
    ),
    // U64: unsigned radix (tag 2); a signed tag reads the high-bit value as
    // negative and sorts it first.
    (
        "U64",
        "fn main() = println(sort([9223372036854775808u64, 1u64, 2u64]))",
    ),
    // Float: IEEE total-order radix (tag 3); an integer tag orders raw bit
    // patterns, misplacing the negative.
    ("Float", "fn main() = println(sort([3.5, 0.0 -. 1.2, 2.8]))"),
];

#[test]
fn native_sort_kind_matches_interpreter() {
    require_cc();
    let mut fails = Vec::new();
    for (label, src) in CASES {
        let full = prism::with_prelude(src);
        // Guard against a vacuous pass: the program must actually lower to the
        // native kernel, or native and interpreter would agree via the generic
        // merge sort without ever exercising a kind tag.
        let core = prism::dump("core", &full).expect("core dump");
        assert!(
            core.contains("sort_prim"),
            "{label}: sort did not specialize to the native kernel; the tag gate would be vacuous"
        );
        if let Err(e) = check(label, &full) {
            fails.push(e);
        }
    }
    assert!(
        fails.is_empty(),
        "sort kind tag mismatch:\n{}",
        fails.join("\n")
    );
}

fn check(label: &str, full: &str) -> Result<(), String> {
    let want = prism::interpret(full).unwrap().term;
    let bin = env::temp_dir().join(format!("prism_sortkind_{}_{label}", std::process::id()));
    prism::build(full, &bin).map_err(|e| format!("{label}: build failed: {e}"))?;
    let out = Command::new(&bin)
        .output()
        .map_err(|e| format!("{label}: spawn failed: {e}"))?;
    cleanup(&bin);
    let got = String::from_utf8_lossy(&out.stdout);
    if got != want {
        return Err(format!(
            "{label}: native disagrees with interpreter (a drifted kind tag):\n  \
             native: {got:?}\n  interp: {want:?}"
        ));
    }
    Ok(())
}

fn cleanup(bin: &Path) {
    for ext in ["bc", "ll"] {
        let _ = fs::remove_file(bin.with_extension(ext));
    }
    let _ = fs::remove_file(bin);
}
