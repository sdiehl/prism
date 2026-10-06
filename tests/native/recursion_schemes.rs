// `Control.Recursion` driven through effects: a tree mirrored as a parametric
// two-operation `Fold` effect, an `Unfold` handler supplying the coalgebra, and
// a direct `hylo` over the same pure pair. The materialized `cata(ana(seed))`
// and the direct form must agree under the interpreter and on every forced
// floor, and the direct form must allocate the layers it walks and nothing
// shaped like the tree it never builds.

use std::fs;
use std::path::{Path, PathBuf};

use prism::EffectTier;

use crate::support::{
    check_native_parity, interpreted, require_cc, source, stat_build_counters, ALLOCATED_SUFFIX,
    ALLOC_STATS,
};

const FIXTURE: &str = "tests/fixtures/language/recursion/scheme_effects.pr";

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE)
}

#[test]
fn materialized_and_direct_agree() {
    assert_eq!(
        interpreted(&source(&fixture())),
        "0: 1 1 true\n1: 5 5 true\n4: 1496 1496 true\n12: 22914881536 22914881536 true\n"
    );
}

#[test]
fn every_floor_agrees_with_the_interpreter() {
    require_cc();
    let path = fixture();
    let roots = prism::default_roots(Path::new("."));
    let mut fails = Vec::new();
    for &tier in &EffectTier::ALL {
        let cfg = crate::forced(tier, true);
        let tag = format!("recursion-{}", tier.label());
        if let Err(e) = check_native_parity(&path, &tag, |full, bin| {
            prism::build_on(full, &roots, bin, &cfg)
        }) {
            fails.push(e);
        }
    }
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}

// A full tree of depth `d` has `2^d` leaves and `2^d - 1` internal nodes. The
// direct form allocates one layer per node, two seeds per internal node, and
// the root seed: `2^(d+2) - 2` cells, with `map_layer`'s rebuilt layer reusing
// the one it consumed. Materializing would add a `Tree` cell per node.
#[test]
fn direct_form_allocates_only_its_layers() {
    require_cc();
    let text = fs::read_to_string(fixture()).unwrap();
    let head = &text[..text.find("fn report").unwrap()];
    for depth in [8_u32, 12] {
        let program = format!("{head}fn main() = println(direct((1, {depth})))\n");
        let cells = stat_build_counters(
            &prism::with_prelude(&program),
            &format!("recursion-direct-{depth}"),
            &[ALLOC_STATS],
            &[ALLOCATED_SUFFIX],
            prism::build,
        )
        .unwrap()[0];
        assert_eq!(cells, (1_i64 << (depth + 2)) - 2, "depth {depth}");
    }
}
