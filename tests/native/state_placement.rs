// Where a `var` sits relative to a multishot delimiter decides what the second
// resumption sees, and no lowering may change it. One program, one choice
// handler, one mutation: a cell allocated outside the handler is shared by both
// resumptions (`[2, 2]`), a cell allocated under it belongs to the captured
// continuation and is restored for each (`[2, 1]`). The interpreter's answer is
// pinned, then every forced floor, with and without var erasure, at both ends of
// the optimizer, must observe the same.

use std::path::Path;

use prism::{EffectTier, OptLevel};

use crate::support::{check_native_parity, interpreted, require_cc, source};

const FIXTURE: &str = "tests/fixtures/language/multishot/state_placement.pr";

#[test]
fn placement_decides_what_a_resumption_sees() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE);
    assert_eq!(interpreted(&source(&path)), "[2, 2]\n[2, 1]\n");
}

#[test]
fn every_floor_keeps_the_placement() {
    require_cc();
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE);
    let roots = prism::default_roots(Path::new("."));
    let mut fails = Vec::new();
    for &tier in &EffectTier::ALL {
        for erasures in [true, false] {
            for opt in [OptLevel::O0, OptLevel::O2] {
                let mut cfg = crate::forced(tier, erasures);
                cfg.update_flags(|flags| flags.opt_level = opt);
                let tag = format!("placement-{}-{erasures}-{opt:?}", tier.label());
                if let Err(e) = check_native_parity(&path, &tag, |full, bin| {
                    prism::build_on(full, &roots, bin, &cfg)
                }) {
                    fails.push(e);
                }
            }
        }
    }
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}
