//! Effect-row checking discipline: a function's effect row is made *equal* to its
//! expected row by scoped-label unification, and a function generalizes with its
//! own latent row left open (`default_open_rows`), so a pure function fits an
//! effectful slot by *solving* that row variable rather than by silent widening.
//! These pin the discriminating behavior that this discipline gives.

use std::path::Path;

use prism::{check_on, default_roots, with_prelude};

fn checks(src: &str) -> Result<(), String> {
    let roots = default_roots(Path::new("."));
    check_on(&with_prelude(src), &roots)
        .map(|_| ())
        .map_err(|e| e.render_plain(src, "<test>"))
}

// A pure function passed where an effectful function is expected. The pure
// function generalizes with an open latent row, so it fits the slot by solving
// that row variable to `{Beep}`, without a subsumption step.
const WIDENS: &str = "\
effect Beep\n\
\x20 ctl beep(Int) : Unit\n\
fn use_it(f : (Int) -> Int ! {Beep}) : !{Beep} Int = f(3)\n\
fn pure_fn(x) = x + 1\n\
fn go() : !{Beep} Int = use_it(pure_fn)\n";

#[test]
fn accepts_pure_via_row_solving() {
    assert!(
        checks(WIDENS).is_ok(),
        "a pure function must fit an effectful slot by solving its open latent row \
         (row-quantified generalization), not by widening"
    );
}

// Ordinary effect code that never relies on widening: a row-polymorphic
// higher-order function applied to an effectful argument. The row variable is
// solved by unification, so this must be accepted just like any effect use.
const POLY: &str = "\
effect Beep\n\
\x20 ctl beep(Int) : Unit\n\
fn apply(f, x) = f(x)\n\
fn boom(n) : !{Beep} Int =\n\
\x20 beep(n)\n\
\x20 n\n\
fn go(n) : !{Beep} Int = apply(boom, n)\n";

#[test]
fn accepts_row_polymorphic_use() {
    assert!(
        checks(POLY).is_ok(),
        "ordinary row-polymorphic effect use must be accepted"
    );
}
