// `dump tier-explain`: the tier decision as prose. One sentence per definition
// naming the rung the cascade took and the recorded fact that put it there. It
// renders the same data `dump tier` and `dump effect-plan` already carry and
// decides nothing of its own, so these check that each sentence tracks the fact
// it claims, across rungs and across causes, plus determinism.

use prism::{dump, with_prelude, EffectStrategy};

fn explain(src: &str) -> String {
    dump("tier-explain", &with_prelude(src)).expect("tier-explain")
}

// The sentence for one definition, by name.
fn line(out: &str, name: &str) -> String {
    out.lines()
        .find(|l| l.starts_with(&format!("{name}:")))
        .unwrap_or_else(|| panic!("no sentence for `{name}` in:\n{out}"))
        .to_string()
}

// A program with no operation anywhere: the cheapest rung, reached with nothing
// in the way, which is the case that must still get a sentence.
const PURE_SRC: &str = "
fn double(x : Int) : Int = x * 2

fn main() = println(double(21))
";

// State by parameter passing: `tick` and `counter` still perform `get`/`put`,
// `run_counter` discharges them at its handler.
const STATE_SRC: &str = include_str!("../../examples/eff_state.pr");

// An escaping `Log` component sharing a program with a fused stream pipeline:
// the region is carved around the escape, so this program has both definitions
// on the rung and definitions off it.
const LOCAL_SRC: &str = include_str!("../../tests/cases/run/local_mono_combined.pr");

// The cheapest rung is explained too, and says that nothing was recorded against
// it rather than staying silent.
#[test]
fn pure_program_reports_the_cheapest_rung() {
    let out = explain(PURE_SRC);
    let rung = EffectStrategy::Pure.to_string();
    assert!(
        line(&out, "program").contains(&format!("lowered to {rung} because no recorded fact")),
        "a program with no operation must name the cheapest rung and no cause:\n{out}"
    );
    assert!(
        line(&out, "double").contains("performs no operation"),
        "a definition reaching no operation must say so:\n{out}"
    );
}

// The cause names the operations themselves, read off the latent map, and
// distinguishes a definition that still performs from one that handles what it
// performs.
#[test]
fn performing_and_handling_are_different_causes() {
    let out = explain(STATE_SRC);
    let rung = EffectStrategy::StateFusion.to_string();
    assert!(
        line(&out, "program").contains(&format!("lowered to {rung} because")),
        "the program sentence must name the rung the cascade took:\n{out}"
    );
    let tick = line(&out, "tick");
    assert!(
        tick.contains("still performs") && tick.contains("`get`") && tick.contains("`put`"),
        "a performing definition must name its operations:\n{out}"
    );
    assert!(
        line(&out, "run_counter").contains("handles every operation it can run"),
        "a definition that discharges what it reaches must say so, not `performs no operation`:\n{out}"
    );
}

// A confined region: the escape is the cause, and a definition the cascade left
// outside the region is reported as outside it rather than given a rung it never
// got.
#[test]
fn confined_region_names_the_escape_and_the_definitions_outside_it() {
    let out = explain(LOCAL_SRC);
    let rung = EffectStrategy::LocalPartial.to_string();
    assert!(
        line(&out, "program").contains(&format!("lowered to {rung} because `logged`"))
            && line(&out, "program").contains("escape"),
        "the program sentence must name the escaping definition:\n{out}"
    );
    assert!(
        line(&out, "logged").contains(&format!("lowered to {rung}")),
        "the escaping definition is in the region:\n{out}"
    );
    assert!(
        line(&out, "square").contains(&format!("stays off the {rung} path")),
        "a definition outside the region must not claim the rung:\n{out}"
    );
    assert!(
        line(&out, "smap").contains("captures an effectful computation"),
        "a capturing definition must report its capture:\n{out}"
    );
}

// Every sentence is one of the two forms, and every definition the plan covers
// gets exactly one.
#[test]
fn every_line_is_one_sentence() {
    for src in [PURE_SRC, STATE_SRC, LOCAL_SRC] {
        for l in explain(src).lines().filter(|l| !l.is_empty()) {
            assert!(
                l.contains(" because ") && l.ends_with('.'),
                "not a cause sentence: {l}"
            );
        }
    }
}

// The dump is a pure function of the source: two runs are byte-identical.
#[test]
fn tier_explain_is_deterministic() {
    assert_eq!(explain(LOCAL_SRC), explain(LOCAL_SRC));
}
