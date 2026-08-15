//! The effect-row operations pinned differentially against the checker.
//!
//! A seeded generator produces three program families, one per row operation:
//! merge (a body performing a shuffled, duplicated multiset of operations),
//! discharge (a `handle` over a performing helper), and absorb (an annotated
//! open-row parameter widened by the body's own performances). An executable
//! model computes each declaration's principal scheme from set algebra alone:
//! labels are sorted-unique, discharge is set subtraction by effect name, and
//! absorption is union threaded through the generalized tail. The checker's
//! `tc-facts` spelling, canonicalized through the versioned scheme contract,
//! must match the model byte for byte.

use std::collections::{BTreeSet, HashMap};
use std::fmt::Write as _;

use serde_json::Value;

/// Fixed generator seed: the corpus is a deterministic function of this value,
/// so a failure reproduces exactly.
const SEED: u64 = 0x51ab_c0de_2026_0814;
/// Generated cases per program family.
const CASES_PER_FAMILY: usize = 16;
/// Most operation performances in one generated body.
const MAX_PERFORMS: usize = 5;
/// The effect pool. Deliberately not declared in alphabetical order anywhere:
/// the model sorts, and the checker must agree independent of declaration and
/// performance order.
const EFFECTS: [&str; 6] = ["Umber", "Cobalt", "Jade", "Amber", "Sienna", "Quartz"];

/// `SplitMix64`: a tiny deterministic PRNG so the corpus needs no dependency.
struct SplitMix64(u64);

impl SplitMix64 {
    const fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, bound: usize) -> usize {
        let bound_u64 = u64::try_from(bound).expect("bound fits in u64");
        usize::try_from(self.next_u64() % bound_u64).expect("residue fits in usize")
    }
}

/// One generated declaration and the scheme the model expects for it.
struct Case {
    name: String,
    decl: String,
    expected: String,
}

fn op_call(effect: &str) -> String {
    format!("{}_op()", effect.to_lowercase())
}

/// The performing body: the operation calls summed onto `x`, or bare `x`.
fn body_sum(picks: &[&str]) -> String {
    let mut terms: Vec<String> = picks.iter().map(|effect| op_call(effect)).collect();
    terms.push("x".to_owned());
    terms.join(" + ")
}

/// The model's row spelling for an inferred closed row: nothing when empty,
/// otherwise the sorted-unique labels.
fn closed_row_suffix(labels: &BTreeSet<&str>) -> String {
    if labels.is_empty() {
        String::new()
    } else {
        let joined = labels.iter().copied().collect::<Vec<_>>().join(", ");
        format!(" ! {{{joined}}}")
    }
}

fn pick_multiset<'pool>(rng: &mut SplitMix64, count: usize) -> Vec<&'pool str> {
    (0..count)
        .map(|_| EFFECTS[rng.below(EFFECTS.len())])
        .collect()
}

/// Merge: performing a multiset of operations infers the sorted-unique closed
/// row of their effects.
fn merge_case(rng: &mut SplitMix64, index: usize) -> Case {
    let count = rng.below(MAX_PERFORMS + 1);
    let picks = pick_multiset(rng, count);
    let set: BTreeSet<&str> = picks.iter().copied().collect();
    let name = format!("merge_{index}");
    Case {
        decl: format!("fn {name}(x : Int) : Int = {}\n", body_sum(&picks)),
        expected: format!("(Int) -> Int{}", closed_row_suffix(&set)),
        name,
    }
}

/// Discharge: `handle` subtracts exactly the handled effect from the
/// performing helper's row. Returns the helper (a merge fact in its own
/// right) and the handling wrapper.
fn discharge_cases(rng: &mut SplitMix64, index: usize) -> (Case, Case) {
    let count = 1 + rng.below(MAX_PERFORMS);
    let picks = pick_multiset(rng, count);
    let set: BTreeSet<&str> = picks.iter().copied().collect();
    let index_in_set = rng.below(set.len());
    let handled = *set
        .iter()
        .nth(index_in_set)
        .expect("performed set is nonempty");
    let mut residual = set.clone();
    residual.remove(handled);
    let helper = format!("perform_{index}");
    let name = format!("discharge_{index}");
    let helper_case = Case {
        decl: format!("fn {helper}(x : Int) : Int = {}\n", body_sum(&picks)),
        expected: format!("(Int) -> Int{}", closed_row_suffix(&set)),
        name: helper,
    };
    let handler_case = Case {
        decl: format!(
            "fn {name}(x : Int) : Int =\n  handle perform_{index}(x) with\n    {}_op() resume k => k(1)\n",
            handled.to_lowercase()
        ),
        expected: format!("(Int) -> Int{}", closed_row_suffix(&residual)),
        name,
    };
    (helper_case, handler_case)
}

/// Absorb: a parameter annotated with an open row is widened to the union of
/// its labels and the body's own performances, threaded through the
/// generalized tail on both the parameter and the result.
fn absorb_case(rng: &mut SplitMix64, index: usize) -> Case {
    let annotated_count = 1 + rng.below(2);
    let annotated: BTreeSet<&str> = pick_multiset(rng, annotated_count).into_iter().collect();
    let performed_count = rng.below(3);
    let performed = pick_multiset(rng, performed_count);
    let union: BTreeSet<&str> = annotated
        .iter()
        .copied()
        .chain(performed.iter().copied())
        .collect();
    let annotation = annotated.iter().copied().collect::<Vec<_>>().join(", ");
    let mut terms: Vec<String> = vec!["g(x)".to_owned()];
    terms.extend(performed.iter().map(|effect| op_call(effect)));
    let body = terms.join(" + ");
    let widened = union.iter().copied().collect::<Vec<_>>().join(", ");
    let name = format!("absorb_{index}");
    Case {
        decl: format!(
            "fn {name}(g : (Int) -> Int ! {{{annotation} | e}}, x : Int) : Int = {body}\n"
        ),
        expected: format!(
            "forall $0. ((Int) -> Int ! {{{widened}, $0}}, Int) -> Int ! {{{widened}, $0}}"
        ),
        name,
    }
}

#[test]
fn inferred_rows_match_the_set_algebra_model() {
    let mut rng = SplitMix64(SEED);
    let mut source = String::new();
    for effect in EFFECTS {
        write!(
            source,
            "effect {effect}\n  {}_op() : Int\n\n",
            effect.to_lowercase()
        )
        .expect("writing to a String cannot fail");
    }
    let mut cases = Vec::new();
    for index in 0..CASES_PER_FAMILY {
        cases.push(merge_case(&mut rng, index));
    }
    for index in 0..CASES_PER_FAMILY {
        let (helper, handler) = discharge_cases(&mut rng, index);
        cases.push(helper);
        cases.push(handler);
    }
    for index in 0..CASES_PER_FAMILY {
        cases.push(absorb_case(&mut rng, index));
    }
    for case in &cases {
        source.push_str(&case.decl);
        source.push('\n');
    }
    source.push_str("fn main() : Int = 0\n");

    let dump = prism::dump("tc-facts", &source).expect("tc-facts dump succeeds");
    let report: Value = serde_json::from_str(&dump).expect("tc-facts is JSON");
    let schemes: HashMap<&str, &str> = report["decls"]
        .as_array()
        .expect("decls array")
        .iter()
        .map(|decl| {
            (
                decl["name"].as_str().expect("decl name"),
                decl["scheme"].as_str().expect("decl scheme"),
            )
        })
        .collect();

    for case in &cases {
        let scheme = schemes
            .get(case.name.as_str())
            .unwrap_or_else(|| panic!("no tc-facts entry for {}\n{}", case.name, case.decl));
        assert_eq!(
            prism::canonical_scheme(scheme),
            case.expected,
            "row disagreement on {}\n{}",
            case.name,
            case.decl
        );
    }
}
