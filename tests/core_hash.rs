// Content-addressed Core hashing: a definition's hash names its behavior, not
// its spelling or position. These pin the load-bearing properties end to end,
// over real elaborated programs: name- and format-independence, dependency
// substitution into a Merkle DAG, propagation that touches exactly the affected
// closure, cycle hashing for mutual recursion, and structural sharing of
// identical definitions.

use std::collections::BTreeMap;

fn hashes(src: &str) -> BTreeMap<String, String> {
    prism::dump("core-hash", &prism::with_prelude(src))
        .expect("core-hash dump")
        .lines()
        .filter_map(|l| {
            l.split_once("  ")
                .map(|(h, n)| (n.to_string(), h.to_string()))
        })
        .collect()
}

fn h(src: &str, name: &str) -> String {
    hashes(src)
        .get(name)
        .cloned()
        .unwrap_or_else(|| panic!("no def `{name}`"))
}

// Renaming a local binder is invisible to the hash.
#[test]
fn local_names_are_erased() {
    let a = h(
        "fn k(n) =\n  let x = n + 1\n  x * x\nfn main() = println(k(3))",
        "k",
    );
    let b = h(
        "fn k(n) =\n  let y = n + 1\n  y * y\nfn main() = println(k(3))",
        "k",
    );
    assert_eq!(a, b);
}

// Renaming a callee leaves the caller's hash untouched (its dependency is
// substituted by hash, not by name), and the callee is identical up to its name.
#[test]
fn dependency_substitution_is_name_independent() {
    let a = hashes("fn inc(n) = n + 1\nfn caller(n) = inc(n) * 2\nfn main() = println(caller(3))");
    let b =
        hashes("fn bump(n) = n + 1\nfn caller(n) = bump(n) * 2\nfn main() = println(caller(3))");
    assert_eq!(a["caller"], b["caller"]);
    assert_eq!(a["inc"], b["bump"]);
}

// A behavioral change to the body changes the hash.
#[test]
fn behavior_changes_the_hash() {
    let a = h("fn f(n) = n + 1\nfn main() = println(f(0))", "f");
    let b = h("fn f(n) = n + 2\nfn main() = println(f(0))", "f");
    assert_ne!(a, b);
}

// Editing one definition rehashes exactly its transitive dependents and nothing
// else: `base` -> `g` -> `h` all move, the unrelated `other` is a cache hit.
#[test]
fn propagation_is_exactly_the_closure() {
    const P: &str = "fn base(n) = n + @\nfn g(n) = base(n) * 2\nfn h(n) = g(n) + 5\n\
                     fn other(n) = n * n\nfn main() = println(h(1) + other(1))";
    let a = hashes(&P.replace('@', "1"));
    let b = hashes(&P.replace('@', "2"));
    assert_ne!(a["base"], b["base"]);
    assert_ne!(a["g"], b["g"]);
    assert_ne!(a["h"], b["h"]);
    assert_eq!(a["other"], b["other"]);
}

// A mutually recursive group is hashed as a unit: members get distinct hashes,
// and renaming the whole cycle preserves them (name-independence through the
// SCC, the one path the corpus never exercises).
#[test]
fn mutual_recursion_is_hashed_and_name_independent() {
    let a = hashes(
        "fn ev(n) = if n == 0 then true else od(n - 1)\n\
         fn od(n) = if n == 0 then false else ev(n - 1)\nfn main() = println(ev(2))",
    );
    let b = hashes(
        "fn even2(n) = if n == 0 then true else odd2(n - 1)\n\
         fn odd2(n) = if n == 0 then false else even2(n - 1)\nfn main() = println(even2(2))",
    );
    assert_ne!(a["ev"], a["od"]);
    assert_eq!(a["ev"], b["even2"]);
    assert_eq!(a["od"], b["odd2"]);
}

// Two definitions with identical Core are the same entry: a user `fact` and the
// prelude's `factorial` (same body, different name) hash to one value.
#[test]
fn identical_definitions_share_a_hash() {
    let m =
        hashes("fn fact(n) = if n == 0 then 1 else n * fact(n - 1)\nfn main() = println(fact(5))");
    assert_eq!(m["fact"], m["factorial"]);
}
