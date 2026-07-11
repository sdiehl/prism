// The read-only face of the codebase-as-a-database: the dependency-graph queries
// and the structural-clone finder, both computed off the same content-hash
// substrate. These check the core semantics (transitive closure, direction,
// clone detection by behavior) over the real stdlib, not a toy.

use prism::resolve::default_roots;
use prism::{dump, query_on, with_prelude, Config};
use std::path::Path;

fn q(kind: &str, target: &str, src: &str) -> String {
    let full = with_prelude(src);
    let roots = default_roots(Path::new("."));
    query_on(kind, target, &full, &roots, &Config::from_env()).expect("query")
}

fn names(out: &str) -> Vec<String> {
    out.lines().skip(1).map(|l| l.trim().to_string()).collect()
}

// `dependents` is the transitive Merkle closure a change would force to re-check,
// so it is a superset of the direct `callers` and reaches indirect users.
#[test]
fn dependents_is_the_transitive_closure_of_callers() {
    let callers: Vec<String> = names(&q("callers", "map", ""));
    let dependents: Vec<String> = names(&q("dependents", "map", ""));
    assert!(callers.len() >= 3, "map should have several direct callers");
    for c in &callers {
        assert!(
            dependents.contains(c),
            "direct caller {c} missing from the transitive dependents"
        );
    }
    assert!(
        dependents.len() > callers.len(),
        "transitive dependents must reach beyond the direct callers"
    );
    // A definition never depends on or calls itself.
    assert!(!dependents.contains(&"Data.List.map".to_string()));
}

// `deps` walks the other direction: what a definition transitively needs.
#[test]
fn deps_walks_dependencies_not_dependents() {
    // `concat_map` is defined via `map` and `concat`, so both are in its closure.
    // Qualified, because the prelude re-exports an unqualified alias too.
    let tail = |d: &String| d.rsplit('.').next().unwrap_or("").to_string();
    let deps: Vec<String> = names(&q("deps", "Data.List.concat_map", ""))
        .iter()
        .map(&tail)
        .collect();
    assert!(deps.contains(&"map".to_string()), "deps: {deps:?}");
    assert!(deps.contains(&"flatten".to_string()), "deps: {deps:?}");
}

// `uses-type` finds definitions by a whole-token type match, so `Option` matches
// `Option(a)` in a signature but not a longer identifier that contains it.
#[test]
fn uses_type_matches_whole_type_tokens() {
    let hits = names(&q("uses-type", "Option", ""));
    assert!(hits.iter().any(|h| h.starts_with("Data.List.head")));
    assert!(hits.iter().any(|h| h.contains("list_to_option")));
}

// Structural duplicates are found by behavior, not name: a user `fact` with the
// prelude `factorial`'s body hashes to the same value and is reported as a clone.
#[test]
fn dupes_finds_structural_clones() {
    let src = "fn fact(n) = if n == 0 then 1 else n * fact(n - 1)\nfn main() = ()";
    let out = dump("dupes", &with_prelude(src)).expect("dupes");
    assert!(
        out.lines()
            .any(|l| l.contains("fact") && l.contains("factorial")),
        "fact/factorial clone not found in:\n{out}"
    );
}
