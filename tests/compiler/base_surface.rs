// The Base ring golden: the always-on prelude's export surface.
//
// Base is the ring that is available without an import: the prelude's own
// definitions plus the handful of `Data.*` modules it re-opens with glob imports
// (see `lib/prelude.pr`). Std is everything else, reached with an explicit
// `import` and distributed as a pinned content-addressed root (see
// `tests/stdlib_hash.rs`, `prism::stdlib_hash`).
//
// This checks Base's surface as a committed golden so accidental growth fails
// loudly in review: a new prelude definition, a new glob-imported module, or a
// newly exported name from one of those modules changes this snapshot. "1.0"
// means this surface is frozen behind a deprecation window; keeping it under a
// golden is how that freeze is enforced mechanically rather than by vigilance.
//
// Regenerate deliberately with: INSTA_UPDATE=always cargo test --test compiler base_surface

// The Base surface is whatever an empty program sees in scope once the prelude
// is prepended: `check` resolves the prelude's glob imports, so the resolved
// program carries every Base value, type, class, and effect. Capturing it here,
// sorted, is the frozen prelude API.
#[test]
fn base_export_surface() {
    let checked = prism::check(prism::with_prelude("").as_str()).expect("prelude checks");

    // The compiler synthesizes one dictionary datatype and constructor per class
    // (`names::dict_ctor`); those are elaboration representation, not user-facing
    // surface, so a change to the dictionary encoding must not read as Base growth.
    let dict_ctors: std::collections::BTreeSet<String> = checked
        .classes
        .keys()
        .map(|c| prism::names::dict_ctor(c.as_str()))
        .collect();

    let mut lines: Vec<String> = Vec::new();
    for d in &checked.decls {
        lines.push(format!("value {}", d.name));
    }
    for name in checked.data.keys() {
        if !dict_ctors.contains(name) {
            lines.push(format!("type  {name}"));
        }
    }
    for name in checked.ctors.keys() {
        if !dict_ctors.contains(name) {
            lines.push(format!("ctor  {name}"));
        }
    }
    for sym in checked.classes.keys() {
        lines.push(format!("class {}", sym.as_str()));
    }
    for name in checked.eff_ops.keys() {
        lines.push(format!("effop {name}"));
    }
    lines.sort();
    lines.dedup();
    insta::with_settings!({
        snapshot_path => "../snapshots",
        prepend_module_to_snapshot => false,
    }, {
        insta::assert_snapshot!("base_surface__base_export_surface", lines.join("\n"));
    });
}
