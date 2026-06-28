// The mid-level optimization tier (`src/core/opt/`) must actually fire. These
// guard that dictionary specialization and newtype erasure transform the Core,
// so a future change cannot silently degrade them into no-ops. Behavior is
// pinned separately by the parity oracle; this pins that the optimization
// happened at all.

fn core(src: &str) -> String {
    prism::dump("core", &prism::with_prelude(src)).expect("core dump")
}

// A constrained function applied to a concrete instance specializes to a clone
// that calls the instance method directly, rather than projecting it from a
// passed dictionary cell. The clone names carry a `$sp` tag and the dispatch
// becomes a direct `i@<instance>@<method>` call.
#[test]
fn dictionary_specialization_inlines_dispatch() {
    let src = std::fs::read_to_string("examples/classes.pr").expect("read classes.pr");
    let c = core(&src);
    assert!(c.contains("$sp"), "no specialized clone was generated");
    assert!(
        c.contains("i@showInt@show"),
        "specialization did not turn typeclass dispatch into a direct instance-method call"
    );
}

// A newtype's one-field box is erased: neither a construction nor a match of its
// constructor survives into Core. `Wrap` (capitalized) cannot collide with a
// generated function name, so its absence is exactly the erased box.
#[test]
fn newtype_box_is_erased() {
    let c = core(
        "newtype Wrap = Wrap(Int)\n\
         fn unwrap(w : Wrap) : Int = match w of { Wrap(n) => n }\n\
         fn main() = println(unwrap(Wrap(42)))",
    );
    assert!(!c.contains("Wrap("), "newtype box was not erased");
}
