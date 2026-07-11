// The mid-level optimization tier (`src/core/opt/`) must actually fire. These
// guard that dictionary specialization and newtype erasure transform the Core,
// so a future change cannot silently degrade them into no-ops. Behavior is
// checked separately by the parity oracle; this checks that the optimization
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
        c.contains("i@shapeCircle@area"),
        "specialization did not turn typeclass dispatch into a direct instance-method call"
    );
}

// A newtype's one-field box is erased: neither a construction nor a match of its
// constructor survives into Core. `Wrap` (capitalized) cannot collide with a
// generated function name, so its absence is exactly the erased box.
#[test]
fn newtype_box_is_erased() {
    let c = core(
        r"newtype Wrap = Wrap(Int)
fn unwrap(w : Wrap) : Int = match w of { Wrap(n) => n }
fn main() = println(unwrap(Wrap(42)))",
    );
    assert!(!c.contains("Wrap("), "newtype box was not erased");
}

// Core Lint is clean over the whole compilable corpus: the optimized Core every
// example and run-case lowers to has no escaped binders or dangling references.
// This is the inter-pass sanity net, run here unconditionally so CI always
// lints what the optimizer produces.
#[test]
fn core_lint_clean_on_corpus() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut checked = 0;
    for dir in ["examples", "tests/cases/run", "tests/cases"] {
        let Ok(entries) = std::fs::read_dir(root.join(dir)) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) != Some("pr") {
                continue;
            }
            let src = std::fs::read_to_string(&path).unwrap();
            // Only files that compile produce Core; skip error cases / library
            // files with no `main` rather than asserting they compile.
            if let Ok(core) = prism::core_of(&src) {
                if let Err(errs) =
                    prism::core::lint_core(&core, prism::core::PassStage::PreLowering)
                {
                    panic!("{}: ill-formed Core:\n{}", path.display(), errs.join("\n"));
                }
                checked += 1;
            }
        }
    }
    assert!(checked > 0, "corpus produced no lintable Core");
}

// The `--passes` spec parser: a two-stage spec lands each pass in the right
// section, in order; a bare list defaults to the pre stage; and the validation
// rules each reject their bad input with a message.
#[test]
fn pass_spec_parse() {
    use prism::{CorePass, PassSpec};

    let spec = PassSpec::parse("pre:EraseNewtypes,Specialize;late:Simplify").expect("valid spec");
    assert_eq!(
        spec.pre,
        vec![CorePass::EraseNewtypes, CorePass::Specialize]
    );
    assert_eq!(spec.late, vec![CorePass::Simplify]);

    // A bare comma-list with no marker is the pre stage.
    let bare = PassSpec::parse("EraseNewtypes,Specialize").expect("valid bare spec");
    assert_eq!(
        bare.pre,
        vec![CorePass::EraseNewtypes, CorePass::Specialize]
    );
    assert!(bare.late.is_empty());

    assert!(PassSpec::parse("pre:Bogus").is_err());
    // A late-only pass placed in the pre section is rejected.
    assert!(PassSpec::parse("pre:Simplify").is_err());
    // Pre passes out of order are rejected.
    assert!(PassSpec::parse("pre:Specialize,EraseNewtypes").is_err());
    // An empty spec is rejected.
    assert!(PassSpec::parse("").is_err());
}

// The optimization tier reaches a fixed point: re-running specialization on the
// already-optimized Core changes nothing (no new clones, no further reductions).
// A pass that churned its own output would fail here.
#[test]
fn specialization_is_idempotent() {
    let src = std::fs::read_to_string("examples/classes.pr").expect("read classes.pr");
    let once = prism::core_of(&src).expect("core_of");
    let twice = prism::core::specialize(&once);
    assert_eq!(
        prism::core::pp_core(&once),
        prism::core::pp_core(&twice),
        "specialization is not idempotent on its own output"
    );
}
