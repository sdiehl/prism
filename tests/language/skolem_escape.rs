// Regression coverage for the skolem-escape soundness fix. The mono
// fast path in `inst` may solve an existential to a candidate type only when
// every variable that type names is bound to the existential's left; a `Uni`
// skolem introduced under an inner `forall` sits to its right, so solving an
// outer existential to it would let the skolem outlive its quantifier. Two
// guarantees have regression coverage here: the offending program is rejected at the call
// that introduces the escape (not at a later use site), and no top-level scheme
// anywhere in the corpus prints an unquantified skolem.

use std::collections::BTreeSet;
use std::path::PathBuf;
use std::{env, fs};

use prism::{Error, TypeError};

// The canonical repro: `\(y) -> x` is checked against `forall a. (a) -> a`, so
// its body `x` is forced to the rigid `a`; but `x` is `bad`'s parameter, bound
// outside the quantifier. Solving it to `a` escapes the skolem, so the call is
// rejected. No prelude, so byte offsets line up with the source below.
const REPRO: &str = r"fn useid(g: forall a. (a) -> a): Int = g(10)
fn bad(x) =
  let _ = useid(\(y) -> x)
  x
";

fn line_of(src: &str, byte: usize) -> usize {
    src[..byte].matches('\n').count() + 1
}

#[test]
fn escape_is_rejected_at_the_offending_call() {
    let err = prism::check(REPRO).expect_err("skolem escape must be rejected");
    // A type error whose message is the rigid skolem `a` failing to absorb an
    // outer type, not some unrelated failure. (`in_fn` routes the underlying
    // mismatch onto the coded catalogue as a `Kind` carrying the wrapped
    // message, so match on the catalogue variant and text, not the pre-wrap one.)
    assert!(
        matches!(err, Error::Type(TypeError::Kind(_))),
        "expected a type error, got: {err}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("type mismatch") && msg.contains("expected a"),
        "the rejection must be the skolem `a` failing to absorb an outer type, got: {msg}"
    );
    // The caret lands inside the `useid(\(y) -> x)` call on line 3, where the
    // escape is introduced, not at the bare `x` on line 4.
    let span = err.primary_span().expect("a mismatch carries a span");
    assert_eq!(
        line_of(REPRO, span.start),
        3,
        "the error must point at the offending call (line 3), not a later use: {err}"
    );
}

// Every `.pr` under the corpus directories that type-checks. Error-demo cases
// under `tests/cases` (which are meant to be rejected) drop out via the
// `check` filter, exactly as the snapshot oracle treats them.
fn corpus_files() -> Vec<PathBuf> {
    let root = env!("CARGO_MANIFEST_DIR");
    let mut out = Vec::new();
    for dir in ["examples", "tests/cases", "tests/cases/run", "lib"] {
        let Ok(entries) = fs::read_dir(format!("{root}/{dir}")) else {
            continue;
        };
        for e in entries.flatten() {
            let path = e.path();
            if path.extension().and_then(|s| s.to_str()) == Some("pr") {
                out.push(path);
            }
        }
    }
    out.sort();
    out
}

// A well-formed generalized scheme binds every variable it mentions under its
// own `forall`/`forall`-row, so a free `Type::Var`/`EffRow::Var` left over is an
// escaped skolem. Sweeping the whole corpus asserts the fix holds not just on
// the repro but everywhere: no printed top-level scheme carries an unquantified
// skolem. (`check` prepends the prelude, so the prelude's own schemes are swept
// too on every file.)
#[test]
fn no_unquantified_skolem_in_corpus_schemes() {
    for path in corpus_files() {
        let src = prism::with_prelude(&fs::read_to_string(&path).unwrap());
        let Ok(checked) = prism::check(&src) else {
            continue;
        };
        for d in &checked.decls {
            let mut tvars = BTreeSet::new();
            d.ty.free_ty_vars(&mut tvars);
            let mut rvars = BTreeSet::new();
            d.ty.free_row_vars(&mut rvars);
            assert!(
                tvars.is_empty() && rvars.is_empty(),
                "{}: `{}` prints an unquantified skolem: {} (type vars {tvars:?}, row vars {rvars:?})",
                path.display(),
                d.name,
                d.ty.show()
            );
        }
    }
}
