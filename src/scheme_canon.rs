//! Versioned canonical spelling used to compare checker output.
//!
//! Rust and the self-hosted checker compare schemes as strings under this
//! contract:
//!
//! - Input is the stable `tc-facts` scheme spelling.
//! - A single leading `forall` is alpha-normalized by renaming its binders to
//!   `$0`, `$1`, and so on at identifier boundaries.
//! - A spelling with no leading `forall` is already canonical.
//!
//! The bootstrap protocol and parity fixture pin both implementations. Changes
//! require a [`SCHEME_CANON_CONTRACT`] bump in both checkers.

use std::collections::HashMap;

/// Version identifier for the canonical scheme spelling.
///
/// Stamped into the bootstrap report and demanded of the shadow checker's
/// protocol header, so a drifted normalization is rejected.
pub const SCHEME_CANON_CONTRACT: &str = "prism-scheme-canon-v1";

const FORALL_PREFIX: &str = "forall ";
const BINDER_BODY_SEPARATOR: &str = ". ";

/// Normalize a stable type spelling to the canonical scheme contract.
#[must_use]
pub fn canonical_scheme(scheme: &str) -> String {
    let Some(rest) = scheme.strip_prefix(FORALL_PREFIX) else {
        return scheme.to_owned();
    };
    let Some((binders, body)) = rest.split_once(BINDER_BODY_SEPARATOR) else {
        return scheme.to_owned();
    };
    let names: Vec<_> = binders.split_whitespace().collect();
    let replacements: HashMap<_, _> = names
        .iter()
        .enumerate()
        .map(|(index, name)| (*name, format!("${index}")))
        .collect();
    let mut normalized = String::with_capacity(body.len());
    let mut token = String::new();
    let flush = |token: &mut String, out: &mut String| {
        if token.is_empty() {
            return;
        }
        if let Some(replacement) = replacements.get(token.as_str()) {
            out.push_str(replacement);
        } else {
            out.push_str(token);
        }
        token.clear();
    };
    for ch in body.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            token.push(ch);
        } else {
            flush(&mut token, &mut normalized);
            normalized.push(ch);
        }
    }
    flush(&mut token, &mut normalized);
    let canonical_binders = (0..names.len())
        .map(|index| format!("${index}"))
        .collect::<Vec<_>>()
        .join(" ");
    format!("forall {canonical_binders}. {normalized}")
}

#[cfg(test)]
mod tests {
    use super::canonical_scheme;

    // The committed golden for contract v1: representative spellings and their
    // exact canonical forms. A diff here is a contract change and requires a
    // version bump on both the Rust and shadow-checker sides.
    #[test]
    fn golden_canonical_spellings() {
        let golden = [
            ("Int", "Int"),
            ("(Int) -> Bool", "(Int) -> Bool"),
            ("forall a. (a) -> a", "forall $0. ($0) -> $0"),
            (
                "forall a b. (a, Maybe(b)) -> a",
                "forall $0 $1. ($0, Maybe($1)) -> $0",
            ),
            (
                "forall a e. (a) -> Unit ! {IO | e}",
                "forall $0 $1. ($0) -> Unit ! {IO | $1}",
            ),
            (
                "forall e a. ((a) -> a ! {Tick, e}, a) -> a ! {Tick, e}",
                "forall $0 $1. (($1) -> $1 ! {Tick, $0}, $1) -> $1 ! {Tick, $0}",
            ),
            (
                "forall a. (List(a), (a) -> Bool) -> List(a)",
                "forall $0. (List($0), ($0) -> Bool) -> List($0)",
            ),
        ];
        for (input, expected) in golden {
            assert_eq!(canonical_scheme(input), expected, "for input {input:?}");
        }
    }

    // Canonicalization is a projection: applying it twice is applying it once.
    // The live-report counterpart (every `rust` fact in a bootstrap report is
    // its own canonical form) rides `tests/bootstrap.rs`.
    #[test]
    fn canonicalization_is_idempotent() {
        let spellings = [
            "Int",
            "(Int) -> Bool",
            "forall a b. (a, Maybe(b)) -> a",
            "forall a e. (a) -> Unit ! {IO | e}",
            "forall e a. ((a) -> a ! {Tick, e}, a) -> a ! {Tick, e}",
            "forall $0. ($0) -> $0",
        ];
        for spelling in spellings {
            let once = canonical_scheme(spelling);
            assert_eq!(canonical_scheme(&once), once, "for input {spelling:?}");
        }
    }

    // Alpha-variant inputs collapse to one canonical form; binder names cannot
    // leak into the contract.
    #[test]
    fn binder_names_are_erased() {
        let variants = [
            "forall a b. (a, Maybe(b)) -> a",
            "forall x y. (x, Maybe(y)) -> x",
            "forall t0 t1. (t0, Maybe(t1)) -> t0",
        ];
        let expected = "forall $0 $1. ($0, Maybe($1)) -> $0";
        for variant in variants {
            assert_eq!(canonical_scheme(variant), expected, "for input {variant:?}");
        }
    }

    // Replacement happens only at identifier-token boundaries: a binder that is
    // a prefix, suffix, or infix of another token never rewrites it.
    #[test]
    fn replacement_respects_token_boundaries() {
        assert_eq!(
            canonical_scheme("forall a. (Va, aV, a_a, a1) -> a"),
            "forall $0. (Va, aV, a_a, a1) -> $0"
        );
    }
}
