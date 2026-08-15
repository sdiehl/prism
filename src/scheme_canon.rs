//! The canonical-scheme contract: one versioned spelling for "these two
//! checkers agree on this declaration's type".
//!
//! The bootstrap workbench compares the authoritative Rust checker against the
//! self-hosted shadow checker declaration by declaration. Each side prints a
//! scheme; agreement is string equality. That only means anything if both sides
//! print the *same function* of the type, so the function is pinned here as a
//! named, versioned contract rather than an ad-hoc convention:
//!
//! - The input is the Rust checker's stable type spelling (the `tc-facts`
//!   `scheme` field).
//! - The only transformation is alpha-normalization of the binders introduced
//!   by a single leading `forall`: the i-th binder becomes `$i`, in both the
//!   binder list and the body. Occurrences are matched at identifier-token
//!   boundaries (maximal runs of ASCII alphanumerics and `_`), so `a` never
//!   rewrites part of `Maybe` or `a1`. Every other byte of the spelling is
//!   preserved.
//! - A spelling with no leading `forall` is already canonical.
//!
//! The shadow checker renders the same form structurally (`canon_scheme` in
//! `packages/tc/src/Bootstrap.pr`), and the two implementations are held
//! together by the version handshake in the bootstrap wire protocol and by the
//! end-to-end parity fixture. Any change to either side's output is a new
//! contract: bump [`SCHEME_CANON_CONTRACT`] and move both implementations in
//! the same commit. Downstream artifacts that state expected schemes
//! (structured refusals, pinned goal schemes) must speak this contract and
//! carry its identifier, never a raw checker spelling.

use std::collections::HashMap;

/// Version identifier for the canonical scheme spelling.
///
/// Stamped into the bootstrap report and demanded of the shadow checker's
/// protocol header, so a drifted normalization fails loudly instead of
/// quietly changing what "agrees" means.
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
