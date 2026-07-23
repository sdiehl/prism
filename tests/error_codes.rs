//! Error-code catalogue guard: every diagnostic identity owns a distinct,
//! well-formed code.
//!
//! Codes live in two places. `src/error/code.rs` defines the phase, lexer,
//! parser, resolver, codegen, runtime, IO, and internal codes as named constants.
//! `src/error/diag.rs` assigns a code to each `ErrKind` variant in the
//! `ErrKind::code()` match. A code is a permanent external identity, so two
//! distinct diagnostics must never share one. The unit test in `code.rs` checks
//! only its own constants against a hand-maintained list; this guard covers the
//! far larger `ErrKind::code()` table too, and pins that the two catalogues stay
//! disjoint, so a copy-pasted arm reusing a live code fails here instead of
//! shipping two errors under one identity.
//!
//! `ErrKind::code()` arms that read `code::SOME_CONST` are references to a named
//! code, not new assignments, so they carry no literal and are not counted twice.

use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;

fn read(rel: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel);
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("reading {rel}: {e}"))
}

/// Every `Ennnn` literal on a line, in first-seen order.
fn codes_on(line: &str) -> Vec<String> {
    let bytes = line.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'"'
            && i + 6 <= bytes.len()
            && bytes[i + 1] == b'E'
            && bytes[i + 2..i + 6].iter().all(u8::is_ascii_digit)
            && bytes.get(i + 6) == Some(&b'"')
        {
            out.push(line[i + 1..i + 6].to_string());
            i += 7;
        } else {
            i += 1;
        }
    }
    out
}

/// `code -> the source lines that assign it`, so a collision names both sites.
fn assign(src: &str, only_match_arms: bool, into: &mut BTreeMap<String, Vec<String>>) {
    for line in src.lines() {
        // In diag.rs, count only the `=> "Ennnn"` match arms of `code()`, not an
        // `Ennnn` that might appear in a message or doc string elsewhere.
        if only_match_arms && !line.contains("=>") {
            continue;
        }
        for code in codes_on(line) {
            into.entry(code).or_default().push(line.trim().to_string());
        }
    }
}

#[test]
fn every_error_code_is_unique_and_well_formed() {
    let mut seen: BTreeMap<String, Vec<String>> = BTreeMap::new();
    assign(&read("src/error/code.rs"), false, &mut seen);
    assign(&read("src/error/diag.rs"), true, &mut seen);

    // Non-vacuous: the named catalogue plus the per-kind table is well over a
    // hundred codes; a scan that found almost none would silently pass.
    assert!(
        seen.len() > 100,
        "found only {} error codes; the catalogue scan is not matching the source",
        seen.len()
    );

    let collisions: Vec<String> = seen
        .iter()
        .filter(|(_, sites)| sites.len() > 1)
        .map(|(code, sites)| {
            format!(
                "  {code} assigned by {} sites:\n    {}",
                sites.len(),
                sites.join("\n    ")
            )
        })
        .collect();
    assert!(
        collisions.is_empty(),
        "an error code is assigned to more than one diagnostic identity.\n{}\n\nA code is a \
         permanent identity: give the new diagnostic its own code, or reference the existing \
         one via its `code::` constant rather than re-typing the literal.",
        collisions.join("\n")
    );
}
