//! Error-code catalogue guards: every diagnostic identity owns a distinct,
//! well-formed code and every live code has exactly one complete explanation.
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

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::PathBuf;
use std::sync::OnceLock;

use prism::cli::explain::{all, lookup};
use prism::error::{ERROR_CODE_DIGITS, ERROR_CODE_PREFIX};

const MIN_CATALOGUE_LEN: usize = 100;
const CODES_PER_FAILURE_LINE: usize = 8;
const FIRST_QUOTED_SEGMENT: usize = 1;
const QUOTED_SEGMENT_STRIDE: usize = 2;

fn read(rel: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel);
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("reading {rel}: {e}"))
}

/// Every `Ennnn` literal on a line, in first-seen order.
fn codes_on(line: &str) -> Vec<String> {
    line.split('"')
        .skip(FIRST_QUOTED_SEGMENT)
        .step_by(QUOTED_SEGMENT_STRIDE)
        .filter(|literal| {
            literal
                .strip_prefix(ERROR_CODE_PREFIX)
                .is_some_and(|digits| {
                    digits.len() == ERROR_CODE_DIGITS
                        && digits.bytes().all(|byte| byte.is_ascii_digit())
                })
        })
        .map(str::to_string)
        .collect()
}

fn assignments() -> &'static BTreeMap<String, Vec<String>> {
    static ASSIGNMENTS: OnceLock<BTreeMap<String, Vec<String>>> = OnceLock::new();
    ASSIGNMENTS.get_or_init(|| {
        let mut seen = BTreeMap::new();
        assign(
            &read("crates/prism-syntax/src/error/code.rs"),
            false,
            &mut seen,
        );
        assign(
            &read("crates/prism-syntax/src/error/diag.rs"),
            true,
            &mut seen,
        );
        assert!(
            seen.len() > MIN_CATALOGUE_LEN,
            "found only {} error codes; the catalogue scan is not matching the source",
            seen.len()
        );
        seen
    })
}

fn catalogue() -> BTreeSet<String> {
    assignments().keys().cloned().collect()
}

fn columns(codes: &[String]) -> String {
    codes
        .chunks(CODES_PER_FAILURE_LINE)
        .map(|chunk| format!("  {}", chunk.join(" ")))
        .collect::<Vec<_>>()
        .join("\n")
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
    let seen = assignments();

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

#[test]
fn every_catalogued_code_is_explained() {
    let missing: Vec<String> = catalogue()
        .into_iter()
        .filter(|code| lookup(code).is_none())
        .collect();
    assert!(
        missing.is_empty(),
        "{} diagnostic code(s) have no `prism explain` entry:\n{}\n\nEvery code a user can see \
         needs a title, prose, an example, and a fix in the matching band shard under \
         src/cli/explain/.",
        missing.len(),
        columns(&missing)
    );
}

#[test]
fn no_explanation_names_a_dead_code() {
    let catalogued = catalogue();
    let dead: Vec<String> = all()
        .map(|entry| entry.code.to_string())
        .filter(|code| !catalogued.contains(code))
        .collect();
    assert!(
        dead.is_empty(),
        "{} explanation(s) name a code the compiler no longer assigns:\n{}\n\nA retired code \
         keeps its prose only while some diagnostic still prints it; otherwise delete the entry.",
        dead.len(),
        columns(&dead)
    );
}

#[test]
fn no_code_is_explained_twice() {
    let mut seen = BTreeSet::new();
    let duplicates: Vec<String> = all()
        .map(|entry| entry.code.to_string())
        .filter(|code| !seen.insert(code.clone()))
        .collect();
    assert!(
        duplicates.is_empty(),
        "{} code(s) appear in more than one explain shard:\n{}\n\nLookup returns the first hit, \
         so a duplicate silently hides one of the two entries. Keep one, in the band shard that \
         owns the range.",
        duplicates.len(),
        columns(&duplicates)
    );
}

#[test]
fn every_explanation_is_fully_written() {
    let empty: Vec<String> = all()
        .filter_map(|entry| {
            let blank: Vec<&str> = [
                ("title", entry.title),
                ("prose", entry.prose),
                ("example", entry.example),
                ("fix", entry.fix),
            ]
            .into_iter()
            .filter(|(_, text)| text.trim().is_empty())
            .map(|(field, _)| field)
            .collect();
            if blank.is_empty() {
                None
            } else {
                Some(format!("  {}: empty {}", entry.code, blank.join(", ")))
            }
        })
        .collect();
    assert!(
        empty.is_empty(),
        "{} explanation(s) have an empty field:\n{}",
        empty.len(),
        empty.join("\n")
    );
}
