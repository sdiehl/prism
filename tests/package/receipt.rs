//! The shadow-parser comparison receipt: its codec, its anti-vacuity refusals,
//! and the two store layers it lands in.
//!
//! The property the tests exist for is the one the receipt is built around: the
//! deterministic half is content-addressed, so re-emitting an unchanged
//! comparison is a hit and re-emitting a changed one is an alarm, while the
//! machine readings stay in the mutable layer where a second run is allowed to
//! differ.

use std::collections::BTreeMap;
use std::time::Duration;

use prism::core::work::WorkCounts;
use prism::store::cert::{check_cert, CertStatus, CLAIM_SHADOW_PARSE_AGREED_NAME};
use prism::store::disk::Written;
use prism::store::receipt::{self, Comparison, ReceiptError, ShadowReceipt};
use prism::store::CodecError;
use prism::PhaseTally;
use rstest::rstest;

use crate::support::TempDir;

const AUTHORITY: &str = "parser-rust@6f1d2c";
const SHADOW: &str = "parser-prism@a19e04";
const CORPUS: &str = "corpus@3b7c55";
const SYNTAX_HASH: &str = "syntax@e40012";
const CORE_HASH: &str = "core@771ab3";

fn agreeing() -> Comparison {
    Comparison {
        authority: AUTHORITY.to_string(),
        shadow: SHADOW.to_string(),
        corpus: CORPUS.to_string(),
        corpus_files: 42,
        syntax_hash_authority: SYNTAX_HASH.to_string(),
        syntax_hash_shadow: SYNTAX_HASH.to_string(),
        core_hash: CORE_HASH.to_string(),
        divergences: 0,
    }
}

const fn tally(invocations: usize, ms: u64, visits: u64, rebuilt: u64, depth: u64) -> PhaseTally {
    PhaseTally {
        invocations,
        wall: Duration::from_millis(ms),
        work: WorkCounts {
            visits,
            rebuilt,
            max_depth: depth,
        },
    }
}

// A plausible shape: a front-end phase that charges nothing on the Core counters,
// and two Core phases that do.
fn tallies() -> BTreeMap<&'static str, PhaseTally> {
    BTreeMap::from([
        ("parse", tally(2, 3, 0, 0, 0)),
        ("elaborate", tally(2, 20, 312, 0, 3)),
        ("opt.pre", tally(1, 15, 7801, 7645, 115)),
    ])
}

fn receipt() -> ShadowReceipt {
    ShadowReceipt::new(agreeing(), &tallies(), &["opt.pre"]).unwrap()
}

#[test]
fn round_trips_through_the_envelope() {
    let r = receipt();
    assert_eq!(receipt::decode(&receipt::encode(&r)), Ok(r));
}

#[test]
fn drops_phases_that_charged_nothing_and_keeps_those_that_did() {
    let r = receipt();
    // `parse` works on the AST and never charges the Core counters; a row of zeros
    // beside rows that mean something would read as a measurement.
    assert!(!r.phases.contains_key("parse"));
    let opt = r.phases.get("opt.pre").expect("an exercised phase");
    assert_eq!((opt.invocations, opt.visits, opt.rebuilt), (1, 7801, 7645));
    // Elaboration charges for its handler scans and rebuilds nothing, which is a
    // fact about the phase rather than a silent instrument.
    assert_eq!(r.phases["elaborate"].rebuilt, 0);
    assert_eq!(r.max_depth, 115);
}

#[rstest]
// A phase the caller named as exercised but whose counter stayed zero: either it
// did not run or the instrument did not see it, and a receipt may claim neither.
#[case(&["parse"], ReceiptError::VacuousPhase("parse".to_string()))]
// A phase that is not in the tallies at all reads the same way.
#[case(&["rc"], ReceiptError::VacuousPhase("rc".to_string()))]
fn refuses_to_claim_a_phase_it_did_not_exercise(
    #[case] exercised: &[&str],
    #[case] expected: ReceiptError,
) {
    assert_eq!(
        ShadowReceipt::new(agreeing(), &tallies(), exercised),
        Err(expected)
    );
}

#[test]
fn refuses_an_empty_corpus_and_a_run_that_exercised_nothing() {
    let mut empty_corpus = agreeing();
    empty_corpus.corpus_files = 0;
    assert_eq!(
        ShadowReceipt::new(empty_corpus, &tallies(), &[]),
        Err(ReceiptError::EmptyCorpus)
    );
    let silent = BTreeMap::from([("parse", tally(1, 3, 0, 0, 0))]);
    assert_eq!(
        ShadowReceipt::new(agreeing(), &silent, &[]),
        Err(ReceiptError::NoPhases)
    );
}

#[test]
fn identity_covers_the_compared_inputs_and_not_the_counters() {
    let base = receipt();

    // Different work over the same inputs is the same comparison, so it must
    // collide rather than land under a subject nobody would look for.
    let mut moved = tallies();
    moved.insert("opt.pre", tally(1, 15, 9000, 8800, 115));
    let heavier = ShadowReceipt::new(agreeing(), &moved, &["opt.pre"]).unwrap();
    assert_eq!(heavier.subject, base.subject);
    assert_ne!(receipt::encode(&heavier), receipt::encode(&base));

    // A different corpus is a different comparison.
    let mut other = agreeing();
    other.corpus = "corpus@ffffff".to_string();
    let elsewhere = ShadowReceipt::new(other, &tallies(), &["opt.pre"]).unwrap();
    assert_ne!(elsewhere.subject, base.subject);
}

#[test]
fn an_unchanged_rerun_is_a_hit_and_a_moved_counter_is_an_alarm() {
    let dir = TempDir::new("receipt", "emit");
    let store = prism::store::disk::Store::open_or_create(dir.store_root()).unwrap();
    let r = receipt();

    assert_eq!(receipt::emit(&store, &r).unwrap(), Written::New);
    // The reproduction proof: the same parser over the same corpus, re-attested.
    assert_eq!(receipt::emit(&store, &r).unwrap(), Written::Hit);

    let mut moved = tallies();
    moved.insert("opt.pre", tally(1, 15, 9000, 8800, 115));
    let heavier = ShadowReceipt::new(agreeing(), &moved, &["opt.pre"]).unwrap();
    // Same inputs, different work. The immutable layer refuses it, which is the
    // event the receipt exists to catch and not a bug to route around.
    assert!(receipt::emit(&store, &heavier).is_err());

    assert_eq!(receipt::get(&store, &r.subject).unwrap(), Some(Ok(r)));
}

#[test]
fn check_reports_agreement_divergence_and_absence_distinctly() {
    let dir = TempDir::new("receipt", "check");
    let store = prism::store::disk::Store::open_or_create(dir.store_root()).unwrap();

    let r = receipt();
    assert!(matches!(
        receipt::check(&store, &r.subject),
        CertStatus::Absent
    ));
    receipt::emit(&store, &r).unwrap();
    let CertStatus::Verified(note) = receipt::check(&store, &r.subject) else {
        panic!("an agreeing receipt verifies");
    };
    assert!(note.contains(CLAIM_SHADOW_PARSE_AGREED_NAME) && note.contains("42"));

    let mut split = agreeing();
    split.syntax_hash_shadow = "syntax@000bad".to_string();
    split.divergences = 3;
    let diverged = ShadowReceipt::new(split, &tallies(), &["opt.pre"]).unwrap();
    receipt::emit(&store, &diverged).unwrap();
    let CertStatus::Unverifiable(note) = receipt::check(&store, &diverged.subject) else {
        panic!("a divergent receipt is reported, never dressed up as a pass");
    };
    assert!(note.contains('3'));
}

#[test]
fn a_foreign_claim_reader_names_it_without_verifying_it() {
    let dir = TempDir::new("receipt", "foreign");
    let store = prism::store::disk::Store::open_or_create(dir.store_root()).unwrap();
    let r = receipt();
    receipt::emit(&store, &r).unwrap();
    // The one global claim number space at work: the parity reader decodes the
    // envelope and reports the claim as recognized rather than as corruption.
    let CertStatus::Unverifiable(note) = check_cert(&store, &r.subject) else {
        panic!("a receipt is well-formed to the parity reader, just not its claim");
    };
    assert!(note.contains(CLAIM_SHADOW_PARSE_AGREED_NAME));
}

#[test]
fn every_decode_is_total() {
    let good = receipt::encode(&receipt());
    // Every strict prefix, the empty slice included, is an error and not a panic.
    for cut in 0..good.len() {
        assert!(receipt::decode(&good[..cut]).is_err(), "prefix of {cut}");
    }
    let mut trailing = good;
    trailing.push(0);
    assert_eq!(receipt::decode(&trailing), Err(CodecError::TrailingBytes));
}

#[test]
fn timing_is_recorded_where_a_second_run_may_differ() {
    let dir = TempDir::new("receipt", "timing");
    let store = prism::store::disk::Store::open_or_create(dir.store_root()).unwrap();
    let r = receipt();
    receipt::emit(&store, &r).unwrap();

    assert!(receipt::get_timing(&store, &r.subject).unwrap().is_empty());
    receipt::put_timing(&store, &r.subject, &tallies()).unwrap();
    let rows = receipt::get_timing(&store, &r.subject).unwrap();
    assert_eq!(rows.len(), 3);
    assert_eq!(rows[0].0, "elaborate");
    assert_eq!(rows[0].1, 2);
    assert_eq!(rows[0].2, Duration::from_millis(20));

    // Two correct runs of the same comparison disagree here, and the layer takes
    // it. These readings therefore do not belong in the certificate.
    let mut slower = tallies();
    slower.insert("elaborate", tally(2, 97, 312, 0, 3));
    receipt::put_timing(&store, &r.subject, &slower).unwrap();
    let rows = receipt::get_timing(&store, &r.subject).unwrap();
    assert_eq!(rows[0].2, Duration::from_millis(97));
    // The attested half is untouched by the reading that moved.
    assert_eq!(receipt::get(&store, &r.subject).unwrap(), Some(Ok(r)));
}
