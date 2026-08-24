// The shadow-parser comparison receipt, produced from a run rather than
// hand-written.
//
// `parser_parity.rs` proves the two parsers agree on fixtures, grammar edges,
// and generated mutation matrices. This lane runs them against committed code:
// the stdlib, the examples, the documentation sources, and the language cases,
// which is the corpus a real parser change is judged on. It then records what
// the run established as one content-addressed receipt, so a later run over the
// same parser and the same corpus is a reproduction check instead of a fresh
// unrelated assertion.
//
// The receipt is split the way the store is: the comparison and the
// compiler-work counters go to the immutable certificate layer, where identical
// bytes are the proof; the wall times go to the mutable decision layer, where a
// second run is allowed to differ.
//
// The corpus is bounded by default and complete under
// `PRISM_PARSER_RECEIPT_FULL=1`. The bound is a deterministic stride, never a
// random sample, and the file count rides in the receipt so a reader always
// knows which lane produced the bytes they are holding.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::{env, fs};

use prism::core::work;
use prism::store::disk::{Store, Written};
use prism::store::receipt::{self, Comparison, ShadowReceipt};
use prism::{default_roots, dump_on, interpret_io_on_with_args, with_prelude, Config, Root};
use prism::{PhaseTally, TimingSink};

use crate::support::TempDir;

// The differential witness and the phase whose artifact it consumes, shared with
// the parity lane next door.
const WITNESS: &str = "tests/fixtures/parser/parity.pr";
const SURFACE_PHASE: &str = "surface-syntax";
// The canonical Core identity, and the phase whose dump runs the whole front end
// under a caller's config. They are two dumps because they must be: the identity
// surface is deliberately config-independent, so it cannot be the run that
// carries the instrument.
const CORE_HASH_PHASE: &str = "core-hash";
const CORE_PHASE: &str = "core";
const OK: &str = "ok";

// Where committed Prism lives. Every corpus file the comparison covers comes
// from one of these, in this order, sorted within each.
const CORPUS_DIRS: [&str; 4] = ["lib", "examples", "docs/examples", "tests/cases"];

// The two parsers, each named by what it is made of. Symmetric on purpose: a
// receipt that identified one by its sources and the other by a version string
// would attest a comparison only half of which a later reader could re-derive,
// and the half left out is the authority.
const AUTHORITY_SOURCES: [&str; 4] = [
    "crates/prism-syntax/src/grammar.lalrpop",
    "crates/prism-syntax/src/ast.rs",
    "crates/prism-syntax/src/lex",
    "crates/prism-syntax/src/parse",
];
const AUTHORITY_EXT: &str = "rs";
const SHADOW_SOURCES: [&str; 1] = ["lib/std/Syntax"];
const PRISM_EXT: &str = "pr";

// The default lane's size, and the knob that runs the whole corpus instead. The
// witness is interpreted Prism, so a complete pass is a nightly-scale run and
// the per-change lane takes a deterministic stride through the same list.
const DEFAULT_CORPUS_FILES: usize = 40;
const FULL_CORPUS_ENV: &str = "PRISM_PARSER_RECEIPT_FULL";
// Fewer compared files than this and the lane has stopped being evidence,
// whatever verdict it reports.
const MIN_CORPUS_FILES: usize = 24;

// Where a divergence is left for a human to read. Under `target/` so it is
// ignored by git and swept by `cargo clean`, and a named directory rather than a
// temporary because an artifact that vanishes with the failing process is not a
// located one.
const DIVERGENCE_DIR: &str = "target/parser-divergence";
const AUTHORITY_SUFFIX: &str = "authority.json";
const SHADOW_SUFFIX: &str = "shadow.json";
// How many diverging files the failure message names. Every divergence is
// written out and the reported count is always exact; this bounds the message,
// not the evidence.
const MAX_NAMED_DIVERGENCES: usize = 12;

// The divergences the committed corpus currently shows, each named by the
// construct it stands for. The Rust parser is authoritative, so a row here is a
// gap in the Prism parser and a debt against parser authority, never a tolerated
// difference. The list is empty: over the whole committed corpus the two parsers
// agree byte for byte, spans and synth bits included.
//
// The set is watched in both directions: a divergence that is not listed fails
// the lane, and a complete sweep also fails when a listed file starts agreeing,
// so the list cannot outlive the gap it records. Empty, the first half is the
// whole gate, and a row may only ever be added with the construct that earned
// it.
const KNOWN_DIVERGENCES: [(&str, &str); 0] = [];

// The front end runs over these to charge the work counters. Named rather than
// taken off the top of a sorted directory, because the counters only need a real
// compile and an alphabetical prefix would silently hand this lane whichever
// example happens to be the most expensive one in the tree.
const COMPILE_SOURCES: [&str; 3] = [
    "examples/factorial.pr",
    "examples/greet.pr",
    "examples/fold.pr",
];

// The phase the receipt requires evidence of. Elaboration always runs and always
// descends, so a zero here means the instrument did not fire, which is exactly
// the vacuity the receipt refuses to attest.
const EXERCISED: [&str; 1] = ["elaborate"];

fn root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

fn roots() -> Vec<Root> {
    default_roots(root())
}

// Hash a list of labelled byte strings. Length-prefixed so no concatenation of
// two entries can spell a third.
fn identity(parts: &[(&str, &[u8])]) -> String {
    let mut h = blake3::Hasher::new();
    for (label, bytes) in parts {
        h.update(&(label.len() as u64).to_le_bytes());
        h.update(label.as_bytes());
        h.update(&(bytes.len() as u64).to_le_bytes());
        h.update(bytes);
    }
    h.finalize().to_hex().to_string()
}

// Every file with `ext` under `path`, sorted, so a file list is a function of
// the tree and not of directory iteration order. A `path` that names a file is
// taken whatever its extension: the extension filter is how a directory is
// narrowed, not a second opinion about a file the caller named outright.
fn files_under(path: &Path, ext: &str) -> Vec<PathBuf> {
    if path.is_file() {
        return vec![path.to_path_buf()];
    }
    let mut out = Vec::new();
    let Ok(entries) = fs::read_dir(path) else {
        return out;
    };
    let mut entries: Vec<PathBuf> = entries.filter_map(|e| e.ok().map(|e| e.path())).collect();
    entries.sort();
    for entry in entries {
        if entry.is_dir() {
            out.extend(files_under(&entry, ext));
        } else if entry.extension().is_some_and(|e| e == ext) {
            out.push(entry);
        }
    }
    out
}

fn pr_files(dir: &Path) -> Vec<PathBuf> {
    files_under(dir, PRISM_EXT)
}

// A parser's artifact identity: the hash of the sources it is built from, each
// entry labelled by its path so moving a file is a change and not a coincidence.
fn artifact_identity(sources: &[&str], ext: &str) -> String {
    let files: Vec<PathBuf> = sources
        .iter()
        .flat_map(|s| files_under(&root().join(s), ext))
        .collect();
    assert!(
        !files.is_empty(),
        "a parser's sources must be findable: {sources:?}"
    );
    let read: Vec<(String, Vec<u8>)> = files
        .iter()
        .map(|p| (rel(p), fs::read(p).expect("read a parser source")))
        .collect();
    let parts: Vec<(&str, &[u8])> = read
        .iter()
        .map(|(name, bytes)| (name.as_str(), bytes.as_slice()))
        .collect();
    identity(&parts)
}

// Whether this run sweeps every committed source rather than a bounded stride.
// Only a complete sweep may judge the watched set stale, since a stride cannot
// distinguish a fixed parser from an unsampled file.
fn full_corpus() -> bool {
    env::var_os(FULL_CORPUS_ENV).is_some()
}

fn corpus_files() -> Vec<PathBuf> {
    let all: Vec<PathBuf> = CORPUS_DIRS
        .iter()
        .flat_map(|dir| pr_files(&root().join(dir)))
        .collect();
    if full_corpus() || all.len() <= DEFAULT_CORPUS_FILES {
        return all;
    }
    // A stride rather than a prefix: a prefix would sample one directory and
    // call it the corpus, and a stride keeps every source kind represented while
    // staying a pure function of the sorted list.
    let stride = all.len().div_ceil(DEFAULT_CORPUS_FILES);
    all.into_iter().step_by(stride).collect()
}

fn rel(path: &Path) -> String {
    path.strip_prefix(root())
        .unwrap_or(path)
        .display()
        .to_string()
}

// One corpus file's surface artifact, or `None` when the authoritative parser
// rejects it. A rejection is not a comparison: the negative corpus lane next
// door is what pins refusal behavior, and counting a refusal here would let a
// corpus of unparseable files report perfect agreement.
fn surface_artifact(path: &Path, cfg: &Config) -> Option<String> {
    let source = fs::read_to_string(path).ok()?;
    dump_on(SURFACE_PHASE, &source, &roots(), cfg).ok()
}

struct Compared {
    /// `(relative path, authority artifact bytes)`, in corpus order.
    artifacts: Vec<(String, String)>,
    /// The shadow's own bytes per file: equal to the authority's where the two
    /// agreed, and the encoding the witness wrote out where they did not.
    shadow: Vec<Vec<u8>>,
    /// `(relative path, the witness's verdict line)` for each file the two
    /// parsers encoded differently, in corpus order.
    diverged: Vec<(String, String)>,
    /// Files the authoritative parser refused, and so were never compared.
    refused: usize,
}

// Leave a divergence somewhere a human can open it: both encodings of the file,
// side by side, under a stable path. Returns that directory.
fn divergence_dir() -> PathBuf {
    let dir = root().join(DIVERGENCE_DIR);
    // A stale encoding from an earlier run beside a fresh one is worse than no
    // encoding at all, so the directory is emptied rather than added to.
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("make a directory for the diverging encodings");
    dir
}

// Judge a run's divergences against the watched set. Every divergence is a debt
// against parser authority; what this decides is only whether the run found a
// debt nobody had written down, or paid one nobody had crossed off.
fn judge(compared: &Compared) {
    let known: BTreeSet<&str> = KNOWN_DIVERGENCES.iter().map(|(name, _)| *name).collect();

    let fresh: Vec<&(String, String)> = compared
        .diverged
        .iter()
        .filter(|(name, _)| !known.contains(name.as_str()))
        .collect();
    if !fresh.is_empty() {
        let mut named: Vec<String> = fresh
            .iter()
            .take(MAX_NAMED_DIVERGENCES)
            .map(|(name, verdict)| format!("  {name}: {verdict}"))
            .collect();
        let rest = fresh.len() - named.len();
        if rest > 0 {
            named.push(format!("  ... and {rest} more, all written out"));
        }
        panic!(
            "the Prism parser diverged from the Rust parser on {} file(s) that are not \
             on the watched list:\n{}\n\
             both encodings of each are under {}/ as *.{AUTHORITY_SUFFIX} and *.{SHADOW_SUFFIX}",
            fresh.len(),
            named.join("\n"),
            DIVERGENCE_DIR
        );
    }

    if !full_corpus() {
        return;
    }
    // A complete sweep saw every committed source, so anything still listed but
    // no longer diverging is a gap that has been closed and a row that must go.
    let compared_names: BTreeSet<&str> = compared
        .artifacts
        .iter()
        .map(|(name, _)| name.as_str())
        .collect();
    let diverged_names: BTreeSet<&str> = compared
        .diverged
        .iter()
        .map(|(name, _)| name.as_str())
        .collect();
    let stale: Vec<String> = KNOWN_DIVERGENCES
        .iter()
        .filter(|(name, _)| !diverged_names.contains(name))
        .map(|(name, construct)| {
            let why = if compared_names.contains(name) {
                "now agrees"
            } else {
                "was never compared (moved, deleted, or refused by the authority)"
            };
            format!("  {name} ({construct}): {why}")
        })
        .collect();
    assert!(
        stale.is_empty(),
        "the watched divergence list is stale; remove {} row(s) from KNOWN_DIVERGENCES:\n{}",
        stale.len(),
        stale.join("\n")
    );
}

// Run the witness over the corpus in one batch and collect both sides' bytes.
fn compare(dir: &TempDir, cfg: &Config) -> Compared {
    let files = corpus_files();
    assert!(!files.is_empty(), "the corpus must not be empty");

    let mut artifacts = Vec::new();
    let mut refused = 0;
    for path in &files {
        match surface_artifact(path, cfg) {
            Some(json) => artifacts.push((rel(path), json)),
            None => refused += 1,
        }
    }
    // The lane's own anti-vacuity floor. A walker that stopped finding sources, or
    // a corpus the authority now refuses wholesale, would otherwise leave a
    // one-file comparison reporting perfect agreement.
    assert!(
        artifacts.len() >= MIN_CORPUS_FILES,
        "only {} of {} corpus file(s) reached the comparison ({refused} refused); \
         a receipt over that is not evidence",
        artifacts.len(),
        files.len()
    );

    // The witness takes filesystem paths, so each artifact is staged beside a
    // mismatch path it may write its own encoding to.
    let staged: Vec<(PathBuf, PathBuf)> = artifacts
        .iter()
        .enumerate()
        .map(|(i, (_, json))| {
            let artifact = dir.join(format!("corpus-{i}.surface-syntax.json"));
            let mismatch = dir.join(format!("corpus-{i}.mismatch.json"));
            fs::write(&artifact, json).expect("stage a surface artifact");
            (artifact, mismatch)
        })
        .collect();
    let pairs: Vec<(&Path, &Path)> = staged
        .iter()
        .map(|(a, m)| (a.as_path(), m.as_path()))
        .collect();
    let verdicts = run_witness(&pairs, cfg);
    assert_eq!(
        verdicts.len(),
        artifacts.len(),
        "one verdict per compared file"
    );

    let mut shadow = Vec::new();
    let mut diverged = Vec::new();
    let mut out = None;
    for (i, verdict) in verdicts.iter().enumerate() {
        let (name, authority) = &artifacts[i];
        if verdict == OK {
            // Agreement means the shadow produced these exact bytes, so the
            // authority's artifact is the shadow's artifact.
            shadow.push(authority.clone().into_bytes());
            continue;
        }
        // The witness writes its own encoding to the mismatch path; where it
        // could not, its verdict line is what the run has to say about the file.
        let bytes = fs::read(&staged[i].1).unwrap_or_else(|_| verdict.clone().into_bytes());
        let dir = out.get_or_insert_with(divergence_dir);
        let stem = name.replace(['/', '\\'], "-");
        fs::write(dir.join(format!("{stem}.{AUTHORITY_SUFFIX}")), authority)
            .expect("leave the authority's encoding");
        fs::write(dir.join(format!("{stem}.{SHADOW_SUFFIX}")), &bytes)
            .expect("leave the shadow's encoding");
        diverged.push((name.clone(), verdict.clone()));
        shadow.push(bytes);
    }
    Compared {
        artifacts,
        shadow,
        diverged,
        refused,
    }
}

fn run_witness(pairs: &[(&Path, &Path)], cfg: &Config) -> Vec<String> {
    let src = fs::read_to_string(root().join(WITNESS)).expect("differential witness source");
    let full = with_prelude(&src);
    let args = pairs
        .iter()
        .flat_map(|(a, m)| [a.display().to_string(), m.display().to_string()])
        .collect();
    let mut sink = Vec::new();
    interpret_io_on_with_args(&full, &roots(), &mut sink, &mut &b""[..], cfg, args)
        .unwrap_or_else(|error| panic!("differential witness run: {error}"));
    String::from_utf8(sink)
        .expect("utf8 witness output")
        .lines()
        .filter(|line| !line.is_empty())
        .map(str::to_string)
        .collect()
}

// Run the front end over a few examples with the work counters live, and return
// what each phase accumulated together with the folded Core identity.
fn compile_for_counters() -> (BTreeMap<&'static str, PhaseTally>, String) {
    // Process-wide by design (the counters are global atomics), which is safe
    // here because the suite runs a process per test. Under a threaded runner a
    // concurrent compile would inflate the deltas, so this lane asserts that the
    // counters fired rather than pinning them to an exact figure.
    work::enable();
    let sink = TimingSink::new();
    let cfg = Config {
        timing: Some(sink.clone()),
        ..Config::from_env()
    };
    let plain = Config::from_env();
    let mut hashes = Vec::new();
    for path in COMPILE_SOURCES.map(|s| root().join(s)) {
        let Ok(source) = fs::read_to_string(&path) else {
            continue;
        };
        let source = with_prelude(&source);
        // The identity dump takes the pre-optimizer Core under a default config on
        // purpose, so that a hash never depends on an env-toggled pass. That also
        // makes it deaf to the instrument, so the counters come from a second run
        // of the same source through the phase that does thread a config.
        let Ok(hash) = dump_on(CORE_HASH_PHASE, &source, &roots(), &plain) else {
            continue;
        };
        if dump_on(CORE_PHASE, &source, &roots(), &cfg).is_ok() {
            hashes.push(format!("{}\t{hash}", rel(&path)));
        }
    }
    assert!(
        !hashes.is_empty(),
        "the front end produced no Core identity to record"
    );
    let core = identity(&[("core", hashes.join("\n").as_bytes())]);
    (sink.tallies(), core)
}

#[test]
fn the_corpus_comparison_is_recorded_as_a_receipt() {
    let dir = TempDir::new("parser-receipt", "corpus");
    let cfg = Config::from_env();
    let compared = compare(&dir, &cfg);
    let (tallies, core_hash) = compile_for_counters();

    let corpus_manifest: Vec<String> = compared
        .artifacts
        .iter()
        .map(|(name, _)| name.clone())
        .collect();
    let authority_bytes = compared
        .artifacts
        .iter()
        .map(|(_, json)| json.as_bytes().to_vec())
        .collect::<Vec<_>>()
        .concat();

    let comparison = Comparison {
        authority: artifact_identity(&AUTHORITY_SOURCES, AUTHORITY_EXT),
        shadow: artifact_identity(&SHADOW_SOURCES, PRISM_EXT),
        corpus: identity(&[("corpus", corpus_manifest.join("\n").as_bytes())]),
        corpus_files: compared.artifacts.len(),
        syntax_hash_authority: identity(&[("surface", &authority_bytes)]),
        syntax_hash_shadow: identity(&[("surface", &compared.shadow.concat())]),
        core_hash,
        divergences: compared.diverged.len(),
    };
    let receipt = ShadowReceipt::new(comparison, &tallies, &EXERCISED)
        .expect("the run exercised a phase and covered a corpus");

    // The comparison is the gate; the receipt only records it. A divergence is a
    // located artifact, never a fallback quietly accepted as success: the failure
    // names the files and leaves both encodings of each one on disk.
    judge(&compared);
    // Byte identity and a zero count are the same fact seen twice, so a run that
    // reports one without the other has an encoder or a hasher that is lying.
    assert_eq!(
        receipt.comparison.syntax_hash_authority == receipt.comparison.syntax_hash_shadow,
        receipt.comparison.divergences == 0,
        "the syntax hashes and the divergence count disagree about whether the run agreed"
    );
    // Anti-vacuity, restated where a reader of this file can see it: the
    // counters describe work that happened.
    let elaborate = receipt
        .phases
        .get(EXERCISED[0])
        .expect("an exercised phase");
    assert!(elaborate.visits > 0 && elaborate.invocations > 0);
    assert!(receipt.max_depth > 0, "a compile descends");

    let store = Store::open_or_create(dir.store_root()).expect("open a store");
    receipt::emit(&store, &receipt).expect("record the comparison");
    // The reproduction check the store performs for free: the same run, recorded
    // twice, must be the same bytes.
    assert_eq!(receipt::emit(&store, &receipt).unwrap(), Written::Hit);
    receipt::put_timing(&store, &receipt.subject, &tallies).expect("record the run's readings");

    let stored = receipt::get(&store, &receipt.subject)
        .expect("read back")
        .expect("a receipt was written")
        .expect("it decodes");
    assert_eq!(stored, receipt);
    // The other half, under the same subject: a reading for every phase the run
    // timed, whether or not it charged the Core counters.
    let timed = receipt::get_timing(&store, &receipt.subject).expect("read back the readings");
    assert_eq!(timed.len(), tallies.len());
    assert!(timed.iter().any(|(phase, _, _)| phase == EXERCISED[0]));

    eprintln!(
        "shadow parse: {} file(s) compared ({}), {} refused by the authority, \
         {} watched divergence(s), {} phase(s) charged, deepest descent {}",
        receipt.comparison.corpus_files,
        if full_corpus() { "complete" } else { "stride" },
        compared.refused,
        receipt.comparison.divergences,
        receipt.phases.len(),
        receipt.max_depth
    );
    for (name, verdict) in &compared.diverged {
        eprintln!("  diverged {name}: {verdict}");
    }
    for (phase, work) in &receipt.phases {
        eprintln!(
            "  {phase}: {} invocation(s), {} visit(s), {} rebuilt",
            work.invocations, work.visits, work.rebuilt
        );
    }
}
