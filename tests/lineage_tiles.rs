//! End-to-end regression for the `examples/lineage_tiles` byte pipeline: the four
//! lineage verbs (`run --record --lineage`, `lineage why`, `diff`, `lineage
//! verify --replay`) composed over a real committed example. The pipeline reads a
//! JSON config and three raw byte tiles, writes a canonical `summary.json`, and
//! prints a digest; the run is a pure function of the fixtures, so its lineage is
//! stable and a one-byte edit to a single tile moves exactly that tile's node plus
//! the outputs that depend on it.

use std::path::{Path, PathBuf};
use std::process::{self, Command};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};
use std::{env, fs};

const fn prism_bin() -> &'static str {
    env!("CARGO_BIN_EXE_prism")
}

// The example's committed directory, the source of the fixtures each test copies.
fn example_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/lineage_tiles")
}

// The one deterministic digest and canonical summary the pipeline produces from
// the committed fixtures, pinned so a regression in Json/Bytes surfaces here.
const DIGEST: &str = "tiles=3 bytes=24 above=11 sum=2804";
const SUMMARY: &str = "{\"threshold\":128,\"tiles\":[\
    {\"above\":3,\"count\":8,\"histogram\":[3,2,2,1],\"name\":\"north\",\"sum\":744},\
    {\"above\":4,\"count\":8,\"histogram\":[1,3,3,1],\"name\":\"south\",\"sum\":1040},\
    {\"above\":4,\"count\":8,\"histogram\":[4,0,0,4],\"name\":\"delta\",\"sum\":1020}],\
    \"total\":{\"above\":11,\"count\":24,\"sum\":2804}}";

// The first byte of `north.gray`, and the one-byte edit the diff step applies. The
// committed tile starts 0x10; bumping it to 0x11 keeps the histogram bucket but
// nudges the sum, so stdout and summary.json move without adding or removing nodes.
const NORTH_ORIGINAL: [u8; 8] = [0x10, 0x20, 0x30, 0x40, 0x60, 0x80, 0xa0, 0xc8];
const NORTH_EDITED: [u8; 8] = [0x11, 0x20, 0x30, 0x40, 0x60, 0x80, 0xa0, 0xc8];

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let mut path = env::temp_dir();
        path.push(format!(
            "prism-lineage-tiles-{tag}-{}-{nanos}-{n}",
            process::id()
        ));
        fs::create_dir_all(path.join("tiles")).unwrap();
        Self { path }
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

// Copy the committed pipeline, config, and tiles into a fresh working directory so
// each test runs hermetically and never mutates the checked-in fixtures.
fn stage() -> TempDir {
    let src = example_dir();
    let dir = TempDir::new("run");
    for name in ["pipeline.pr", "config.json"] {
        fs::copy(src.join(name), dir.path.join(name)).unwrap();
    }
    for tile in ["north.gray", "south.gray", "delta.gray"] {
        fs::copy(
            src.join("tiles").join(tile),
            dir.path.join("tiles").join(tile),
        )
        .unwrap();
    }
    dir
}

fn prism(dir: &Path, args: &[&str]) -> process::Output {
    Command::new(prism_bin())
        .current_dir(dir)
        .args(args)
        .output()
        .expect("runs prism")
}

// Record a run in `dir`, writing the given replay and lineage sidecar names, and
// require it succeeded and produced the pinned digest and canonical summary.
fn record(dir: &Path, replay: &str, lineage: &str) {
    let out = prism(
        dir,
        &[
            "run",
            "pipeline.pr",
            "--record",
            replay,
            "--lineage",
            lineage,
        ],
    );
    assert!(
        out.status.success(),
        "record failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        String::from_utf8_lossy(&out.stdout).contains(DIGEST),
        "digest missing: {}",
        String::from_utf8_lossy(&out.stdout)
    );
    assert_eq!(
        fs::read_to_string(dir.join("summary.json")).unwrap().trim(),
        SUMMARY,
        "summary.json is not the canonical encoding"
    );
}

// The whole four-verb loop over the real example: record, explain the write,
// verify by replay, then edit one tile and diff.
#[test]
fn four_verb_loop_over_the_tiles_pipeline() {
    let dir = stage();
    let p = dir.path.as_path();

    // 1. record.
    record(p, "run.replay", "old.plineage");

    // 2. `lineage why summary.json`: the write explains itself from the sidecar,
    // naming the config and the tiles it read.
    let why = prism(p, &["lineage", "why", "old.plineage", "summary.json"]);
    assert!(
        why.status.success(),
        "why failed: {}",
        String::from_utf8_lossy(&why.stderr)
    );
    let why_out = String::from_utf8_lossy(&why.stdout);
    assert!(
        why_out.contains("why written file summary.json"),
        "why names the write: {why_out}"
    );
    for input in [
        "input-file: config.json",
        "input-file: tiles/north.gray",
        "input-file: tiles/south.gray",
        "input-file: tiles/delta.gray",
    ] {
        assert!(why_out.contains(input), "why names {input}: {why_out}");
    }

    // 3. `lineage verify --replay`: a fresh run reproduces its trace, stdout, and
    // file digests.
    let verify = prism(p, &["lineage", "verify", "old.plineage", "--replay"]);
    assert!(
        verify.status.success(),
        "verify --replay failed: {}",
        String::from_utf8_lossy(&verify.stderr)
    );
    assert!(
        String::from_utf8_lossy(&verify.stdout).contains("replay matches the sidecar"),
        "verify reports what it checked"
    );

    // 4. edit one tile, re-record, and diff: exactly that tile plus its downstream
    // move; the other tiles and the config are preserved; nothing is added/removed.
    fs::write(p.join("tiles/north.gray"), NORTH_EDITED).unwrap();
    let out = prism(
        p,
        &[
            "run",
            "pipeline.pr",
            "--record",
            "run.replay",
            "--lineage",
            "new.plineage",
        ],
    );
    assert!(out.status.success(), "re-record failed");

    let diff = prism(p, &["diff", "old.plineage", "new.plineage"]);
    assert!(
        !diff.status.success(),
        "a moved node must make diff exit nonzero so it can gate CI"
    );
    let d = String::from_utf8_lossy(&diff.stdout);
    for moved in [
        "moved    input-file tiles/north.gray",
        "moved    trace",
        "moved    stdout",
        "moved    file-write summary.json",
    ] {
        assert!(d.contains(moved), "diff must report `{moved}`:\n{d}");
    }
    for same in [
        "same     input-file config.json",
        "same     input-file tiles/south.gray",
        "same     input-file tiles/delta.gray",
    ] {
        assert!(d.contains(same), "diff must preserve `{same}`:\n{d}");
    }
    assert!(
        d.contains("0 added, 0 removed"),
        "the edit moves nodes but adds/removes none:\n{d}"
    );

    // Restoring the tile makes the run reproduce the original lineage byte for byte.
    fs::write(p.join("tiles/north.gray"), NORTH_ORIGINAL).unwrap();
    record(p, "run.replay", "restored.plineage");
    assert_eq!(
        fs::read_to_string(p.join("old.plineage")).unwrap(),
        fs::read_to_string(p.join("restored.plineage")).unwrap(),
        "restoring the tile restores the sidecar exactly"
    );
}
