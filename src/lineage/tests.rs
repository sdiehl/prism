//! Cross-module behavioral tests over a synthetic run graph: explain, diff, verify,
//! logical-key stability, file-write observability, and answer-object JSON.

use std::path::Path;

use crate::lineage::provenance::{self, TraceDigest, EVENT_HASH_SCHEME};

use super::diff::{diff, DiffReport};
use super::explain::{why_output, why_world_state, Explanation, SelectedOutput};
use super::graph::{
    self, ArgvPayload, Edge, EdgeKind, FileWritePayload, InputFilePayload, LineageRoot, Node,
    NodeId, NodeKind, OutputPayload, RootRole, TracePayload, Variant, WorldForkPayload,
    WorldLawPayload, WorldStatePayload, WriteMode, STDOUT_SELECTOR,
};
use super::verify::{verify_run_replay, verify_world};
use super::{BuildRequest, CompilerPayload, CompilerRow, LogicalKey, RequestKind};

fn test_root(role: RootRole, root: &str) -> LineageRoot {
    LineageRoot {
        role,
        name: None,
        origin: None,
        artifact_kind: "namespace".to_string(),
        scheme: "sha256".to_string(),
        root: root.to_string(),
    }
}

fn test_input(path: &str, contents: &str) -> InputFilePayload {
    InputFilePayload {
        path: path.to_string(),
        digest_scheme: EVENT_HASH_SCHEME.to_string(),
        digest: provenance::sha256_hex(contents.as_bytes()),
        bytes: contents.len() as u64,
    }
}

fn test_write(path: &str, mode: WriteMode, contents: &str) -> FileWritePayload {
    FileWritePayload {
        path: path.to_string(),
        mode,
        digest_scheme: EVENT_HASH_SCHEME.to_string(),
        digest: provenance::sha256_hex(contents.as_bytes()),
        bytes: contents.len() as u64,
    }
}

fn test_compiler() -> CompilerPayload {
    CompilerPayload {
        fingerprint: "compiler=test;".to_string(),
        rows: vec![CompilerRow {
            key: "compiler".to_string(),
            value: "test".to_string(),
        }],
    }
}

fn test_output(bytes: &[u8]) -> OutputPayload {
    OutputPayload {
        digest_scheme: EVENT_HASH_SCHEME.to_string(),
        digest: provenance::sha256_hex(bytes),
        bytes: bytes.len() as u64,
    }
}

// A minimal run star mirroring the run assembler's topology: the request at the
// center, roots/argv/input-file as inputs, trace/stdout/file-writes as outputs.
fn run_graph(
    input: &InputFilePayload,
    argv: &[&str],
    stdout: &str,
    writes: &[FileWritePayload],
) -> graph::LineageGraph {
    let request = BuildRequest::run(Path::new("pipe.pr"));
    let request_id = graph::request_node_id(&request);
    let mut nodes = vec![Node {
        id: request_id.clone(),
        kind: NodeKind::Request(request),
    }];
    let mut edges = Vec::new();
    let source = test_root(RootRole::Source, "src-root");
    let stdlib = test_root(RootRole::Stdlib, "std-root");
    let argv_payload = ArgvPayload {
        args: argv.iter().map(|s| (*s).to_string()).collect(),
    };
    let compiler = test_compiler();
    let trace = TracePayload {
        scheme: EVENT_HASH_SCHEME.to_string(),
        hash: provenance::sha256_hex(format!("trace:{stdout}").as_bytes()),
        events: 2,
        replay: None,
    };
    let out = test_output(stdout.as_bytes());

    let inputs = [
        (source.node_id(), NodeKind::SourceRoot(source)),
        (stdlib.node_id(), NodeKind::StdlibRoot(stdlib)),
        (argv_payload.node_id(), NodeKind::Argv(argv_payload)),
        (input.node_id(), NodeKind::InputFile(input.clone())),
    ];
    for (id, kind) in inputs {
        edges.push(Edge {
            from: request_id.clone(),
            to: id.clone(),
            kind: EdgeKind::Input,
        });
        nodes.push(Node { id, kind });
    }
    let outputs = [
        (
            graph::minted_id(compiler.fingerprint.as_bytes()),
            NodeKind::CompilerIdentity(compiler),
            EdgeKind::IdentifiedBy,
        ),
        (trace.node_id(), NodeKind::Trace(trace), EdgeKind::Produced),
        (out.node_id(), NodeKind::Stdout(out), EdgeKind::Produced),
    ];
    for (id, kind, edge) in outputs {
        edges.push(Edge {
            from: request_id.clone(),
            to: id.clone(),
            kind: edge,
        });
        nodes.push(Node { id, kind });
    }
    for write in writes {
        let id = write.node_id();
        edges.push(Edge {
            from: request_id.clone(),
            to: id.clone(),
            kind: EdgeKind::Produced,
        });
        nodes.push(Node {
            id,
            kind: NodeKind::FileWrite(write.clone()),
        });
    }
    graph::finalize(Variant::Run, nodes, edges)
}

// --- World timeline ----------------------------------------------------------

const WORLD_DIMS: &str = "6x6";
const CONWAY_RULE: &str = "B3/S23";
const HIGHLIFE_RULE: &str = "B36/S23";
const CONWAY_HASH: &str = "c07a9b3d1e2f4a5b";
const HIGHLIFE_HASH: &str = "8f36512347abcd90";

fn law_node(rule: &str, hash: &str) -> Node {
    let payload = WorldLawPayload {
        rule: rule.to_string(),
        law_hash: hash.to_string(),
    };
    Node {
        id: payload.node_id(),
        kind: NodeKind::WorldLaw(payload),
    }
}

fn state_node(id: &str, tick: u32, branch: u32) -> Node {
    Node {
        id: NodeId(id.to_string()),
        kind: NodeKind::WorldState(WorldStatePayload {
            tick,
            branch,
            dims: WORLD_DIMS.to_string(),
        }),
    }
}

fn law_edge(state: &NodeId, law_hash: &str) -> Edge {
    Edge {
        from: state.clone(),
        to: NodeId(law_hash.to_string()),
        kind: EdgeKind::IdentifiedBy,
    }
}

fn pred_edge(state: &NodeId, pred: &NodeId) -> Edge {
    Edge {
        from: state.clone(),
        to: pred.clone(),
        kind: EdgeKind::Input,
    }
}

// A two-branch timeline mirroring the resident's emission: branch 0 runs Conway
// over ticks 0..4; branch 1 forks (unperturbed) at tick 2 under HighLife and
// diverges at tick 3, so it shares states 0..2 and owns states 3..4. Distinct
// content hashes stand in for the compiler's blake3 state digests.
fn two_branch_world() -> graph::LineageGraph {
    let s: [&str; 5] = [
        "aa00000000000000000000000000000000000000000000000000000000000000",
        "bb11111111111111111111111111111111111111111111111111111111111111",
        "cc22222222222222222222222222222222222222222222222222222222222222",
        "dd33333333333333333333333333333333333333333333333333333333333333",
        "ee44444444444444444444444444444444444444444444444444444444444444",
    ];
    let f: [&str; 2] = [
        "f733333333333333333333333333333333333333333333333333333333333333",
        "f844444444444444444444444444444444444444444444444444444444444444",
    ];
    let mut nodes = vec![
        law_node(CONWAY_RULE, CONWAY_HASH),
        law_node(HIGHLIFE_RULE, HIGHLIFE_HASH),
    ];
    let mut edges = Vec::new();

    // Branch 0: Conway, ticks 0..4. The seed carries a law edge too, so every state
    // has exactly one.
    for (t, id) in s.iter().enumerate() {
        let node = state_node(id, u32::try_from(t).unwrap(), 0);
        edges.push(law_edge(&node.id, CONWAY_HASH));
        if t > 0 {
            edges.push(pred_edge(&node.id, &NodeId(s[t - 1].to_string())));
        }
        nodes.push(node);
    }

    // Branch 1: HighLife tail owning ticks 3..4, whose predecessor chain runs back
    // into the shared Conway prefix at state 2.
    let fork_tick = 2u32;
    let divergent = NodeId(f[0].to_string());
    for (k, id) in f.iter().enumerate() {
        let tick = fork_tick + 1 + u32::try_from(k).unwrap();
        let node = state_node(id, tick, 1);
        edges.push(law_edge(&node.id, HIGHLIFE_HASH));
        let pred = if k == 0 {
            NodeId(s[fork_tick as usize].to_string())
        } else {
            NodeId(f[k - 1].to_string())
        };
        edges.push(pred_edge(&node.id, &pred));
        nodes.push(node);
    }

    let fork = WorldForkPayload {
        parent_branch: 0,
        fork_tick,
        perturbed: false,
    };
    let parent_state = NodeId(s[fork_tick as usize].to_string());
    let fork_id = graph::world_fork_node_id(&fork, &parent_state, &divergent);
    edges.push(Edge {
        from: fork_id.clone(),
        to: parent_state,
        kind: EdgeKind::Input,
    });
    edges.push(Edge {
        from: fork_id.clone(),
        to: divergent,
        kind: EdgeKind::Produced,
    });
    nodes.push(Node {
        id: fork_id,
        kind: NodeKind::WorldFork(fork),
    });

    graph::finalize(Variant::World, nodes, edges)
}

#[test]
fn why_world_walks_back_through_law_and_fork() {
    let g = two_branch_world();
    // The HighLife tip at branch 1, tick 4.
    let tip = "ee44444444444444444444444444444444444444444444444444444444444444";
    let hl_tip = "f844444444444444444444444444444444444444444444444444444444444444";
    let _ = tip;
    let explanation = why_world_state(&g, hl_tip).unwrap();
    assert_eq!(explanation.state.branch, 1);
    assert_eq!(explanation.state.tick, 4);

    // Newest first: the HighLife run over ticks 3..4, then the Conway run 0..2.
    assert_eq!(
        explanation.runs.len(),
        2,
        "two law runs: {:?}",
        explanation.runs
    );
    assert_eq!(explanation.runs[0].law_rule, HIGHLIFE_RULE);
    assert_eq!(explanation.runs[0].branch, 1);
    assert_eq!(
        (explanation.runs[0].from_tick, explanation.runs[0].to_tick),
        (3, 4)
    );
    assert_eq!(explanation.runs[1].law_rule, CONWAY_RULE);
    assert_eq!(explanation.runs[1].branch, 0);
    assert_eq!(
        (explanation.runs[1].from_tick, explanation.runs[1].to_tick),
        (0, 2)
    );

    // Exactly the one fork was crossed, at the tick it branched.
    assert_eq!(explanation.forks.len(), 1, "one fork crossed");
    assert_eq!(explanation.forks[0].fork_tick, 2);
    assert_eq!(explanation.forks[0].parent_branch, 0);
    assert!(!explanation.forks[0].perturbed);
}

#[test]
fn why_world_resolves_an_unambiguous_prefix() {
    let g = two_branch_world();
    // The state hashes share no leading nibble, so a short prefix names one state.
    let explanation = why_world_state(&g, "f84").unwrap();
    assert_eq!(explanation.state.tick, 4);
    assert_eq!(explanation.state.branch, 1);
}

#[test]
fn verify_world_accepts_a_wellformed_timeline() {
    let g = two_branch_world();
    let report = verify_world(&g).unwrap();
    assert_eq!(report.laws, 2);
    assert_eq!(report.states, 7, "5 base + 2 owned by the fork");
    assert_eq!(report.forks, 1);
}

#[test]
fn verify_world_rejects_an_edge_to_a_missing_node() {
    let mut g = two_branch_world();
    g.edges.push(Edge {
        from: NodeId(CONWAY_HASH.to_string()),
        to: NodeId("nope-no-such-node".to_string()),
        kind: EdgeKind::Input,
    });
    let err = verify_world(&g).unwrap_err().to_string();
    assert!(err.contains("names no node"), "{err}");
}

#[test]
fn verify_world_rejects_a_state_with_no_law_edge() {
    let mut g = two_branch_world();
    // Drop the seed's law edge, leaving a state with zero law edges.
    let seed =
        NodeId("aa00000000000000000000000000000000000000000000000000000000000000".to_string());
    g.edges
        .retain(|edge| !(edge.from == seed && edge.kind == EdgeKind::IdentifiedBy));
    let err = verify_world(&g).unwrap_err().to_string();
    assert!(err.contains("law edges, expected 1"), "{err}");
}

#[test]
fn world_timeline_serializes_byte_identically_twice() {
    // The same timeline exports byte-for-byte the same, so a re-export is a no-op
    // diff: finalize sorts and dedups, and serialization is deterministic.
    let a = two_branch_world().to_json_string().unwrap();
    let b = two_branch_world().to_json_string().unwrap();
    assert_eq!(a, b, "a world timeline must serialize deterministically");
}

#[test]
fn world_timeline_round_trips_through_the_decoder() {
    // What the browser emits is what the Rust decoder reads: a serialized world
    // graph decodes back to an equal graph under the shared envelope.
    let g = two_branch_world();
    let text = g.to_json_string().unwrap();
    let back: graph::LineageGraph = serde_json::from_str(&text).unwrap();
    assert_eq!(g, back, "a world graph must round-trip through serde");
    assert_eq!(back.variant, Variant::World);
}

// The committed `tests/fixtures/world.plineage` is the shape contract the browser
// emitter must match: it decodes under this crate's serde types and drives the CLI
// world-lineage tests. It is generated from `two_branch_world` (the one canonical
// shape both producers target); re-bless with `PRISM_BLESS_WORLD_FIXTURE=1`.
const WORLD_FIXTURE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/world.plineage");

#[test]
fn world_fixture_matches_the_builder() {
    let expected = two_branch_world().to_json_string().unwrap();
    if std::env::var_os("PRISM_BLESS_WORLD_FIXTURE").is_some() {
        std::fs::write(WORLD_FIXTURE, format!("{expected}\n")).unwrap();
    }
    let committed = std::fs::read_to_string(WORLD_FIXTURE)
        .expect("tests/fixtures/world.plineage exists (bless with PRISM_BLESS_WORLD_FIXTURE=1)");
    assert_eq!(
        committed.trim_end(),
        expected,
        "the world fixture drifted; re-bless with PRISM_BLESS_WORLD_FIXTURE=1"
    );
}

#[test]
fn why_output_stdout_walks_back_to_inputs() {
    let input = test_input("input.json", "{\"t\": 5}");
    let g = run_graph(&input, &["a", "b"], "hello\n", &[]);
    let explanation = why_output(&g, STDOUT_SELECTOR).unwrap();
    assert_eq!(explanation.request.kind, RequestKind::Run);
    assert!(explanation.source.is_some(), "source root is reached");
    assert!(explanation.stdlib.is_some(), "stdlib root is reached");
    assert_eq!(
        explanation.input_files.len(),
        1,
        "the one input file is grouped"
    );
    assert_eq!(explanation.input_files[0].path, "input.json");
    assert_eq!(
        explanation.argv.as_ref().map(|a| a.args.clone()),
        Some(vec!["a".to_string(), "b".to_string()])
    );
    assert!(explanation.trace.is_some(), "the trace is reported");
    assert!(
        explanation.compiler.is_some(),
        "compiler identity is reported"
    );
}

#[test]
fn why_output_matches_an_input_file_by_path() {
    let input = test_input("input.json", "{\"t\": 5}");
    let g = run_graph(&input, &["a"], "out\n", &[]);
    let explanation = why_output(&g, "input.json").unwrap();
    assert!(matches!(
        explanation.selected,
        SelectedOutput::InputFile(ref f) if f.path == "input.json"
    ));
}

#[test]
fn why_output_unknown_selector_lists_available_outputs() {
    let input = test_input("input.json", "{\"t\": 5}");
    let g = run_graph(&input, &["a"], "out\n", &[]);
    let err = why_output(&g, "no/such/path").unwrap_err().to_string();
    assert!(err.contains("stdout"), "lists stdout: {err}");
    assert!(err.contains("input.json"), "lists the input file: {err}");
}

// A written file is a selectable output; selecting it names it and walks back to the
// run's inputs.
#[test]
fn why_output_names_a_written_file() {
    let input = test_input("input.json", "{\"t\": 5}");
    let write = test_write("out.txt", WriteMode::Write, "result\n");
    let g = run_graph(&input, &["a"], "done\n", &[write]);
    let explanation = why_output(&g, "out.txt").unwrap();
    assert!(matches!(
        explanation.selected,
        SelectedOutput::FileWrite(ref w) if w.path == "out.txt"
    ));
    assert!(
        explanation.source.is_some(),
        "the write's inputs are reached"
    );
    assert!(
        explanation
            .input_files
            .iter()
            .any(|f| f.path == "input.json"),
        "the input the write depended on is listed"
    );
}

#[test]
fn diff_names_a_changed_input_as_moved_and_downstream_outputs() {
    let old = run_graph(
        &test_input("input.json", "{\"t\": 5}"),
        &["a"],
        "old\n",
        &[],
    );
    let new = run_graph(
        &test_input("input.json", "{\"t\": 6}"),
        &["a"],
        "new\n",
        &[],
    );
    let d = diff(&old, &new);
    assert!(d.changed(), "changed input and output must show as moved");
    assert!(
        d.added.is_empty(),
        "no logical key was added: {:?}",
        d.added
    );
    assert!(
        d.removed.is_empty(),
        "no logical key was removed: {:?}",
        d.removed
    );
    let moved: Vec<String> = d.moved.iter().map(|m| m.key.label()).collect();
    assert!(
        moved.contains(&"input-file input.json".to_string()),
        "{moved:?}"
    );
    assert!(moved.contains(&"stdout".to_string()), "{moved:?}");
    let preserved: Vec<String> = d.preserved.iter().map(|p| p.key.label()).collect();
    assert!(preserved.contains(&"argv".to_string()), "{preserved:?}");
    assert!(
        preserved.contains(&"source-root".to_string()),
        "{preserved:?}"
    );
}

// Changing an input that feeds a written file moves both the input and the written
// output; the written file aligns by path, so it is `moved`, never add/remove.
#[test]
fn diff_moves_a_written_output_when_its_content_changes() {
    let old = run_graph(
        &test_input("input.json", "5"),
        &["a"],
        "done\n",
        &[test_write("out.txt", WriteMode::Write, "five")],
    );
    let new = run_graph(
        &test_input("input.json", "6"),
        &["a"],
        "done\n",
        &[test_write("out.txt", WriteMode::Write, "six")],
    );
    let d = diff(&old, &new);
    let moved: Vec<String> = d.moved.iter().map(|m| m.key.label()).collect();
    assert!(
        moved.contains(&"file-write out.txt".to_string()),
        "{moved:?}"
    );
    assert!(
        d.added.is_empty() && d.removed.is_empty(),
        "aligned by path, not add/remove"
    );
}

#[test]
fn diff_of_a_graph_with_itself_is_all_preserved() {
    let g = run_graph(&test_input("input.json", "x"), &["a"], "y\n", &[]);
    let d = diff(&g, &g);
    assert!(!d.changed(), "a graph is unchanged against itself");
    assert!(d.moved.is_empty() && d.added.is_empty() && d.removed.is_empty());
    assert_eq!(d.preserved.len(), g.nodes.len());
}

#[test]
fn verify_run_replay_flags_a_changed_trace() {
    let g = run_graph(&test_input("input.json", "x"), &["a"], "y\n", &[]);
    let wrong = TraceDigest {
        scheme: EVENT_HASH_SCHEME,
        hash: "deadbeef".to_string(),
        events: 2,
    };
    let err = verify_run_replay(&g, &wrong, b"y\n", Path::new("."))
        .unwrap_err()
        .to_string();
    assert!(err.contains("trace node changed"), "{err}");
}

#[test]
fn verify_run_replay_flags_changed_stdout() {
    let g = run_graph(&test_input("input.json", "x"), &["a"], "y\n", &[]);
    let good = TraceDigest {
        scheme: EVENT_HASH_SCHEME,
        hash: provenance::sha256_hex(b"trace:y\n"),
        events: 2,
    };
    let err = verify_run_replay(&g, &good, b"tampered", Path::new("."))
        .unwrap_err()
        .to_string();
    assert!(err.contains("stdout node changed"), "{err}");
}

#[test]
fn logical_key_is_stable_across_a_digest_change() {
    let a = test_input("input.json", "one");
    let b = test_input("input.json", "two");
    let na = Node {
        id: a.node_id(),
        kind: NodeKind::InputFile(a),
    };
    let nb = Node {
        id: b.node_id(),
        kind: NodeKind::InputFile(b),
    };
    assert_ne!(na.id, nb.id, "the digest changed");
    assert_eq!(
        LogicalKey::of(&na),
        LogicalKey::of(&nb),
        "but the logical key (path) is stable, so it aligns as moved"
    );
}

// The answer objects are the single source for both terminal and `--json` output,
// so they must round-trip through serde deterministically.
#[test]
fn explanation_round_trips_through_serde() {
    let g = run_graph(&test_input("input.json", "{\"t\": 5}"), &["a"], "hi\n", &[]);
    let explanation = why_output(&g, STDOUT_SELECTOR).unwrap();
    let json = serde_json::to_string(&explanation).unwrap();
    let back: Explanation = serde_json::from_str(&json).unwrap();
    assert_eq!(explanation, back, "an Explanation must round-trip");
    assert_eq!(
        json,
        serde_json::to_string(&back).unwrap(),
        "and be deterministic"
    );
}

#[test]
fn diff_report_round_trips_through_serde() {
    let old = run_graph(&test_input("input.json", "5"), &["a"], "old\n", &[]);
    let new = run_graph(&test_input("input.json", "6"), &["a"], "new\n", &[]);
    let report = diff(&old, &new);
    let json = serde_json::to_string(&report).unwrap();
    let back: DiffReport = serde_json::from_str(&json).unwrap();
    assert_eq!(report, back, "a DiffReport must round-trip");
    assert_eq!(
        json,
        serde_json::to_string(&back).unwrap(),
        "and be deterministic"
    );
}
