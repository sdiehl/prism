use std::collections::BTreeMap;

use prism::{module_graph, ModuleGraph, ModuleInvalidationCause, Root, MODULE_GRAPH_FORMAT};

const SOURCE: &str = "import Data.List\nimport Data.Maybe\n";

#[test]
fn graph_is_canonical_versioned_and_self_verifying() {
    let roots = [Root::Embedded(prism::stdlib::STDLIB)];
    let graph = module_graph(SOURCE, &roots).unwrap();
    assert_eq!(graph.format, MODULE_GRAPH_FORMAT);
    assert!(graph
        .nodes
        .windows(2)
        .all(|pair| pair[0].name < pair[1].name));
    assert!(graph.nodes.iter().any(|node| node.name == "<root>"));
    assert!(graph.nodes.iter().any(|node| node.name == "Data.List"));

    let json = graph.to_json().unwrap();
    assert_eq!(ModuleGraph::from_json(&json).unwrap(), graph);

    let mut corrupt = graph;
    corrupt.nodes[0].source_digest = "0".repeat(corrupt.nodes[0].source_digest.len());
    assert!(ModuleGraph::from_json(&corrupt.to_json().unwrap()).is_err());
}

#[test]
fn graph_identity_moves_only_for_the_changed_source_node() {
    let roots = [Root::Embedded(prism::stdlib::STDLIB)];
    let before = module_graph(SOURCE, &roots).unwrap();
    let after = module_graph(&format!("{SOURCE}\n-- trivia\n"), &roots).unwrap();

    let changed = before
        .nodes
        .iter()
        .zip(&after.nodes)
        .filter(|(left, right)| left.digest != right.digest)
        .map(|(node, _)| node.name.as_str())
        .collect::<Vec<_>>();
    assert_eq!(changed, ["<root>"]);
    assert_ne!(before.digest, after.digest);
}

#[test]
fn invalidation_walks_the_exact_reverse_dependency_cone() {
    let root = "import A\n";
    let modules = |body: &str| {
        Root::source_bundle(
            "fixture".to_string(),
            BTreeMap::from([
                (
                    "A".to_string(),
                    "import B\npub fn a() : Int = B.b()\n".to_string(),
                ),
                ("B".to_string(), body.to_string()),
                (
                    "Unused".to_string(),
                    "pub fn unused() : Int = 0\n".to_string(),
                ),
            ]),
        )
    };
    let before = module_graph(root, &[modules("pub fn b() : Int = 1\n")]).unwrap();
    let after = module_graph(root, &[modules("pub fn b() : Int = 2\n")]).unwrap();
    let closure = after.invalidation_closure(&before).unwrap();

    assert_eq!(
        closure
            .iter()
            .map(|row| row.name.as_str())
            .collect::<Vec<_>>(),
        ["<root>", "A", "B"]
    );
    assert_eq!(closure[2].cause, ModuleInvalidationCause::InputChanged);
    assert_eq!(
        closure[1].cause,
        ModuleInvalidationCause::DependencyChanged {
            dependencies: vec!["B".to_string()]
        }
    );
    assert_eq!(
        closure[0].cause,
        ModuleInvalidationCause::DependencyChanged {
            dependencies: vec!["A".to_string()]
        }
    );
}
