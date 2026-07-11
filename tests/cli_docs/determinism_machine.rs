//! Composition gates for the Determinism Machine residents.
//!
//! The behavioral contracts live in focused tests (`boids_*`, `chaos_swarm`,
//! `pendulum_scrubber`, `kont_suspend`, and `showcase`). This file checks the
//! public composition layer: each web resident has a page, a Vite entry, the
//! expected wasm export, the matching Prism example/sentinel when applicable,
//! and a Rust acceptance test exists for every advertised behavior.

use std::fs;
use std::path::Path;

const WEB: &str = "web";
const WEB_SRC: &str = "web/src";
const WEB_GALLERY: &str = "web/gallery.html";
const VITE_CONFIG: &str = "web/vite.config.ts";
const EXAMPLES: &str = "examples";
const TESTS: &str = "tests";
const PKG_IMPORT: &str = "../pkg/prism.js";
const SCRUBBER_SENTINEL: &str = "-- @scrubber:main-below";
const CHAOS_SENTINEL: &str = "-- @chaos:main-below";
const WORLD_SENTINEL: &str = "-- @world:main-below";
const CHAOS_WORKER: &str = "chaos-worker.ts";
const WORLD_WORKER: &str = "prism-world-worker.ts";

#[derive(Clone, Copy)]
struct Resident {
    slug: &'static str,
    // Listed on the gallery page. A resident can be built, wired, and reachable
    // by URL while deliberately unlisted (the world resident currently is).
    gallery: bool,
    route: &'static str,
    page: &'static str,
    script: &'static str,
    // A resident whose wasm exports are reached from a dedicated worker names it
    // here; the export check then also looks in the worker module.
    worker: Option<&'static str>,
    exports: &'static [&'static str],
    example: Option<&'static str>,
    sentinel: Option<&'static str>,
}

const WEB_RESIDENTS: &[Resident] = &[
    Resident {
        slug: "scrubber",
        gallery: true,
        route: "scrub",
        page: "scrubber.html",
        script: "scrubber.ts",
        worker: None,
        exports: &["boids_run"],
        example: Some("boids.pr"),
        sentinel: Some(SCRUBBER_SENTINEL),
    },
    Resident {
        slug: "pendulum",
        gallery: true,
        route: "pendulum",
        page: "pendulum.html",
        script: "pendulum.ts",
        worker: None,
        exports: &["pendulum_run"],
        example: Some("pendulum.pr"),
        sentinel: Some(SCRUBBER_SENTINEL),
    },
    Resident {
        slug: "branch",
        gallery: true,
        route: "branch",
        page: "branch.html",
        script: "branch.ts",
        worker: None,
        exports: &["boids_run_full", "boids_run_from"],
        example: Some("boids.pr"),
        sentinel: Some(SCRUBBER_SENTINEL),
    },
    Resident {
        slug: "chaos",
        gallery: true,
        route: "chaos",
        page: "chaos.html",
        script: "chaos.ts",
        worker: Some(CHAOS_WORKER),
        exports: &["chaos_run"],
        example: Some("chaos_swarm.pr"),
        sentinel: Some(CHAOS_SENTINEL),
    },
    Resident {
        slug: "schedule",
        gallery: true,
        route: "schedule",
        page: "schedule.html",
        script: "schedule.ts",
        worker: None,
        exports: &["chaos_run"],
        example: Some("chaos_swarm.pr"),
        sentinel: Some(CHAOS_SENTINEL),
    },
    Resident {
        slug: "teleport",
        gallery: true,
        route: "teleport",
        page: "teleport.html",
        script: "teleport.ts",
        worker: None,
        exports: &[
            "teleport_bundle",
            "teleport_cuts",
            "teleport_prefix",
            "teleport_resume",
            "teleport_source",
            "teleport_suspend",
        ],
        example: Some("teleport.pr"),
        sentinel: None,
    },
    Resident {
        slug: "world",
        gallery: false,
        route: "world",
        page: "prism-world.html",
        script: "prism-world.ts",
        worker: Some(WORLD_WORKER),
        exports: &["world_run", "world_law_hash", "world_source"],
        example: Some("world.pr"),
        sentinel: Some(WORLD_SENTINEL),
    },
];

const ACCEPTANCE_TESTS: &[&str] = &[
    "runtime/boids_scrubber.rs",
    "runtime/boids_branch.rs",
    "runtime/chaos_swarm.rs",
    "runtime/pendulum_scrubber.rs",
    "runtime/kont_suspend.rs",
    "runtime/showcase.rs",
    "cli_docs/world.rs",
];

fn read(path: impl AsRef<Path>) -> String {
    fs::read_to_string(path.as_ref())
        .unwrap_or_else(|e| panic!("read {}: {e}", path.as_ref().display()))
}

fn assert_contains(haystack: &str, needle: &str, label: &str) {
    assert!(haystack.contains(needle), "{label} is missing `{needle}`");
}

#[test]
fn gallery_and_vite_wire_every_resident() {
    let gallery = read(WEB_GALLERY);
    let vite = read(VITE_CONFIG);

    for resident in WEB_RESIDENTS {
        let gallery_link = format!("href=\"../{}/\"", resident.route);
        if resident.gallery {
            assert_contains(&gallery, &gallery_link, resident.slug);
        } else {
            // Unlisted is a decision, not an accident: the card must be absent,
            // not merely unnoticed, so relisting is a deliberate flip here.
            assert!(
                !gallery.contains(&gallery_link),
                "{} is marked unlisted but the gallery links it",
                resident.slug
            );
        }
        assert_contains(
            &vite,
            &format!("{}: \"{}\"", resident.slug, resident.page),
            resident.slug,
        );
        let page = read(Path::new(WEB).join(resident.page));
        assert_contains(
            &page,
            &format!("src=\"/src/{}\"", resident.script),
            resident.page,
        );
    }
}

#[test]
fn frontend_scripts_import_the_expected_wasm_exports() {
    for resident in WEB_RESIDENTS {
        let script = read(Path::new(WEB_SRC).join(resident.script));
        let worker = resident
            .worker
            .map(|w| (w, read(Path::new(WEB_SRC).join(w))));
        // The script imports the bundle directly, or reaches it through a worker
        // that does; either way the module that names the export must import it.
        let source_importer = worker.as_ref().map_or(&script, |(_, w)| w);
        assert_contains(source_importer, PKG_IMPORT, resident.script);
        for export in resident.exports {
            assert!(
                script.contains(export) || worker.as_ref().is_some_and(|(_, w)| w.contains(export)),
                "{} is missing wasm export `{export}`",
                resident.script
            );
        }
    }
}

#[test]
fn examples_and_acceptance_tests_cover_each_claim() {
    for resident in WEB_RESIDENTS {
        if let Some(example) = resident.example {
            let source = read(Path::new(EXAMPLES).join(example));
            if let Some(sentinel) = resident.sentinel {
                assert_contains(&source, sentinel, example);
            }
        }
    }
    for acceptance_test in ACCEPTANCE_TESTS {
        let test = read(Path::new(TESTS).join(acceptance_test));
        assert_contains(&test, "#[test]", acceptance_test);
    }
}

#[test]
fn world_export_mirrors_the_lineage_graph_vocabulary() {
    // The timeline export rides the one lineage graph, never a web-only dialect.
    // The page has an Export button and the emitter mirrors graph.rs's node/edge
    // spellings verbatim; the Rust decoder rejects any drift, and the committed
    // `tests/fixtures/world.plineage` plus the `world_lineage` CLI cases are the
    // shape contract that a browser-emitted graph parses under the same decoder.
    let page = read(Path::new(WEB).join("prism-world.html"));
    let script = read(Path::new(WEB_SRC).join("prism-world.ts"));

    assert_contains(&page, "id=\"export\"", "prism-world.html");
    // The shared-vocabulary comment must point at graph.rs as the one home.
    assert_contains(&script, "src/lineage/graph.rs", "prism-world.ts");
    // The exact node-kind, edge-kind, and envelope spellings the decoder reads.
    for needle in [
        "prism-lineage-graph-v1",
        "world-law",
        "world-state",
        "world-fork",
        "identified-by",
        "plineage",
    ] {
        assert_contains(&script, needle, "prism-world.ts");
    }
}

#[test]
fn teleport_names_same_origin_migration_protocol() {
    let page = read(Path::new(WEB).join("teleport.html"));
    let recv = read(Path::new(WEB).join("teleport-recv.html"));
    let script = read(Path::new(WEB_SRC).join("teleport.ts"));

    for needle in [
        "same-origin BroadcastChannel",
        "openReceiver",
        "receiverStatus",
    ] {
        assert_contains(&page, needle, "teleport.html");
    }
    assert_contains(&recv, "recvIdentity", "teleport-recv.html");
    for needle in [
        "kind: \"ready\"",
        "transfer: number",
        "env.bundle !== mine",
        "bundle-mismatch",
    ] {
        assert_contains(&script, needle, "teleport.ts");
    }
}
