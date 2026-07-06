//! Composition gates for the Determinism Machine residents.
//!
//! The behavioral contracts live in focused tests (`boids_*`, `chaos_swarm`,
//! `pendulum_scrubber`, `kont_suspend`, and `showcase`). This file pins the
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
const CHAOS_WORKER: &str = "chaos-worker.ts";

#[derive(Clone, Copy)]
struct Resident {
    slug: &'static str,
    route: &'static str,
    page: &'static str,
    script: &'static str,
    exports: &'static [&'static str],
    example: Option<&'static str>,
    sentinel: Option<&'static str>,
}

const WEB_RESIDENTS: &[Resident] = &[
    Resident {
        slug: "scrubber",
        route: "scrub",
        page: "scrubber.html",
        script: "scrubber.ts",
        exports: &["boids_run"],
        example: Some("boids.pr"),
        sentinel: Some(SCRUBBER_SENTINEL),
    },
    Resident {
        slug: "pendulum",
        route: "pendulum",
        page: "pendulum.html",
        script: "pendulum.ts",
        exports: &["pendulum_run"],
        example: Some("pendulum.pr"),
        sentinel: Some(SCRUBBER_SENTINEL),
    },
    Resident {
        slug: "branch",
        route: "branch",
        page: "branch.html",
        script: "branch.ts",
        exports: &["boids_run_full", "boids_run_from"],
        example: Some("boids.pr"),
        sentinel: Some(SCRUBBER_SENTINEL),
    },
    Resident {
        slug: "chaos",
        route: "chaos",
        page: "chaos.html",
        script: "chaos.ts",
        exports: &["chaos_run"],
        example: Some("chaos_swarm.pr"),
        sentinel: Some(CHAOS_SENTINEL),
    },
    Resident {
        slug: "schedule",
        route: "schedule",
        page: "schedule.html",
        script: "schedule.ts",
        exports: &["chaos_run"],
        example: Some("chaos_swarm.pr"),
        sentinel: Some(CHAOS_SENTINEL),
    },
    Resident {
        slug: "teleport",
        route: "teleport",
        page: "teleport.html",
        script: "teleport.ts",
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
];

const ACCEPTANCE_TESTS: &[&str] = &[
    "boids_scrubber.rs",
    "boids_branch.rs",
    "chaos_swarm.rs",
    "pendulum_scrubber.rs",
    "kont_suspend.rs",
    "showcase.rs",
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
        assert_contains(
            &gallery,
            &format!("href=\"../{}/\"", resident.route),
            resident.slug,
        );
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
        let worker =
            (resident.slug == "chaos").then(|| read(Path::new(WEB_SRC).join(CHAOS_WORKER)));
        assert_contains(&script, PKG_IMPORT, resident.script);
        for export in resident.exports {
            assert!(
                script.contains(export) || worker.as_deref().is_some_and(|w| w.contains(export)),
                "{} is missing wasm export `{export}`",
                resident.script
            );
        }
        if let Some(worker) = worker {
            assert_contains(&worker, PKG_IMPORT, CHAOS_WORKER);
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
