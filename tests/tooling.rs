//! The tooling target: the CLI end-to-end surfaces (`index`, `test`, durable
//! resume, stable locks), the package and store layers, the lineage graph, and
//! the out-of-tree backend fixture.

mod support;

#[path = "tooling/bootstrap.rs"]
mod bootstrap;
#[path = "tooling/bootstrap_worker.rs"]
mod bootstrap_worker;
#[path = "tooling/classification_tables.rs"]
mod classification_tables;
#[path = "tooling/durable_driver.rs"]
mod durable_driver;
#[path = "tooling/index.rs"]
mod index;
#[path = "tooling/isa_fixture.rs"]
mod isa_fixture;
#[path = "tooling/lane_ledger.rs"]
mod lane_ledger;
#[path = "tooling/lint.rs"]
mod lint;
#[path = "tooling/prism_test.rs"]
mod prism_test;
#[path = "tooling/stable_lock.rs"]
mod stable_lock;

#[path = "package/cert.rs"]
mod cert;
#[path = "package/certificates.rs"]
mod certificates;
#[path = "package/pkg.rs"]
mod pkg;
#[path = "package/pkg_transport.rs"]
mod pkg_transport;
#[path = "package/receipt.rs"]
mod receipt;

#[path = "store_pkg/store_coherence.rs"]
mod store_coherence;
#[path = "store_pkg/store_layout.rs"]
mod store_layout;

#[path = "lineage_suite/facts.rs"]
mod facts;
#[path = "lineage_suite/lineage.rs"]
mod lineage;
#[path = "lineage_suite/lineage_tiles.rs"]
mod lineage_tiles;
#[path = "lineage_suite/run_lineage.rs"]
mod run_lineage;
#[path = "lineage_suite/world_lineage.rs"]
mod world_lineage;

#[path = "compiler/parser_receipt.rs"]
mod parser_receipt;
#[path = "compiler/stdlib_hash.rs"]
mod stdlib_hash;

#[path = "cli_docs/cli_examples.rs"]
mod cli_examples;
#[path = "cli_docs/determinism_machine.rs"]
mod determinism_machine;
#[path = "cli_docs/docs_runner.rs"]
mod docs_runner;
#[path = "cli_docs/project.rs"]
mod project;
#[path = "cli_docs/time_compile.rs"]
mod time_compile;
#[path = "cli_docs/world.rs"]
mod world;
