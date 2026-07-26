//! Lineage: the shared, content-addressed provenance graph and its queries.
//!
//! A lineage sidecar is a typed graph whose nodes are named by digest and whose
//! edges say which operation produced what, so an emitted artifact or a recorded
//! run can explain what produced it. This crate owns the graph vocabulary and
//! the pure queries over it (diff, explain, verify, render, provenance,
//! node identity); the adapters that CAPTURE lineage from a build or a run
//! know the compiler's driver and stay with it.

pub mod diff;
pub mod explain;
pub mod graph;
pub mod node_id;
pub mod provenance;
pub mod render;
pub mod verify;

#[cfg(test)]
mod tests;
