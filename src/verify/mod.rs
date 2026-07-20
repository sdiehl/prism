//! The solver-neutral verification substrate.
//!
//! Prism owns the logical question, names, sorts, and obligation identity; an
//! external solver is an interchangeable search engine over bytes Prism has
//! already fixed. This module holds the canonical first-order `logic` IR, the
//! stable builtin `registry`, and the independent `wf` well-formedness
//! verifier. The SMT-LIB encoder, alpha-normalizer/digest, query codec, and
//! solver-response parser live alongside them.
//!
//! The substrate introduces no surface syntax and touches no `check`/`build`/`run`,
//! optimizer, effect-lowering, or codegen path. An obligation's bytes are a pure
//! function of its logical term, invariant across every tier and backend, and
//! independent of the Core content hash by construction: a solver never sees
//! Core.

// The verification read side (certificate decode and dependency-closure
// verification, the reserved logic and trust discriminants) is built but not yet
// reached by the `prism verify` flow or its tests; it is consumed once
// modular-call verification conditions land. `expect` self-clears each item the
// moment it is wired, so it cannot mask newly introduced debt the way a blanket
// `allow` would.
#![expect(dead_code)]

pub(crate) mod certificate;
pub(crate) mod check;
pub(crate) mod interface;
pub(crate) mod logic;
pub(crate) mod normalize;
pub(crate) mod query;
pub(crate) mod ranking;
pub(crate) mod registry;
pub(crate) mod response;
pub(crate) mod result;
pub(crate) mod run;
pub(crate) mod smtlib;
pub(crate) mod solver;
pub(crate) mod store;
pub(crate) mod totality;
pub(crate) mod vc;
pub(crate) mod wf;

pub(crate) use check::check_program;

#[cfg(test)]
mod tests;
