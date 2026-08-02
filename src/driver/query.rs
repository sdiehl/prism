//! The query subsystem: the read-only face of the codebase-as-a-database
//! (`callers`/`dependents`/`deps`/`uses-type`), plus the small text helpers the
//! query and report surfaces share. Split out of the driver so `mod.rs` holds
//! the compile pipeline and this module holds the graph queries. Every external
//! path (`prism::query_on`) resolves through the re-export in `mod.rs`, so the
//! split is invisible to callers.

use std::fmt::Write as _;

use crate::core::DepGraph;
use crate::error::Error;
use crate::resolve::Root;
use crate::sym::Sym;

use super::{check_on, frontend, Config};

/// Answer a dependency-graph query over a program (prelude included), the
/// read-only face of the codebase-as-a-database.
///
/// `kind` is one of `callers`
/// (direct), `dependents` (the transitive Merkle closure, the exact set a change
/// to `target` would force to re-check), `deps` (what `target` transitively
/// depends on), or `uses-type` (definitions whose inferred type mentions the type
/// named `target`).
///
/// # Errors
/// Fails on front-end errors, an unknown `kind`, or a `target` that names no
/// definition (or, for the graph queries, an ambiguous unqualified name).
pub fn query_on(
    kind: &str,
    target: &str,
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<String, Error> {
    match kind {
        "callers" | "dependents" | "deps" => {
            let (_, _, core) = frontend(src, roots, cfg)?;
            let graph = DepGraph::of(&core);
            let sym = resolve_query_target(&graph, target)?;
            let set = match kind {
                "callers" => graph.direct_callers(sym),
                "dependents" => graph.dependents(sym),
                _ => graph.dependencies(sym),
            };
            let mut names: Vec<&str> = set.iter().map(|s| s.as_str()).collect();
            names.sort_unstable();
            let mut out = String::new();
            writeln!(out, "{kind} of {} ({})", sym.as_str(), names.len()).unwrap();
            for n in names {
                writeln!(out, "  {n}").unwrap();
            }
            Ok(out)
        }
        "uses-type" => {
            let checked = check_on(src, roots)?;
            let mut hits: Vec<String> = checked
                .decls
                .iter()
                .filter(|d| type_mentions(&checked.show_sig(d), target))
                .map(|d| format!("  {} : {}", d.name, checked.show_sig(d)))
                .collect();
            hits.sort_unstable();
            hits.dedup();
            let mut out = String::new();
            writeln!(out, "uses-type {target} ({})", hits.len()).unwrap();
            out.push_str(&hits.join("\n"));
            out.push('\n');
            Ok(out)
        }
        other => Err(Error::CodegenBackend(format!(
            "unknown query {other}; try callers | dependents | deps | uses-type"
        ))),
    }
}

// Resolve a query target name to a single definition, reporting no-match and
// ambiguity as errors so the caller can qualify.
fn resolve_query_target(graph: &DepGraph, target: &str) -> Result<Sym, Error> {
    let mut candidates = graph.resolve(target);
    match candidates.len() {
        1 => Ok(candidates.remove(0)),
        0 => Err(Error::CodegenBackend(format!(
            "no definition named `{target}`"
        ))),
        _ => {
            candidates.sort_by_key(|s| s.as_str());
            let list: Vec<&str> = candidates.iter().map(|s| s.as_str()).collect();
            Err(Error::CodegenBackend(format!(
                "`{target}` is ambiguous; qualify one of: {}",
                list.join(", ")
            )))
        }
    }
}

/// The identifier tokens of a rendered type, the unit this query matches on.
///
/// Splitting on non-identifier characters is what makes `List` match `List(Int)`
/// but not `Listable`.
///
/// The code index deliberately does *not* share this rule, and the difference is
/// not an oversight. This query answers a name a human typed at a shell, where
/// matching a bare `Option` wherever it appears is the useful behavior and the
/// user can qualify to narrow. The index emits edges between canonical
/// identities, where the same looseness is a correctness bug: two modules that
/// each declare a `List` tokenize identically, so a bare match would link to both
/// and one of those edges would be false. It walks the checked type structurally
/// instead and keys on the resolved symbol. Convenience here, exactness there.
pub fn type_tokens(ty: &str) -> impl Iterator<Item = &str> {
    ty.split(|c: char| !c.is_alphanumeric() && c != '_')
        .filter(|tok| !tok.is_empty())
}

// Whether a shown type string mentions the type named `name` as a whole token.
fn type_mentions(ty: &str, name: &str) -> bool {
    type_tokens(ty).any(|tok| tok == name)
}

// The module's target triple and data layout are host-derived, so they differ
// between machines. They are irrelevant to the snapshotted pipeline (clang
// re-derives them at link time), so drop them from the dump.
#[cfg(feature = "native")]
pub(super) fn strip_target(ir: &str) -> String {
    ir.lines()
        .filter(|l| !l.starts_with("target datalayout") && !l.starts_with("target triple"))
        .collect::<Vec<_>>()
        .join("\n")
}

pub(super) fn section(out: &mut String, title: &str, body: &str) {
    writeln!(out, "== {title} ==").unwrap();
    writeln!(out, "{body}").unwrap();
    out.push('\n');
}
