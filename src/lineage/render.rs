//! Human-readable rendering of the lineage answer objects.
//!
//! Every terminal prose string lives here, consuming the typed answer objects
//! ([`super::explain::Explanation`], [`super::diff::DiffReport`]) and the graph. The
//! machine-readable `--json` projections serialize the same objects, so the two
//! renderings cannot drift.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::core::HASH_PREFIX_HEX;

use super::diff::DiffReport;
use super::explain::{Explanation, WorldExplanation};
use super::graph::{self, LineageGraph, LineageRoot, NodeKind, Variant};

// Abbreviate a content-hash id to the same width the human dumps use, so a
// rendered timeline shows the leading nibbles the resident also shows. Ids arrive
// from deserialized, possibly hand-authored input, so this truncates on a char
// boundary rather than a raw byte index: a genuine hex hash yields the same leading
// nibbles, while a value whose byte-16 boundary would split a multibyte char
// truncates without panicking.
fn short_hash(hash: &str) -> &str {
    match hash.char_indices().nth(HASH_PREFIX_HEX) {
        Some((boundary, _)) => &hash[..boundary],
        None => hash,
    }
}

/// A friendly, non-authoritative rendering of the graph.
#[must_use]
pub fn render_human(graph: &LineageGraph) -> String {
    if graph.variant == Variant::World {
        return render_world(graph);
    }
    let mut out = String::new();
    if let Some(request) = graph.first_request() {
        let _ = writeln!(out, "lineage {}", request.path);
        let _ = writeln!(
            out,
            "why: artifact exists because `{}` produced `{}` with the recorded inputs",
            graph::request_kind_tag(request.kind),
            request.entry
        );
    }
    for node in &graph.nodes {
        match &node.kind {
            NodeKind::SourceRoot(root) => render_root(&mut out, "source", root),
            NodeKind::StdlibRoot(root) => render_root(&mut out, "stdlib", root),
            NodeKind::PackageRoot(root) => render_root(&mut out, "package", root),
            _ => {}
        }
    }
    if let Some(compiler) = graph.compiler() {
        let _ = writeln!(out, "compiler:");
        for row in &compiler.rows {
            let _ = writeln!(out, "  {} = {}", row.key, row.value);
        }
    }
    render_run_inputs(&mut out, graph);
    render_docs(&mut out, graph);
    if graph
        .nodes
        .iter()
        .any(|node| matches!(node.kind, NodeKind::Artifact(_)))
    {
        let _ = writeln!(out, "artifacts:");
        for node in &graph.nodes {
            if let NodeKind::Artifact(artifact) = &node.kind {
                let _ = writeln!(
                    out,
                    "  {} {} {}:{} ({} bytes)",
                    artifact.kind,
                    artifact.path,
                    artifact.digest_scheme,
                    artifact.digest,
                    artifact.bytes
                );
            }
        }
    }
    for node in &graph.nodes {
        if let NodeKind::CacheSummary(cache) = &node.kind {
            let _ = writeln!(
                out,
                "cache: enabled={} hit={} written={}",
                cache.enabled, cache.objects_hit, cache.objects_written
            );
        }
    }
    out
}

// The run-specific sections: argv, observed environment reads and input files,
// produced file writes, the trace digest, and the produced stdout. Each is skipped
// when a build graph has no such node, so a build sidecar renders exactly as before.
fn render_run_inputs(out: &mut String, graph: &LineageGraph) {
    for node in &graph.nodes {
        if let NodeKind::Argv(argv) = &node.kind {
            let _ = writeln!(out, "argv: {:?}", argv.args);
        }
    }
    for node in &graph.nodes {
        if let NodeKind::EnvRead(env) = &node.kind {
            let _ = writeln!(
                out,
                "env-read: {} = {}:{}",
                env.name, env.value_scheme, env.value_digest
            );
        }
    }
    for node in &graph.nodes {
        if let NodeKind::InputFile(file) = &node.kind {
            let _ = writeln!(
                out,
                "input-file: {} {}:{} ({} bytes)",
                file.path, file.digest_scheme, file.digest, file.bytes
            );
        }
    }
    for node in &graph.nodes {
        if let NodeKind::FileWrite(write) = &node.kind {
            let _ = writeln!(
                out,
                "file-write: {} [{}] {}:{} ({} bytes)",
                write.path,
                write.mode.tag(),
                write.digest_scheme,
                write.digest,
                write.bytes
            );
        }
    }
    for node in &graph.nodes {
        if let NodeKind::Trace(trace) = &node.kind {
            let _ = writeln!(
                out,
                "trace: {}:{} ({} events)",
                trace.scheme, trace.hash, trace.events
            );
        }
    }
    for node in &graph.nodes {
        if let NodeKind::Stdout(stdout) = &node.kind {
            let _ = writeln!(
                out,
                "stdout: {}:{} ({} bytes)",
                stdout.digest_scheme, stdout.digest, stdout.bytes
            );
        }
    }
}

// The docs-specific sections: the generator that rendered the pages and each
// doctest that ran. The pages themselves render under the shared "artifacts"
// section (they are `docs-page` artifacts), so only these two are added here.
fn render_docs(out: &mut String, graph: &LineageGraph) {
    for node in &graph.nodes {
        if let NodeKind::DocsGenerator(generator) = &node.kind {
            let _ = writeln!(out, "docs-generator: {}", generator.format);
        }
    }
    for node in &graph.nodes {
        if let NodeKind::Doctest(test) = &node.kind {
            let _ = writeln!(
                out,
                "doctest: {} {}:{}",
                test.location, test.output_scheme, test.output_digest
            );
        }
    }
}

// A world-timeline summary: the laws in play, each branch's tick span, the fork
// points, and the total state count. Derived from the state/law/fork nodes, so a
// hand-authored or browser-emitted timeline renders identically.
fn render_world(graph: &LineageGraph) -> String {
    let mut out = String::new();
    let states = graph.world_states();
    let _ = writeln!(out, "lineage world timeline ({} states)", states.len());

    let mut laws = graph.world_laws();
    laws.sort_by(|a, b| a.1.rule.cmp(&b.1.rule));
    if !laws.is_empty() {
        let _ = writeln!(out, "laws:");
        for (id, law) in laws {
            let _ = writeln!(out, "  {} {}", law.rule, short_hash(&id.0));
        }
    }

    // Per-branch tick span, folded from the state nodes so branches need not be
    // their own node kind.
    let mut spans: BTreeMap<u32, (u32, u32, String)> = BTreeMap::new();
    for (_, state) in &states {
        let dims = state.dims.clone();
        spans
            .entry(state.branch)
            .and_modify(|(lo, hi, _)| {
                *lo = (*lo).min(state.tick);
                *hi = (*hi).max(state.tick);
            })
            .or_insert((state.tick, state.tick, dims));
    }
    if !spans.is_empty() {
        let _ = writeln!(out, "branches:");
        for (branch, (lo, hi, dims)) in &spans {
            let name = if *branch == 0 {
                "main".to_string()
            } else {
                format!("branch {branch}")
            };
            let _ = writeln!(out, "  {name}: ticks {lo}..{hi} on a {dims} grid");
        }
    }

    let mut forks = graph.world_forks();
    forks.sort_by(|a, b| {
        a.1.parent_branch
            .cmp(&b.1.parent_branch)
            .then_with(|| a.1.fork_tick.cmp(&b.1.fork_tick))
    });
    if !forks.is_empty() {
        let _ = writeln!(out, "forks:");
        for (_, fork) in forks {
            let poked = if fork.perturbed {
                " (poked one cell)"
            } else {
                ""
            };
            let _ = writeln!(
                out,
                "  from branch {} at tick {}{poked}",
                fork.parent_branch, fork.fork_tick
            );
        }
    }
    out
}

/// Render a world-state `why` explanation deterministically: the selected state,
/// its history compressed into per-law runs (newest first), and the fork points
/// crossed on the way back to the seed.
#[must_use]
pub fn render_world_explanation(explanation: &WorldExplanation) -> String {
    let mut out = String::new();
    let _ = writeln!(
        out,
        "why world state {} (branch {}, tick {})",
        short_hash(&explanation.state_id),
        explanation.state.branch,
        explanation.state.tick
    );
    for run in &explanation.runs {
        let name = if run.branch == 0 {
            "main".to_string()
        } else {
            format!("branch {}", run.branch)
        };
        if run.from_tick == run.to_tick {
            let _ = writeln!(
                out,
                "  tick {} on {name} under {} ({})",
                run.from_tick,
                run.law_rule,
                short_hash(&run.law_hash)
            );
        } else {
            let _ = writeln!(
                out,
                "  ticks {}..{} on {name} under {} ({})",
                run.from_tick,
                run.to_tick,
                run.law_rule,
                short_hash(&run.law_hash)
            );
        }
    }
    for fork in &explanation.forks {
        let poked = if fork.perturbed {
            " (poked one cell)"
        } else {
            ""
        };
        let _ = writeln!(
            out,
            "  crossed fork from branch {} at tick {}{poked}",
            fork.parent_branch, fork.fork_tick
        );
    }
    out
}

fn render_root(out: &mut String, label: &str, root: &LineageRoot) {
    let _ = writeln!(
        out,
        "{label}: kind={} scheme={} root={} name={} origin={}",
        root.artifact_kind,
        root.scheme,
        root.root,
        root.name.as_deref().unwrap_or("-"),
        root.origin.as_deref().unwrap_or("-")
    );
}

/// Render a `why-output` explanation deterministically.
#[must_use]
pub fn render_explanation(explanation: &Explanation) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "why {}", explanation.selected.describe());
    let _ = writeln!(
        out,
        "  produced by `{}` of `{}`",
        graph::request_kind_tag(explanation.request.kind),
        explanation.request.entry
    );
    if let Some(source) = &explanation.source {
        let _ = writeln!(out, "  source root: {}:{}", source.scheme, source.root);
    }
    if let Some(stdlib) = &explanation.stdlib {
        let _ = writeln!(out, "  stdlib root: {}:{}", stdlib.scheme, stdlib.root);
    }
    for package in &explanation.packages {
        let _ = writeln!(
            out,
            "  package root: {} {}:{}",
            package.name.as_deref().unwrap_or("-"),
            package.scheme,
            package.root
        );
    }
    if let Some(argv) = &explanation.argv {
        let _ = writeln!(out, "  argv: {:?}", argv.args);
    }
    for env in &explanation.env_reads {
        let _ = writeln!(
            out,
            "  env-read: {} = {}:{}",
            env.name, env.value_scheme, env.value_digest
        );
    }
    for file in &explanation.input_files {
        let _ = writeln!(
            out,
            "  input-file: {} {}:{} ({} bytes)",
            file.path, file.digest_scheme, file.digest, file.bytes
        );
    }
    if let Some(trace) = &explanation.trace {
        let _ = writeln!(
            out,
            "  trace: {}:{} ({} events)",
            trace.scheme, trace.hash, trace.events
        );
    }
    if let Some(compiler) = &explanation.compiler {
        let _ = writeln!(out, "  compiler:");
        for row in &compiler.rows {
            let _ = writeln!(out, "    {} = {}", row.key, row.value);
        }
    }
    for artifact in &explanation.artifacts {
        let _ = writeln!(
            out,
            "  artifact: {} {} {}:{} ({} bytes)",
            artifact.kind, artifact.path, artifact.digest_scheme, artifact.digest, artifact.bytes
        );
    }
    for write in &explanation.file_writes {
        let _ = writeln!(
            out,
            "  file-write: {} [{}] {}:{} ({} bytes)",
            write.path,
            write.mode.tag(),
            write.digest_scheme,
            write.digest,
            write.bytes
        );
    }
    out
}

/// Render a lineage diff deterministically. The verdict line comes first so a
/// caller (or a human) reads the outcome before the sections.
#[must_use]
pub fn render_diff(diff: &DiffReport) -> String {
    let mut out = String::new();
    if diff.changed() {
        let _ = writeln!(
            out,
            "lineage diff: {} moved, {} added, {} removed, {} preserved",
            diff.moved.len(),
            diff.added.len(),
            diff.removed.len(),
            diff.preserved.len()
        );
    } else {
        let _ = writeln!(
            out,
            "lineage diff: unchanged ({} preserved)",
            diff.preserved.len()
        );
    }
    for entry in &diff.moved {
        let _ = writeln!(
            out,
            "  moved    {}: {} -> {}",
            entry.key.label(),
            entry.old.0,
            entry.new.0
        );
    }
    for entry in &diff.added {
        let _ = writeln!(out, "  added    {}: {}", entry.key.label(), entry.digest.0);
    }
    for entry in &diff.removed {
        let _ = writeln!(out, "  removed  {}: {}", entry.key.label(), entry.digest.0);
    }
    for entry in &diff.preserved {
        let _ = writeln!(out, "  same     {}: {}", entry.key.label(), entry.digest.0);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::short_hash;
    use crate::core::HASH_PREFIX_HEX;

    #[test]
    fn short_hash_truncates_ascii_to_the_prefix_width() {
        let hash = "0123456789abcdef0123456789abcdef";
        assert_eq!(short_hash(hash), &hash[..HASH_PREFIX_HEX]);
    }

    #[test]
    fn short_hash_returns_a_short_id_whole() {
        assert_eq!(short_hash("abc"), "abc");
    }

    #[test]
    fn short_hash_does_not_panic_when_byte_boundary_splits_a_multibyte_char() {
        // A multibyte char straddles the prefix width, so a raw byte slice at
        // HASH_PREFIX_HEX would land mid-character. The abbreviation must truncate
        // on a char boundary instead of panicking on untrusted input.
        let hash = "0123456789abcde\u{00e9}tail";
        let short = short_hash(hash);
        assert!(hash.starts_with(short));
        assert!(short.len() <= hash.len());
    }
}
