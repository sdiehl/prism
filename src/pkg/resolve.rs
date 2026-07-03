//! The resolver: the Merkle-DAG closure over a set of pinned root hashes.
//!
//! Resolution is not version solving. To resolve a build we walk the transitive
//! closure of the pinned root hashes over the dependency edges the store already
//! records inside each object, and that is the whole algorithm: no unification,
//! no ranges, no diamond conflicts, because two callers that pinned different
//! hashes for the same name simply hold two different hashes and each resolves
//! its own. The closure is read straight from the objects: every stored `def`
//! frame decodes to the content hashes of its direct Merkle children (its
//! external dependencies), so the walk is `fetch`, `decode`, recurse.
//!
//! Objects are read through the [`Transport`] seam, so the resolver does not know
//! or care whether an object comes from the local store, a git clone, or a
//! mirror; the transport verifies each fetched blob against the hash that asked
//! for it before returning it, so an untrusted host supplies availability but
//! never integrity. The resolver is driven local-store-only, by
//! a [`DiskTransport`](crate::pkg::transport::DiskTransport) over the configured
//! store: a hash absent from that store is a [`ResolveError::Missing`] naming the
//! hash and the edge that pulled it in, and pointing the transport at a remote is
//! the whole of what the transport stage adds.
//!
//! The resolved [`Closure`] is the store-backed build unit. The compiler funnels
//! every build through `resolve_modules_in` over a set of roots (`src/resolve/`),
//! so once the closure's objects are present locally it is the input a
//! store-backed build reads, exactly where `Root::Dir` source directories feed a
//! source build today. Materializing the closure's anonymous Core back into that
//! seam rides on `prism export` (the transport stage) and is left as the one
//! documented boundary, so the resolver stays independent of the pipeline below.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;

use crate::pkg::transport::{Transport, TransportError};
use crate::store::codec::decode_def;

/// The reason a closure walk could not complete.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolveError {
    /// A hash in the closure is not available through the transport. `wanted_by`
    /// is the dependent hash whose edge pulled it in, or `None` when the missing
    /// hash is a pinned root named directly.
    Missing {
        hash: String,
        wanted_by: Option<String>,
    },
    /// A transport or decode failure while reading an object (a corrupt object, an
    /// integrity mismatch the transport rejected, or a backing IO error).
    Transport(String),
}

impl fmt::Display for ResolveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Missing { hash, wanted_by } => match wanted_by {
                Some(parent) => write!(
                    f,
                    "missing object {hash}: pulled in by the dependency edge from {parent}, but \
                     no transport could supply it"
                ),
                None => write!(
                    f,
                    "missing object {hash}: this pinned root is not available through any transport"
                ),
            },
            Self::Transport(msg) => write!(f, "transport error during resolution: {msg}"),
        }
    }
}

impl std::error::Error for ResolveError {}

/// The transitive Merkle closure of a set of roots.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Closure {
    /// Every hash reachable from the roots, the roots included. This is the exact
    /// set of objects a build over these roots reads, and holding all of them is
    /// the warm-cache condition.
    pub hashes: BTreeSet<String>,
    /// The forward dependency edges: each hash mapped to the content hashes of its
    /// direct Merkle children, in the object's own order.
    pub edges: BTreeMap<String, Vec<String>>,
}

/// Walk the Merkle closure of `roots`, reading every object through `transport`.
///
/// Each hash reached is fetched (and, by the transport, verified) for its own
/// dependency edges, until the closure is complete. The returned [`Closure`] is
/// deterministic (its sets and maps are ordered) regardless of walk order.
///
/// # Errors
/// [`ResolveError::Missing`] when a hash cannot be supplied by the transport,
/// naming the edge that wanted it; [`ResolveError::Transport`] on a decode,
/// integrity, or backing failure.
pub fn resolve_closure(
    transport: &dyn Transport,
    roots: &[String],
) -> Result<Closure, ResolveError> {
    let mut closure = Closure::default();
    // Each queued hash carries the edge that requested it, so a missing object
    // names the dependent that pulled it in. Roots have no requesting edge.
    let mut queue: VecDeque<(String, Option<String>)> =
        roots.iter().map(|h| (h.clone(), None)).collect();

    while let Some((hash, wanted_by)) = queue.pop_front() {
        if !closure.hashes.insert(hash.clone()) {
            continue;
        }
        let bytes = fetch(transport, &hash, wanted_by.as_deref())?;
        let deps = decode_def(&bytes)
            .map_err(|e| ResolveError::Transport(format!("decoding {hash}: {e}")))?
            .dep_hashes;
        for dep in &deps {
            if !closure.hashes.contains(dep) {
                queue.push_back((dep.clone(), Some(hash.clone())));
            }
        }
        closure.edges.insert(hash, deps);
    }
    Ok(closure)
}

// Fetch one object, translating a transport "missing" into a resolver error that
// names the edge that wanted it.
fn fetch(
    transport: &dyn Transport,
    hash: &str,
    wanted_by: Option<&str>,
) -> Result<Vec<u8>, ResolveError> {
    transport.fetch(hash).map_err(|e| match e {
        TransportError::Missing(h) => ResolveError::Missing {
            hash: h,
            wanted_by: wanted_by.map(str::to_string),
        },
        other => ResolveError::Transport(other.to_string()),
    })
}

/// The dependency path that pulled `target` into the closure.
///
/// A chain of hashes from a pinned root down to `target`, root first, or `None`
/// when `target` is not in the closure. This is the answer `prism why` prints.
#[must_use]
pub fn trace(closure: &Closure, roots: &[String], target: &str) -> Option<Vec<String>> {
    if !closure.hashes.contains(target) {
        return None;
    }
    // Breadth-first over the forward edges from the roots, recording each hash's
    // discoverer, then walk the predecessors back from the target. BFS gives a
    // shortest such path, which is the least surprising explanation.
    let mut pred: BTreeMap<&str, &str> = BTreeMap::new();
    let mut queue: VecDeque<&str> = VecDeque::new();
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    for r in roots {
        if seen.insert(r) {
            queue.push_back(r);
        }
    }
    while let Some(h) = queue.pop_front() {
        if h == target {
            break;
        }
        for dep in closure.edges.get(h).into_iter().flatten() {
            if seen.insert(dep) {
                pred.insert(dep, h);
                queue.push_back(dep);
            }
        }
    }
    let mut chain = vec![target];
    let mut cur = target;
    while let Some(&p) = pred.get(cur) {
        chain.push(p);
        cur = p;
    }
    chain.reverse();
    Some(chain.into_iter().map(str::to_string).collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    // A tiny closure with a diamond: root -> {a, b}, a -> c, b -> c.
    fn diamond() -> Closure {
        let mut edges = BTreeMap::new();
        edges.insert("root".to_string(), vec!["a".to_string(), "b".to_string()]);
        edges.insert("a".to_string(), vec!["c".to_string()]);
        edges.insert("b".to_string(), vec!["c".to_string()]);
        edges.insert("c".to_string(), vec![]);
        let hashes = ["root", "a", "b", "c"]
            .iter()
            .map(ToString::to_string)
            .collect();
        Closure { hashes, edges }
    }

    #[test]
    fn trace_finds_a_path_from_a_root_to_a_leaf() {
        let c = diamond();
        let roots = vec!["root".to_string()];
        let path = trace(&c, &roots, "c").unwrap();
        assert_eq!(path.first().map(String::as_str), Some("root"));
        assert_eq!(path.last().map(String::as_str), Some("c"));
        // A diamond has two shortest paths; either is a valid explanation.
        assert!(path == ["root", "a", "c"] || path == ["root", "b", "c"]);
    }

    #[test]
    fn trace_of_a_root_is_the_singleton_and_of_an_absent_hash_is_none() {
        let c = diamond();
        let roots = vec!["root".to_string()];
        assert_eq!(trace(&c, &roots, "root"), Some(vec!["root".to_string()]));
        assert_eq!(trace(&c, &roots, "absent"), None);
    }
}
