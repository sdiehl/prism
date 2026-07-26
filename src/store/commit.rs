//! Committing an elaborated program into the content store.
//!
//! The one write path that knows Core's shape (definitions, SCC groups,
//! dependency edges). Lives above the generic disk store because a store
//! object is just bytes; only the compiler knows a program's decomposition
//! into them.

use std::collections::{BTreeMap, BTreeSet};
use std::io;

use crate::core::{scc_groups, Core, CoreFn, DepGraph, Hashes};
use crate::store::codec;
use crate::store::disk::{CommitStats, DefMeta, Store, Written};
use crate::sym::Sym;

/// Commit a whole elaborated program into the store.
///
/// Writes one anonymous object per definition (via the [`codec`] seam), its
/// metadata, the name bindings, and the reverse-dependency edges. Idempotent:
/// committing an unchanged program a second time writes zero objects (every hash
/// is a hit).
///
/// `hashes` maps each definition's canonical symbol to its content hash;
/// `hash_meta` supplies each definition's rendered out-of-Core elaboration
/// inputs (type, principal row, borrow mask), the same string the content hash
/// commits to, which the codec round-trips verbatim; `graph` supplies direct
/// dependencies; `metas` supplies the human metadata-layer facts. A definition
/// without a hash (there should be none) is skipped.
///
/// # Errors
/// Fails on any filesystem error or a byte mismatch against an existing object
/// (which would mean two different definitions collided on one hash).
pub fn commit_program(
    store: &Store,
    core: &Core,
    hashes: &Hashes,
    hash_meta: &BTreeMap<Sym, String>,
    graph: &DepGraph,
    metas: &BTreeMap<Sym, DefMeta>,
) -> io::Result<CommitStats> {
    let mut stats = CommitStats::default();
    let mut names: BTreeMap<String, String> = BTreeMap::new();
    let mut dependents: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();

    let fnmap: BTreeMap<Sym, &CoreFn> = core.fns.iter().map(|f| (f.name, f)).collect();

    // A definition's content hash folds in its whole recursive group (a cycle's
    // members hash in each other), so each member's object serializes the group
    // and names which member it is keyed by. A singleton group is the common case.
    for group_syms in scc_groups(core) {
        let members: Vec<&CoreFn> = group_syms
            .iter()
            .filter_map(|s| fnmap.get(s).copied())
            .collect();
        if members.len() != group_syms.len() {
            continue;
        }

        for (target, func) in members.iter().enumerate() {
            let Some(hash) = hashes.get(&func.name) else {
                continue;
            };
            let payload = codec::encode_def(&codec::AnonEntry {
                group: &members,
                target,
                hash,
                deps: hashes,
                meta: hash_meta,
            });
            let derived = codec::decode_def(&payload)
                .ok()
                .and_then(|decoded| decoded.rehash())
                .ok_or_else(|| {
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!("could not rehash encoded object for {}", func.name.as_str()),
                    )
                })?;
            if &derived != hash {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "encoded object for {} hashes to {derived}, not store key {hash}",
                        func.name.as_str()
                    ),
                ));
            }
            match store.put(hash, &payload)? {
                Written::New => stats.objects_written += 1,
                Written::Hit => stats.objects_hit += 1,
            }

            if let Some(m) = metas.get(&func.name) {
                store.put_meta(hash, m)?;
                stats.meta_written += 1;
                names.insert(m.name.clone(), hash.as_str().to_string());
                stats.names_bound += 1;
            }

            // Reverse-dependency edges: each direct dependency hash gains this
            // definition as a dependent. Builtins carry no top-level hash and drop
            // out, exactly as the namespace export does.
            for dep in graph.direct_deps(func.name) {
                if let Some(dep_hash) = hashes.get(&dep) {
                    dependents
                        .entry(dep_hash.as_str().to_string())
                        .or_default()
                        .insert(hash.as_str().to_string());
                }
            }
        }
    }

    if !names.is_empty() {
        store.bind_names(&names)?;
    }
    if !dependents.is_empty() {
        store.add_dependents(&dependents)?;
    }
    Ok(stats)
}
