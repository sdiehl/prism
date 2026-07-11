//! Store-level instance coherence: the `(class, type-head) -> canonical
//! instance-hash` bindings written when a program is committed, and the
//! cross-program conflict that makes a second, divergent canonical for one key a
//! hard error.
//!
//! The file world already enforces coherence *within* one program: at most one
//! canonical instance per `(class, type-head)`, with a second undesignated
//! instance a definition-site error (see `crate::tc`). This layer lifts that
//! guarantee *across* programs. Each program that commits records the
//! content-addressed identity of its canonical instance for a key
//! ([`crate::core::instance_digest`], the same digest the stdlib fingerprint
//! uses); committing a program whose canonical for some key differs from the one
//! already bound is refused, because two assembled programs disagreeing on
//! `Ord(Int)` is exactly the incoherence the store exists to prevent. A
//! same-hash re-commit is a no-op.
//!
//! Because the store is opt-in (a cache, never required for correctness), this fires only on
//! the commit path; normal compilation is unchanged.

use std::collections::BTreeMap;
use std::io;

use crate::core::{instance_digest, Digest, Hashes};
use crate::names::instance_method_prefix;
use crate::store::disk::{CanonicalKey, Store};
use crate::syntax::ast::{CanonicalDecl, InstanceDecl, Phase, Span, Ty};

// The classes whose instance choice affects a container's runtime representation
// and must therefore be reified into container type identity for cross-program
// coherence: a `Set`/`Map` built under one `Ord`/`Hash` and shipped to a program
// that canonicalized a different one is silent corruption. Reserved for that
// later reification pass; no caller reads it yet, and the rest of coherence is
// representation-neutral (`Show`, `Functor`, and the like are harmless to mix).
// This is the one canonical home the reification will consult.
const REPRESENTATION_AFFECTING: &[&str] = &["Ord", "Hash"];

/// Whether a class's instance choice affects representation.
///
/// A cross-program value of a representation-affecting class must carry that
/// instance's hash in its type for coherence to survive the boundary. Reserved:
/// reification is a later release and nothing reads this today; it fixes the
/// classification in one place so the shape is not a breaking change when that
/// pass lands.
#[must_use]
pub fn is_representation_affecting(class: &str) -> bool {
    REPRESENTATION_AFFECTING.contains(&class)
}

/// A failed coherence commit: a filesystem error, or a genuine conflict against a
/// binding another program already committed.
#[derive(Debug)]
pub enum CoherenceError {
    /// A store filesystem error while reading or writing the canonical index.
    Io(io::Error),
    /// A different instance is already canonical for this `(class, head)`.
    Conflict {
        /// The offending instance or `canonical` declaration.
        span: Span,
        /// The rendered caret diagnostic, naming the class, head, and both hashes.
        msg: String,
    },
}

impl From<io::Error> for CoherenceError {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}

// One program's canonical binding for a `(class, head)`: the key, the instance's
// content-addressed identity, and where to caret a conflict.
struct Binding {
    key: CanonicalKey,
    instance_hash: String,
    span: Span,
}

/// Compute a program's canonical bindings and commit them, refusing any that
/// conflicts with a binding already in the store.
///
/// For each `(class, head)` the program's canonical instance is the sole instance
/// (canonical automatically) or, when several share the head, the one a
/// `canonical` declaration designates. Its identity digest is checked against the
/// store: an equal binding is a no-op, a different one is a [`CoherenceError::Conflict`],
/// and an absent one is written. Conflicts are detected before any write, so a
/// rejected commit leaves the canonical index untouched.
///
/// # Errors
/// Returns [`CoherenceError::Conflict`] when this program's canonical for some
/// key differs from the committed one, or [`CoherenceError::Io`] on a filesystem
/// error.
pub fn commit_canonical<P: Phase>(
    store: &Store,
    instances: &[InstanceDecl<P>],
    canonicals: &[CanonicalDecl],
    hashes: &Hashes,
) -> Result<(), CoherenceError> {
    let bindings = canonical_bindings(instances, canonicals, hashes);
    let rows: Vec<_> = bindings
        .iter()
        .map(|b| (b.key.clone(), b.instance_hash.clone()))
        .collect();
    if let Err(conflict) = store.merge_canonicals(&rows)? {
        let Some(b) = bindings.get(conflict.incoming_index) else {
            return Err(CoherenceError::Io(io::Error::other(
                "canonical conflict did not correspond to an incoming binding",
            )));
        };
        return Err(CoherenceError::Conflict {
            span: b.span,
            msg: conflict_msg(&b.key, &conflict.existing, &b.instance_hash),
        });
    }
    Ok(())
}

// The canonical binding of every `(class, head)` the program designates one for.
// Iterated deterministically (the group map is ordered) so a conflict diagnostic
// is stable across runs.
fn canonical_bindings<P: Phase>(
    instances: &[InstanceDecl<P>],
    canonicals: &[CanonicalDecl],
    hashes: &Hashes,
) -> Vec<Binding> {
    // Instances sharing a `(class, head)`; and the explicit designation for each
    // such key, if any.
    let mut groups: BTreeMap<(String, String), Vec<&InstanceDecl<P>>> = BTreeMap::new();
    for i in instances {
        if let Some(head) = head_key(&i.head) {
            groups.entry((i.class.clone(), head)).or_default().push(i);
        }
    }
    let mut designated: BTreeMap<(String, String), &CanonicalDecl> = BTreeMap::new();
    for c in canonicals {
        if let Some(head) = head_key(&c.head) {
            designated.insert((c.class.clone(), head), c);
        }
    }

    let mut out = Vec::new();
    for (key, group) in &groups {
        // The canonical instance: the sole one, or the designated one when several
        // share the head. An undesignated overlap is already a typecheck error, so
        // the commit path never reaches it; skip defensively rather than guess.
        let decl = designated.get(key);
        let chosen: &InstanceDecl<P> = if group.len() == 1 {
            group[0]
        } else {
            match decl.and_then(|d| group.iter().find(|i| i.name == d.name).copied()) {
                Some(i) => i,
                None => continue,
            }
        };
        let methods = method_hashes(&chosen.name, hashes);
        out.push(Binding {
            key: CanonicalKey {
                class: key.0.clone(),
                head: key.1.clone(),
            },
            instance_hash: instance_digest(&chosen.class, &chosen.head, &methods).into_string(),
            // Caret the `canonical` declaration when one designates this key (that
            // is where the author re-designates); otherwise the instance itself.
            span: decl.map_or(chosen.span, |d| d.span),
        });
    }
    out
}

// An instance's method behavior hashes, keyed by method name, recovered from the
// lowered `i@<inst>@<method>` CoreFns. Mirrors the stdlib fingerprint so an
// instance's store identity equals the one the fingerprint anchors.
fn method_hashes(inst: &str, hashes: &Hashes) -> BTreeMap<String, Digest> {
    let prefix = instance_method_prefix(inst);
    hashes
        .iter()
        .filter_map(|(k, v)| {
            k.as_str()
                .strip_prefix(&prefix)
                .map(|m| (m.to_string(), v.clone()))
        })
        .collect()
}

// The type-head key an instance is stored under: the head constructor's name,
// arguments dropped (an instance head is a primitive or a constructor applied to
// distinct variables, so the outermost name identifies it). `None` for a head
// with no nominal constructor, which an instance head never is.
fn head_key(head: &Ty) -> Option<String> {
    let name = match head {
        Ty::Int => "Int",
        Ty::I64 => "I64",
        Ty::U64 => "U64",
        Ty::Bool => "Bool",
        Ty::Unit => "Unit",
        Ty::Float => "Float",
        Ty::Char => "Char",
        Ty::Str => "Str",
        Ty::Con(n, _) => return Some(n.clone()),
        _ => return None,
    };
    Some(name.to_string())
}

// The conflict diagnostic: names the class, the head, both instance hashes, and
// the remedy.
fn conflict_msg(key: &CanonicalKey, existing: &str, incoming: &str) -> String {
    let CanonicalKey { class, head } = key;
    format!(
        "instance coherence conflict for {class}({head}): the store already binds \
         instance {existing} as canonical, but committing this program would bind a \
         different instance {incoming}; one canonical instance per (class, type head) \
         must hold across every program sharing the store, so re-designate explicitly \
         with `canonical {class}({head}) = name` to agree with the committed instance"
    )
}
