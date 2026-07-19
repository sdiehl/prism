//! The content-addressed lock manifest for stable migrations.
//!
//! Freezing a rung's record shape is not enough: the same old bytes could decode
//! into a different current value if an upgrade body changed while both record
//! shapes stayed fixed. Every ordinary function already carries a canonical
//! semantic hash over pre-optimizer Core; a stable migration reuses that identity
//! rather than introducing a second behavioral hashing system.
//!
//! This module is the pure half: the identity scheme (an edge hash over a family,
//! its two adjacent rung shape digests, and the upgrade and downgrade semantic
//! hashes; a route hash over a family, its endpoint shapes, and the ordered
//! adjacent edge identities it composes), the manifest data model, its canonical
//! serialization, and the drift comparison. Deriving a manifest from source (which
//! needs the per-definition Core hashes) and comparing it against a committed file
//! live in `driver::stable_lock`; building one family's record from a `stable`
//! block lives beside the rest of the rung logic in `syntax::desugar::stable`.
//!
//! Every identity here is a pure function of the source and the pinned inputs: the
//! shape digests are structural, and the component hashes are taken over
//! pre-optimizer Core, so no backend, optimizer level, or checkout root can move a
//! hash. That is the determinism contract the manifest exists to hold.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use serde::{Deserialize, Serialize};

use crate::names::{
    STABLE_LOCK_MANIFEST_FORMAT, STABLE_MIGRATION_EDGE_SCHEME, STABLE_MIGRATION_ROUTE_SCHEME,
};

// A migration route mode, recorded for review and rendered in the preview. The
// identity a build compares is the hash set, never the mode: an `auto` row and a
// handwritten converter that elaborate to the same Core carry the same hashes and
// so are not drift, even though their modes read differently.
pub const MODE_AUTO: &str = "auto";
pub const MODE_DEFAULT: &str = "default";
pub const MODE_MANUAL: &str = "manual";

// One tagged content hash: the scheme tag followed by each length-prefixed field,
// so no field's bytes can forge a boundary and collide two distinct inputs. The
// same discipline `driver::identity::interface_digest` uses.
fn tagged(scheme: &str, fields: &[&str]) -> String {
    let mut h = blake3::Hasher::new();
    h.update(scheme.as_bytes());
    for field in fields {
        h.update(&(field.len() as u64).to_le_bytes());
        h.update(field.as_bytes());
    }
    h.finalize().to_hex().to_string()
}

/// The identity of one adjacent migration edge: the family, the source and target
/// rung shape digests, and the upgrade and downgrade canonical semantic hashes.
///
/// Defaults ride in the upgrade hash and generated loss labels ride in the
/// downgrade hash, because both are string literals in the converters' Core, so
/// the two component hashes already commit to them.
#[must_use]
pub fn edge_hash(
    family: &str,
    source_shape: &str,
    target_shape: &str,
    upgrade: &str,
    downgrade: &str,
) -> String {
    tagged(
        STABLE_MIGRATION_EDGE_SCHEME,
        &[family, source_shape, target_shape, upgrade, downgrade],
    )
}

/// The identity of one explicitly supported longer route: the family, its endpoint
/// shape digests, and the ordered adjacent edge identities it composes.
///
/// The route commits to composition order without copying or rehashing the
/// composed bodies, so changing one rung invalidates precisely the routes crossing
/// it and no others.
#[must_use]
pub fn route_hash(
    family: &str,
    source_shape: &str,
    target_shape: &str,
    edges: &[String],
) -> String {
    let mut fields: Vec<&str> = Vec::with_capacity(edges.len() + 3);
    fields.push(family);
    fields.push(source_shape);
    fields.push(target_shape);
    for edge in edges {
        fields.push(edge);
    }
    tagged(STABLE_MIGRATION_ROUTE_SCHEME, &fields)
}

/// One rung's version tag paired with its structural shape digest.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RungShape {
    pub ver: String,
    pub shape: String,
}

/// The locked identity of one adjacent migration edge.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EdgeLock {
    pub from: String,
    pub to: String,
    /// Descriptive route mode; never part of the drift comparison.
    pub mode: String,
    /// Canonical semantic hash of the upgrade function.
    pub upgrade: String,
    /// Canonical semantic hash of the downgrade function.
    pub downgrade: String,
    /// The edge identity over the family, both shapes, and the two component hashes.
    pub edge: String,
    /// The derived downgrade loss paths, recorded for the drift diagnostic. They
    /// already ride inside `downgrade`; this is the human-readable projection.
    pub loss: Vec<String>,
}

/// The locked identity of one explicitly supported longer route.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RouteLock {
    pub from: String,
    pub to: String,
    /// Descriptive route mode; never part of the drift comparison.
    pub mode: String,
    /// The ordered adjacent edge identities this route composes.
    pub edges: Vec<String>,
    /// The route identity over the family, both endpoint shapes, and `edges`.
    pub route: String,
}

/// The locked identity of one stable family's migration surface.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FamilyLock {
    /// The rung shape digests, oldest rung first, current rung last.
    pub rungs: Vec<RungShape>,
    /// The adjacent ladder edges, oldest edge first.
    pub edges: Vec<EdgeLock>,
    /// The explicitly declared longer routes to the current rung, by source rung.
    pub routes: Vec<RouteLock>,
}

/// A committed lock manifest: the locked families, keyed by family name.
///
/// A family present here is locked and re-derived on the next build; a family
/// absent here is not checked, exactly as an unfrozen rung is not checked.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LockManifest {
    pub format: String,
    pub families: BTreeMap<String, FamilyLock>,
}

/// One changed identity within a drifted edge or route.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DriftLine {
    pub label: String,
    pub old: String,
    pub new: String,
}

/// A detected drift: a locked family whose re-derived identity no longer matches
/// the manifest. Names the family, the drifted edge or route, the changed
/// component identities, and the derived loss paths.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Drift {
    pub family: String,
    pub edge: String,
    pub changes: Vec<DriftLine>,
    pub loss: Vec<String>,
}

impl LockManifest {
    /// An empty manifest: no family is locked.
    #[must_use]
    pub fn empty() -> Self {
        Self {
            format: STABLE_LOCK_MANIFEST_FORMAT.to_string(),
            families: BTreeMap::new(),
        }
    }

    /// True when no family is locked.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.families.is_empty()
    }

    /// The canonical serialization written to the committed lock file.
    ///
    /// Deterministic: families are name-sorted (a `BTreeMap`) and every inner
    /// sequence is already in semantic order, so the bytes are stable across roots
    /// and declaration reordering, and a second serialization of an unchanged
    /// manifest is byte-identical.
    ///
    /// # Errors
    /// Fails only if serialization of this closed data structure fails.
    pub fn to_text(&self) -> Result<String, serde_json::Error> {
        let mut text = serde_json::to_string_pretty(self)?;
        text.push('\n');
        Ok(text)
    }

    /// Read a committed lock file, rejecting a foreign format version.
    ///
    /// # Errors
    /// Fails on malformed JSON or an unrecognized `format` tag.
    pub fn from_text(text: &str) -> Result<Self, String> {
        let manifest: Self = serde_json::from_str(text).map_err(|e| e.to_string())?;
        if manifest.format != STABLE_LOCK_MANIFEST_FORMAT {
            return Err(format!(
                "unsupported stable lock manifest format {:?}",
                manifest.format
            ));
        }
        Ok(manifest)
    }

    /// A readable preview of every locked family, rung, edge, and route identity,
    /// printed before a lock is written so the change is reviewable.
    #[must_use]
    pub fn render(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "{}", self.format);
        for (name, family) in &self.families {
            let _ = writeln!(out, "family {name}");
            for rung in &family.rungs {
                let _ = writeln!(out, "  rung {} shape {}", rung.ver, rung.shape);
            }
            for edge in &family.edges {
                let _ = writeln!(
                    out,
                    "  edge {} -> {} [{}] up {} down {} edge {}",
                    edge.from, edge.to, edge.mode, edge.upgrade, edge.downgrade, edge.edge
                );
                if !edge.loss.is_empty() {
                    let _ = writeln!(out, "    loss {}", edge.loss.join(", "));
                }
            }
            for route in &family.routes {
                let _ = writeln!(
                    out,
                    "  route {} -> {} [{}] route {}",
                    route.from, route.to, route.mode, route.route
                );
            }
        }
        out
    }
}

/// The first drift of any locked family in `committed` against its re-derived
/// counterpart in `derived`, or `None` when every locked family re-verifies clean.
///
/// Only the content identities are compared (shape digests, component and edge
/// hashes, route hashes); the descriptive mode is ignored, so replacing an `auto`
/// row with a handwritten converter that elaborates to the same Core is not drift.
/// A family absent from `derived` (its `stable` block was removed) drifts, since
/// its locked behavior is no longer addressable.
#[must_use]
pub fn first_drift(committed: &LockManifest, derived: &LockManifest) -> Option<Drift> {
    for (name, locked) in &committed.families {
        let Some(fresh) = derived.families.get(name) else {
            return Some(Drift {
                family: name.clone(),
                edge: "family".to_string(),
                changes: vec![DriftLine {
                    label: "present".to_string(),
                    old: "locked".to_string(),
                    new: "removed".to_string(),
                }],
                loss: Vec::new(),
            });
        };
        if let Some(drift) = family_drift(name, locked, fresh) {
            return Some(drift);
        }
    }
    None
}

fn family_drift(name: &str, locked: &FamilyLock, fresh: &FamilyLock) -> Option<Drift> {
    for locked_rung in &locked.rungs {
        let fresh_shape = fresh
            .rungs
            .iter()
            .find(|r| r.ver == locked_rung.ver)
            .map(|r| r.shape.as_str());
        if fresh_shape != Some(locked_rung.shape.as_str()) {
            return Some(Drift {
                family: name.to_string(),
                edge: format!("rung {}", locked_rung.ver),
                changes: vec![DriftLine {
                    label: "shape".to_string(),
                    old: locked_rung.shape.clone(),
                    new: fresh_shape.unwrap_or("absent").to_string(),
                }],
                loss: Vec::new(),
            });
        }
    }
    for locked_edge in &locked.edges {
        let fresh_edge = fresh
            .edges
            .iter()
            .find(|e| e.from == locked_edge.from && e.to == locked_edge.to);
        let label = format!("{} -> {}", locked_edge.from, locked_edge.to);
        let changes = fresh_edge.map_or_else(
            || {
                vec![DriftLine {
                    label: "edge".to_string(),
                    old: locked_edge.edge.clone(),
                    new: "absent".to_string(),
                }]
            },
            |fresh| edge_changes(locked_edge, fresh),
        );
        if !changes.is_empty() {
            let loss = fresh_edge.map_or_else(|| locked_edge.loss.clone(), |e| e.loss.clone());
            return Some(Drift {
                family: name.to_string(),
                edge: label,
                changes,
                loss,
            });
        }
    }
    for locked_route in &locked.routes {
        let fresh_route = fresh
            .routes
            .iter()
            .find(|r| r.from == locked_route.from && r.to == locked_route.to);
        let new = fresh_route.map_or("absent", |r| r.route.as_str());
        if new != locked_route.route {
            return Some(Drift {
                family: name.to_string(),
                edge: format!("route {} -> {}", locked_route.from, locked_route.to),
                changes: vec![DriftLine {
                    label: "route".to_string(),
                    old: locked_route.route.clone(),
                    new: new.to_string(),
                }],
                loss: Vec::new(),
            });
        }
    }
    None
}

fn edge_changes(locked: &EdgeLock, fresh: &EdgeLock) -> Vec<DriftLine> {
    let mut changes = Vec::new();
    let mut note = |label: &str, old: &str, new: &str| {
        if old != new {
            changes.push(DriftLine {
                label: label.to_string(),
                old: old.to_string(),
                new: new.to_string(),
            });
        }
    };
    note("upgrade", &locked.upgrade, &fresh.upgrade);
    note("downgrade", &locked.downgrade, &fresh.downgrade);
    note("edge", &locked.edge, &fresh.edge);
    changes
}

#[cfg(test)]
mod tests {
    use super::*;

    fn edge(mode: &str) -> EdgeLock {
        EdgeLock {
            from: "V1".to_string(),
            to: "V2".to_string(),
            mode: mode.to_string(),
            upgrade: "up".to_string(),
            downgrade: "down".to_string(),
            edge: "e".to_string(),
            loss: vec!["fog".to_string()],
        }
    }

    fn family(edge: EdgeLock) -> FamilyLock {
        FamilyLock {
            rungs: vec![
                RungShape {
                    ver: "V1".to_string(),
                    shape: "s1".to_string(),
                },
                RungShape {
                    ver: "V2".to_string(),
                    shape: "s2".to_string(),
                },
            ],
            edges: vec![edge],
            routes: Vec::new(),
        }
    }

    // Replacing an `auto` row with a handwritten converter that elaborates to the
    // same Core changes the recorded mode but nothing hashed, so it is not drift.
    #[test]
    fn mode_is_not_part_of_the_compared_identity() {
        let committed = LockManifest {
            format: STABLE_LOCK_MANIFEST_FORMAT.to_string(),
            families: BTreeMap::from([("Save".to_string(), family(edge(MODE_AUTO)))]),
        };
        let derived = LockManifest {
            format: STABLE_LOCK_MANIFEST_FORMAT.to_string(),
            families: BTreeMap::from([("Save".to_string(), family(edge(MODE_MANUAL)))]),
        };
        assert_eq!(first_drift(&committed, &derived), None);
    }

    // The route identity commits to composition order, so the same edges in a
    // different order are a different route.
    #[test]
    fn route_hash_commits_to_composition_order() {
        let forward = route_hash("Save", "s1", "s3", &["a".to_string(), "b".to_string()]);
        let backward = route_hash("Save", "s1", "s3", &["b".to_string(), "a".to_string()]);
        assert_ne!(forward, backward);
    }
}
