//! Diffing two indexes: what changed between one revision and another.
//!
//! This compares two existing artifacts without running the compiler.
//!
//! Content addressing folds dependencies into each definition's hash. Comparing
//! the hash with the source distinguishes direct edits from dependent rehashes:
//!
//! | hash | source | meaning |
//! |------|--------|---------|
//! | same | same   | untouched |
//! | same | differs| [`Status::Cosmetic`]: reformatted or recommented, same behavior |
//! | differs | differs | [`Status::Changed`]: the author edited this |
//! | differs | same | [`Status::Cone`]: only a dependency moved |
//!
//! Claims, visibility, documentation, and deprecation are compared separately
//! because they do not affect executable hashes. Changes to them are authored.
//!
//! A rename is likewise free: a definition whose bytes are unchanged but whose
//! canonical name moved keeps its hash, so it appears as [`Status::Moved`] rather
//! than as an unrelated add and delete.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use super::{Def, Edge, Index};

/// Schema tag for the diff artifact.
pub const INDEX_DIFF_FORMAT: &str = "prism-index-diff-v1";

/// What happened to one definition between the two revisions.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Status {
    /// Present only in the new revision.
    Added,
    /// Present only in the old revision.
    Removed,
    /// The same bytes under a different canonical name: a rename, or a move
    /// between modules. Recognized by hash, so it is a fact rather than a
    /// similarity heuristic.
    Moved,
    /// The author edited this definition: its behavior moved, or a review-facing
    /// fact its hash never sees did (claims, visibility, doc, deprecation).
    Changed,
    /// Its text is byte-identical; it re-hashed only because something it depends
    /// on changed. The dependent cone of the real edits.
    Cone,
    /// Its text changed but its behavior did not: a reformat, a comment, a
    /// renamed local. Worth separating from a real edit, and from noise.
    Cosmetic,
}

impl Status {
    /// Whether this is something the author did, as opposed to something that
    /// happened to a definition because of what the author did elsewhere.
    #[must_use]
    pub const fn is_authored(self) -> bool {
        matches!(
            self,
            Self::Added | Self::Removed | Self::Moved | Self::Changed
        )
    }
}

/// One definition's fate, carrying whichever revisions of it exist.
///
/// The records travel with the entry so the artifact is self-contained: a
/// consumer renders a side-by-side without also loading both indexes, exactly as
/// it renders a definition without loading its source file.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Entry {
    pub status: Status,
    /// The canonical name in the new revision, or the old one when removed.
    pub id: String,
    /// The old canonical name, when [`Status::Moved`] made it differ from `id`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub old_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub old: Option<Def>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub new: Option<Def>,
}

/// One side of the comparison.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Side {
    pub title: String,
    /// That revision's namespace root, used to validate the diff's inputs.
    pub contract: String,
    /// The highlight classes indexed by this side's [`Def::tokens`].
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub token_classes: Vec<String>,
    /// The rendered types this side's carried [`Def::types`] index, for the
    /// same reason.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub type_table: Vec<String>,
}

/// How many definitions fell into each class, including the untouched ones the
/// entry list omits.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
pub struct Counts {
    pub added: usize,
    pub removed: usize,
    pub moved: usize,
    pub changed: usize,
    pub cone: usize,
    pub cosmetic: usize,
    pub unchanged: usize,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct DiffEnvelope {
    pub format: String,
    pub compiler: String,
    pub old: Side,
    pub new: Side,
    pub counts: Counts,
}

/// The edges one revision has and the other does not.
///
/// The entries carry each changed definition's two records, which is enough to
/// show its two bodies but not its two *neighbourhoods*: who called it before,
/// what it called, which tests reached it. Those are edges, and an edge's other
/// end is very often an untouched definition the entry list omits. Carrying the
/// whole old edge set would repeat the index; carrying the difference is a few
/// rows per edit, and a consumer that has the new index recovers the old edge
/// set exactly as `new − added + removed`.
///
/// Always present, even when empty, so a consumer can tell "nothing moved" from
/// an artifact written before the delta existed.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
pub struct EdgeDelta {
    /// In the new revision only. Sorted like an index's edge list.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub added: Vec<Edge>,
    /// In the old revision only.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub removed: Vec<Edge>,
}

/// The diff artifact.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct IndexDiff {
    pub envelope: DiffEnvelope,
    /// Every definition that is not untouched, ordered by status and then by
    /// name. Untouched definitions are omitted rather than listed: a review view
    /// wants what moved, and the count is in the envelope.
    pub entries: Vec<Entry>,
    /// What moved in the dependency graph. Absent only in an artifact older
    /// than the field, which a consumer should treat as "unknown" rather than
    /// "nothing".
    #[serde(default)]
    pub edges: Option<EdgeDelta>,
}

impl IndexDiff {
    /// Serialize with stable indentation and field order.
    ///
    /// # Errors
    /// Fails only if the derived JSON serializer rejects the document.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        let mut json = serde_json::to_string_pretty(self)?;
        json.push('\n');
        Ok(json)
    }

    /// Decode and validate a diff artifact.
    ///
    /// # Errors
    /// Refuses an unknown format tag, or an entry whose carried revisions do not
    /// match its status.
    pub fn from_json(text: &str) -> Result<Self, String> {
        let doc: Self = serde_json::from_str(text).map_err(|e| e.to_string())?;
        if doc.envelope.format != INDEX_DIFF_FORMAT {
            return Err(format!(
                "unsupported index-diff format `{}` (expected `{INDEX_DIFF_FORMAT}`)",
                doc.envelope.format
            ));
        }
        for e in &doc.entries {
            let want = match e.status {
                Status::Added => e.old.is_none() && e.new.is_some(),
                Status::Removed => e.old.is_some() && e.new.is_none(),
                _ => e.old.is_some() && e.new.is_some(),
            };
            if !want {
                return Err(format!(
                    "`{}` is {:?} but carries the wrong revisions",
                    e.id, e.status
                ));
            }
        }
        Ok(doc)
    }

    /// A one-line human summary, in the order a reviewer cares about.
    #[must_use]
    pub fn summary(&self) -> String {
        let c = self.envelope.counts;
        format!(
            "{} changed, {} added, {} removed, {} moved, {} in the cone, {} cosmetic, \
             {} unchanged",
            c.changed, c.added, c.removed, c.moved, c.cone, c.cosmetic, c.unchanged
        )
    }
}

/// Compare two indexes.
///
/// # Errors
/// Refuses a pair whose envelopes commit to different hash schemes. Digests
/// from different schemes are not comparable in either direction: equal strings
/// prove nothing, and unequal ones would report identical source as a
/// program-wide dependency cone. The stale side must be regenerated by a
/// compiler speaking the current scheme.
pub fn diff(old: &Index, new: &Index) -> Result<IndexDiff, String> {
    if old.envelope.scheme != new.envelope.scheme {
        return Err(format!(
            "cannot compare addresses across hash schemes: the old index commits to \
             `{}` and the new to `{}`; regenerate the old artifact with the current \
             compiler",
            old.envelope.scheme, new.envelope.scheme
        ));
    }
    let old_by_id: BTreeMap<&str, &Def> = old.defs.iter().map(|d| (d.id.as_str(), d)).collect();
    let new_by_id: BTreeMap<&str, &Def> = new.defs.iter().map(|d| (d.id.as_str(), d)).collect();

    let mut counts = Counts::default();
    let mut entries = Vec::new();

    // Definitions under the same name in both revisions.
    for (id, new_def) in &new_by_id {
        let Some(old_def) = old_by_id.get(id) else {
            continue;
        };
        let status = classify(old_def, new_def);
        match status {
            Some(Status::Cone) => counts.cone += 1,
            Some(Status::Cosmetic) => counts.cosmetic += 1,
            Some(_) => counts.changed += 1,
            None => {
                counts.unchanged += 1;
                continue;
            }
        }
        entries.push(Entry {
            status: status.unwrap_or(Status::Changed),
            id: (*id).to_string(),
            old_id: None,
            old: Some((*old_def).clone()),
            new: Some((*new_def).clone()),
        });
    }

    // What is left is present on one side only: a rename keeps its bytes, so pair
    // those off by hash before calling anything added or removed.
    let gone: Vec<&Def> = old
        .defs
        .iter()
        .filter(|d| !new_by_id.contains_key(d.id.as_str()))
        .collect();
    let fresh: Vec<&Def> = new
        .defs
        .iter()
        .filter(|d| !old_by_id.contains_key(d.id.as_str()))
        .collect();
    let (moved, gone, fresh) = pair_moves(&gone, &fresh);

    for (old_def, new_def) in moved {
        counts.moved += 1;
        entries.push(Entry {
            status: Status::Moved,
            id: new_def.id.clone(),
            old_id: Some(old_def.id.clone()),
            old: Some(old_def.clone()),
            new: Some(new_def.clone()),
        });
    }
    for d in gone {
        counts.removed += 1;
        entries.push(Entry {
            status: Status::Removed,
            id: d.id.clone(),
            old_id: None,
            old: Some(d.clone()),
            new: None,
        });
    }
    for d in fresh {
        counts.added += 1;
        entries.push(Entry {
            status: Status::Added,
            id: d.id.clone(),
            old_id: None,
            old: None,
            new: Some(d.clone()),
        });
    }

    // Authored changes first, then the cone they caused, then noise; by name
    // within each. A reviewer reads this top to bottom.
    entries.sort_by(|a, b| a.status.cmp(&b.status).then_with(|| a.id.cmp(&b.id)));

    // Both edge lists are sorted and deduplicated, so the two differences are
    // set differences and come out in the same order.
    let old_edges: BTreeSet<&Edge> = old.edges.iter().collect();
    let new_edges: BTreeSet<&Edge> = new.edges.iter().collect();
    let edges = EdgeDelta {
        added: new_edges
            .difference(&old_edges)
            .map(|e| (*e).clone())
            .collect(),
        removed: old_edges
            .difference(&new_edges)
            .map(|e| (*e).clone())
            .collect(),
    };

    Ok(IndexDiff {
        envelope: DiffEnvelope {
            format: INDEX_DIFF_FORMAT.to_string(),
            compiler: new.envelope.compiler.clone(),
            old: Side {
                title: old.envelope.title.clone(),
                contract: old.envelope.contract.clone(),
                token_classes: old.token_classes.clone(),
                type_table: old.type_table.clone(),
            },
            new: Side {
                title: new.envelope.title.clone(),
                contract: new.envelope.contract.clone(),
                token_classes: new.token_classes.clone(),
                type_table: new.type_table.clone(),
            },
            counts,
        },
        entries,
        edges: Some(edges),
    })
}

// The fate of a definition present under the same name in both revisions, or
// `None` when nothing about it moved.
//
// A kind that carries no content address (a synonym, a row alias) can only be
// compared by text, so a change to it always reads as authored; there is no hash
// to tell a cone re-address from a real edit, and claiming otherwise would be a
// guess.
fn classify(old: &Def, new: &Def) -> Option<Status> {
    let same_text = old.source == new.source;
    // Claims and other review metadata do not affect the behavior hash. Doc
    // comments also sit outside `source`, so compare all metadata explicitly.
    let same_meta = old.claims == new.claims
        && old.vis == new.vis
        && old.doc == new.doc
        && old.deprecated == new.deprecated;
    match (&old.hash, &new.hash) {
        // Same address: executable behavior is identical by construction. What
        // the author can still have edited is the metadata above; failing that,
        // any text difference is presentation.
        (Some(a), Some(b)) if a == b => {
            if same_meta {
                (!same_text).then_some(Status::Cosmetic)
            } else {
                Some(Status::Changed)
            }
        }
        // Both addressed and the address moved. Unmoved text and metadata mean
        // nothing here was edited and only a dependency did.
        (Some(_), Some(_)) => Some(if same_text && same_meta {
            Status::Cone
        } else {
            Status::Changed
        }),
        // Neither is addressed (a synonym, a row alias): text and metadata are
        // all there is to compare, so a difference always reads as authored.
        // There is no hash to tell a cone re-address from a real edit, and
        // claiming otherwise would be a guess.
        (None, None) => (!same_text || !same_meta).then_some(Status::Changed),
        // One side addressed and the other not: the definition entered or left the
        // compiled program, which is a real change to what the build contains.
        (None, Some(_)) | (Some(_), None) => Some(Status::Changed),
    }
}

// Pair a removed definition with an added one that has its exact bytes: a rename
// or a move between modules.
//
// Only an unambiguous pairing counts. Two definitions can legitimately share a
// behavior hash (that is the dedup property), so a hash matching several
// candidates on either side identifies nothing, and guessing which went where
// would invent a rename that may not have happened.
fn pair_moves<'a>(
    gone: &[&'a Def],
    fresh: &[&'a Def],
) -> (Vec<(&'a Def, &'a Def)>, Vec<&'a Def>, Vec<&'a Def>) {
    let mut by_hash: BTreeMap<&str, (Vec<&'a Def>, Vec<&'a Def>)> = BTreeMap::new();
    for d in gone {
        if let Some(h) = &d.hash {
            by_hash.entry(h.as_str()).or_default().0.push(d);
        }
    }
    for d in fresh {
        if let Some(h) = &d.hash {
            by_hash.entry(h.as_str()).or_default().1.push(d);
        }
    }
    let mut moved = Vec::new();
    let mut paired: BTreeSet<&str> = BTreeSet::new();
    for (_, (from, to)) in by_hash {
        if let ([old], [new]) = (from.as_slice(), to.as_slice()) {
            paired.insert(old.id.as_str());
            paired.insert(new.id.as_str());
            moved.push((*old, *new));
        }
    }
    let unpaired = |set: &[&'a Def]| -> Vec<&'a Def> {
        set.iter()
            .filter(|d| !paired.contains(d.id.as_str()))
            .copied()
            .collect()
    };
    (moved, unpaired(gone), unpaired(fresh))
}
