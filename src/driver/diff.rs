//! The behavior-diff subsystem: hash two revisions of a source and report what
//! changed semantically (edited definitions, their dependents cone, and the
//! text-only respellings hashes cannot see). Split out of the driver so `mod.rs`
//! holds the compile pipeline and this module holds the content-addressed diff.
//! Every external path (`prism::diff_on`, `prism::source_diff_on`,
//! `prism::SourceDiff`) resolves through the re-export in `mod.rs`, so the split
//! is invisible to callers.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use crate::core::fbip::borrow_sigs;
use crate::core::{fip_annots, hash_program, DepGraph, Digest};
use crate::error::Error;
use crate::parse::parse;
use crate::resolve::Root;
use crate::sym::Sym;

use super::{elaborated, hash_meta, Config, PRELUDE};

// One revision's per-definition hashes and dependency graph. `deep` is the
// Merkle-substituted behavior identity (the regime `core-hash`, `namespace`, and
// the store commit all share, over pre-optimizer elaborated Core); `shallow` is
// each definition's own-content hash with dependencies by name, which attributes
// a deep-hash move to the definition actually edited rather than to a ripple
// through it (under the deep hash, editing one definition moves every transitive
// dependent's hash too).
struct Revision {
    deep: crate::core::Hashes,
    shallow: crate::core::Hashes,
    graph: DepGraph,
}

fn program_hashes(src: &str, roots: &[Root]) -> Result<Revision, Error> {
    let (program, checked, core) = elaborated(src, roots)?;
    let meta = hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program));
    let deep = hash_program(&core, &meta);
    let shallow = crate::core::shallow_hashes(&core, &meta);
    let graph = DepGraph::of(&core);
    Ok(Revision {
        deep,
        shallow,
        graph,
    })
}

// The prelude's own definition symbols, under the same pre-optimizer regime the
// diff hashes both revisions with, so they can be filtered out: the prelude is
// identical in both sources and would otherwise bury the user's own changes and
// inflate the unchanged count.
fn prelude_hash_names(roots: &[Root]) -> Result<std::collections::HashSet<Sym>, Error> {
    let (_, _, core) = elaborated(PRELUDE, roots)?;
    Ok(core.into_core().fns.into_iter().map(|f| f.name).collect())
}

/// A behavior diff between two revisions of a source.
///
/// Because every definition is content-addressed, two revisions diff
/// *semantically*: match definitions by name, compare content hashes, and report
/// what changed in behavior rather than in bytes. A pure refactor (renamed
/// locals, renamed `var`s, reordered definitions, reformatting) leaves every
/// hash fixed and so diffs to zero changed.
///
/// A real logic edit reports the exact set of definitions a developer *edited*
/// (their own content moved, detected by the shallow hash) plus the dependents
/// cone those edits affect (via [`DepGraph::dependents`] over the new revision).
/// The split matters because the deep behavior hash is Merkle: editing one
/// definition moves the hash of every transitive dependent, so a deep-hash
/// comparison alone cannot tell the edit apart from its ripple. The shallow hash
/// isolates the edit; the graph gives the blast radius.
///
/// This is store-independent: both sides are hashed in memory, so no
/// `PRISM_STORE` and no on-disk commit are involved. Prelude definitions are
/// filtered from both sides (they are identical in both and are not the subject
/// of a diff).
///
/// # Errors
/// Fails on any front-end error in either revision.
/// One definition whose behavior hash moved between two revisions.
#[derive(Debug, Clone, serde::Serialize)]
pub struct DiffChangedDef {
    pub name: String,
    pub old: Digest,
    pub new: Digest,
}

/// One definition named by a hash on one side only, or held-but-respelled.
#[derive(Debug, Clone, serde::Serialize)]
pub struct DiffNamedDef {
    pub name: String,
    pub hash: Digest,
}

/// The structured behavior diff between two source revisions.
///
/// Carries what moved behaviorally (deep hash), what was added or removed,
/// which dependents sit in the edited set's cone, and, the classification only
/// source text can see, which definitions changed spelling while the
/// canonicalized hash held.
#[derive(Debug, Clone, serde::Serialize)]
pub struct SourceDiff {
    pub format: &'static str,
    pub behavioral: Vec<DiffChangedDef>,
    pub added: Vec<DiffNamedDef>,
    pub removed: Vec<DiffNamedDef>,
    pub text_only: Vec<DiffNamedDef>,
    pub dependents: Vec<String>,
    pub unchanged: usize,
}

/// The format tag `SourceDiff` serializes under.
pub const SOURCE_DIFF_FORMAT: &str = "prism-source-diff-v1";

// Per-definition source slices, for the text-only classification: bare name to
// the trimmed span text of each top-level function. Parse-only, no checking.
fn decl_slices(src: &str) -> Result<std::collections::BTreeMap<String, String>, Error> {
    let parsed = parse(src)?;
    Ok(parsed
        .program
        .fns
        .iter()
        .filter_map(|d| {
            let text = src.get(d.span.start..d.span.end)?;
            Some((d.name.clone(), text.trim().to_string()))
        })
        .collect())
}

/// The structured diff behind `prism diff` over two source revisions.
///
/// # Errors
/// Fails when either revision fails the frontend.
pub fn source_diff_on(
    old_src: &str,
    new_src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<SourceDiff, Error> {
    source_diff_on_roots(old_src, new_src, roots, roots, cfg)
}

/// Like [`source_diff_on`], but resolves each revision against its own module
/// roots. Project revisions can move imported modules, so resolving both sides
/// through one tree would compare the same imports twice.
pub(crate) fn source_diff_on_roots(
    old_src: &str,
    new_src: &str,
    old_roots: &[Root],
    new_roots: &[Root],
    _cfg: &Config,
) -> Result<SourceDiff, Error> {
    let mut prelude = prelude_hash_names(old_roots)?;
    prelude.extend(prelude_hash_names(new_roots)?);
    let old = program_hashes(old_src, old_roots)?;
    let new = program_hashes(new_src, new_roots)?;

    let is_user = |s: &Sym| !prelude.contains(s);
    let names = |hs: &crate::core::Hashes| -> BTreeSet<Sym> {
        hs.keys().copied().filter(is_user).collect()
    };
    let old_names = names(&old.deep);
    let new_names = names(&new.deep);

    // A definition present in both revisions is *edited* when its own content
    // moved (shallow hash), *unchanged* when its behavior held (deep hash), and
    // otherwise only rippled by a dependency (it lands in the cone below, not
    // here). Edited lines carry the deep (behavior) hashes, the identity that
    // actually moved.
    let mut changed: Vec<(Sym, Digest, Digest)> = Vec::new();
    let mut unchanged = 0usize;
    for sym in old_names.intersection(&new_names) {
        if old.deep[sym] == new.deep[sym] {
            unchanged += 1;
        } else if old.shallow[sym] != new.shallow[sym] {
            changed.push((*sym, old.deep[sym].clone(), new.deep[sym].clone()));
        }
    }
    let mut added: Vec<(Sym, Digest)> = new_names
        .difference(&old_names)
        .map(|s| (*s, new.deep[s].clone()))
        .collect();
    let mut removed: Vec<(Sym, Digest)> = old_names
        .difference(&new_names)
        .map(|s| (*s, old.deep[s].clone()))
        .collect();

    // The dependents cone of the edited set over the new revision's graph: every
    // user definition transitively affected by an edit. Edited and added
    // definitions are reported on their own lines, so they are excluded from the
    // cone, as is the prelude (which never depends on user code).
    let edited: BTreeSet<Sym> = changed.iter().map(|(s, _, _)| *s).collect();
    let added_set: BTreeSet<Sym> = added.iter().map(|(s, _)| *s).collect();
    let mut cone: BTreeSet<Sym> = BTreeSet::new();
    for sym in &edited {
        cone.extend(new.graph.dependents(*sym));
    }
    cone.retain(|s| is_user(s) && !edited.contains(s) && !added_set.contains(s));

    changed.sort_by(|a, b| a.0.as_str().cmp(b.0.as_str()));
    added.sort_by(|a, b| a.0.as_str().cmp(b.0.as_str()));
    removed.sort_by(|a, b| a.0.as_str().cmp(b.0.as_str()));

    // The classification hashes cannot see: a definition whose canonicalized
    // hashes held on both sides but whose written text moved (a rename, a
    // reformat, a comment). Only definitions visible in both parses classify;
    // canonical (module-qualified) names match a parsed bare name by tail.
    let old_text = decl_slices(old_src)?;
    let new_text = decl_slices(new_src)?;
    let bare = |s: &str| s.rsplit_once('.').map_or(s, |(_, t)| t).to_string();
    let mut text_only: Vec<DiffNamedDef> = Vec::new();
    for sym in old_names.intersection(&new_names) {
        if old.deep[sym] != new.deep[sym] || old.shallow[sym] != new.shallow[sym] {
            continue;
        }
        let key = bare(sym.as_str());
        if let (Some(a), Some(b)) = (old_text.get(&key), new_text.get(&key)) {
            if a != b {
                text_only.push(DiffNamedDef {
                    name: sym.as_str().to_string(),
                    hash: new.deep[sym].clone(),
                });
            }
        }
    }
    text_only.sort_by(|a, b| a.name.cmp(&b.name));

    let mut dependents: Vec<String> = cone.iter().map(|s| s.as_str().to_string()).collect();
    dependents.sort_unstable();

    Ok(SourceDiff {
        format: SOURCE_DIFF_FORMAT,
        behavioral: changed
            .into_iter()
            .map(|(s, o, n)| DiffChangedDef {
                name: s.as_str().to_string(),
                old: o,
                new: n,
            })
            .collect(),
        added: added
            .into_iter()
            .map(|(s, h)| DiffNamedDef {
                name: s.as_str().to_string(),
                hash: h,
            })
            .collect(),
        removed: removed
            .into_iter()
            .map(|(s, h)| DiffNamedDef {
                name: s.as_str().to_string(),
                hash: h,
            })
            .collect(),
        text_only,
        dependents,
        unchanged,
    })
}

/// The human behavior diff between two source revisions, rendered from
/// [`source_diff_on`]'s structured result.
///
/// # Errors
/// Fails when either revision fails the frontend.
pub fn diff_on(
    old_src: &str,
    new_src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<String, Error> {
    diff_on_roots(old_src, new_src, roots, roots, cfg)
}

/// Like [`diff_on`], but resolves each revision against its own module roots.
pub(crate) fn diff_on_roots(
    old_src: &str,
    new_src: &str,
    old_roots: &[Root],
    new_roots: &[Root],
    cfg: &Config,
) -> Result<String, Error> {
    let d = source_diff_on_roots(old_src, new_src, old_roots, new_roots, cfg)?;
    Ok(render_source_diff(&d))
}

/// Render the human summary for a structured source diff.
#[must_use]
pub(crate) fn render_source_diff(d: &SourceDiff) -> String {
    let short = |h: &str| h[..crate::core::HASH_PREFIX_HEX].to_string();
    let mut out = String::new();
    writeln!(
        out,
        "diff: {} changed, {} added, {} removed, {} unchanged",
        d.behavioral.len(),
        d.added.len(),
        d.removed.len(),
        d.unchanged,
    )
    .unwrap();
    for c in &d.behavioral {
        writeln!(
            out,
            "  ~ {}  {} -> {}",
            c.name,
            short(&c.old),
            short(&c.new)
        )
        .unwrap();
    }
    for a in &d.added {
        writeln!(out, "  + {}  {}", a.name, short(&a.hash)).unwrap();
    }
    for r in &d.removed {
        writeln!(out, "  - {}  {}", r.name, short(&r.hash)).unwrap();
    }
    // Spelling moved, behavior held: named so a pure refactor reads as exactly
    // that, zero behavioral changes with the text movement accounted for.
    if !d.text_only.is_empty() {
        let names: Vec<&str> = d.text_only.iter().map(|t| t.name.as_str()).collect();
        writeln!(
            out,
            "text-only: {} respelled, behavior held ({})",
            names.len(),
            names.join(", ")
        )
        .unwrap();
    }
    if d.dependents.is_empty() {
        writeln!(out, "cone: 0 affected").unwrap();
    } else {
        writeln!(
            out,
            "cone: {} affected ({})",
            d.dependents.len(),
            d.dependents.join(", ")
        )
        .unwrap();
    }
    out
}
