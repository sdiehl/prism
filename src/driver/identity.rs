//! Naming artifacts by digest: the content-addressed identities the driver
//! hands to persistence and package boundaries.
//!
//! A program's namespace root (the Merkle fold over its definition, shape, class,
//! and instance digests), the whole standard library's fingerprint, and the
//! native continuation table that names saved native frames by definition hash
//! all live here. Every digest is taken over the one canonical identity surface
//! (pre-optimizer elaborated Core), so the store commit, the `core-hash` /
//! `namespace` dumps, package tags, and this module agree by construction.

use std::collections::BTreeMap;
use std::sync::OnceLock;

use crate::core::fbip::borrow_sigs;
use crate::core::{fip_annots, hash_program, Digest, ElaboratedCore, HASH_SCHEME};
use crate::error::Error;
use crate::resolve::Root;
#[cfg(feature = "native")]
use crate::resolve::SourceBundleKind;
use crate::syntax::ast::{Core as CorePhase, Program};
use crate::types::Checked;

#[cfg(feature = "native")]
use crate::codegen::{native_kont_table, NativeKontIdentityRow};

use super::{elaborated, hash_meta, with_prelude, WireKind, NAMESPACE_ARTIFACT_KIND};
#[cfg(feature = "native")]
use super::{ArtifactField, ArtifactIdentity, Config};

/// Structured identity for a whole-program namespace artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NamespaceIdentity {
    /// The hash scheme that gives `root` its meaning.
    pub scheme: &'static str,
    /// The artifact kind this root names.
    pub kind: &'static str,
    /// The Merkle fold over the namespace entries.
    pub root: Digest,
}

/// The namespace identity of a program: artifact kind plus the Merkle fold over
/// its definition, data/effect shape, class, and instance digests.
///
/// This is the single value a published package tag maps to and `prism audit`
/// re-derives: the same digest a `dump namespace` export carries as its contract,
/// and the same fold [`stdlib_hash`] uses for the whole standard library, so the
/// root names the exact program interface (a type whose shape changes moves it
/// even when no definition body's bytes move). A tag names a root; the root names
/// the exact set of behaviors and interfaces under it.
///
/// # Errors
/// Fails on any front-end error.
pub fn namespace_identity(src: &str, roots: &[Root]) -> Result<NamespaceIdentity, Error> {
    let (program, checked, core) = elaborated(src, roots)?;
    Ok(NamespaceIdentity {
        scheme: HASH_SCHEME,
        kind: NAMESPACE_ARTIFACT_KIND,
        root: namespace_root_of(&program, &checked, &core)?,
    })
}

/// The namespace root of a program.
///
/// Prefer [`namespace_identity`] at persistence/package boundaries so the scheme
/// and artifact kind travel with the digest.
///
/// # Errors
/// Fails on any front-end error.
pub fn namespace_root(src: &str, roots: &[Root]) -> Result<String, Error> {
    Ok(namespace_identity(src, roots)?.root.into_string())
}

// The complete namespace-entry map a root commits to: every definition and
// inlined-constant behavior hash, every data/effect shape digest, every class
// digest, and every instance digest, keyed by a kind tag so declarations that
// share a name across namespaces (a value and an instance are both lowercase)
// cannot collide. This is the single fold the namespace contract, the
// `dump namespace` export, the package tag, audit re-derivation, and the
// standard-library root all share, so a change to a type's shape or an instance's
// method moves the root even when no definition body's bytes change. Folding only
// definitions (the previous behavior) let `Token(Int)` and `Token(String)` share
// one namespace contract.
fn namespace_entries(
    program: &Program<CorePhase>,
    checked: &Checked,
    core: &ElaboratedCore,
) -> Result<BTreeMap<String, Digest>, Error> {
    // Top-level constants are inlined at use sites, so they are not in the
    // compiled Core; elaborate them as zero-param CoreFns so each contributes its
    // own behavior hash, exactly as the standard-library root does.
    let mut core = core.clone();
    core.0.fns.extend(crate::core::konst_fns(program, checked)?);
    let defs = hash_program(
        &core,
        &hash_meta(checked, &borrow_sigs(program), &fip_annots(program)),
    );
    let shapes = crate::core::shape_digests(&program.types, &program.effects);
    let classes = crate::core::class_digests(&program.classes);
    let instances = instance_digests(program, &defs);
    Ok(merge_namespace_entries(
        &defs, &shapes, &classes, &instances,
    ))
}

// Merge the four namespace layers into one kind-tagged `name -> digest` map. The
// one place the tag strings live, shared by the whole-program root and the
// standard-library root so the two folds cannot drift.
pub(crate) fn merge_namespace_entries(
    defs: &crate::core::Hashes,
    shapes: &BTreeMap<String, Digest>,
    classes: &BTreeMap<String, Digest>,
    instances: &BTreeMap<String, Digest>,
) -> BTreeMap<String, Digest> {
    let mut entries: BTreeMap<String, Digest> = BTreeMap::new();
    for (sym, h) in defs {
        entries.insert(
            format!("{} {}", WireKind::Def.tag(), sym.as_str()),
            h.clone(),
        );
    }
    for (name, h) in shapes {
        entries.insert(format!("shape {name}"), h.clone());
    }
    for (name, h) in classes {
        entries.insert(format!("class {name}"), h.clone());
    }
    for (name, h) in instances {
        entries.insert(format!("instance {name}"), h.clone());
    }
    entries
}

// Each instance's identity folds its already-computed method behavior hashes (the
// `i@<inst>@<method>` CoreFns) with its class and head. Nearly free, and the same
// value doubles as the coherence seed.
pub(crate) fn instance_digests(
    program: &Program<CorePhase>,
    defs: &crate::core::Hashes,
) -> BTreeMap<String, Digest> {
    let defs_str: BTreeMap<String, Digest> = defs
        .iter()
        .map(|(k, v)| (k.as_str().to_string(), v.clone()))
        .collect();
    let mut instances: BTreeMap<String, Digest> = BTreeMap::new();
    for inst in &program.instances {
        let prefix = crate::names::instance_method_prefix(&inst.name);
        let methods: BTreeMap<String, Digest> = defs_str
            .iter()
            .filter_map(|(k, v)| k.strip_prefix(&prefix).map(|m| (m.to_string(), v.clone())))
            .collect();
        instances.insert(
            inst.name.clone(),
            crate::core::instance_digest(&inst.class, &inst.head, &methods),
        );
    }
    instances
}

// The whole-program namespace root: the full fold over `namespace_entries`. This
// is the published/audited contract a package tag maps to.
pub(crate) fn namespace_root_of(
    program: &Program<CorePhase>,
    checked: &Checked,
    core: &ElaboratedCore,
) -> Result<Digest, Error> {
    Ok(crate::core::hash_root(&namespace_entries(
        program, checked, core,
    )?))
}

// The definition-layer Merkle fold: a root over definition content hashes only.
// The reified-continuation bundle uses this (its call sites carry the def-hash
// map, not the full program), a distinct envelope from the namespace contract.
pub(crate) fn def_layer_root(hashes: &crate::core::Hashes) -> Digest {
    crate::core::hash_root(
        &hashes
            .iter()
            .map(|(sym, h)| {
                (
                    format!("{} {}", WireKind::Def.tag(), sym.as_str()),
                    h.clone(),
                )
            })
            .collect(),
    )
}

#[cfg(feature = "native")]
pub(super) fn native_kont_table_of(
    hashes: &crate::core::Hashes,
    roots: &[Root],
    cfg: &Config,
    identity_rows: NativeKontIdentityRows,
) -> Result<String, Error> {
    let bundle = def_layer_root(hashes);
    Ok(native_kont_table(
        hashes,
        &bundle,
        &native_kont_identity(cfg, &bundle, roots, identity_rows)?,
    ))
}

#[cfg(feature = "native")]
pub(super) fn native_kont_table_for(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<String, Error> {
    native_kont_table_for_with_rows(src, roots, cfg, NativeKontIdentityRows::Full)
}

#[cfg(feature = "native")]
pub(super) fn native_kont_table_for_with_rows(
    src: &str,
    roots: &[Root],
    cfg: &Config,
    identity_rows: NativeKontIdentityRows,
) -> Result<String, Error> {
    let (program, checked, core) = elaborated(src, roots)?;
    let hashes = hash_program(
        &core,
        &hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program)),
    );
    native_kont_table_of(&hashes, roots, cfg, identity_rows)
}

#[cfg(feature = "native")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum NativeKontIdentityRows {
    Full,
    Portable,
}

#[cfg(feature = "native")]
fn native_kont_identity(
    cfg: &Config,
    source_root: &str,
    roots: &[Root],
    identity_rows: NativeKontIdentityRows,
) -> Result<Vec<NativeKontIdentityRow<'static>>, Error> {
    // The native table is built from an already-computed source root (the caller
    // holds the hashes), so wrap it as a namespace identity and fold in the roots
    // through the one `BuildIdentity`, rather than re-walking the search path.
    let source = NamespaceIdentity {
        scheme: HASH_SCHEME,
        kind: NAMESPACE_ARTIFACT_KIND,
        root: source_root.to_string().into(),
    };
    let identity = BuildIdentity::from_source_identity(source, roots, cfg, BACKEND_LLVM)?;
    let rows = match identity_rows {
        NativeKontIdentityRows::Full => identity.artifact.rows(),
        NativeKontIdentityRows::Portable => identity.artifact.portable_rows(),
    };
    Ok(rows
        .into_iter()
        .filter(|row| {
            !matches!(
                row.field,
                ArtifactField::Compiler
                    | ArtifactField::HashScheme
                    | ArtifactField::Target
                    | ArtifactField::Backend
            )
        })
        .map(|row| NativeKontIdentityRow {
            key: row.field.label(),
            value: row.value,
        })
        .collect())
}

/// The backend label the native continuation table's artifact identity is taken
/// under: always the LLVM backend, the one that emits the table.
#[cfg(feature = "native")]
const BACKEND_LLVM: &str = "llvm";

/// Artifact-kind label for the in-binary standard library, used when the module
/// search path carries no Std source bundle. Named once so the lineage sidecar and
/// the identity walk cannot disagree on the string.
#[cfg(feature = "native")]
pub(crate) const EMBEDDED_STDLIB_KIND: &str = "embedded-stdlib";

/// A resolved module-search root reduced to its content identity: the fields the
/// lineage sidecar and the artifact fingerprint both read. A package root carries a
/// `(name, origin)`; the Std root does not.
#[cfg(feature = "native")]
#[derive(Clone, Debug)]
pub(crate) struct BuildRoot {
    pub artifact_kind: String,
    pub scheme: String,
    pub root: String,
    pub package: Option<PackageOrigin>,
}

/// The package identity a [`BuildRoot`] carries when it is a package source bundle.
#[cfg(feature = "native")]
#[derive(Clone, Debug)]
pub(crate) struct PackageOrigin {
    pub name: String,
    pub origin: String,
}

#[cfg(feature = "native")]
impl BuildRoot {
    /// The `<name>@<origin>@<kind>@<scheme>:<root>` (package) or
    /// `<kind>@<scheme>:<root>` (Std) descriptor that names this root in an artifact
    /// fingerprint. One spelling, shared by the fingerprint and the sidecar.
    pub(crate) fn descriptor(&self) -> String {
        match &self.package {
            Some(PackageOrigin { name, origin }) => {
                format!(
                    "{name}@{origin}@{}@{}:{}",
                    self.artifact_kind, self.scheme, self.root
                )
            }
            None => format!("{}@{}:{}", self.artifact_kind, self.scheme, self.root),
        }
    }
}

/// The one root walk: reduce a module search path to its Std root (a Std source
/// bundle, or the embedded stdlib) and its package roots, sorted by descriptor.
/// Shared by the lineage sidecar and the artifact fingerprint so neither
/// re-derives the discrimination.
///
/// # Errors
/// Fails only if the embedded-stdlib fingerprint cannot be computed.
#[cfg(feature = "native")]
pub(crate) fn walk_roots(roots: &[Root]) -> Result<(Option<BuildRoot>, Vec<BuildRoot>), Error> {
    let mut stdlib = None;
    let mut packages = Vec::new();
    let mut saw_embedded_std = false;
    for root in roots {
        match root {
            Root::Embedded(_) => saw_embedded_std = true,
            Root::Dir(_) => {}
            Root::SourceBundle { .. } => {
                if let Some(identity) = root.source_bundle_identity() {
                    match &identity.kind {
                        SourceBundleKind::Std => {
                            stdlib = Some(BuildRoot {
                                artifact_kind: identity.artifact_kind.to_string(),
                                scheme: identity.scheme.clone(),
                                root: identity.root.clone(),
                                package: None,
                            });
                        }
                        SourceBundleKind::Package { name, origin } => {
                            packages.push(BuildRoot {
                                artifact_kind: identity.artifact_kind.to_string(),
                                scheme: identity.scheme.clone(),
                                root: identity.root.clone(),
                                package: Some(PackageOrigin {
                                    name: name.clone(),
                                    origin: origin.as_str().to_string(),
                                }),
                            });
                        }
                    }
                }
            }
        }
    }
    if stdlib.is_none() && saw_embedded_std {
        stdlib = Some(BuildRoot {
            artifact_kind: EMBEDDED_STDLIB_KIND.to_string(),
            scheme: HASH_SCHEME.to_string(),
            root: stdlib_hash()?.root.into_string(),
            package: None,
        });
    }
    packages.sort_by_key(BuildRoot::descriptor);
    Ok((stdlib, packages))
}

/// Every content-addressed fact about a build, computed once from its inputs and
/// passed by value to the lineage sidecar, the native continuation table, and the
/// store, so no consumer re-assembles the pieces (source root, Std root, package
/// roots, and the compiler/artifact identity) on its own.
#[cfg(feature = "native")]
pub(crate) struct BuildIdentity {
    /// The program's own namespace root (its source identity).
    pub source: NamespaceIdentity,
    /// The Std root, or `None` when the search path carries no standard library.
    pub stdlib: Option<BuildRoot>,
    /// Package source-bundle roots, sorted by descriptor.
    pub packages: Vec<BuildRoot>,
    /// The compiler/artifact identity, with the three roots already folded in.
    pub artifact: ArtifactIdentity,
}

#[cfg(feature = "native")]
impl BuildIdentity {
    /// Fold an already-known source identity together with the resolved roots into
    /// one identity. For callers that already hold the namespace root.
    ///
    /// # Errors
    /// Fails only if the embedded-stdlib fingerprint cannot be computed.
    pub(crate) fn from_source_identity(
        source: NamespaceIdentity,
        roots: &[Root],
        cfg: &Config,
        backend: &str,
    ) -> Result<Self, Error> {
        let (stdlib, packages) = walk_roots(roots)?;
        let mut artifact = cfg
            .artifact_identity_for(backend)
            .with_source_root(source.root.clone())
            .with_package_roots(packages.iter().map(BuildRoot::descriptor));
        if let Some(std) = &stdlib {
            artifact = artifact.with_stdlib_root(std.root.clone());
        }
        Ok(Self {
            source,
            stdlib,
            packages,
            artifact,
        })
    }

    /// Derive the namespace root from source, then fold in the roots: the entry
    /// point for consumers that start from source text.
    ///
    /// # Errors
    /// Fails on any front-end error, or if the embedded-stdlib fingerprint cannot
    /// be computed.
    pub(crate) fn from_source(
        src: &str,
        roots: &[Root],
        cfg: &Config,
        backend: &str,
    ) -> Result<Self, Error> {
        Self::from_source_identity(namespace_identity(src, roots)?, roots, cfg, backend)
    }
}

// The composed source that pulls in the entire documented standard library:
// the always-on prelude plus one import per embedded module. Docs and the
// stdlib hash share this one definition of "the stdlib", so the import list is
// derived from the embedded module table rather than hand-typed: a module in
// `STDLIB` that was missing here would silently get no hash badge in the
// generated docs and, worse, fall outside the stdlib Merkle root (its types
// and functions would never reach the elaborated Core the hash is taken
// from). Qualified-only (no `(..)`): the driver body never names anything
// from these modules directly, and opening them all unqualified collides
// (`Concurrent.Outcome` vs `Quickcheck.Outcome`); a bare import still
// resolves and elaborates the module, and is harmless beside the prelude's
// own glob imports.
pub(crate) fn stdlib_driver_src() -> String {
    let mut imports = String::new();
    for (name, _) in crate::stdlib::STDLIB {
        imports.push_str("import ");
        imports.push_str(name);
        imports.push('\n');
    }
    with_prelude(&imports)
}

/// One entry of a program's public surface: an exported name paired with the
/// content hash that pins its meaning (a function's behavior hash, a datatype or
/// effect's shape digest).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PublicDef {
    pub name: String,
    pub scheme: &'static str,
    pub hash: String,
}

/// The public API surface of a program, name-sorted.
///
/// Every `pub`/`opaque` top-level name is paired with its content hash, so a
/// package's exported surface can be compared across revisions by digest rather
/// than by source text.
///
/// `entry_src` is the module's own source, read only for its export set;
/// `full_src` is that source with the prelude prepended, elaborated for the
/// hashes. Prelude and imported names, and private definitions, are excluded.
///
/// # Errors
/// Fails if either source fails to parse, or `full_src` fails to elaborate.
pub fn public_surface(
    entry_src: &str,
    full_src: &str,
    roots: &[Root],
) -> Result<Vec<PublicDef>, Error> {
    let exports = crate::parse::parse(entry_src)?.program.exports;
    let (program, checked, mut core) = elaborated(full_src, roots)?;
    // Top-level constants inline at use sites, so lift them to zero-param CoreFns
    // for their own behavior hash, exactly as the stdlib fingerprint does.
    core.0
        .fns
        .extend(crate::core::konst_fns(&program, &checked)?);
    let defs = hash_program(
        &core,
        &hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program)),
    );
    let shapes = crate::core::shape_digests(&program.types, &program.effects);
    let mut surface: BTreeMap<String, Digest> = BTreeMap::new();
    for (sym, hash) in &defs {
        if exports.contains(sym.as_str()) {
            surface.insert(sym.as_str().to_string(), hash.clone());
        }
    }
    // A datatype or effect is pinned by its shape digest; it never shares a name
    // with a value in the same module, so it fills only names a value did not.
    for (name, hash) in &shapes {
        if exports.contains(name) {
            surface.entry(name.clone()).or_insert_with(|| hash.clone());
        }
    }
    Ok(surface
        .into_iter()
        .map(|(name, hash)| PublicDef {
            name,
            scheme: HASH_SCHEME,
            hash: hash.into_string(),
        })
        .collect())
}

/// A content-addressed fingerprint of the whole standard library.
///
/// One namespace root (a branch-hash-style fold) over every documented
/// definition's behavior hash and every datatype/effect's shape digest, tagged
/// with the hashing scheme and the compiler version that produced it.
#[derive(Debug, Clone)]
pub struct StdlibHash {
    /// The single fold over every entry below; the value anchored in the docs.
    pub root: Digest,
    /// The hashing scheme tag every constituent hash commits to.
    pub scheme: &'static str,
    /// The compiler version that produced this fingerprint.
    pub version: &'static str,
    /// Per-definition behavior hashes (term level).
    pub defs: crate::core::Hashes,
    /// Per-declaration structural shape digests (datatypes and effects).
    pub shapes: BTreeMap<String, Digest>,
    /// Per-class interface digests (name, superclasses, method signatures).
    pub classes: BTreeMap<String, Digest>,
    /// Per-instance identity digests (class, head, method behavior hashes).
    pub instances: BTreeMap<String, Digest>,
}

/// Compute the standard-library fingerprint. See [`StdlibHash`].
///
/// The fingerprint is a pure function of the embedded standard library, a
/// compile-time constant, so the whole computation is memoized process-wide: the
/// first call elaborates and folds, every later one clones the cached result.
/// This is what keeps the prelude from being re-elaborated per command and per
/// test in one process. The content hash commits to pre-optimizer Core, so no
/// environment knob (opt level, effect tier) can change it.
///
/// # Errors
/// Fails only if the embedded stdlib does not parse, type-check, or elaborate,
/// which would be a compiler bug.
pub fn stdlib_hash() -> Result<StdlibHash, Error> {
    static CACHE: OnceLock<StdlibHash> = OnceLock::new();
    if let Some(cached) = CACHE.get() {
        return Ok(cached.clone());
    }
    let computed = stdlib_hash_uncached()?;
    // A concurrent first caller may win the race; either way every caller sees
    // the same bytes, so ignore whose value the cache kept.
    let _ = CACHE.set(computed.clone());
    Ok(computed)
}

fn stdlib_hash_uncached() -> Result<StdlibHash, Error> {
    let src = stdlib_driver_src();
    let (program, checked, mut core) = elaborated(&src, &[Root::Embedded(crate::stdlib::STDLIB)])?;
    // Top-level constants (`let`) are inlined at use sites, so they are not in the
    // compiled Core. Elaborate them as zero-param CoreFns so each gets its own
    // behavior hash (addressable and displayable), then hash the whole set.
    core.0
        .fns
        .extend(crate::core::konst_fns(&program, &checked)?);
    let defs = hash_program(
        &core,
        &hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program)),
    );
    let shapes = crate::core::shape_digests(&program.types, &program.effects);
    let classes = crate::core::class_digests(&program.classes);
    let instances = instance_digests(&program, &defs);
    // The whole-program root uses the shared fold, so the standard-library root
    // and a package/namespace contract cannot drift apart.
    let entries = merge_namespace_entries(&defs, &shapes, &classes, &instances);
    Ok(StdlibHash {
        root: crate::core::hash_root(&entries),
        scheme: HASH_SCHEME,
        version: env!("CARGO_PKG_VERSION"),
        defs,
        shapes,
        classes,
        instances,
    })
}
