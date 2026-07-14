//! Naming artifacts by digest: the content-addressed identities the driver
//! hands to persistence and package boundaries.
//!
//! A program's namespace root (the Merkle fold over its definition, shape, class,
//! and instance digests), the whole standard library's fingerprint, and the
//! native continuation table that names saved native frames by definition hash
//! all live here. Every digest is taken over the one canonical identity surface
//! (pre-optimizer elaborated Core), so the store commit, the `core-hash` /
//! `namespace` dumps, package tags, and this module agree by construction.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;
use std::fs;
use std::sync::OnceLock;

use serde::{Deserialize, Serialize};

use crate::core::fbip::borrow_sigs;
use crate::core::{fip_annots, hash_program, Digest, ElaboratedCore, HASH_SCHEME};
use crate::error::Error;
use crate::resolve::Root;
#[cfg(feature = "native")]
use crate::resolve::SourceBundleKind;
use crate::syntax::ast::{Core as CorePhase, Fip, Program};
use crate::types::{Checked, Type};

#[cfg(feature = "native")]
use crate::codegen::{native_kont_table, NativeKontIdentityRow};

use super::{elaborated, hash_meta, with_prelude, WireKind, NAMESPACE_ARTIFACT_KIND};
#[cfg(feature = "native")]
use super::{ArtifactField, ArtifactIdentity, Config};

/// Fingerprint of the executable that is executing compiler queries.
///
/// Durable frontend artifacts are tied to this byte identity rather than to a
/// Core hash or package version alone, so a locally rebuilt compiler never
/// accepts facts produced by older compiler code.
pub(super) fn compiler_binary_fingerprint() -> Result<&'static str, Error> {
    static FINGERPRINT: OnceLock<String> = OnceLock::new();
    if let Some(value) = FINGERPRINT.get() {
        return Ok(value);
    }
    let bytes = fs::read(std::env::current_exe()?)?;
    let _ = FINGERPRINT.set(blake3::hash(&bytes).to_hex().to_string());
    Ok(FINGERPRINT.get().expect("compiler fingerprint initialized"))
}

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
#[cfg(feature = "native")]
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

#[cfg(all(feature = "native", test))]
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
    let imports = crate::stdlib::STDLIB
        .iter()
        .fold(String::new(), |mut imports, (name, _)| {
            writeln!(imports, "import {name}").unwrap();
            imports
        });
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

/// Version tag for serialized checked module interfaces.
pub const MODULE_INTERFACE_FORMAT: &str = "prism-module-interface-v3";

/// One deterministic semantic row exported to an importing checker.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModuleInterfaceEntry {
    /// Semantic namespace (`value`, `shape`, `class`, or `instance`).
    pub kind: String,
    /// Exported canonical name.
    pub name: String,
    /// Canonical generalized signature or structural contract.
    pub signature: String,
    /// Digest of this row alone.
    pub digest: String,
}

/// Checked public facts an importer may consume without reading dependency
/// bodies. The digest moves on an exported type/effect/class/instance/usage
/// change, but not on an implementation-only body edit.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModuleInterface {
    /// Versioned serialization/semantics tag.
    pub format: String,
    /// Name-sorted checked interface rows.
    pub entries: Vec<ModuleInterfaceEntry>,
    /// Digest over the complete ordered interface.
    pub digest: String,
}

impl ModuleInterface {
    /// Canonical JSON projection used by the durable query store.
    ///
    /// # Errors
    /// Fails only if serialization of this closed data structure fails.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    /// Read a canonical interface projection, refusing foreign format versions
    /// and a digest that does not match the contained rows.
    ///
    /// # Errors
    /// Fails on malformed JSON, a foreign format, or a digest mismatch.
    pub fn from_json(text: &str) -> Result<Self, String> {
        let interface: Self = serde_json::from_str(text).map_err(|e| e.to_string())?;
        interface.validate()?;
        Ok(interface)
    }

    /// Rehydrate the exported value schemes an importing checker may seed into
    /// its environment without loading implementation bodies.
    ///
    /// # Errors
    /// Fails if an exported signature is not valid under this interface format.
    pub fn exported_value_env(&self) -> Result<crate::types::Env, String> {
        self.validate()?;
        let mut env = crate::types::Env::new();
        for entry in self.entries.iter().filter(|entry| entry.kind == "value") {
            let ty = crate::tc::parse_checked_signature(&entry.name, &entry.signature)
                .map_err(|e| e.to_string())?;
            env.insert(crate::sym::Sym::from(entry.name.as_str()), ty);
        }
        Ok(env)
    }

    /// Rehydrate exported checked facts without reading implementation bodies.
    ///
    /// # Errors
    /// Fails if any metadata payload or canonical type signature is malformed.
    pub fn rehydrate(&self) -> Result<super::interface::RehydratedModuleInterface, String> {
        super::interface::rehydrate(self)
    }

    fn validate(&self) -> Result<(), String> {
        if self.format != MODULE_INTERFACE_FORMAT {
            return Err(format!(
                "unsupported module interface format {:?}",
                self.format
            ));
        }
        if !self
            .entries
            .windows(2)
            .all(|pair| (&pair[0].kind, &pair[0].name) < (&pair[1].kind, &pair[1].name))
        {
            return Err("module interface entries are not in canonical order".to_string());
        }
        for entry in &self.entries {
            let derived = interface_entry(&entry.kind, &entry.name, &entry.signature).digest;
            if entry.digest != derived {
                return Err(format!(
                    "module interface row {}:{} has digest {}, derived {derived}",
                    entry.kind, entry.name, entry.digest
                ));
            }
        }
        let digest = interface_digest(&self.entries);
        if digest != self.digest {
            return Err(format!(
                "module interface digest mismatch: stored {}, derived {digest}",
                self.digest
            ));
        }
        Ok(())
    }
}

fn interface_digest(entries: &[ModuleInterfaceEntry]) -> String {
    let mut h = blake3::Hasher::new();
    h.update(MODULE_INTERFACE_FORMAT.as_bytes());
    for entry in entries {
        for field in [&entry.kind, &entry.name, &entry.signature, &entry.digest] {
            h.update(&(field.len() as u64).to_le_bytes());
            h.update(field.as_bytes());
        }
    }
    h.finalize().to_hex().to_string()
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

/// Build the checked semantic interface consumed by importing modules.
///
/// Function rows contain generalized signatures and principal effects, never
/// behavior hashes. Datatype/effect/class rows contain their structural digest;
/// root-module instance rows contain class/head/context and canonical status.
///
/// # Errors
/// Fails if either source does not parse, check, or elaborate.
pub fn module_interface(
    entry_src: &str,
    full_src: &str,
    roots: &[Root],
) -> Result<ModuleInterface, Error> {
    let entry = crate::parse::parse(entry_src)?.program;
    let (program, checked, _) = elaborated(full_src, roots)?;
    module_interface_from_checked(&entry, None, &program, &checked)
}

pub(crate) fn module_interface_from_checked(
    entry: &Program,
    module_path: Option<&str>,
    program: &Program<CorePhase>,
    checked: &Checked,
) -> Result<ModuleInterface, Error> {
    let exports = super::interface::exported_names(entry, module_path);
    let shapes = crate::core::shape_digests(&program.types, &program.effects);
    let classes = crate::core::class_digests(&program.classes);
    let mut entries = Vec::new();

    for decl in &checked.decls {
        let kind = if exports.contains(&decl.name) {
            "value"
        } else {
            "dependency-value"
        };
        entries.push(interface_entry(kind, &decl.name, decl.ty.show()));
    }
    // Per-export usage facts: a `usage` row per exported value carrying a
    // caller-visible ownership or discipline contract, so an importer's checker
    // and codegen see which arguments transfer ownership (the borrow mask) and
    // which loop discipline the body was certified under (`fip`/`fbip`). The
    // mask and keyword use the same spelling the content hash does (`hash_meta`,
    // via the single `Fip::keyword` home) so the two cannot drift. Only a
    // non-trivial fact (a borrowed parameter or a declared discipline) earns a
    // row, so an all-owned undisciplined function adds none.
    let borrows = borrow_sigs(program);
    let fips = fip_annots(program);
    for decl in &checked.decls {
        if !exports.contains(&decl.name) {
            continue;
        }
        let sym = crate::sym::Sym::new(&decl.name);
        let mask: String = borrows.get(&sym).map_or_else(String::new, |bs| {
            bs.iter().map(|b| if *b { 'b' } else { '.' }).collect()
        });
        let fip = fips.get(&sym).copied().and_then(Fip::keyword);
        if mask.contains('b') || fip.is_some() {
            entries.push(interface_entry(
                "usage",
                &decl.name,
                format!("borrow={mask}|fip={}", fip.unwrap_or("")),
            ));
        }
    }
    for (name, digest) in shapes {
        let kind = if exports.contains(&name) {
            "shape"
        } else {
            "dependency-shape"
        };
        entries.push(interface_entry(kind, &name, digest.as_str()));
    }
    for (name, digest) in classes {
        let kind = if exports.contains(&name) {
            "class"
        } else {
            "dependency-class"
        };
        entries.push(interface_entry(kind, &name, digest.as_str()));
    }
    entries.extend(
        super::interface::metadata_entries(entry, module_path, checked)
            .map_err(|error| Error::CodegenDump(error.to_string()))?,
    );
    let root_instances = entry
        .instances
        .iter()
        .map(|instance| instance.name.as_str())
        .collect::<BTreeSet<_>>();
    for (name, instance) in &checked.instances {
        let exported_head = matches!(
            &instance.head,
            Type::Con(head, _) if exports.contains(head.as_str())
        );
        let owns_module = module_path.map_or_else(
            || instance.module.is_empty(),
            |path| instance.module == path,
        );
        if !owns_module || (!root_instances.contains(name.as_str()) && !exported_head) {
            continue;
        }
        let context = instance
            .context
            .iter()
            .map(|(class, ty)| format!("{}({})", class.as_str(), ty.show()))
            .collect::<Vec<_>>()
            .join(",");
        let canonical = checked.canonical.values().any(|selected| selected == name);
        let signature = format!(
            "{}({})|context={context}|canonical={canonical}",
            instance.class.as_str(),
            instance.head.show()
        );
        entries.push(interface_entry("instance", name.as_str(), signature));
    }
    entries.sort_by(|a, b| (&a.kind, &a.name).cmp(&(&b.kind, &b.name)));
    let digest = interface_digest(&entries);
    Ok(ModuleInterface {
        format: MODULE_INTERFACE_FORMAT.to_string(),
        entries,
        digest,
    })
}

pub(super) fn interface_entry(
    kind: &str,
    name: &str,
    signature: impl Into<String>,
) -> ModuleInterfaceEntry {
    let signature = signature.into();
    let mut h = blake3::Hasher::new();
    for field in [kind, name, &signature] {
        h.update(&(field.len() as u64).to_le_bytes());
        h.update(field.as_bytes());
    }
    ModuleInterfaceEntry {
        kind: kind.to_string(),
        name: name.to_string(),
        signature,
        digest: h.finalize().to_hex().to_string(),
    }
}

/// Cached checker facts for the embedded prelude and standard library.
///
/// Module queries use this as their immutable foundation instead of rechecking
/// the shipped standard-library module graph for every project command.
pub(crate) fn stdlib_typecheck_seed() -> Result<crate::types::TypecheckSeed, Error> {
    static CACHE: OnceLock<crate::types::TypecheckSeed> = OnceLock::new();
    if let Some(seed) = CACHE.get() {
        return Ok(seed.clone());
    }
    let src = stdlib_driver_src();
    let (_, checked, _) = elaborated(&src, &[Root::Embedded(crate::stdlib::STDLIB)])?;
    let seed = crate::types::TypecheckSeed::from_checked(&checked);
    let _ = CACHE.set(seed.clone());
    Ok(CACHE.get().cloned().unwrap_or(seed))
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
