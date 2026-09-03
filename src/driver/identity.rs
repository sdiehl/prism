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
use std::env;
use std::fmt::Write;
use std::fs;
use std::io::ErrorKind;
use std::sync::OnceLock;

#[cfg(feature = "native")]
use prism_native::{native_kont_table, NativeKontIdentityRow};
use serde::{Deserialize, Serialize};

use crate::core::fbip::borrow_sigs;
#[cfg(feature = "native")]
use crate::core::hash_root;
use crate::core::{
    class_digests, fip_annots, hash_program, instance_digest, konst_fns, shape_digests, Digest,
    ElaboratedCore, Hashes, HASH_SCHEME,
};
use crate::error::Error;
use crate::names::instance_method_prefix;
use crate::parse::parse;
use crate::resolve::Root;
#[cfg(feature = "native")]
use crate::resolve::SourceBundleKind;
use crate::stdlib::STDLIB;
use crate::store::disk::Written;
use crate::sym::Sym;
use crate::syntax::ast::{Core as CorePhase, Fip, Program};
#[cfg(feature = "native")]
use crate::syntax::reflect::parse_unit;
use crate::tc::parse_checked_signature;
use crate::types::{Checked, Env, Type, TypecheckSeed};

use super::front::{run_front, Front, FrontRequest};
use super::input::field;
use super::{elaborated, hash_meta, stage_validation_error, with_prelude, Config};
#[cfg(feature = "native")]
use super::{ArtifactField, ArtifactIdentity};

/// Artifact kind for a whole-program namespace root.
pub const NAMESPACE_ARTIFACT_KIND: &str = "namespace";

/// Layout version of the `dump namespace` export envelope. The export records it
/// so a reader can tell which layout it is decoding and dispatch on it; a
/// layout-breaking change to the envelope bumps this. It is independent of the
/// hash scheme tag, which versions the hashing itself, not the export around it.
pub(crate) const NAMESPACE_FORMAT: u32 = 1;

/// The wire envelope's kind tag: the five things every serialized envelope can
/// name.
///
/// One header shape, `[scheme tag][kind][contract digest][body?]`, read five ways
/// rather than five formats. This enum is the single home of the family; the `dump namespace`
/// export and (later) the binary codec name their kind from here rather than
/// re-typing the strings. When the `lib/std/Wire.pr` codec needs the same
/// strings, they cross the phase boundary as a pinned hook (the `names.rs`
/// pattern: one canonical home with tested inverses), never a re-typed literal.
///
/// The textual name is what the human-facing header spells; the varint tag is
/// reserved for the compact binary body and is pinned here so the two encodings
/// agree on the family and its ordering before that body exists.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WireKind {
    /// A value at a frozen layout: contract digest names the type's `Stable.Vn`.
    Value,
    /// A definition: contract digest is the scheme identity, body is anonymous Core.
    Def,
    /// An effect signature: contract digest is the signature's shape digest.
    Protocol,
    /// A reified continuation: a `value` over `def` digests.
    Kont,
    /// A certificate: an attestation braided with the replay log.
    Cert,
}

impl WireKind {
    /// The textual header name, the stable string every text reader dispatches on.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::Value => "value",
            Self::Def => "def",
            Self::Protocol => "protocol",
            Self::Kont => "kont",
            Self::Cert => "cert",
        }
    }

    /// The varint discriminant reserved for the compact binary codec. Not emitted
    /// in the text envelope; pinned alongside `tag` so both encodings share one
    /// family ordering even though the text envelope does not emit it.
    #[must_use]
    pub const fn varint(self) -> u8 {
        match self {
            Self::Value => 0,
            Self::Def => 1,
            Self::Protocol => 2,
            Self::Kont => 3,
            Self::Cert => 4,
        }
    }

    /// Recover a kind from its textual tag, rejecting anything outside the family.
    #[must_use]
    pub fn parse(tag: &str) -> Option<Self> {
        [
            Self::Value,
            Self::Def,
            Self::Protocol,
            Self::Kont,
            Self::Cert,
        ]
        .into_iter()
        .find(|k| k.tag() == tag)
    }
}

/// The envelope header recovered from a `dump namespace` export: enough to
/// dispatch a reader before it touches the body.
///
/// [`parse`](Self::parse) rejects a
/// scheme it does not recognize and a kind outside the family, so a stale or
/// foreign frame is caught on the header, not three fields into the body:
/// the contract is checked before the body, always.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnvelopeHeader {
    /// Which of the five envelope kinds this frame carries.
    pub kind: WireKind,
    /// The contract digest the reader checks before touching the body.
    pub contract: String,
    /// The export layout version (`NAMESPACE_FORMAT`).
    pub format: u32,
}

impl EnvelopeHeader {
    /// Parse the `envelope` object of a serialized export. Returns `None` on a
    /// foreign scheme, an unknown kind, or a missing/ill-typed field.
    #[must_use]
    pub fn parse(doc: &serde_json::Value) -> Option<Self> {
        let env = doc.get("envelope")?;
        if env.get("scheme")?.as_str()? != HASH_SCHEME {
            return None;
        }
        Some(Self {
            kind: WireKind::parse(env.get("kind")?.as_str()?)?,
            contract: env.get("contract")?.as_str()?.to_string(),
            format: u32::try_from(env.get("format")?.as_u64()?).ok()?,
        })
    }
}

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
    let bytes = fs::read(env::current_exe()?)?;
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

/// The four content-addressed layers a namespace root commits to, kept apart.
///
/// Every definition and inlined-constant behavior hash, every data/effect shape
/// digest, every class interface digest, and every instance identity digest,
/// plus the one Merkle [`root`](Self::root) folded over all four. The root is the
/// single value the namespace contract, the `dump namespace` export, a package
/// tag, and audit re-derivation all agree on, so a change to a type's shape or an
/// instance's method moves it even when no definition body's bytes change.
///
/// The layers are kept separate rather than pre-merged because a tool that
/// addresses *individual* definitions (the code index) needs to know which
/// namespace a name was addressed in: a value and an instance are both lowercase,
/// so `map` in the definition layer and `map` in the instance layer are different
/// things, which is exactly what the kind tags the merge applies encode before
/// the fold.
#[derive(Debug, Clone)]
pub struct NamespaceLayers {
    /// The single fold over every entry below; the value a package tag names.
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

// Elaborated Core with the inlined top-level constants folded back in, so every
// *addressable* definition is a Core node.
//
// A `let` constant is inlined at its use sites and so never reaches compiled
// Core, but it still has its own behavior hash and its own dependency edges. Both
// the namespace fold and the dependency graph want it present, and they must agree
// on the augmented set, so the augmentation has one home here.
fn with_konsts(
    program: &Program<CorePhase>,
    checked: &Checked,
    core: &ElaboratedCore,
) -> Result<ElaboratedCore, Error> {
    core.clone()
        .with_functions(konst_fns(program, checked)?)
        .map_err(|violations| stage_validation_error("elaborated", &violations))
}

// The layers of an already-augmented program (see [`with_konsts`]).
fn layers_of_augmented(
    program: &Program<CorePhase>,
    checked: &Checked,
    core: &ElaboratedCore,
) -> NamespaceLayers {
    let defs = hash_program(
        core,
        &hash_meta(checked, &borrow_sigs(program), &fip_annots(program)),
    );
    let shapes = shape_digests(&program.types, &program.effects);
    let classes = class_digests(&program.classes);
    let instances = instance_digests(program, &defs);
    let root = crate::core::hash_root(&merge_namespace_entries(
        &defs, &shapes, &classes, &instances,
    ));
    NamespaceLayers {
        root,
        scheme: HASH_SCHEME,
        version: env!("CARGO_PKG_VERSION"),
        defs,
        shapes,
        classes,
        instances,
    }
}

// The layers of an elaborated program. The one computation behind the
// whole-program root, the standard-library fingerprint, and the code index, so
// the three cannot drift on what a namespace contains.
fn layers_of(
    program: &Program<CorePhase>,
    checked: &Checked,
    core: &ElaboratedCore,
) -> Result<NamespaceLayers, Error> {
    Ok(layers_of_augmented(
        program,
        checked,
        &with_konsts(program, checked, core)?,
    ))
}

/// Everything a tool needs to address a program's definitions individually: the
/// elaborated program, its checked view, its Core with every addressable
/// definition present as a node, and its [`NamespaceLayers`].
///
/// One elaboration serves all four. A consumer that computed them separately
/// would pay for three front-end passes and, worse, could build a dependency
/// graph over a different definition set than the one it hashed.
pub(crate) struct AddressableSurface {
    pub program: Program<CorePhase>,
    pub checked: Checked,
    /// Core augmented by [`with_konsts`]: the node set the layers are taken over,
    /// so a [`crate::core::DepGraph`] built from it and the digests in `layers`
    /// describe the same definitions.
    pub core: ElaboratedCore,
    pub layers: NamespaceLayers,
}

/// Elaborate `src` and return its [`AddressableSurface`].
///
/// Computed over the identity surface (pre-optimizer elaborated Core), so it is a
/// pure function of `src` and `roots`.
///
/// # Errors
/// Fails on any front-end error.
pub(crate) fn addressable_surface(src: &str, roots: &[Root]) -> Result<AddressableSurface, Error> {
    addressable_surface_in(src, roots, &Config::default())
}

/// [`addressable_surface`] under an explicit configuration.
///
/// The identity preset consults no optimizer or retarget knob, so `cfg` changes
/// nothing here except the one thing upstream of it: the build mode.
/// `BuildMode::Test` retains `test fn` declarations that a production elaboration
/// strips before it hashes anything, so a test-mode surface is the only place a
/// test's own content address and dependency edges exist.
///
/// # Errors
/// Fails on any front-end error.
pub(crate) fn addressable_surface_in(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<AddressableSurface, Error> {
    let (program, checked, core) =
        run_front(src, roots, cfg, FrontRequest::IdentityTooltips).map(Front::into_elaborated)?;
    let core = with_konsts(&program, &checked, &core)?;
    let layers = layers_of_augmented(&program, &checked, &core);
    Ok(AddressableSurface {
        program,
        checked,
        core,
        layers,
    })
}

/// The namespace layers of a program: every definition, shape, class, and
/// instance digest it commits to, plus their fold.
///
/// [`namespace_identity`] answers "what is this program's one address"; this
/// answers "what addresses are *in* it", which is what a tool needs to link a
/// source declaration to its content hash. Computed over the identity surface
/// (pre-optimizer elaborated Core), so it is a pure function of `src` and
/// `roots` and no compiler knob can move a digest.
///
/// # Errors
/// Fails on any front-end error.
pub fn namespace_layers(src: &str, roots: &[Root]) -> Result<NamespaceLayers, Error> {
    let (program, checked, core) = elaborated(src, roots)?;
    layers_of(&program, &checked, &core)
}

// Merge the four namespace layers into one kind-tagged `name -> digest` map. The
// one place the tag strings live, shared by the whole-program root and the
// standard-library root so the two folds cannot drift.
pub(crate) fn merge_namespace_entries(
    defs: &Hashes,
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
    defs: &Hashes,
) -> BTreeMap<String, Digest> {
    let defs_str: BTreeMap<String, Digest> = defs
        .iter()
        .map(|(k, v)| (k.as_str().to_string(), v.clone()))
        .collect();
    let mut instances: BTreeMap<String, Digest> = BTreeMap::new();
    for inst in &program.instances {
        let prefix = instance_method_prefix(&inst.name);
        let methods: BTreeMap<String, Digest> = defs_str
            .iter()
            .filter_map(|(k, v)| k.strip_prefix(&prefix).map(|m| (m.to_string(), v.clone())))
            .collect();
        instances.insert(
            inst.name.clone(),
            instance_digest(&inst.class, &inst.head, &methods),
        );
    }
    instances
}

// The whole-program namespace root: the fold over every namespace layer. This is
// the published/audited contract a package tag maps to.
pub(crate) fn namespace_root_of(
    program: &Program<CorePhase>,
    checked: &Checked,
    core: &ElaboratedCore,
) -> Result<Digest, Error> {
    Ok(layers_of(program, checked, core)?.root)
}

// The definition-layer Merkle fold: a root over definition content hashes only.
// The reified-continuation bundle uses this (its call sites carry the def-hash
// map, not the full program), a distinct envelope from the namespace contract.
#[cfg(feature = "native")]
pub(crate) fn def_layer_root(hashes: &Hashes) -> Digest {
    hash_root(
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
    hashes: &Hashes,
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
    pub root: Digest,
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
/// Fails only if the embedded-stdlib fingerprint cannot be computed or read.
#[cfg(feature = "native")]
pub(crate) fn walk_roots(
    roots: &[Root],
    cfg: &Config,
) -> Result<(Option<BuildRoot>, Vec<BuildRoot>), Error> {
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
                                root: Digest::from(identity.root.clone()),
                                package: None,
                            });
                        }
                        SourceBundleKind::Package { name, origin } => {
                            packages.push(BuildRoot {
                                artifact_kind: identity.artifact_kind.to_string(),
                                scheme: identity.scheme.clone(),
                                root: Digest::from(identity.root.clone()),
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
            root: stdlib_layers(cfg)?.root,
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
        let (stdlib, packages) = walk_roots(roots, cfg)?;
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
    let imports = STDLIB.iter().fold(String::new(), |mut imports, (name, _)| {
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
    pub hash: Digest,
}

/// Version tag for serialized checked module interfaces.
///
/// Unlike the driver's cache-bust query salts, this is a real content-identity
/// version: it is hashed into `interface_digest`, so its value must not be
/// renumbered casually (a change reseats every interface digest). `v4` is simply
/// the current format; there is no legacy reader, a non-`v4` document is rejected
/// outright in `validate`.
pub const MODULE_INTERFACE_FORMAT: &str = "prism-module-interface-v4";

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
    pub digest: Digest,
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
    pub digest: Digest,
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
    pub fn exported_value_env(&self) -> Result<Env, String> {
        self.validate()?;
        let mut env = Env::new();
        for entry in self.entries.iter().filter(|entry| entry.kind == "value") {
            let ty = parse_checked_signature(&entry.name, &entry.signature)
                .map_err(|e| e.to_string())?;
            env.insert(Sym::from(entry.name.as_str()), ty);
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
        if digest != self.digest.as_str() {
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
        for field in [
            entry.kind.as_str(),
            entry.name.as_str(),
            entry.signature.as_str(),
            entry.digest.as_str(),
        ] {
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
    let exports = parse(entry_src)?.program.exports;
    let (program, checked, core) = elaborated(full_src, roots)?;
    // Top-level constants inline at use sites, so lift them to zero-param CoreFns
    // for their own behavior hash, exactly as the stdlib fingerprint does.
    let core = core
        .with_functions(konst_fns(&program, &checked)?)
        .map_err(|violations| stage_validation_error("elaborated", &violations))?;
    let defs = hash_program(
        &core,
        &hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program)),
    );
    let shapes = shape_digests(&program.types, &program.effects);
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
            hash,
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
    let entry = parse(entry_src)?.program;
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
    let shapes = shape_digests(&program.types, &program.effects);
    let classes = class_digests(&program.classes);
    let mut entries = Vec::new();

    for decl in &checked.defs.decls {
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
    for decl in &checked.defs.decls {
        if !exports.contains(&decl.name) {
            continue;
        }
        let sym = Sym::new(&decl.name);
        let mask: String = borrows.get(&sym).map_or_else(String::new, |bs| {
            bs.iter().map(|b| if *b { 'b' } else { '.' }).collect()
        });
        let fip = fips.get(&sym).copied().and_then(Fip::render);
        if mask.contains('b') || fip.is_some() {
            entries.push(interface_entry(
                "usage",
                &decl.name,
                format!("borrow={mask}|fip={}", fip.unwrap_or_default()),
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
    for (name, instance) in &checked.dispatch.instances {
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
        let canonical = checked
            .dispatch
            .canonical
            .values()
            .any(|selected| selected == name);
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
        digest: Digest::from(digest),
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
        digest: Digest::from(h.finalize().to_hex().to_string()),
    }
}

/// Cached checker facts for the embedded prelude and standard library.
///
/// Module queries use this as their immutable foundation instead of rechecking
/// the shipped standard-library module graph for every project command.
pub(crate) fn stdlib_typecheck_seed() -> Result<TypecheckSeed, Error> {
    static CACHE: OnceLock<TypecheckSeed> = OnceLock::new();
    if let Some(seed) = CACHE.get() {
        return Ok(seed.clone());
    }
    let src = stdlib_driver_src();
    let (_, checked, _) = elaborated(&src, &[Root::Embedded(STDLIB)])?;
    let seed = TypecheckSeed::try_from_checked(&checked)
        .map_err(|error| Error::ResolveModule(error.to_string()))?;
    let _ = CACHE.set(seed.clone());
    Ok(CACHE.get().cloned().unwrap_or(seed))
}

/// Exported standard-library values paired with their owning module and scheme.
///
/// Search consumes this interface view rather than the foundation environment,
/// which also contains private helpers needed only while checking Std itself.
/// Native-only: the CLI type-query commands are its only consumers.
#[cfg(feature = "native")]
pub(crate) fn stdlib_value_schemes() -> Result<Vec<(String, String, Type)>, Error> {
    static CACHE: OnceLock<Vec<(String, String, Type)>> = OnceLock::new();
    if let Some(rows) = CACHE.get() {
        return Ok(rows.clone());
    }
    let seed = stdlib_typecheck_seed()?;
    let mut rows = BTreeMap::<String, (String, Type)>::new();

    // The unqualified foundation is the always-on Base interface.
    for (name, ty) in seed.environment().iter() {
        if !name.as_str().contains('.') && !name.as_str().contains('@') {
            rows.insert(name.to_string(), ("Base".to_string(), ty.clone()));
        }
    }

    for (module, source) in STDLIB {
        let entry = parse_unit(source)?;
        let exports = super::interface::exported_names(&entry, Some(module));
        for export in &exports {
            if let Some(ty) = seed.environment().get(&Sym::from(export.as_str())) {
                rows.insert(export.clone(), ((*module).to_string(), ty.clone()));
            }
            if let Some(data) = seed.data_types().get(export) {
                for constructor in &data.ctors {
                    if let Some(ty) = seed.environment().get(&Sym::from(constructor.as_str())) {
                        rows.insert(constructor.clone(), ((*module).to_string(), ty.clone()));
                    }
                }
            }
            if let Some(class) = seed.classes().get(&Sym::from(export.as_str())) {
                for (method, _ty) in &class.methods {
                    if let Some(ty) = seed.environment().get(method) {
                        rows.insert(method.to_string(), ((*module).to_string(), ty.clone()));
                    }
                }
            }
        }
        for (operation, info) in seed.effect_operations() {
            if exports.contains(info.effect_name.as_str()) {
                if let Some(ty) = seed.environment().get(&Sym::from(operation.as_str())) {
                    rows.insert(operation.clone(), ((*module).to_string(), ty.clone()));
                }
            }
        }
    }
    let rows = rows
        .into_iter()
        .map(|(name, (module, ty))| (module, name, ty))
        .collect::<Vec<_>>();
    let _ = CACHE.set(rows.clone());
    Ok(CACHE.get().cloned().unwrap_or(rows))
}

/// A content-addressed fingerprint of the whole standard library: the
/// [`NamespaceLayers`] of the embedded stdlib.
///
/// One namespace root (a branch-hash-style fold) over every documented
/// definition's behavior hash and every datatype/effect's shape digest, tagged
/// with the hashing scheme and the compiler version that produced it. An alias
/// rather than its own type: the standard library is addressed exactly like any
/// other program, so the two must never grow separate layer sets.
pub type StdlibHash = NamespaceLayers;

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
    // The standard library goes through the shared layer computation, so its root
    // and a package/namespace contract cannot drift apart.
    namespace_layers(&stdlib_driver_src(), &[Root::Embedded(STDLIB)])
}

// Store query kind and schema tag for the durable fingerprint table.
const STDLIB_LAYERS_QUERY: &str = "stdlib-layers";
const STDLIB_LAYERS_SCHEMA: &str = "stdlib-layers.v1";

// Line tags of the durable fingerprint encoding.
const LAYER_SCHEME: &str = "scheme";
const LAYER_VERSION: &str = "version";
const LAYER_ROOT: &str = "root";
const LAYER_DEF: &str = "def";
const LAYER_SHAPE: &str = "shape";
const LAYER_CLASS: &str = "class";
const LAYER_INSTANCE: &str = "instance";

/// The standard-library fingerprint, memoized process-wide and durably in the
/// store. See [`StdlibHash`].
///
/// The fingerprint is a pure function of the compiler binary (the stdlib is
/// embedded in it), yet computing it elaborates the whole stdlib, and a build
/// reads it on every front miss (the lineage sidecar, the continuation table,
/// and the artifact identity fold in its root; the clone warnings compare
/// against its definition layer). So the durable key is the binary fingerprint
/// under a schema tag, gated like every other durable query. A malformed or
/// swept stored table is a miss, never an error.
///
/// # Errors
/// Fails on a store open or write failure, or if the embedded stdlib does not
/// elaborate (a compiler bug).
pub(super) fn stdlib_layers(cfg: &Config) -> Result<StdlibHash, Error> {
    static CACHE: OnceLock<StdlibHash> = OnceLock::new();
    if let Some(cached) = CACHE.get() {
        return Ok(cached.clone());
    }
    let durable = if cfg.flags().compiler_cache && !cfg.flags().store {
        let mut h = blake3::Hasher::new();
        field(&mut h, STDLIB_LAYERS_SCHEMA.as_bytes());
        field(&mut h, compiler_binary_fingerprint()?.as_bytes());
        Some((cfg.open_store()?, h.finalize().to_hex().to_string()))
    } else {
        None
    };
    let stored = match &durable {
        Some((store, key)) => match store.get_query(STDLIB_LAYERS_QUERY, key)? {
            Some(hash) => match store.get(&hash) {
                Ok(bytes) => decode_layers(&bytes),
                Err(e) if e.kind() == ErrorKind::NotFound => None,
                Err(e) => return Err(Error::Io(e)),
            },
            None => None,
        },
        None => None,
    };
    let layers = if let Some(layers) = stored {
        layers
    } else {
        let layers = stdlib_hash()?;
        if let Some((store, key)) = &durable {
            let bytes = encode_layers(&layers);
            let hash = blake3::hash(&bytes).to_hex().to_string();
            match store.put(&hash, &bytes)? {
                Written::New | Written::Hit => {}
            }
            store.put_query(STDLIB_LAYERS_QUERY, key, &hash)?;
        }
        layers
    };
    let _ = CACHE.set(layers.clone());
    Ok(layers)
}

// One tab-separated line per entry: the three header fields, then every layer
// entry as `<layer> <name> <digest>` in the tables' sorted order.
fn encode_layers(layers: &StdlibHash) -> Vec<u8> {
    let mut out = String::new();
    let mut line = |tag: &str, name: &str, digest: &str| {
        out.push_str(tag);
        out.push('\t');
        out.push_str(name);
        out.push('\t');
        out.push_str(digest);
        out.push('\n');
    };
    line(LAYER_SCHEME, layers.scheme, "");
    line(LAYER_VERSION, layers.version, "");
    line(LAYER_ROOT, layers.root.as_str(), "");
    for (name, digest) in &layers.defs {
        line(LAYER_DEF, name.as_str(), digest.as_str());
    }
    for (name, digest) in &layers.shapes {
        line(LAYER_SHAPE, name, digest.as_str());
    }
    for (name, digest) in &layers.classes {
        line(LAYER_CLASS, name, digest.as_str());
    }
    for (name, digest) in &layers.instances {
        line(LAYER_INSTANCE, name, digest.as_str());
    }
    out.into_bytes()
}

// The inverse of `encode_layers`. The scheme and version lines must name this
// binary's constants: the two are static strings, so a table from any other
// producer is a miss rather than a value with a foreign tag.
fn decode_layers(bytes: &[u8]) -> Option<StdlibHash> {
    let text = std::str::from_utf8(bytes).ok()?;
    let mut lines = text.lines();
    let header = |tag: &str, line: Option<&str>| -> Option<String> {
        let (t, rest) = line?.split_once('\t')?;
        let (value, empty) = rest.split_once('\t')?;
        (t == tag && empty.is_empty() && !value.is_empty()).then(|| value.to_string())
    };
    let scheme = header(LAYER_SCHEME, lines.next())?;
    let version = header(LAYER_VERSION, lines.next())?;
    let root = header(LAYER_ROOT, lines.next())?;
    if scheme != HASH_SCHEME || version != env!("CARGO_PKG_VERSION") {
        return None;
    }
    let mut layers = StdlibHash {
        root: Digest::from(root),
        scheme: HASH_SCHEME,
        version: env!("CARGO_PKG_VERSION"),
        defs: Hashes::new(),
        shapes: BTreeMap::new(),
        classes: BTreeMap::new(),
        instances: BTreeMap::new(),
    };
    for line in lines {
        let (tag, rest) = line.split_once('\t')?;
        let (name, digest) = rest.split_once('\t')?;
        if name.is_empty() || digest.is_empty() {
            return None;
        }
        let table = match tag {
            LAYER_DEF => {
                layers.defs.insert(Sym::new(name), Digest::from(digest));
                continue;
            }
            LAYER_SHAPE => &mut layers.shapes,
            LAYER_CLASS => &mut layers.classes,
            LAYER_INSTANCE => &mut layers.instances,
            _ => return None,
        };
        table.insert(name.to_string(), Digest::from(digest));
    }
    Some(layers)
}

#[cfg(test)]
mod stdlib_layer_codec_tests {
    use std::collections::BTreeMap;

    use super::{decode_layers, encode_layers, StdlibHash};
    use crate::core::{Digest, Hashes, HASH_SCHEME};
    use crate::sym::Sym;

    fn sample() -> StdlibHash {
        StdlibHash {
            root: Digest::from("r00t"),
            scheme: HASH_SCHEME,
            version: env!("CARGO_PKG_VERSION"),
            defs: Hashes::from([
                (Sym::new("Data.Map@helper"), Digest::from("d1")),
                (Sym::new("map"), Digest::from("d2")),
            ]),
            shapes: BTreeMap::from([("Option".to_string(), Digest::from("s1"))]),
            classes: BTreeMap::from([("Show".to_string(), Digest::from("c1"))]),
            instances: BTreeMap::from([("Show@Int".to_string(), Digest::from("i1"))]),
        }
    }

    #[test]
    fn layers_round_trip_through_the_store_encoding() {
        let layers = sample();
        let decoded = decode_layers(&encode_layers(&layers)).expect("decodes");
        assert_eq!(decoded.root, layers.root);
        assert_eq!(decoded.defs, layers.defs);
        assert_eq!(decoded.shapes, layers.shapes);
        assert_eq!(decoded.classes, layers.classes);
        assert_eq!(decoded.instances, layers.instances);
    }

    #[test]
    fn a_foreign_or_damaged_table_is_a_miss() {
        let mut foreign = sample();
        foreign.version = "0.0.0";
        assert!(decode_layers(&encode_layers(&foreign)).is_none());
        let mut bytes = encode_layers(&sample());
        bytes.truncate(bytes.len() - 3);
        assert!(decode_layers(&bytes).is_none());
        assert!(decode_layers(b"def\tmap\n").is_none());
    }
}
