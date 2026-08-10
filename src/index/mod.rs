//! `prism index`: the whole-codebase index a program viewer reads.
//!
//! One deterministic artifact per revision, holding the two things a reviewer
//! navigates by: **definitions** (each with the content address the compiler
//! gives it, its inferred type and effect row, its doc comment, and the exact
//! source range of its body) and **relationships** between them. It is a
//! projection of facts the compiler already computes, not a new analysis: the
//! addresses are the namespace layers (`driver::namespace_layers`), the `calls`
//! edges are the Core dependency graph (`core::DepGraph`, the same adjacency
//! `prism store query callers` answers and the content hasher walks), and the
//! `performs` edges are the checked effect rows.
//!
//! Two properties make it a viewer substrate rather than a second doc generator:
//!
//! - **Addressed, not located.** A definition's identity is its canonical name
//!   plus its content hash, so a bookmark, a note, or a review mark survives
//!   reformatting and file moves, and two revisions can be aligned by identity.
//!   Source ranges are carried too, but as rendering data, not identity.
//! - **Whole-set edges.** `callers`/`dependents` answer one question at a time
//!   from the CLI; the index carries the full edge set, so a viewer can traverse
//!   in either direction without re-running the compiler.
//!
//! Addressing every definition means compiling more than a build does: "everything
//! the entry point reaches" is the wrong set for a reader, because a library
//! package's modules are not reachable from its `[bin]` entry and are most of what
//! someone opened a viewer to read. The caller therefore supplies a `source` that
//! reaches every module it lists (`cli::index` appends one qualified import per
//! module to the build's own input); a module the program does not reach is still
//! indexed, but carries no address.
//!
//! The artifact is a pure function of the indexed source (it is taken over the
//! identity surface, pre-optimizer elaborated Core), so `--check` can gate a
//! committed copy in CI the way `prism docs --check` gates committed pages.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

mod build;
pub mod diff;
mod edges;
pub mod occurrences;
mod surface;
mod typed;

#[cfg(test)]
mod tests;

pub use build::{build, IndexInput};
pub use diff::{diff, IndexDiff, Status, INDEX_DIFF_FORMAT};
pub use occurrences::{Occurrences, OCCURRENCES_FORMAT};

/// Schema tag for the index artifact.
pub const INDEX_FORMAT: &str = "prism-index-v1";

/// The self-describing header: what this artifact is, what produced it, and the
/// one digest that names the exact program it describes.
///
/// `contract` is the indexed program's namespace root, so a consumer can tell two
/// indexes apart (and a stale one from a current one) without reading a single
/// definition. It names the program *the index describes*, which includes every
/// listed module, so for a project whose entry point does not reach all of them it
/// is deliberately not the same root a build or a package tag would publish.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Envelope {
    pub format: String,
    /// The hash scheme every address below commits to.
    pub scheme: String,
    /// The compiler version that produced the artifact.
    pub compiler: String,
    /// The indexed program's namespace root.
    pub contract: String,
    /// A display name for the indexed unit (package name, directory, or file).
    pub title: String,
    /// Whether the test layer is present, and why not when it is absent. Tests
    /// are only retained under a test-mode elaboration, which is a second
    /// front-end pass over the same source; recording its outcome keeps a missing
    /// `tests` edge set from reading as "this code has no tests".
    pub tests: TestLayer,
}

/// Whether the index's test layer was built.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum TestLayer {
    /// Test declarations and their `tests` edges are present.
    Included,
    /// The test-mode pass was not attempted (no test declarations in the input).
    Empty,
    /// The test-mode pass failed; the carried message is its diagnostic. Every
    /// other layer is unaffected, so an index of code whose tests do not compile
    /// is still a usable index of that code.
    Unavailable(String),
}

/// One indexed module: where its source lives and what it says about itself.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct IndexModule {
    /// The dotted module path (`Data.List`), the key `Def::module` refers to.
    pub dotted: String,
    /// The source path, relative to the indexed root.
    pub path: String,
    /// The module's own `-- |` description.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub doc: Option<String>,
    /// True for the prelude, whose declarations are in unqualified global scope
    /// and are therefore addressed by bare name.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub prelude: bool,
    /// The module's source text, so the artifact is self-contained and a viewer
    /// can slice `Def::span` without filesystem access. Omitted by
    /// `index --no-source`, for a consumer that reads the working tree itself.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
    /// The front end's diagnostic when this module's source does not parse. Its
    /// declarations are then absent from the definition layer, and this is what
    /// keeps that absence from reading as "an empty module": the same honesty
    /// [`TestLayer::Unavailable`] gives a test layer that could not be built.
    /// One broken file — a scratch buffer, a fixture that exists to be invalid —
    /// must not take the index of everything else down with it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// What kind of declaration a definition is.
///
/// The surface kind, not the Core one: a viewer renders and groups by what the
/// author wrote. Several kinds erase before Core and so carry no `hash` (see
/// [`Def::hash`]).
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Kind {
    /// A `fn`.
    Value,
    /// A top-level `let` constant.
    Const,
    /// A `test fn`.
    Test,
    /// A `logic fn` proof-level declaration.
    Logic,
    /// A `type`/`newtype` declaration.
    Type,
    /// A type synonym (`alias T = ...`).
    Synonym,
    /// An effect-row alias (`alias E = {..}`).
    RowAlias,
    /// An `effect` declaration.
    Effect,
    /// An `error` declaration (a one-op effect).
    Error,
    /// A type class.
    Class,
    /// An instance.
    Instance,
    /// A `pattern` extractor.
    Pattern,
    /// A `stable` version family. Its generated rungs and converters are indexed
    /// as ordinary types and values; this entry is the family declaration itself.
    Stable,
}

impl Kind {
    /// Whether this kind is a term: something with a value, an inferred type, and
    /// an effect row, addressed in the definition layer. The type-level kinds and
    /// instances are not.
    #[must_use]
    pub const fn is_term(self) -> bool {
        matches!(self, Self::Value | Self::Const | Self::Test | Self::Logic)
    }
}

/// A declaration's visibility outside its defining module.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Vis {
    /// Not exported: reachable only inside its module.
    #[default]
    Private,
    /// `pub`.
    Public,
    /// `opaque`: exported by name with its constructors hidden.
    Opaque,
}

impl Vis {
    // Taken by reference because `skip_serializing_if` hands serde the field that
    // way, not by choice.
    #[allow(clippy::trivially_copy_pass_by_ref)]
    const fn is_private(&self) -> bool {
        matches!(self, Self::Private)
    }
}

/// A checked claim a definition carries. Each is erased before executable Core,
/// so it is a property of the declaration rather than of its behavior hash;
/// a reviewer wants them on the definition card.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Claim {
    /// `total fn`: termination is proved.
    Total,
    /// `assume total fn`: termination is an explicit trust root.
    AssumeTotal,
    /// `fbip fn`: allocates nothing fresh.
    Fbip,
    /// `fip fn`: `fbip` plus linearity.
    Fip,
    /// `replayable fn`: the inferred row stays inside the recordable set.
    Replayable,
    /// `@ noalloc`: the whole call tree allocates no fresh heap cell.
    NoAlloc,
    /// Carries SMT contract clauses (`requires`/`ensures`).
    Contract,
}

/// Inclusive-exclusive byte range within the defining module's source.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

/// One name written inside a definition's [`Def::source`], and what it means.
///
/// Offsets are into `source` itself, so a consumer renders a navigable body by
/// slicing between them — no file access, no second coordinate system, no
/// knowledge of where the definition sat in whatever the compiler compiled.
///
/// `target` may name a definition the index does not contain, exactly as an edge
/// endpoint may; a builtin or a prelude function a project calls is still worth
/// showing as a name, just not as a link.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SourceRef {
    pub start: usize,
    pub end: usize,
    pub target: String,
}

/// One indexed definition.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Def {
    /// The canonical name, and the index's own key: the name Core knows this
    /// definition by (`Data.List.map` exported, `Data.Map@helper` private, a bare
    /// name in the prelude or the entry module). Edges refer to definitions by
    /// this string.
    pub id: String,
    /// The unqualified name as written.
    pub name: String,
    /// The defining module's dotted path (empty for the entry module).
    pub module: String,
    pub kind: Kind,
    /// The content address, in the namespace layer this kind is addressed in: a
    /// behavior hash for a term, a shape digest for a type or effect, an
    /// interface digest for a class, an identity digest for an instance.
    ///
    /// Two definitions with equal hashes are interchangeable by construction, so a
    /// consumer groups by this field to find behavioral duplicates; the artifact
    /// carries no separate equivalence edge set.
    ///
    /// Absent for the kinds that have no independent address: a synonym and a row
    /// alias erase into the types that mention them, a `pattern` lowers to hidden
    /// view/make functions, and a `stable` family desugars into its rungs. Also
    /// absent for a definition in a module the indexed program never reached, which
    /// `prism index` avoids by importing every module it lists, but which a library
    /// caller supplying its own [`IndexInput::source`] can produce.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub hash: Option<String>,
    /// The typechecker's inferred type, rendered. Terms only.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ty: Option<String>,
    /// Highlight spans over `ty`, packed exactly like [`Def::tokens`].
    ///
    /// A rendered type is not source — no file holds it, so it has no occurrence
    /// rows and no lexer has run over it. But it is written in the language's own
    /// type syntax, so running the compiler's lexer across the rendered string
    /// classifies it correctly, and the alternative is a second tokenizer in the
    /// consumer that would disagree with this one about what a name is.
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub ty_tokens: String,
    /// Every name in `ty` that resolves to a definition. A signature is the part of
    /// a definition a reader reads first, and `List`, `Concurrent.Async` and
    /// `Wire.Bytes` are as worth following there as in the body.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub ty_refs: Vec<SourceRef>,
    /// The inferred effect row, rendered (`{}` for a pure term). Terms only, and
    /// omitted when empty so a pure definition carries no field.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub effects: Option<String>,
    /// Highlight spans over `effects`, packed like [`Def::tokens`].
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub eff_tokens: String,
    /// Every name in `effects` that resolves to a definition.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub eff_refs: Vec<SourceRef>,
    /// The declaration as the author wrote it, sliced from the module source:
    /// signature, body, `where` block, and contract clauses. This is what a
    /// viewer folds and unfolds.
    pub source: String,
    /// Where `source` came from in the module, so a consumer holding the working
    /// tree can re-slice it (and so a viewer can link out to an editor).
    pub span: Span,
    #[serde(default, skip_serializing_if = "Vis::is_private")]
    pub vis: Vis,
    /// The `-- |` doc comment.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub doc: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub claims: Vec<Claim>,
    /// The author's replacement suggestion from a `deprecated "..."` annotation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub deprecated: Option<String>,
    /// The type of each name written in `source`: `gap length index` triples in
    /// the same packed form as `tokens`, where `index` selects from
    /// [`Index::type_table`].
    ///
    /// Variables only. Every subterm has a type, and carrying all of them would
    /// multiply the payload and nest spans inside one another — the whole
    /// `Row(gap, children)` contains `gap` — while a reader hovering a body is
    /// asking what the names in it are. Names cannot overlap, so a consumer merges
    /// these with the other span sets as flat intervals.
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub types: String,
    /// Highlight spans over `source`: whitespace-separated `gap length class`
    /// triples, where `gap` is the bytes since the previous span's end and `class`
    /// indexes [`Index::token_classes`].
    ///
    /// A string of numbers rather than an array of them, which looks like the
    /// wrong shape and is not. The artifact is pretty-printed, so a JSON array
    /// spends a newline and six spaces of indent on every element: over the
    /// standard library that is 167,000 elements and about 1.3 MB of whitespace,
    /// for data no one reads element-wise. One object per token
    /// (`{start, end, class}`) would cost 2 MB — most of the artifact again, to
    /// colour text. Unstyled spans (an ordinary lowercase identifier) are omitted,
    /// which is why the gap is needed rather than assuming spans abut.
    ///
    /// Baked rather than computed in the browser for two reasons. The spans come
    /// from the compiler's own lexer, so highlighting cannot disagree with the
    /// compiler about what a token is; and highlighting is wanted at first paint,
    /// while the wasm compiler sits behind a worker boundary and would arrive
    /// after it.
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub tokens: String,
    /// The names this declaration introduces inside itself, in source order: a
    /// type's constructors, a class's methods, an effect's operations. Empty for
    /// a declaration that introduces none.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub members: Vec<Member>,
    /// Every name written in `source` that resolves to a definition, in source
    /// order. This is what makes a rendered body navigable rather than merely
    /// readable: the edges say what a definition depends on, these say *where*.
    ///
    /// Only names the AST gives a span of their own appear — an expression
    /// variable, an effect-row label; see
    /// [`occurrences`] for why a constructor pattern
    /// and an instance's class do not.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub refs: Vec<SourceRef>,
}

/// A name a declaration introduces inside itself: a data constructor, a class
/// method, an effect operation.
///
/// None of these is a definition in its own right — a reference to one resolves
/// to the declaration that owns it — so without this they exist in the artifact
/// only as text inside a `source` field. That is enough to read and not enough to
/// *find*: `Cons`, `Nil` and `pure` are among the most written names in any Prism
/// program, and a consumer searching by name could not turn one up. Recovering
/// them from occurrences would find only the ones something happens to use, which
/// is exactly backwards for `Output`'s operations, performed by programs this
/// index does not contain.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Member {
    pub name: String,
    /// Where the owning declaration's [`Def::source`] names it.
    pub start: usize,
    pub end: usize,
}

/// A relationship between two definitions.
///
/// Every kind here is *derived*: the compiler already knows it, so it cannot go
/// stale against the code. Author-asserted relations (`equivalent`, `replaces`)
/// are a separate, later layer; the two are deliberately not mixed, because a
/// derived edge is a fact and an asserted one is a claim.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum EdgeKind {
    /// `from`'s body calls or captures `to`. The Merkle child relation: reversed,
    /// it is "who calls this", and its transitive closure is the exact set a
    /// change to `to` forces to re-hash.
    Calls,
    /// `from`'s type mentions the type `to`: a term's inferred type, or a type
    /// written into a declaration's own signature (a constructor's field, a class
    /// method, an effect operation, a synonym, an instance head).
    ///
    /// Resolved structurally, on the symbol rather than the written name, so two
    /// modules that each declare a `List` stay distinct. Only to a type the index
    /// contains: deriving it for everything in scope would bury a project's own
    /// structure under an `Int`/`Option` edge on nearly every definition.
    UsesType,
    /// `from`'s inferred effect row contains the effect `to`. Exact (read off the
    /// checked row), not a textual match on the rendered type.
    Performs,
    /// `from` has a handler clause for an operation of the effect `to`; reversed,
    /// "what interprets this effect".
    ///
    /// The other half of `Performs`, and not derivable from it: handling an effect
    /// *removes* it from the row, so the definition that gives an effect its
    /// meaning is exactly the one whose inferred row no longer mentions it. In the
    /// standard library `Output` is performed by nothing and handled four times —
    /// programs perform it, the library interprets it — so without this an effect
    /// declaration relates to nothing at all in either direction.
    Handles,
    /// `from` is an instance of the class `to`.
    InstanceOf,
    /// `from` is a test whose dependency closure contains `to`; reversed, "the
    /// tests that exercise this". Present only when the test layer is
    /// [`TestLayer::Included`].
    Tests,
}

/// One edge. Endpoints are [`Def::id`] strings.
///
/// An endpoint may name a definition the index does not contain (a prelude
/// function a project calls, say). That is deliberate: the outgoing edges of an
/// indexed definition are complete, so a viewer can show and label a link that
/// leaves the index rather than silently dropping it.
#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Edge {
    pub kind: EdgeKind,
    pub from: String,
    pub to: String,
}

/// The index artifact.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Index {
    pub envelope: Envelope,
    /// Indexed modules, in the order the caller supplied them.
    pub modules: Vec<IndexModule>,
    /// Every indexed definition, in module order and then source order, so the
    /// artifact reads like the code.
    pub defs: Vec<Def>,
    /// Every derived edge, sorted by `(kind, from, to)` and deduplicated.
    pub edges: Vec<Edge>,
    /// The compiler's own primitives.
    ///
    /// A reference to one resolves to no definition because there is none: it is
    /// implemented in the compiler rather than in Prism, so there is nothing to
    /// navigate to and nothing missing. Carried so a consumer can say *that*
    /// instead of reporting the name as absent from the artifact, which reads as
    /// an incomplete index when it is nothing of the kind — `byte_at` and
    /// `buf_push` are not gaps, they are `ByteAt` and `BufPush`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub builtins: Vec<Primitive>,
    /// The highlight categories [`Def::tokens`] indexes, so the class names are
    /// stored once rather than per token.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub token_classes: Vec<String>,
    /// The rendered types [`Def::types`] indexes. Interned for the same reason and
    /// with more force: one type is written at many names, and a `forall` repeated
    /// a thousand times would be most of the payload.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub type_table: Vec<String>,
}

/// One compiler primitive: what source calls it, and its type where the compiler
/// records one.
///
/// The signature is what makes a primitive readable rather than merely named. A
/// reader hovering `byte_at` wants `(String, Int) -> Int`; that it has no Prism
/// definition is the less interesting half.
#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Primitive {
    pub name: String,
    /// Which compiler namespace the primitive occupies. Builtin types and
    /// effects are navigation destinations just as builtin values are; keeping
    /// the distinction here lets a viewer present a real virtual declaration
    /// instead of a generic "implemented elsewhere" label.
    #[serde(default)]
    pub kind: PrimitiveKind,
    /// The signature the checker seeds. Absent for a primitive the table records
    /// no surface type for (one reached only through lowering).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub signature: Option<String>,
    /// A short compiler-owned description for wired entities that have no Prism
    /// doc comment of their own.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub doc: Option<String>,
}

/// The namespace occupied by a compiler primitive.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum PrimitiveKind {
    /// A callable or runtime-provided value.
    #[default]
    Value,
    /// A wired type constructor, including the eight scalar types.
    Type,
    /// A wired effect with no source declaration.
    Effect,
}

impl Index {
    /// Join independently compiled units into one navigable artifact.
    ///
    /// Each unit keeps the compiler facts it was built with. The only rewrite is
    /// to the two interned span tables: their small integer indexes are rebased
    /// onto one shared table while definitions, references, and edges retain
    /// their canonical names. This is what lets a documentation site combine the
    /// standard library and packages without teaching its viewer about multiple
    /// wire documents.
    ///
    /// # Errors
    /// Refuses an empty set, compiler/scheme mismatches, duplicate module or
    /// definition identities, conflicting primitive records, and malformed
    /// packed span data.
    pub fn merge(title: String, indexes: Vec<Self>) -> Result<Self, String> {
        let Some(first) = indexes.first() else {
            return Err("cannot merge an empty set of indexes".into());
        };
        let scheme = first.envelope.scheme.clone();
        let compiler = first.envelope.compiler.clone();
        let mut hasher = blake3::Hasher::new();
        merge_hash_field(&mut hasher, INDEX_FORMAT.as_bytes());
        merge_hash_field(&mut hasher, title.as_bytes());

        let mut modules = Vec::new();
        let mut module_names = BTreeSet::new();
        let mut defs = Vec::new();
        let mut def_ids = BTreeSet::new();
        let mut edges = BTreeSet::new();
        let mut builtins: BTreeMap<String, Primitive> = BTreeMap::new();
        let mut token_classes = Vec::new();
        let mut type_table = Vec::new();
        let mut any_tests = false;
        let mut unavailable_tests = Vec::new();

        for mut index in indexes {
            if index.envelope.scheme != scheme {
                return Err(format!(
                    "cannot merge `{}`: hash scheme `{}` differs from `{scheme}`",
                    index.envelope.title, index.envelope.scheme
                ));
            }
            if index.envelope.compiler != compiler {
                return Err(format!(
                    "cannot merge `{}`: compiler `{}` differs from `{compiler}`",
                    index.envelope.title, index.envelope.compiler
                ));
            }
            merge_hash_field(&mut hasher, index.envelope.title.as_bytes());
            merge_hash_field(&mut hasher, index.envelope.contract.as_bytes());
            match index.envelope.tests {
                TestLayer::Included => any_tests = true,
                TestLayer::Empty => {}
                TestLayer::Unavailable(why) => {
                    unavailable_tests.push(format!("{}: {why}", index.envelope.title));
                }
            }

            for module in index.modules {
                if !module_names.insert(module.dotted.clone()) {
                    return Err(format!(
                        "module `{}` occurs in more than one merged index",
                        module.dotted
                    ));
                }
                modules.push(module);
            }
            for def in &mut index.defs {
                if !def_ids.insert(def.id.clone()) {
                    return Err(format!(
                        "definition `{}` occurs in more than one merged index; index projects with \
                         `--as-library` so their entry modules are qualified",
                        def.id
                    ));
                }
                def.tokens = merge_packed(&def.tokens, &index.token_classes, &mut token_classes)?;
                def.ty_tokens =
                    merge_packed(&def.ty_tokens, &index.token_classes, &mut token_classes)?;
                def.eff_tokens =
                    merge_packed(&def.eff_tokens, &index.token_classes, &mut token_classes)?;
                def.types = merge_packed(&def.types, &index.type_table, &mut type_table)?;
            }
            defs.extend(index.defs);
            edges.extend(index.edges);
            for builtin in index.builtins {
                match builtins.get(&builtin.name) {
                    Some(existing) if existing != &builtin => {
                        return Err(format!(
                            "primitive `{}` has conflicting records in merged indexes",
                            builtin.name
                        ));
                    }
                    Some(_) => {}
                    None => {
                        builtins.insert(builtin.name.clone(), builtin);
                    }
                }
            }
        }

        let tests = if unavailable_tests.is_empty() {
            if any_tests {
                TestLayer::Included
            } else {
                TestLayer::Empty
            }
        } else {
            TestLayer::Unavailable(unavailable_tests.join("\n"))
        };
        let merged = Self {
            envelope: Envelope {
                format: INDEX_FORMAT.into(),
                scheme,
                compiler,
                contract: hasher.finalize().to_hex().to_string(),
                title,
                tests,
            },
            modules,
            defs,
            edges: edges.into_iter().collect(),
            builtins: builtins.into_values().collect(),
            token_classes,
            type_table,
        };
        // Keep the same validation boundary as an artifact read from disk.
        Self::from_json(&merged.to_json().map_err(|e| e.to_string())?)
    }

    /// Serialize with stable indentation and field order.
    ///
    /// Deterministic: identical source yields byte-identical JSON, which is what
    /// lets a committed index be checked in CI.
    ///
    /// # Errors
    /// Fails only if the derived JSON serializer rejects the document.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        let mut json = serde_json::to_string_pretty(self)?;
        json.push('\n');
        Ok(json)
    }

    /// Decode and validate an index artifact.
    ///
    /// # Errors
    /// Refuses an unknown format tag or an edge whose `from` names no indexed
    /// definition (an edge may point *out* of the index, never in from nowhere).
    pub fn from_json(text: &str) -> Result<Self, String> {
        let doc: Self = serde_json::from_str(text).map_err(|e| e.to_string())?;
        if doc.envelope.format != INDEX_FORMAT {
            return Err(format!(
                "unsupported index format `{}` (expected `{INDEX_FORMAT}`)",
                doc.envelope.format
            ));
        }
        let ids: BTreeSet<&str> = doc.defs.iter().map(|d| d.id.as_str()).collect();
        if let Some(edge) = doc.edges.iter().find(|e| !ids.contains(e.from.as_str())) {
            return Err(format!(
                "edge `{:?}` starts at `{}`, which is not an indexed definition",
                edge.kind, edge.from
            ));
        }
        Ok(doc)
    }

    /// The definition with this canonical name.
    ///
    /// A linear scan: this is a wire format, and a consumer that looks definitions
    /// up in a loop should build its own map over [`Def::id`] rather than call this
    /// repeatedly.
    #[must_use]
    pub fn def(&self, id: &str) -> Option<&Def> {
        self.defs.iter().find(|d| d.id == id)
    }
}

fn merge_hash_field(hasher: &mut blake3::Hasher, bytes: &[u8]) {
    hasher.update(&(bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

// Rebase packed `gap length index` triples from one intern table onto another.
// Gaps and lengths are byte offsets and therefore survive unchanged.
fn merge_packed(packed: &str, from: &[String], to: &mut Vec<String>) -> Result<String, String> {
    if packed.is_empty() {
        return Ok(String::new());
    }
    let fields: Vec<&str> = packed.split_whitespace().collect();
    if fields.len() % 3 != 0 {
        return Err(format!(
            "malformed packed spans: expected triples, found {} fields",
            fields.len()
        ));
    }
    let mut out = String::new();
    for triple in fields.chunks_exact(3) {
        let gap = triple[0]
            .parse::<usize>()
            .map_err(|_| format!("malformed span gap `{}`", triple[0]))?;
        let len = triple[1]
            .parse::<usize>()
            .map_err(|_| format!("malformed span length `{}`", triple[1]))?;
        let old = triple[2]
            .parse::<usize>()
            .map_err(|_| format!("malformed span table index `{}`", triple[2]))?;
        let value = from
            .get(old)
            .ok_or_else(|| format!("span table index {old} is out of bounds ({})", from.len()))?;
        let new = to.iter().position(|v| v == value).unwrap_or_else(|| {
            to.push(value.clone());
            to.len() - 1
        });
        if !out.is_empty() {
            out.push(' ');
        }
        use std::fmt::Write as _;
        write!(out, "{gap} {len} {new}").expect("writing to a String cannot fail");
    }
    Ok(out)
}
