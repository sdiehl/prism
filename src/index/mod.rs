//! `prism index`: the whole-codebase index a program viewer reads.
//!
//! One deterministic artifact per revision, containing definitions and their
//! relationships. It projects existing compiler facts: namespace addresses,
//! Core dependency edges, and checked effect rows.
//!
//! Two properties make it suitable for a viewer:
//!
//! - A canonical name and content hash identify each definition. Source ranges
//!   are rendering data.
//! - The complete edge set supports traversal in either direction without
//!   re-running the compiler.
//!
//! `cli::index` imports every listed module so library code outside the binary's
//! reachability set also receives an address. Unreachable modules remain in the
//! index without one.
//!
//! The artifact is a pure function of the indexed source (it is taken over the
//! identity surface, pre-optimizer elaborated Core), so `--check` can gate a
//! committed copy in CI the way `prism docs --check` gates committed pages.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

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

/// Identifies the artifact, its producer, and the indexed program.
///
/// `contract` is the namespace root of all listed modules. It may differ from a
/// build or package root whose entry point reaches fewer modules.
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
    /// The front-end diagnostic when this module does not parse. Other modules
    /// remain indexed.
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

/// A checked claim carried separately because claims are erased before Core.
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
/// Offsets are relative to `source`, so consumers need no source file or compiler
/// coordinates.
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
    /// Equal hashes identify behaviorally equivalent definitions.
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
    /// Rendered types are lexed by the compiler so consumers need no second type
    /// tokenizer.
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
    /// Contains variables only. Their spans do not overlap, so consumers can
    /// merge them with the other span sets as flat intervals.
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub types: String,
    /// Highlight spans over `source`: whitespace-separated `gap length class`
    /// triples, where `gap` is the bytes since the previous span's end and `class`
    /// indexes [`Index::token_classes`].
    ///
    /// The numeric string keeps pretty-printed JSON compact. Unstyled spans are
    /// omitted, so each encoded span includes its gap from the previous one.
    ///
    /// Spans come from the compiler lexer and are ready before the browser's wasm
    /// worker starts.
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub tokens: String,
    /// The names this declaration introduces inside itself, in source order: a
    /// type's constructors, a class's methods, an effect's operations. Empty for
    /// a declaration that introduces none.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub members: Vec<Member>,
    /// Every name in `source` that resolves to a definition, in source order.
    ///
    /// Only names with their own AST span appear. See [`occurrences`].
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub refs: Vec<SourceRef>,
}

/// A name a declaration introduces inside itself: a data constructor, a class
/// method, an effect operation.
///
/// Members resolve to their owning declaration. Recording every declared member
/// also makes unused constructors, methods, and operations searchable.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Member {
    pub name: String,
    /// Where the owning declaration's [`Def::source`] names it.
    pub start: usize,
    pub end: usize,
}

/// A relationship between two definitions.
///
/// These are derived compiler facts. Author-asserted relations belong to a
/// separate layer.
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
    /// Complements `Performs`. Handling removes an effect from the inferred row,
    /// so this relation is collected from handler clauses.
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
    /// implemented in the compiler rather than in Prism. This table lets a
    /// consumer distinguish primitives from missing definitions.
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
/// Includes a signature when the compiler records one.
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
    if !fields.len().is_multiple_of(3) {
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
        write!(out, "{gap} {len} {new}").expect("writing to a String cannot fail");
    }
    Ok(out)
}
