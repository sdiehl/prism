//! Building the index: joining each module's surface declarations to the
//! addresses, types, and effect rows the compiler computed for them.
//!
//! Two elaborations at most. The first is the ordinary production one, which
//! supplies every address, type, effect row, and dependency edge. The second runs
//! only when the input declares tests, in test mode, because a production
//! elaboration strips `test fn` before it hashes anything: it is the only place a
//! test's own address and dependency closure exist.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use crate::core::{DepGraph, Digest};
use crate::driver::{addressable_surface, addressable_surface_in, AddressableSurface, BuildMode};
use crate::error::Error;
use crate::names;
use crate::resolve::Root;
use crate::sym::Sym;
use crate::types::show_effects;
use crate::Config;

use super::{
    edges, occurrences, surface, Def, Envelope, Index, IndexModule, Kind, Primitive, PrimitiveKind,
    SourceRef, Span, TestLayer, Vis, INDEX_FORMAT,
};

/// What to index.
#[derive(Debug)]
pub struct IndexInput<'a> {
    /// The modules to index, in the order a viewer should list them. Reuses the
    /// doc generator's module description so one path resolution
    /// (`cli::docs::resolve_docs_input`) serves both surfaces.
    pub modules: &'a [crate::ModuleSource],
    /// The merged program source the addresses are taken over: the entry module
    /// with the prelude prepended, exactly as a build sees it. Imported modules
    /// resolve out of `roots`.
    pub source: &'a str,
    /// The module search path `source`'s imports resolve against.
    pub roots: &'a [Root],
    /// The dotted name of the module compiled as the entry, whose declarations are
    /// addressed by bare name because they are compiled at the root rather than
    /// imported. `None` when there is no such module, as when indexing the
    /// standard library.
    pub entry: Option<&'a str>,
    /// A display name for the indexed unit.
    pub title: String,
    /// Embed each module's source text, so the artifact is self-contained.
    pub embed_source: bool,
}

/// Build the index for `input`.
///
/// # Errors
/// Fails if a module does not parse, or if the merged program does not
/// type-check or elaborate. A failure in the *test-mode* pass is not an error: it
/// is recorded in [`Envelope::tests`] and every other layer is still built, so an
/// index of code whose tests do not compile is still a usable index of that code.
pub fn build(input: IndexInput<'_>) -> Result<Index, Error> {
    let production = addressable_surface(input.source, input.roots)?;

    // Walk each module's own source for what the author wrote, keyed by module.
    // A module that does not parse is carried with its diagnostic instead of
    // failing the build: one broken file — a scratch buffer, a fixture that
    // exists to be invalid — must not take the index of everything else down
    // with it. The same posture the test layer takes, for the same reason.
    let mut walked = Vec::new();
    for m in input.modules {
        walked.push((m, surface::walk(&m.source, m.is_prelude)));
    }

    // The test layer, attempted only when some module actually declares a test:
    // a second front-end pass over a whole project is not free, and `Empty` says
    // honestly that there was nothing to find rather than that something failed.
    let declares_tests = walked.iter().any(|(_, module)| {
        module
            .as_ref()
            .is_ok_and(|module| module.decls.iter().any(|d| d.kind == Kind::Test))
    });
    let (tests, test_surface) = if declares_tests {
        let cfg = Config {
            mode: BuildMode::Test,
            ..Config::default()
        };
        match addressable_surface_in(input.source, input.roots, &cfg) {
            Ok(surface) => (TestLayer::Included, Some(surface)),
            // The message is the front-end diagnostic, unrendered: the artifact
            // carries no source, so a span-annotated render would have nothing to
            // point at. A caller that wants the pointed report runs `prism test`.
            Err(e) => (TestLayer::Unavailable(e.to_string()), None),
        }
    } else {
        (TestLayer::Empty, None)
    };

    let addresses = Addresses::of(&production, test_surface.as_ref());
    let mut defs = Vec::new();
    let mut modules = Vec::new();
    // Module order is the caller's; within a module, source order (`surface::walk`
    // sorts by span). A viewer reads the artifact top to bottom and gets the code
    // back in the order it was written.
    for (source, module) in &walked {
        let scope = Scope {
            module: &source.dotted,
            prelude: source.is_prelude,
            entry: input.entry,
        };
        for decl in module.iter().flat_map(|m| &m.decls) {
            defs.push(addresses.address(scope, decl, &source.source));
        }
        modules.push(IndexModule {
            dotted: source.dotted.clone(),
            path: source.source_path.clone(),
            doc: module.as_ref().ok().and_then(|m| m.doc.clone()),
            prelude: source.is_prelude,
            source: input.embed_source.then(|| source.source.clone()),
            // The message is the front-end diagnostic, unrendered, exactly as
            // `TestLayer::Unavailable` carries its own.
            error: module.as_ref().err().map(ToString::to_string),
        });
    }
    let owners = member_owners(&production.program);
    attach_members(&mut defs, &production.program);
    attach_refs(
        &mut defs,
        &occurrences::extract(input.source, input.roots)?,
        &owners,
    );
    let builtins = builtin_names();
    attach_type_refs(&mut defs, &owners, &builtins);
    let token_classes = attach_tokens(&mut defs);
    let type_table = super::typed::attach_types(&mut defs, &production);
    let indexed: BTreeSet<String> = defs.iter().map(|d| d.id.clone()).collect();

    let edges = edges::derive(&edges::Sources {
        defs: &defs,
        indexed: &indexed,
        production: &production,
        test_graph: test_surface.as_ref().map(|s| DepGraph::of(&s.core)),
    });

    Ok(Index {
        envelope: Envelope {
            format: INDEX_FORMAT.to_string(),
            scheme: production.layers.scheme.to_string(),
            compiler: production.layers.version.to_string(),
            contract: production.layers.root.as_str().to_string(),
            title: input.title,
            tests,
        },
        modules,
        defs,
        edges,
        builtins,
        token_classes,
        type_table,
    })
}

// The primitives a reference can resolve to with no definition behind it.
//
// Three sources, because the compiler keeps its primitives in three places: the
// elaborator's builtin table, the float operations (a separate table, which is why
// `to_float` looked like an unexplained gap until it was included), and the
// wired-in effects and the one operation that have no declaration anywhere. Every
// other capability (`Console`, `Output`, `Alloc`) is declared in Prism and is
// indexed like any other effect.
fn builtin_names() -> Vec<Primitive> {
    let mut arities = BTreeMap::new();
    crate::core::builtin_arities(&mut arities);
    let mut names: BTreeMap<String, Primitive> = arities
        .into_keys()
        .map(|name| {
            (
                name.clone(),
                Primitive {
                    name,
                    kind: PrimitiveKind::Value,
                    signature: None,
                    doc: None,
                },
            )
        })
        .collect();
    names.extend(crate::core::builtins::FLOAT_OPS_BY_WIRE.iter().map(|op| {
        let name = op.name().to_string();
        (
            name.clone(),
            Primitive {
                name,
                kind: PrimitiveKind::Value,
                signature: Some(op.signature().to_string()),
                doc: None,
            },
        )
    }));
    // The enum-backed builtins are the ones that record a surface signature; the
    // table above supplies the rest of the names.
    for b in crate::core::builtins::BUILTINS_BY_WIRE {
        if let Some(sig) = b.signature() {
            let name = b.name().to_string();
            names.insert(
                name.clone(),
                Primitive {
                    name,
                    kind: PrimitiveKind::Value,
                    signature: Some(sig.to_string()),
                    doc: None,
                },
            );
        }
    }
    for scalar in crate::types::Type::SCALARS {
        let name = scalar.show();
        names.insert(
            name.clone(),
            Primitive {
                doc: scalar_doc(&name).map(str::to_string),
                name,
                kind: PrimitiveKind::Type,
                signature: Some("Type".into()),
            },
        );
    }
    names.insert(
        crate::kw::TY_OR_NULL.into(),
        Primitive {
            name: crate::kw::TY_OR_NULL.into(),
            kind: PrimitiveKind::Type,
            signature: Some("(Type) -> Type".into()),
            doc: Some(
                "A non-allocating nullable type whose element occupies one non-null word.".into(),
            ),
        },
    );
    for effect in [names::IO_EFFECT, names::EXN_EFFECT, names::FAIL_EFFECT] {
        names.insert(
            effect.to_string(),
            Primitive {
                name: effect.to_string(),
                kind: PrimitiveKind::Effect,
                signature: None,
                doc: Some("A compiler-wired effect with no Prism declaration.".into()),
            },
        );
    }
    names.insert(
        names::FAIL_OP.to_string(),
        Primitive {
            name: names::FAIL_OP.to_string(),
            kind: PrimitiveKind::Value,
            signature: Some("forall a. () -> a".into()),
            doc: Some("Abort the current computation through the wired Fail effect.".into()),
        },
    );
    names.into_values().collect()
}

fn scalar_doc(name: &str) -> Option<&'static str> {
    match name {
        crate::kw::TY_UNIT => Some("The unit type, whose sole value is ()."),
        crate::kw::TY_INT => Some("An arbitrary-precision integer."),
        crate::kw::TY_I64 => Some("A wrapping signed 64-bit integer."),
        crate::kw::TY_U64 => Some("A wrapping unsigned 64-bit integer."),
        crate::kw::TY_BOOL => Some("The boolean type, with values true and false."),
        crate::kw::TY_FLOAT => Some("An IEEE-754 double-precision floating-point number."),
        crate::kw::TY_CHAR => Some("A Unicode scalar value."),
        crate::kw::TY_STRING => Some("An immutable UTF-8 string."),
        _ => None,
    }
}

// Bake each definition's highlight spans, and return the class table they index.
//
// The same lexer pass `attach_type_refs` needs, so the two share the walk rather
// than lexing every body twice.
fn attach_tokens(defs: &mut [Def]) -> Vec<String> {
    let mut classes: Vec<String> = Vec::new();
    for def in defs.iter_mut() {
        def.tokens = pack_tokens(&def.source, &mut classes);
        // A rendered type and effect row are not source, but they are written in
        // the language's own syntax, so the same lexer classifies them and the
        // consumer needs no second one.
        def.ty_tokens = def
            .ty
            .as_ref()
            .map(|t| pack_tokens(t, &mut classes))
            .unwrap_or_default();
        def.eff_tokens = def
            .effects
            .as_ref()
            .map(|t| pack_tokens(t, &mut classes))
            .unwrap_or_default();
    }
    classes
}

// One text's highlight spans, as the packed `gap length class` triples
// [`Def::tokens`] documents, interning each class into `classes`.
fn pack_tokens(text: &str, classes: &mut Vec<String>) -> String {
    let mut flat = String::new();
    let mut prev_end = 0usize;
    for (start, end, class) in crate::lex::highlight::token_spans(text) {
        // An ordinary identifier has no colour, so its span is not worth a
        // triple; the gap to the next one absorbs it.
        if class == crate::lex::highlight::PLAIN_CLASS {
            continue;
        }
        let index = classes.iter().position(|c| c == class).unwrap_or_else(|| {
            classes.push(class.to_string());
            classes.len() - 1
        });
        if !flat.is_empty() {
            flat.push(' ');
        }
        // Saturating: a span that somehow ran backwards would otherwise
        // underflow, and a mispainted body is not worth a panic in a viewer.
        let _ = write!(
            flat,
            "{} {} {index}",
            start.saturating_sub(prev_end),
            end.saturating_sub(start)
        );
        prev_end = end;
    }
    flat
}

// Add a reference for each type name written in a definition's own text.
//
// The renamer cannot supply these: `Ty` carries no spans, so a type name resolved
// there has no position to report (see `occurrences`). But a written type is
// exactly what a reader wants to click — `d : Doc` should reach `Doc` — so the
// positions are recovered by lexing the definition's source.
//
// Lexing rather than searching, because only the lexer knows what is code: a
// `Doc` inside a comment or a string literal is not a reference, and a substring
// match would link both. Only an uppercase identifier or a qualified name is
// considered, which is what a type, a constructor, a class, and an effect are
// spelled as.
//
// The *name* is then resolved conservatively. A bare token is accepted only when
// exactly one indexed declaration bears that name, so the cross-module ambiguity
// that made `Outcome` link to three types cannot come back through this door; a
// token that names several is left as text rather than pointed somewhere plausible.
fn attach_type_refs(defs: &mut [Def], owners: &MemberOwners, builtins: &[Primitive]) {
    // Owned, not borrowed: `defs` is mutated below.
    let mut by_name: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for d in &*defs {
        if matches!(
            d.kind,
            Kind::Type
                | Kind::Synonym
                | Kind::RowAlias
                | Kind::Effect
                | Kind::Error
                | Kind::Class
                | Kind::Stable
        ) {
            by_name
                .entry(d.name.clone())
                .or_default()
                .insert(d.id.clone());
            by_name
                .entry(d.id.clone())
                .or_default()
                .insert(d.id.clone());
        }
    }
    for builtin in builtins {
        if matches!(builtin.kind, PrimitiveKind::Type | PrimitiveKind::Effect) {
            by_name
                .entry(builtin.name.clone())
                .or_default()
                .insert(builtin.name.clone());
        }
    }
    let indexed: BTreeSet<String> = defs.iter().map(|d| d.id.clone()).collect();
    // A constructor spelled in a pattern reaches the type that declares it, the
    // same destination its use in an expression already reaches.
    let resolve = |token: &str| -> Option<String> {
        let bare = crate::names::bare_name(token);
        if let Some(candidates) = by_name.get(token).or_else(|| by_name.get(bare)) {
            let mut it = candidates.iter();
            if let (Some(only), None) = (it.next(), it.next()) {
                return Some(only.clone());
            }
            return None;
        }
        let owner = owners.get(token).or_else(|| owners.get(bare))?;
        indexed.contains(owner).then(|| owner.clone())
    };

    for def in defs.iter_mut() {
        // A declaration's own member sites are not references. `Tip` and `Bin`
        // inside `type Map = Tip | Bin(..)` are where those members come into
        // being — `attach_members` has already recorded them, and a viewer sends
        // them to the member's users. Resolving them here instead would turn each
        // into a link from the declaration back to itself, and list the
        // declaration among its own members' users.
        let blocked: Vec<(usize, usize)> = def
            .refs
            .iter()
            .map(|r| (r.start, r.end))
            .chain(def.members.iter().map(|m| (m.start, m.end)))
            .collect();
        let mut found = named_in(&def.source, &resolve, &blocked);
        def.refs.append(&mut found);
        def.refs.sort_by_key(|r| (r.start, r.end));
        def.refs.dedup();
        // The signature gets the same treatment. It is the part of a definition a
        // reader reads first, and the renamer cannot help here either: no file
        // holds this text, the typechecker rendered it.
        def.ty_refs = def
            .ty
            .as_ref()
            .map(|t| named_in(t, &resolve, &[]))
            .unwrap_or_default();
        def.eff_refs = def
            .effects
            .as_ref()
            .map(|t| named_in(t, &resolve, &[]))
            .unwrap_or_default();
    }
}

// Every type-like name in `text` that `resolve` recognizes, skipping anything
// overlapping a `taken` span (an established reference, a member's own
// declaration site).
//
// Lexing rather than searching, because only the lexer knows what is code.
fn named_in(
    text: &str,
    resolve: &impl Fn(&str) -> Option<String>,
    taken: &[(usize, usize)],
) -> Vec<SourceRef> {
    let Ok((tokens, _)) = crate::lex::lex_raw(text) else {
        // A slice that does not lex on its own (it never should, having come from
        // a parsed program) simply gains no type links.
        return Vec::new();
    };
    let mut found: Vec<SourceRef> = Vec::new();
    for (start, token, end) in tokens {
        let name = match &token {
            crate::lex::Token::UIdent(name) | crate::lex::Token::QualName(name) => name.as_str(),
            crate::lex::Token::KwInt => crate::kw::TY_INT,
            crate::lex::Token::KwI64 => crate::kw::TY_I64,
            crate::lex::Token::KwU64 => crate::kw::TY_U64,
            crate::lex::Token::KwBool => crate::kw::TY_BOOL,
            crate::lex::Token::KwFloat => crate::kw::TY_FLOAT,
            crate::lex::Token::KwChar => crate::kw::TY_CHAR,
            crate::lex::Token::KwString => crate::kw::TY_STRING,
            crate::lex::Token::KwUnit => crate::kw::TY_UNIT,
            _ => continue,
        };
        // Never displace a reference the renamer established, or a member's
        // declaration site.
        if taken.iter().any(|&(from, to)| from < end && start < to) {
            continue;
        }
        if let Some(target) = resolve(name) {
            found.push(SourceRef { start, end, target });
        }
    }
    found
}

// Record where each declaration names its own members.
//
// The names come from the parsed declaration, so the list is complete and
// authoritative — every constructor, method and operation, including the ones
// nothing uses. That completeness is the point: recovering members from
// occurrences finds only the used ones, and an effect's operations are performed
// by *programs*, so a library index of `Output` would list none of them.
//
// The positions come from lexing the declaration's own text, because the AST has
// no span for a member's name (`ClassDecl::methods` is `(String, Ty)`, `EffOp` and
// `Ctor` are the same). Having the authoritative name list is what makes lexing
// safe here rather than a guess: only a token equal to a name this declaration
// actually declares is considered, preferring the `name :` form a method and an
// operation are declared with, then the first whole token otherwise, which is
// where a constructor sits in `= Nil | Cons(a, List(a))`.
fn attach_members(
    defs: &mut [Def],
    program: &crate::syntax::ast::Program<crate::syntax::ast::Core>,
) {
    let mut declared: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for d in &program.types {
        declared.insert(&d.name, d.ctors.iter().map(|c| c.name.as_str()).collect());
    }
    for e in &program.effects {
        declared.insert(&e.name, e.ops.iter().map(|op| op.name.as_str()).collect());
    }
    for c in &program.classes {
        declared.insert(&c.name, c.methods.iter().map(|(m, _)| m.as_str()).collect());
    }
    for def in defs.iter_mut() {
        let Some(names) = declared.get(def.id.as_str()) else {
            continue;
        };
        let Ok((tokens, _)) = crate::lex::lex_raw(&def.source) else {
            continue;
        };
        for canonical in names {
            // The renamer canonicalizes a constructor (`Data.Pretty.DNil`) while
            // leaving a method and an operation bare, and the source spells all
            // three the same way: unqualified.
            let name = names::bare_name(canonical);
            let hits: Vec<usize> = tokens
                .iter()
                .enumerate()
                .filter(|(_, (start, token, end))| {
                    matches!(
                        token,
                        crate::lex::Token::Ident(t) | crate::lex::Token::UIdent(t) if t == name
                    ) && def.source.get(*start..*end) == Some(name)
                })
                .map(|(i, _)| i)
                .collect();
            let is_signature = |i: &&usize| {
                matches!(
                    tokens.get(**i + 1).map(|(_, t, _)| t),
                    Some(crate::lex::Token::Colon)
                )
            };
            let Some(&at) = hits.iter().find(is_signature).or_else(|| hits.first()) else {
                continue;
            };
            let (start, _, end) = tokens[at];
            def.members.push(super::Member {
                name: name.to_string(),
                start,
                end,
            });
        }
        def.members.sort_by_key(|m| m.start);
    }
}

// A name that resolves to something with no declaration of its own, mapped to the
// declaration a reader should navigate to instead.
//
// A constructor is written inside a `type`, an operation inside an `effect`, a
// method inside a `class`. None is a definition in its own right, so a reference
// to one resolves to a name the index has no entry for — and `Cons`, `Some`, and
// `Err` are among the most frequently written names in any program. This is the
// same retarget `edges` applies to a lowered instance method, for the same reason:
// send the reader where the source actually is.
//
// Only an unambiguous mapping counts. The renamer canonicalizes constructors but
// leaves operation and method names bare (they are not module binders), so two
// effects can each declare a `get`. A name owned by more than one declaration
// identifies nothing, and picking one would fabricate navigation.
pub(super) fn member_owners(
    program: &crate::syntax::ast::Program<crate::syntax::ast::Core>,
) -> MemberOwners {
    let mut candidates: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut claim = |member: &str, owner: &str| {
        candidates
            .entry(member.to_string())
            .or_default()
            .insert(owner.to_string());
    };
    for d in &program.types {
        for c in &d.ctors {
            claim(&c.name, &d.name);
        }
    }
    for e in &program.effects {
        for op in &e.ops {
            claim(&op.name, &e.name);
        }
    }
    for c in &program.classes {
        for (method, _) in &c.methods {
            claim(method, &c.name);
        }
    }
    candidates
        .into_iter()
        .filter_map(|(member, owners)| {
            let mut it = owners.into_iter();
            match (it.next(), it.next()) {
                (Some(only), None) => Some((member, only)),
                _ => None,
            }
        })
        .collect()
}

pub(super) type MemberOwners = BTreeMap<String, String>;

// Place every resolved reference inside the definition that contains it.
//
// Matched by canonical name, which is the index's own key, and rebased onto the
// definition's `source` with the owner offset the renamer recorded. That offset
// is what lets this work at all: a reference in the root module is reported at
// its position in the compiled source, which starts with the prelude, while the
// index holds that module's declarations at positions in its own file. The
// difference between a reference and its owner is the same in either.
//
// A reference that does not land inside the text it claims to be in is dropped
// rather than emitted: the two spans then came from different parses, and a link
// at a wrong offset is worse than a missing one.
fn attach_refs(defs: &mut [Def], seen: &occurrences::Occurrences, owners: &MemberOwners) {
    // Owned rather than borrowed from `defs`, which is about to be mutated.
    let indexed: BTreeSet<String> = defs.iter().map(|d| d.id.clone()).collect();
    // A reference to a constructor, an operation, or a method points at the
    // declaration that writes it, when the index has that declaration.
    let retarget = |target: &str| -> String {
        if indexed.contains(target) {
            return target.to_string();
        }
        match owners.get(target) {
            Some(owner) if indexed.contains(owner) => owner.clone(),
            _ => target.to_string(),
        }
    };
    let mut by_owner: BTreeMap<&str, Vec<&occurrences::Ref>> = BTreeMap::new();
    for r in &seen.refs {
        by_owner.entry(r.owner.as_str()).or_default().push(r);
    }
    for def in defs.iter_mut() {
        let Some(refs) = by_owner.get(def.id.as_str()) else {
            continue;
        };
        let mut placed: Vec<SourceRef> = refs
            .iter()
            .filter_map(|r| {
                let start = r.start.checked_sub(r.owner_start)?;
                let end = r.end.checked_sub(r.owner_start)?;
                (end <= def.source.len() && start < end).then(|| SourceRef {
                    start,
                    end,
                    target: retarget(&r.target),
                })
            })
            .collect();
        placed.sort_by_key(|r| (r.start, r.end));
        placed.dedup();
        def.refs = placed;
    }
}

// Where a declaration sits, which is what decides how it is named.
#[derive(Clone, Copy)]
struct Scope<'a> {
    module: &'a str,
    prelude: bool,
    entry: Option<&'a str>,
}

// The four namespace layers plus the test layer, as the one lookup a declaration
// is addressed through.
struct Addresses<'a> {
    production: &'a AddressableSurface,
    // Every test's behavior hash, from the test-mode pass. Keyed by canonical
    // name like the production definition layer.
    test_defs: BTreeMap<String, Digest>,
    // Each term definition's inferred type and effect row, by canonical name.
    // Production first, then the test layer, so a test gets the type and row its
    // own elaboration inferred (production has stripped it).
    terms: BTreeMap<&'a str, &'a crate::types::DeclInfo>,
}

impl<'a> Addresses<'a> {
    fn of(production: &'a AddressableSurface, test: Option<&'a AddressableSurface>) -> Self {
        let mut terms: BTreeMap<&'a str, &'a crate::types::DeclInfo> = test
            .into_iter()
            .flat_map(|s| s.checked.decls.iter())
            .map(|d| (d.name.as_str(), d))
            .collect();
        terms.extend(
            production
                .checked
                .decls
                .iter()
                .map(|d| (d.name.as_str(), d)),
        );
        Self {
            production,
            test_defs: test
                .map(|s| {
                    s.layers
                        .defs
                        .iter()
                        .map(|(sym, h)| (sym.as_str().to_string(), h.clone()))
                        .collect()
                })
                .unwrap_or_default(),
            terms,
        }
    }

    // The digest a name has in the layer this kind is addressed in, if any.
    fn lookup(&self, kind: Kind, name: &str) -> Option<&Digest> {
        let layers = &self.production.layers;
        match kind {
            Kind::Value | Kind::Const | Kind::Logic => layers.defs.get(&Sym::new(name)),
            // A test is absent from production Core by construction, so its
            // address comes from the test-mode layer or nowhere.
            Kind::Test => self.test_defs.get(name),
            Kind::Type | Kind::Effect | Kind::Error => layers.shapes.get(name),
            Kind::Class => layers.classes.get(name),
            Kind::Instance => layers.instances.get(name),
            // No independent address: a synonym and a row alias erase into the
            // types that mention them, a `pattern` lowers to hidden view/make
            // functions, and a `stable` family desugars into rungs and converters
            // that are indexed as ordinary declarations in their own right.
            Kind::Synonym | Kind::RowAlias | Kind::Pattern | Kind::Stable => None,
        }
    }

    // Join one surface declaration to its address, type, and effect row.
    fn address(&self, scope: Scope<'_>, decl: &surface::Decl, module_source: &str) -> Def {
        let global = is_global(scope, decl);
        let mut id = None;
        let mut hash = None;
        for candidate in candidates(scope.module, &decl.name, global) {
            if let Some(digest) = self.lookup(decl.kind, &candidate) {
                hash = Some(digest.as_str().to_string());
                id = Some(candidate);
                break;
            }
        }
        // No address: either the kind has none, or the indexed program never
        // reached this module, so it was never elaborated or hashed. Both are
        // honest states for a viewer to show; the caller avoids the second by
        // supplying a source that imports every module it lists.
        let id = id.unwrap_or_else(|| structural(scope, &decl.name, global, decl.vis));
        let term = decl
            .kind
            .is_term()
            .then(|| self.terms.get(id.as_str()))
            .flatten();
        Def {
            id,
            name: decl.name.clone(),
            module: scope.module.to_string(),
            kind: decl.kind,
            hash,
            ty: term.map(|t| t.ty.show()),
            // An empty row is omitted rather than rendered `{}`: a pure definition
            // should carry no effect field at all.
            effects: term
                .map(|t| show_effects(&t.effects))
                .filter(|row| row != "{}"),
            source: slice(module_source, decl.span),
            span: decl.span,
            vis: decl.vis,
            doc: decl.doc.clone(),
            claims: decl.claims.clone(),
            deprecated: decl.deprecated.clone(),
            // All filled after every definition is addressed: a reference is
            // placed by the canonical name of the declaration holding it, a name
            // resolves only against the whole set, and the highlight spans share
            // that same lexer pass.
            members: Vec::new(),
            types: String::new(),
            refs: Vec::new(),
            tokens: String::new(),
            ty_tokens: String::new(),
            ty_refs: Vec::new(),
            eff_tokens: String::new(),
            eff_refs: Vec::new(),
        }
    }
}

// Whether a declaration is addressed by bare name.
//
// Three ways to be: the prelude's declarations are in unqualified global scope
// (they are prepended, not imported), the entry module is compiled at the root
// rather than imported, and an instance is global because coherence is
// program-wide. A root-module input has no module name at all.
fn is_global(scope: Scope<'_>, decl: &surface::Decl) -> bool {
    scope.module.is_empty()
        || scope.prelude
        || Some(scope.module) == scope.entry
        || decl.kind == Kind::Instance
}

// The canonical spellings a declaration could have, most specific first.
//
// A global declaration has exactly one: its bare name. Anything else is either
// exported (`Data.Map.insert`) or module-private (`Data.Map@helper`), and which
// one it is could be read off the `pub` marker — but it is read off the layer
// instead, by probing both, so the index cannot disagree with Core about a name.
// The bare form is deliberately *not* a candidate for a non-global module: it
// would silently match an unrelated same-named definition in the entry module.
fn candidates(module: &str, name: &str, global: bool) -> Vec<String> {
    if global {
        return vec![name.to_string()];
    }
    vec![format!("{module}.{name}"), names::private(module, name)]
}

// The name a declaration must have when no layer claims it, from its `pub` marker.
fn structural(scope: Scope<'_>, name: &str, global: bool, vis: Vis) -> String {
    if global {
        name.to_string()
    } else if matches!(vis, Vis::Public | Vis::Opaque) {
        format!("{}.{name}", scope.module)
    } else {
        names::private(scope.module, name)
    }
}

// A declaration's own text. Spans come from the parser over this same source, so
// they are on character boundaries; a span that somehow is not yields the empty
// string rather than panicking, because an index is a read-only view and must not
// be the thing that crashes.
fn slice(source: &str, span: Span) -> String {
    source
        .get(span.start..span.end)
        .unwrap_or_default()
        .to_string()
}
