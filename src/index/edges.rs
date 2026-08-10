//! Deriving the relationship set.
//!
//! Every edge here is read off something the compiler already computed, so none
//! of it can go stale against the code:
//!
//! - `calls` is the Core dependency adjacency (`core::DepGraph`) — the same
//!   relation the content hasher walks for its Merkle substitution and
//!   `prism store query callers` answers one name at a time.
//! - `performs` is the checked effect row, read as a set rather than matched as
//!   text, so it is exact.
//! - `uses-type` is a structural walk over the checked type and over the types
//!   written into a declaration's own signature, keyed on the resolved symbol.
//!   Deliberately not the token rule `prism store query uses-type` applies: that
//!   query matches a name a human typed, where looseness is convenient, while an
//!   edge between canonical identities has to be exact.
//! - `instance-of` is the resolved instance's class.
//! - `tests` is a test's transitive dependency closure in the test-mode graph.
//!
//! Behavioral equivalence is deliberately *not* an edge kind: two definitions are
//! interchangeable exactly when their [`super::Def::hash`] fields are equal, so a
//! consumer groups by hash and the artifact carries no redundant (and potentially
//! quadratic) edge set.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::DepGraph;
use crate::driver::AddressableSurface;
use crate::sym::Sym;

use super::{Def, Edge, EdgeKind, Kind};

/// Everything the derivation reads.
pub(super) struct Sources<'a> {
    pub defs: &'a [Def],
    /// The ids the index contains, for deciding which endpoints resolve.
    pub indexed: &'a BTreeSet<String>,
    pub production: &'a AddressableSurface,
    /// The test-mode dependency graph, when the test layer was built.
    pub test_graph: Option<DepGraph>,
}

/// Derive every edge, sorted by `(kind, from, to)` and deduplicated.
pub(super) fn derive(sources: &Sources<'_>) -> Vec<Edge> {
    let mut edges = BTreeSet::new();
    let lowered = lowered_methods(sources);
    let synthetic = synthetic_owners(sources);
    calls(sources, &lowered, &synthetic, &mut edges);
    types_and_effects(sources, &lowered, &mut edges);
    handles(sources, &mut edges);
    instances(sources, &mut edges);
    tests(sources, &mut edges);
    edges.into_iter().collect()
}

// `calls`: each indexed definition's direct Core dependencies.
//
// Driven from the indexed definitions rather than from the graph's own node set,
// so the outgoing edges of everything in the index are complete. A target outside
// the index (a prelude function a project calls) is still emitted, named by its
// canonical name: a viewer can render and label a link that leaves the index,
// which is more useful than a silently missing one.
fn calls(
    sources: &Sources<'_>,
    lowered: &Lowered,
    synthetic: &BTreeMap<String, String>,
    out: &mut BTreeSet<Edge>,
) {
    let graph = DepGraph::of(&sources.production.core);
    for def in sources.defs {
        for name in core_names(def, lowered) {
            for dep in graph.direct_deps(Sym::new(name)) {
                let to = resolve_target(sources, synthetic, dep.as_str());
                // A method calling a sibling of the same instance is not the
                // instance calling itself.
                if to != def.id {
                    out.insert(Edge {
                        kind: EdgeKind::Calls,
                        from: def.id.clone(),
                        to,
                    });
                }
            }
        }
    }
}

/// The lowered method names elaboration gave each indexed instance.
type Lowered = BTreeMap<String, Vec<String>>;

// The Core names a definition's body lives under.
//
// For everything but an instance this is just its own name. Elaboration lifts each
// instance method to its own top-level function (`i@showInt@show`), so an instance
// has *no* Core node of its own and its dependencies belong to those lifted names.
// Asking the graph about the instance's own name therefore answered nothing: not
// one of the standard library's 100 instances had a single outgoing edge, so a card
// for `arbitraryFloat` could show the class it implements and nothing about the
// `gen_run` and `gen_float` plainly written in its body.
fn core_names<'a>(def: &'a Def, lowered: &'a Lowered) -> Vec<&'a str> {
    if def.kind == Kind::Instance {
        return lowered
            .get(&def.id)
            .map(|names| names.iter().map(String::as_str).collect())
            .unwrap_or_default();
    }
    if def.kind.is_term() {
        return vec![def.id.as_str()];
    }
    Vec::new()
}

// Every lowered instance method in Core, grouped by the instance it belongs to.
// Read off the Core function names rather than the AST, which is the same source
// `resolve_target` reverses when an edge *points at* one of these.
fn lowered_methods(sources: &Sources<'_>) -> Lowered {
    let mut out: Lowered = BTreeMap::new();
    for f in &sources.production.core.fns {
        let name = f.name.as_str();
        if let Some((instance, _)) = crate::names::parse_instance_method(name) {
            if sources.indexed.contains(instance) {
                out.entry(instance.to_string())
                    .or_default()
                    .push(name.to_string());
            }
        }
    }
    out
}

// The definition a call target names, as a viewer should navigate to it.
//
// Elaboration lowers each instance method to its own top-level function
// (`i@showInt@show`), so a dictionary-dispatched call lands on a name with no
// declaration of its own. The method's source is written inside its instance, so
// the edge is retargeted there: a link that resolves to where the code actually
// is beats one that resolves to nothing. Any other name passes through unchanged,
// including one outside the index.
fn resolve_target(
    sources: &Sources<'_>,
    synthetic: &BTreeMap<String, String>,
    target: &str,
) -> String {
    if sources.indexed.contains(target) {
        return target.to_string();
    }
    if let Some(owner) = synthetic.get(target) {
        return owner.clone();
    }
    if let Some((instance, _)) = crate::names::parse_instance_method(target) {
        if sources.indexed.contains(instance) {
            return instance.to_string();
        }
        if let Some(owner) = synthetic.get(instance) {
            return owner.clone();
        }
    }
    target.to_string()
}

// Compiler-synthesized call targets have no declaration of their own. A derived
// instance's methods are written by `deriving (...)` on its datatype, and a
// structural `_show_*` helper is generated for the one indexed datatype in its
// signature. Send both to that datatype so every dependency chip reaches the
// source that caused the helper to exist.
fn synthetic_owners(sources: &Sources<'_>) -> BTreeMap<String, String> {
    let mut owners = BTreeMap::new();
    for instance in &sources.production.program.instances {
        let crate::syntax::ast::Ty::Con(owner, _) = &instance.head else {
            continue;
        };
        // Derived instances use the synthetic zero span. Preserve an external
        // owner too: a package index may derive through an imported stdlib type,
        // and the target becomes local when those artifacts are merged. A real
        // imported instance keeps its own identity instead.
        if instance.span.start == 0
            && instance.span.end == 0
            && !sources.indexed.contains(&instance.name)
        {
            owners.insert(instance.name.clone(), owner.clone());
        }
    }
    for decl in &sources.production.checked.decls {
        if !decl.name.starts_with("_show_") || sources.indexed.contains(&decl.name) {
            continue;
        }
        let mut mentioned = BTreeSet::new();
        type_cons(&decl.ty, &mut mentioned);
        let mut indexed = mentioned
            .into_iter()
            .filter(|name| sources.indexed.contains(name.as_str()));
        if let (Some(owner), None) = (indexed.next(), indexed.next()) {
            owners.insert(decl.name.clone(), owner.as_str().to_string());
        }
    }
    owners
}

// `uses-type` and `performs`.
//
// `uses-type` resolves only to *indexed* types. Deriving it for every type in
// scope would bury a project's own structure under an `Int`/`List`/`Option` edge
// on nearly every definition; the types a reviewer navigates by are the ones in
// front of them. `performs` has no such restriction: an effect row is short, and
// `IO` is exactly the kind of edge a reviewer wants even with no definition behind
// it, so an unindexed effect is emitted named by its row label.
fn types_and_effects(sources: &Sources<'_>, lowered: &Lowered, out: &mut BTreeSet<Edge>) {
    // Keyed by canonical name, not by the written one. A structural walk yields
    // the resolved symbol, so two modules that each declare a `List` stay distinct
    // here; matching a rendered type's tokens against bare names could not tell
    // them apart and emitted an edge to both, one of which was wrong.
    let indexed_types: BTreeSet<&str> = sources
        .defs
        .iter()
        .filter(|d| matches!(d.kind, Kind::Type | Kind::Synonym))
        .map(|d| d.id.as_str())
        .collect();
    let mut effects: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for def in sources.defs {
        if matches!(def.kind, Kind::Effect | Kind::Error) {
            effects.entry(&def.name).or_default().push(&def.id);
        }
    }
    // Indexed once: a per-definition scan of the checked declarations would be
    // quadratic in the size of the codebase.
    // An instance method is checked from inside its instance, so it is not a
    // `DeclInfo` and its row lives in the typechecker's own record of what each
    // method performs, keyed by the name elaboration lifts it to. Without it an
    // instance says nothing about its effects: five class methods in the standard
    // library declare a concrete one (`decode` and `from_json` may `Fail`,
    // `arbitrary` uses `Random`), and every instance of those classes was silent.
    let rows: BTreeMap<&str, &crate::types::Effects> = sources
        .production
        .checked
        .decls
        .iter()
        .map(|d| (d.name.as_str(), &d.effects))
        .chain(
            sources
                .production
                .checked
                .method_effects
                .iter()
                .map(|(name, effects)| (name.as_str(), effects)),
        )
        .collect();
    let checked: BTreeMap<&str, &crate::types::Type> = sources
        .production
        .checked
        .decls
        .iter()
        .map(|d| (d.name.as_str(), &d.ty))
        .collect();
    // Type references written in a *declaration's* signature rather than inferred
    // for a term: a constructor's field types, a class method's signature, an
    // effect operation's parameters. Without these, "who uses this type" reaches
    // the functions over it but not the types that embed it.
    let declared = declared_type_refs(sources);

    for def in sources.defs {
        let mut mentions: BTreeSet<String> = BTreeSet::new();
        if let Some(ty) = checked.get(def.id.as_str()) {
            let mut cons = BTreeSet::new();
            type_cons(ty, &mut cons);
            mentions.extend(cons.into_iter().map(|s| s.as_str().to_string()));
        }
        if let Some(refs) = declared.get(def.id.as_str()) {
            mentions.extend(refs.iter().cloned());
        }
        for target in mentions {
            if target != def.id && indexed_types.contains(target.as_str()) {
                out.insert(Edge {
                    kind: EdgeKind::UsesType,
                    from: def.id.clone(),
                    to: target,
                });
            }
        }
        // The row is read from the checked declaration, not from the rendered
        // type, so a label is matched as a label. An effect declared in an indexed
        // module resolves to that declaration; anything else (a builtin row like
        // `IO`, or a capability from a module outside the index) is named by its
        // label.
        for label in core_names(def, lowered)
            .into_iter()
            .filter_map(|name| rows.get(name))
            .flat_map(|r| r.iter())
        {
            let label = label.to_string();
            match effects.get(crate::names::bare_name(&label)) {
                Some(ids) => {
                    for target in ids {
                        out.insert(Edge {
                            kind: EdgeKind::Performs,
                            from: def.id.clone(),
                            to: (*target).to_string(),
                        });
                    }
                }
                None => {
                    out.insert(Edge {
                        kind: EdgeKind::Performs,
                        from: def.id.clone(),
                        to: label,
                    });
                }
            }
        }
    }
}

// Every type constructor a checked type mentions, at any depth.
//
// Structural rather than textual: `Type::each_child` is the exhaustive statement
// of what a type contains, so this cannot miss a position (an effect-row argument,
// a coeffect's inner type) and cannot mistake a type variable for a constructor.
fn type_cons(ty: &crate::types::Type, out: &mut BTreeSet<Sym>) {
    if let crate::types::Type::Con(name, _) = ty {
        out.insert(*name);
    }
    ty.each_child(&mut |child| type_cons(child, out));
}

// The same, over a surface type, whose names the renamer has already canonicalized.
fn surface_cons(ty: &crate::syntax::ast::Ty, out: &mut BTreeSet<String>) {
    if let crate::syntax::ast::Ty::Con(name, _) = ty {
        out.insert(name.clone());
    }
    ty.each_child(&mut |child| surface_cons(child, out));
}

// Type references written into a declaration's own signature, by the canonical
// name of the declaration that writes them.
//
// Read from the merged program, where the renamer has canonicalized every type
// name, so a reference resolves to the same symbol a term's inferred type would
// carry. Each declaration kind contributes the positions where a type can be
// written: a datatype's constructor fields, a class's method signatures, an
// effect operation's parameters and result, a synonym's right-hand side, an
// instance's head, and an extractor's subject type.
fn declared_type_refs(sources: &Sources<'_>) -> BTreeMap<String, BTreeSet<String>> {
    let program = &sources.production.program;
    let mut out: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut add = |owner: &str, ty: &crate::syntax::ast::Ty| {
        let mut cons = BTreeSet::new();
        surface_cons(ty, &mut cons);
        out.entry(owner.to_string()).or_default().extend(cons);
    };

    for d in &program.types {
        for ctor in &d.ctors {
            for t in &ctor.args {
                add(&d.name, t);
            }
            for (_, t) in ctor.fields.iter().flatten() {
                add(&d.name, t);
            }
        }
    }
    for c in &program.classes {
        for (_, t) in &c.methods {
            add(&c.name, t);
        }
    }
    for e in &program.effects {
        for op in &e.ops {
            for t in &op.params {
                add(&e.name, t);
            }
            add(&e.name, &op.ret);
        }
    }
    for s in &program.synonyms {
        add(&s.name, &s.ty);
    }
    for i in &program.instances {
        add(&i.name, &i.head);
    }
    out
}

// `instance-of`: the class each resolved instance implements.
//
// Read from the merged program rather than from the surface, so the class name is
// the canonical one the class layer is keyed by — the same string the class's own
// `Def::id` resolved to, so the two ends of the edge agree by construction.
// `handles`: from a definition with a handler clause to the effect that clause
// interprets.
//
// The other half of `performs`, and it cannot be read off a row, because handling
// an effect is exactly what *removes* it from one: the definition that gives an
// effect its meaning is the one whose inferred row no longer mentions it. The
// standard library's `Output` shows what that costs. Nothing there performs it —
// programs do — and four definitions handle it, so before this its card related to
// nothing whatsoever in either direction, and the four interpreters of a
// user-facing capability were unreachable from the capability.
//
// Read off the handler clauses the parser already produced, mapped through the
// same owner table a written operation name resolves through. A clause head has no
// span of its own (`HandlerArm::Op` carries a bare `String`), so this is an edge
// rather than an occurrence: the relation is exact, the position is not available.
fn handles(sources: &Sources<'_>, out: &mut BTreeSet<Edge>) {
    let owners = super::build::member_owners(&sources.production.program);
    for def in sources.defs {
        let Some(decl) = sources
            .production
            .program
            .fns
            .iter()
            .find(|d| d.name == def.id)
        else {
            continue;
        };
        let mut handled: BTreeSet<&str> = BTreeSet::new();
        walk(&decl.body, &mut |e| {
            let crate::syntax::ast::Expr::Handle(_, arms, _) = &e.node else {
                return;
            };
            for arm in arms {
                let crate::syntax::ast::HandlerArm::Op(op, ..) = arm else {
                    continue;
                };
                if let Some(effect) = owners.get(op.as_str()) {
                    if sources.indexed.contains(effect) {
                        handled.insert(effect);
                    }
                }
            }
        });
        for effect in handled {
            out.insert(Edge {
                kind: EdgeKind::Handles,
                from: def.id.clone(),
                to: effect.to_string(),
            });
        }
    }
}

// Every expression in a tree, the node itself first.
fn walk(
    e: &crate::syntax::ast::S<crate::syntax::ast::Expr<crate::syntax::ast::Core>>,
    f: &mut impl FnMut(&crate::syntax::ast::S<crate::syntax::ast::Expr<crate::syntax::ast::Core>>),
) {
    f(e);
    e.node.each_child(&mut |child| walk(child, f));
}

fn instances(sources: &Sources<'_>, out: &mut BTreeSet<Edge>) {
    let indexed_instances: BTreeSet<&str> = sources
        .defs
        .iter()
        .filter(|d| d.kind == Kind::Instance)
        .map(|d| d.id.as_str())
        .collect();
    for inst in &sources.production.program.instances {
        if indexed_instances.contains(inst.name.as_str()) {
            out.insert(Edge {
                kind: EdgeKind::InstanceOf,
                from: inst.name.clone(),
                to: inst.class.clone(),
            });
        }
    }
}

// `tests`: from each test to every indexed definition in its transitive
// dependency closure.
//
// Transitive rather than direct on purpose. "The tests that exercise this
// function" must include a test that reaches it through a helper, which is the
// common case; a direct-only edge set would quietly answer "none" for most
// definitions. Restricting the targets to indexed definitions is what keeps the
// closure from dragging in the whole prelude on every test.
fn tests(sources: &Sources<'_>, out: &mut BTreeSet<Edge>) {
    let Some(graph) = &sources.test_graph else {
        return;
    };
    for def in sources.defs.iter().filter(|d| d.kind == Kind::Test) {
        for target in graph.dependencies(Sym::new(&def.id)) {
            let target = target.as_str();
            if sources.indexed.contains(target) {
                out.insert(Edge {
                    kind: EdgeKind::Tests,
                    from: def.id.clone(),
                    to: target.to_string(),
                });
            }
        }
    }
}
