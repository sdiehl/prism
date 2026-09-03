//! The surface layer: what one module's source says about its own declarations.
//!
//! Everything here comes from a plain parse of a single module, so it is exactly
//! what the author wrote: the declaration kinds, their byte ranges, their `pub`
//! markers, their claims, and their `-- |` doc comments. Nothing here knows about
//! content hashes or types; the addressing layer joins those on afterwards
//! (`super::build`), keyed by module and name.
//!
//! Parsing per module rather than reading the merged whole-program AST is
//! deliberate: name resolution inlines imported modules into one `Program` whose
//! spans no longer index any single file, and a viewer needs ranges it can slice
//! out of the source it is displaying.

use crate::docs::extract::{extract, Docs};
use crate::error::Error;
use crate::parse::{parse, ParseResult};
use crate::syntax::ast::{Decl as AstDecl, Fip, Program, Span as AstSpan, Total};

use super::{Claim, Kind, Span, Vis};

/// One declaration as its own module describes it, before it is addressed.
pub(super) struct Decl {
    pub name: String,
    pub kind: Kind,
    pub span: Span,
    pub vis: Vis,
    pub claims: Vec<Claim>,
    pub doc: Option<String>,
    pub deprecated: Option<String>,
}

/// One module's surface: its own description and its declarations in source order.
pub(super) struct Module {
    pub doc: Option<String>,
    pub decls: Vec<Decl>,
}

/// Parse `source` and collect every top-level declaration it makes.
///
/// `prelude` marks the module whose declarations enter unqualified global scope.
/// It carries no `pub` markers because it needs none, so treating its
/// declarations as private would be a rendering lie; they are reported public.
///
/// # Errors
/// Fails if the module does not parse.
pub(super) fn walk(source: &str, prelude: bool) -> Result<Module, Error> {
    let ParseResult { program, trivia } = parse(source)?;
    let docs = extract(&trivia, &starts(&program));
    let mut decls = Vec::new();
    collect(&program, prelude, &docs, &mut decls);
    // Source order: a viewer renders a module top to bottom, and doc-comment
    // association already relies on this order upstream.
    decls.sort_by_key(|d| d.span.start);
    Ok(Module {
        doc: docs.module.clone(),
        decls,
    })
}

// Every top-level declaration start in the module, sorted.
//
// This must list *every* item kind, including ones the index does not itself
// emit (imports, canonical designations): doc-comment association bounds each
// block by the previous declaration's start, so an omitted item would let a
// comment written inside it leak onto the next declaration.
fn starts(p: &Program) -> Vec<usize> {
    let mut s: Vec<usize> = Vec::new();
    s.extend(p.imports.iter().map(|i| i.span.start));
    s.extend(p.types.iter().map(|d| d.span.start));
    s.extend(p.effects.iter().map(|d| d.span.start));
    s.extend(p.errors.iter().map(|d| d.span.start));
    s.extend(p.aliases.iter().map(|d| d.span.start));
    s.extend(p.synonyms.iter().map(|d| d.span.start));
    s.extend(p.classes.iter().map(|d| d.span.start));
    s.extend(p.instances.iter().map(|d| d.span.start));
    s.extend(p.canonicals.iter().map(|d| d.span.start));
    s.extend(p.patterns.iter().map(|d| d.span.start));
    s.extend(p.stable.iter().map(|d| d.span.start));
    s.extend(p.fns.iter().map(|d| d.span.start));
    s.extend(p.logic_fns.iter().map(|d| d.span.start));
    s.sort_unstable();
    s.dedup();
    s
}

// Collect one record per top-level declaration, in a single flat pass over the
// `Program`'s per-kind vectors.
fn collect(p: &Program, prelude: bool, docs: &Docs, out: &mut Vec<Decl>) {
    // (name, kind, span, claims) for every declaration, gathered first so that
    // building the records below is one uniform step. The shape of this list is
    // the shape of the AST: a new declaration kind shows up here as a missing
    // line rather than as a silently unindexed definition.
    let mut items: Vec<(&str, Kind, AstSpan, Vec<Claim>)> = Vec::new();
    for d in &p.types {
        items.push((&d.name, Kind::Type, d.span, Vec::new()));
    }
    for d in &p.synonyms {
        items.push((&d.name, Kind::Synonym, d.span, Vec::new()));
    }
    for d in &p.aliases {
        items.push((&d.name, Kind::RowAlias, d.span, Vec::new()));
    }
    for d in &p.effects {
        items.push((&d.name, Kind::Effect, d.span, Vec::new()));
    }
    for d in &p.errors {
        items.push((&d.name, Kind::Error, d.span, Vec::new()));
    }
    for d in &p.classes {
        items.push((&d.name, Kind::Class, d.span, Vec::new()));
    }
    for d in &p.stable {
        items.push((&d.name, Kind::Stable, d.span, Vec::new()));
    }
    for d in &p.patterns {
        items.push((&d.name, Kind::Pattern, d.span, Vec::new()));
    }
    for d in &p.instances {
        items.push((&d.name, Kind::Instance, d.span, Vec::new()));
    }
    for d in &p.fns {
        items.push((&d.name, term_kind(d), d.span, claims_of(d)));
    }
    for d in &p.logic_fns {
        items.push((&d.name, Kind::Logic, d.span, claims_of(d)));
    }

    for (name, kind, span, claims) in items {
        out.push(Decl {
            name: name.to_string(),
            kind,
            span: Span {
                start: span.start,
                end: span.end,
            },
            vis: vis_of(p, prelude, name, kind),
            claims,
            doc: docs.get(span.start).map(str::to_string),
            deprecated: p.deprecated.get(name).cloned(),
        });
    }
}

// A declaration's visibility outside its module.
//
// An instance is always public: it has no `pub` marker because visibility would
// be meaningless for it (coherence is program-wide). The prelude likewise carries
// no markers because its names are global already, so reporting its declarations
// private would be a rendering lie.
fn vis_of(p: &Program, prelude: bool, name: &str, kind: Kind) -> Vis {
    if kind == Kind::Instance || prelude {
        Vis::Public
    } else if p.opaques.contains(name) {
        Vis::Opaque
    } else if p.exports.contains(name) {
        Vis::Public
    } else {
        Vis::Private
    }
}

// Which flavor of term a `fn` declaration is. `test` wins over `konst` because a
// `test fn` is never a constant; the two flags cannot both be set.
const fn term_kind(d: &AstDecl) -> Kind {
    if d.test {
        Kind::Test
    } else if d.konst {
        Kind::Const
    } else {
        Kind::Value
    }
}

// The checked claims a term declaration carries. Each is erased before executable
// Core, so none of them moves the definition's behavior hash; they belong on the
// definition as reviewer-facing facts.
fn claims_of(d: &AstDecl) -> Vec<Claim> {
    let mut claims = Vec::new();
    match d.total {
        Total::No => {}
        Total::Prove => claims.push(Claim::Total),
        Total::Assume => claims.push(Claim::AssumeTotal),
    }
    match d.fip {
        Fip::No => {}
        Fip::Fbip(_) => claims.push(Claim::Fbip),
        Fip::Fip(_) => claims.push(Claim::Fip),
    }
    if d.replayable {
        claims.push(Claim::Replayable);
    }
    if d.no_alloc {
        claims.push(Claim::NoAlloc);
    }
    if d.bounded_stack {
        claims.push(Claim::BoundedStack);
    }
    if d.linear {
        claims.push(Claim::Linear);
    }
    if !d.requires.is_empty() || !d.ensures.is_empty() {
        claims.push(Claim::Contract);
    }
    claims
}
