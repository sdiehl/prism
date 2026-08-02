//! Hover types for the names inside a definition.
//!
//! A reader looking at `fn row(gap : Int, children : List(Pict))` wants to know
//! what `gap` is where it is *used*, not only where it is declared, and the
//! signature two lines up answers that only for the simplest bodies. The
//! typechecker already knows: it stamps every expression node with an identity and
//! records the zonked type against it, which is what `prism dump typespans` and
//! the book's typed tooltips read.
//!
//! This joins the same two tables — a node's span from the AST, its type from the
//! checked facts — for every module rather than only the entry one, and rebases
//! the spans onto each definition's own source. It costs no extra pass: the index's
//! own elaboration asks for the type strings (`FrontRequest::IdentityTooltips`),
//! which only fills side tables, so the Core every address is taken over is
//! byte-identical to the one without them.
//!
//! Names only, deliberately: the variables a body mentions and the binders a
//! pattern introduces. Every subterm has a type, and emitting all of them would
//! multiply the payload and nest spans inside each other — the whole
//! `Row(gap, children)` contains `gap` — while a reader hovering a body is asking
//! about the names in it. Names also cannot overlap, which keeps the consumer's
//! painting a flat merge of intervals rather than a tree.
//!
//! A pattern binder costs one thing extra. `y` in `Cons(y, rest)` is a `Pattern`,
//! not an expression, and identity is what the type tables are keyed by — so
//! `desugar::ids` stamps arm patterns alongside the expressions around them, and
//! `check_pat` records each binder's type where it already computes it. Over the
//! standard library that is 1,786 further names for 14 kB, the payload growing far
//! more slowly than the span count because a binder's type is nearly always one
//! the table already holds.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::driver::AddressableSurface;
use crate::syntax::ast::{Core, Expr, Pattern, S};
use crate::types::Type;

use super::Def;

/// One name, and the type the checker gave it.
struct Typed {
    start: usize,
    end: usize,
    rendered: String,
}

/// A declaration's parameters and the domains of its checked type.
type Header<'a> = (Vec<&'a str>, Vec<&'a Type>);

/// Attach every definition's hover types, returning the table they index.
///
/// Interned because the same type is written over and over — a handful of distinct
/// types account for most occurrences — and a rendered `forall` repeated a thousand
/// times would be most of what the payload weighs.
pub(super) fn attach_types(defs: &mut [Def], production: &AddressableSurface) -> Vec<String> {
    let hir = crate::hir::build(&production.checked);
    let checked: BTreeMap<&str, &Type> = production
        .checked
        .decls
        .iter()
        .map(|d| (d.name.as_str(), &d.ty))
        .collect();

    // Collected per declaration, since a span is an offset into whichever file that
    // declaration was written in and only its owner knows how to rebase it.
    let mut found: BTreeMap<&str, Vec<Typed>> = BTreeMap::new();
    let mut headers: BTreeMap<&str, Header<'_>> = BTreeMap::new();
    for decl in &production.program.fns {
        let mut out = Vec::new();
        variables(&decl.body, &hir, &mut out);
        rebase_onto(&mut out, decl.span.start);
        if !out.is_empty() {
            found.entry(decl.name.as_str()).or_default().extend(out);
        }
        if let Some(Type::Fun(doms, _, _)) = checked.get(decl.name.as_str()).copied().map(bare) {
            headers.insert(
                decl.name.as_str(),
                (
                    decl.params.iter().map(|p| p.name.as_str()).collect(),
                    doms.iter().collect(),
                ),
            );
        }
    }
    // An instance's methods are lifted to their own top-level functions later; here
    // they are still inside the instance, which is the definition a reader has open.
    for inst in &production.program.instances {
        let mut out = Vec::new();
        for method in &inst.methods {
            variables(&method.body, &hir, &mut out);
        }
        rebase_onto(&mut out, inst.span.start);
        if !out.is_empty() {
            found.entry(inst.name.as_str()).or_default().extend(out);
        }
    }

    let mut table: Vec<String> = Vec::new();
    for def in defs.iter_mut() {
        let mut spans: Vec<Typed> = found
            .get(def.id.as_str())
            .into_iter()
            .flatten()
            .filter_map(|t| rebase(t, def))
            .collect();
        spans.extend(header_names(def, headers.get(def.id.as_str())));
        def.types = pack(spans, &mut table);
    }
    table
}

/// A declaration's scheme with its quantifiers stripped, so a polymorphic function
/// yields the same arrow a monomorphic one does. The variables inside are the
/// generalized ones a reader sees in the signature.
fn bare(ty: &Type) -> &Type {
    match ty {
        Type::Forall(_, inner) | Type::RowForall(_, inner) => bare(inner),
        other => other,
    }
}

/// Every variable in an expression tree, with the type the checker synthesized.
fn variables(e: &S<Expr<Core>>, hir: &crate::hir::CheckedHir<'_>, out: &mut Vec<Typed>) {
    if matches!(e.node, Expr::Var(_)) {
        // The presentable string, not the raw node type. The latter still carries
        // the checker's own inference variables, which are unreadable and, since
        // every definition numbers them afresh, defeat interning entirely: dropping
        // the filter below takes the standard library's table from 2036 entries to
        // 2758. The fallback is the node's own term, and only when that resolved to
        // something readable, since an unsolved existential prints as `?846`, which
        // is worse than silence.
        //
        // An argument was long assumed to be missing here, on the reasoning that it
        // is checked against its parameter rather than synthesized. It is not: a
        // call reconciles head and arguments by unification, so both carry a type,
        // and pushing the checked type from `check` was measured against the whole
        // standard library and produced zero additional spans. What made the gap
        // look real was a coordinate bug in `rebase_onto`, which dropped every body
        // span whenever a prelude had been prepended.
        out.extend(typed_at(e.id, e.span, hir));
    }
    // Patterns are not expressions, so the structural walk does not reach them.
    if let Expr::Match(_, arms) = &e.node {
        for arm in arms {
            binders(&arm.pat, hir, out);
        }
    }
    e.node.each_child(&mut |child| variables(child, hir, out));
}

/// Every name a pattern binds, with the type the checker gave the binding site.
///
/// Only `Var` carries a name a reader can hover; the rest are structure, walked
/// through to reach the binders nested inside them.
fn binders(p: &S<Pattern>, hir: &crate::hir::CheckedHir<'_>, out: &mut Vec<Typed>) {
    if matches!(p.node, Pattern::Var(_)) {
        out.extend(typed_at(p.id, p.span, hir));
    }
    p.node.each_child(&mut |sub| binders(sub, hir, out));
}

/// The type to show for one node, if the checker left a presentable one.
fn typed_at(
    id: crate::syntax::ast::NodeId,
    span: marginalia::Span,
    hir: &crate::hir::CheckedHir<'_>,
) -> Option<Typed> {
    let rendered = hir.tooltip(id).map(ToString::to_string).or_else(|| {
        // A binder reaches only this fallback: the canonical string is built per
        // expression node from its effect row, and a binding site has neither.
        hir.node_type(id)
            .map(Type::show)
            .filter(|t| !t.contains('?'))
    })?;
    Some(Typed {
        start: span.start,
        end: span.end,
        rendered,
    })
}

// Move a declaration's spans onto the declaration itself, subtracting where the
// compiler placed it rather than where the index did.
//
// The two are not the same coordinate, and this is the whole difficulty. A body
// node is reported at its position in the compiled source, which begins with the
// prelude; the index holds the declaration at its position in its own file. The
// difference between a node and its owner is the same in either, so subtracting
// the owner here yields an offset both agree on — the same bargain `attach_refs`
// makes, and it has to be made in the same coordinate system the spans came from.
// Subtracting the index's own `Def::span` instead silently drops every body type
// whenever a prelude was prepended, which is every single-file index.
fn rebase_onto(spans: &mut Vec<Typed>, owner: usize) {
    spans.retain_mut(|t| {
        let (Some(start), Some(end)) = (t.start.checked_sub(owner), t.end.checked_sub(owner))
        else {
            return false;
        };
        t.start = start;
        t.end = end;
        true
    });
}

// A span that does not land inside the text it claims to be in is dropped rather
// than emitted: the two then came from different parses, and a tooltip at a wrong
// offset is worse than a missing one.
fn rebase(t: &Typed, def: &Def) -> Option<Typed> {
    (t.end <= def.source.len() && t.start < t.end).then(|| Typed {
        start: t.start,
        end: t.end,
        rendered: t.rendered.clone(),
    })
}

/// The parameters at their binding site, which have no node of their own.
///
/// These are rendered from the declaration's generalized scheme, so they use the
/// same variable names as the signature above them. A body node agrees with them
/// because the checker now renders every span of a declaration under that same
/// scheme (`generalize_seeded`) rather than canonicalizing each node on its own:
/// `map`'s `xs` read `List(b)` here and `List(a)` two lines down until it did.
///
/// A parameter is not an expression, so it carries neither an identity nor a span,
/// and the header is exactly where a reader looks first. The names come from the
/// declaration and their types from the domains of its checked type, so only the
/// position is recovered from the text — the same bargain the member list makes,
/// and safe for the same reason: only a token equal to a name this declaration
/// actually binds is considered.
fn header_names(def: &Def, header: Option<&Header<'_>>) -> Vec<Typed> {
    let Some((names, doms)) = header else {
        return Vec::new();
    };
    let Ok((tokens, _)) = crate::lex::lex_raw(&def.source) else {
        return Vec::new();
    };
    // Bounded to the header: a parameter used again in the body is the expression
    // walk's business, and it has an exact span there.
    let body = tokens
        .iter()
        .position(|(_, t, _)| matches!(t, crate::lex::Token::Eq))
        .unwrap_or(tokens.len());
    let mut out = Vec::new();
    for (name, dom) in names.iter().zip(doms) {
        let found = tokens[..body].iter().find(|(start, token, end)| {
            matches!(token, crate::lex::Token::Ident(t) if t == name)
                && def.source.get(*start..*end) == Some(*name)
        });
        if let Some(&(start, _, end)) = found {
            out.push(Typed {
                start,
                end,
                rendered: dom.show(),
            });
        }
    }
    out
}

/// Pack one definition's spans as `gap length index` triples over its own source,
/// the same encoding the highlight spans use.
fn pack(mut spans: Vec<Typed>, table: &mut Vec<String>) -> String {
    spans.sort_unstable_by_key(|t| (t.start, t.end));
    let mut flat = String::new();
    let mut prev = 0usize;
    for t in spans {
        // A name cannot contain another name; anything overlapping came from a
        // different parse, so it is dropped rather than emitted at a wrong offset.
        if t.start < prev {
            continue;
        }
        let index = table
            .iter()
            .position(|entry| *entry == t.rendered)
            .unwrap_or_else(|| {
                table.push(t.rendered);
                table.len() - 1
            });
        if !flat.is_empty() {
            flat.push(' ');
        }
        let _ = write!(flat, "{} {} {index}", t.start - prev, t.end - t.start);
        prev = t.end;
    }
    flat
}
