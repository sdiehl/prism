//! Hover types for the names inside a definition.
//!
//! The typechecker records a zonked type for each expression identity. This
//! module maps those types to the names in each definition's source.
//!
//! Spans come from the AST and types from checked facts. The index requests these
//! side tables with `FrontRequest::IdentityTooltips`; Core remains unchanged.
//!
//! Only variable uses and pattern binders are emitted. Their spans do not
//! overlap, so consumers can merge them as flat intervals.
//!
//! Pattern binders receive identities in `desugar::ids`; `check_pat` records
//! their types.

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
/// Types are interned because many occurrences share the same rendering.
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
        // Prefer the presentable tooltip over the raw node type, which may contain
        // unstable inference variables. The fallback omits unsolved existentials.
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

// Rebase compiler-source spans onto the declaration. Compiler coordinates include
// the prepended prelude, while index coordinates refer to the module file.
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
/// Types come from the generalized scheme, and positions are recovered from the
/// declaration text because parameters have no expression identity or span.
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
