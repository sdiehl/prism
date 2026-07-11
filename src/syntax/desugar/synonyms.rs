//! Type synonym expansion.

use std::collections::BTreeMap;

use marginalia::Span;

use crate::error::{ErrKind, TypeError};
use crate::syntax::ast::{Decl, Program, Ty};

// Type synonyms are purely syntactic: each names a parameterized type and is
// expanded (with its arguments substituted for its parameters) here, before
// checking, so the typechecker only ever sees the underlying types. Bodies are
// resolved transitively first, with a cycle check, then every type position in
// the program is rewritten against the resolved table.
type SynMap = BTreeMap<String, (Vec<String>, Ty, Span)>;

pub(super) fn expand_synonyms(prog: &mut Program) -> Result<(), TypeError> {
    if prog.synonyms.is_empty() {
        return Ok(());
    }
    let mut map = SynMap::new();
    let names: Vec<String> = prog.synonyms.iter().map(|s| s.name.clone()).collect();
    for n in &names {
        resolve_synonym(n, prog, &mut map, &mut Vec::new())?;
    }
    for d in &mut prog.fns {
        apply_syn_decl(d, &map)?;
    }
    for c in &mut prog.classes {
        for (_, t) in &mut c.methods {
            apply_syn(t, &map)?;
        }
    }
    for i in &mut prog.instances {
        apply_syn(&mut i.head, &map)?;
        for c in &mut i.context {
            apply_syn(&mut c.ty, &map)?;
        }
        for m in &mut i.methods {
            apply_syn_decl(m, &map)?;
        }
    }
    for ty in &mut prog.types {
        for c in &mut ty.ctors {
            for a in &mut c.args {
                apply_syn(a, &map)?;
            }
            if let Some(fs) = &mut c.fields {
                for (_, ft) in fs {
                    apply_syn(ft, &map)?;
                }
            }
        }
    }
    for e in &mut prog.effects {
        for op in &mut e.ops {
            for p in &mut op.params {
                apply_syn(p, &map)?;
            }
            apply_syn(&mut op.ret, &map)?;
        }
    }
    Ok(())
}

// Resolve one synonym's body to a fully expanded type, recursing through nested
// synonyms and detecting cycles along `path`.
fn resolve_synonym(
    name: &str,
    prog: &Program,
    map: &mut SynMap,
    path: &mut Vec<String>,
) -> Result<(Vec<String>, Ty), TypeError> {
    if let Some((ps, t, _)) = map.get(name) {
        return Ok((ps.clone(), t.clone()));
    }
    let s = prog
        .synonyms
        .iter()
        .find(|s| s.name == name)
        .ok_or_else(|| ErrKind::UnknownSynonym { name: name.into() }.at(Span::empty(0)))?;
    if path.iter().any(|p| p == name) {
        return Err(ErrKind::DefCycle {
            kind: "type synonym".into(),
            path: format!("{} -> {name}", path.join(" -> ")),
        }
        .at(s.span));
    }
    path.push(name.into());
    let mut body = s.ty.clone();
    expand_syn_ty(&mut body, prog, map, path)?;
    path.pop();
    map.insert(name.into(), (s.params.clone(), body.clone(), s.span));
    Ok((s.params.clone(), body))
}

// Expand synonyms inside `t` during table construction (may resolve as-yet
// unseen synonyms via `resolve_synonym`).
fn expand_syn_ty(
    t: &mut Ty,
    prog: &Program,
    map: &mut SynMap,
    path: &mut Vec<String>,
) -> Result<(), TypeError> {
    // Only `Con` is node-specific (its head may name a synonym to expand); every
    // other variant just recurses into its children, so route the whole rest
    // through the structural spine and stay total as `Ty` grows.
    if let Ty::Con(name, args) = t {
        for a in args.iter_mut() {
            expand_syn_ty(a, prog, map, path)?;
        }
        if prog.synonyms.iter().any(|s| &s.name == name) {
            let (params, body) = resolve_synonym(name, prog, map, path)?;
            check_arity(name, params.len(), args.len(), prog)?;
            let sub = params.into_iter().zip(args.iter().cloned()).collect();
            *t = subst_ty(&body, &sub);
        }
        return Ok(());
    }
    t.try_each_child_mut(&mut |c| expand_syn_ty(c, prog, map, path))
}

// Rewrite `t` against the completed synonym table.
fn apply_syn(t: &mut Ty, map: &SynMap) -> Result<(), TypeError> {
    // As in `expand_syn_ty`, only `Con` is node-specific; the rest recurse through
    // the structural spine so a new `Ty` variant cannot be silently skipped.
    if let Ty::Con(name, args) = t {
        for a in args.iter_mut() {
            apply_syn(a, map)?;
        }
        if let Some((params, body, span)) = map.get(name) {
            if params.len() != args.len() {
                return Err(ErrKind::SynonymArity {
                    name: name.clone(),
                    want: params.len(),
                    got: args.len(),
                }
                .at(*span));
            }
            let sub = params.iter().cloned().zip(args.iter().cloned()).collect();
            *t = subst_ty(body, &sub);
        }
        return Ok(());
    }
    t.try_each_child_mut(&mut |c| apply_syn(c, map))
}

fn apply_syn_decl(d: &mut Decl, map: &SynMap) -> Result<(), TypeError> {
    for p in &mut d.params {
        if let Some(t) = &mut p.ty {
            apply_syn(t, map)?;
        }
    }
    if let Some(t) = &mut d.ret {
        apply_syn(t, map)?;
    }
    for c in &mut d.constraints {
        apply_syn(&mut c.ty, map)?;
    }
    Ok(())
}

fn check_arity(name: &str, want: usize, got: usize, prog: &Program) -> Result<(), TypeError> {
    if want == got {
        return Ok(());
    }
    let span = prog
        .synonyms
        .iter()
        .find(|s| s.name == name)
        .map_or_else(|| Span::empty(0), |s| s.span);
    Err(ErrKind::SynonymArity {
        name: name.into(),
        want,
        got,
    }
    .at(span))
}

// Substitute synonym parameters with their arguments in an expanded body.
fn subst_ty(t: &Ty, sub: &BTreeMap<String, Ty>) -> Ty {
    match t {
        Ty::Var(n) => sub.get(n).cloned().unwrap_or_else(|| t.clone()),
        // A higher-kinded application `f(a)`: the head may itself be a synonym
        // parameter, so substitute it, distributing over the head's arg list when
        // the argument is another application/constructor.
        Ty::App(n, args) => {
            let args: Vec<Ty> = args.iter().map(|a| subst_ty(a, sub)).collect();
            match sub.get(n) {
                Some(Ty::Var(h)) => Ty::App(h.clone(), args),
                Some(Ty::Con(h, hargs)) => {
                    Ty::Con(h.clone(), hargs.iter().cloned().chain(args).collect())
                }
                Some(Ty::App(h, hargs)) => {
                    Ty::App(h.clone(), hargs.iter().cloned().chain(args).collect())
                }
                _ => Ty::App(n.clone(), args),
            }
        }
        Ty::Forall(vs, b) => {
            let mut s2 = sub.clone();
            for v in vs {
                s2.remove(v);
            }
            Ty::Forall(vs.clone(), Box::new(subst_ty(b, &s2)))
        }
        // Con / Tuple / Fun / RowLit / leaves: no node-specific rewrite, so recurse
        // into every child (including row-label argument types) through the spine.
        other => {
            let mut out = other.clone();
            out.each_child_mut(&mut |c| *c = subst_ty(c, sub));
            out
        }
    }
}
