//! Type synonym expansion.

use std::collections::BTreeMap;

use marginalia::Span;

use crate::error::TypeError;
use crate::syntax::ast::{Decl, EffLabel, Program, Row, Ty};

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
        .ok_or_else(|| TypeError::Other {
            span: Span::empty(0),
            msg: format!("unknown type synonym `{name}`"),
        })?;
    if path.iter().any(|p| p == name) {
        return Err(TypeError::Other {
            span: s.span,
            msg: format!("type synonym cycle: {} -> {name}", path.join(" -> ")),
        });
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
    match t {
        Ty::Fun(args, row, ret) => {
            for a in args {
                expand_syn_ty(a, prog, map, path)?;
            }
            if let Row::Cons(ls, _) = row {
                for l in ls {
                    for a in &mut l.args {
                        expand_syn_ty(a, prog, map, path)?;
                    }
                }
            }
            expand_syn_ty(ret, prog, map, path)?;
        }
        Ty::Forall(_, b) => expand_syn_ty(b, prog, map, path)?,
        Ty::Tuple(items) => {
            for i in items {
                expand_syn_ty(i, prog, map, path)?;
            }
        }
        Ty::Con(name, args) => {
            for a in args.iter_mut() {
                expand_syn_ty(a, prog, map, path)?;
            }
            if prog.synonyms.iter().any(|s| &s.name == name) {
                let (params, body) = resolve_synonym(name, prog, map, path)?;
                check_arity(name, params.len(), args.len(), prog)?;
                let sub = params.into_iter().zip(args.iter().cloned()).collect();
                *t = subst_ty(&body, &sub);
            }
        }
        _ => {}
    }
    Ok(())
}

// Rewrite `t` against the completed synonym table.
fn apply_syn(t: &mut Ty, map: &SynMap) -> Result<(), TypeError> {
    match t {
        Ty::Fun(args, row, ret) => {
            for a in args {
                apply_syn(a, map)?;
            }
            if let Row::Cons(ls, _) = row {
                for l in ls {
                    for a in &mut l.args {
                        apply_syn(a, map)?;
                    }
                }
            }
            apply_syn(ret, map)?;
        }
        Ty::Forall(_, b) => apply_syn(b, map)?,
        Ty::Tuple(items) => {
            for i in items {
                apply_syn(i, map)?;
            }
        }
        Ty::Con(name, args) => {
            for a in args.iter_mut() {
                apply_syn(a, map)?;
            }
            if let Some((params, body, span)) = map.get(name) {
                if params.len() != args.len() {
                    return Err(TypeError::Other {
                        span: *span,
                        msg: format!(
                            "type synonym `{name}` expects {} argument(s), got {}",
                            params.len(),
                            args.len()
                        ),
                    });
                }
                let sub = params.iter().cloned().zip(args.iter().cloned()).collect();
                *t = subst_ty(body, &sub);
            }
        }
        _ => {}
    }
    Ok(())
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
    Err(TypeError::Other {
        span,
        msg: format!("type synonym `{name}` expects {want} argument(s), got {got}"),
    })
}

// Substitute synonym parameters with their arguments in an expanded body.
fn subst_ty(t: &Ty, sub: &BTreeMap<String, Ty>) -> Ty {
    match t {
        Ty::Var(n) => sub.get(n).cloned().unwrap_or_else(|| t.clone()),
        Ty::Con(n, args) => Ty::Con(n.clone(), args.iter().map(|a| subst_ty(a, sub)).collect()),
        Ty::Tuple(xs) => Ty::Tuple(xs.iter().map(|x| subst_ty(x, sub)).collect()),
        Ty::Fun(args, row, ret) => Ty::Fun(
            args.iter().map(|a| subst_ty(a, sub)).collect(),
            subst_row(row, sub),
            Box::new(subst_ty(ret, sub)),
        ),
        Ty::Forall(vs, b) => {
            let mut s2 = sub.clone();
            for v in vs {
                s2.remove(v);
            }
            Ty::Forall(vs.clone(), Box::new(subst_ty(b, &s2)))
        }
        _ => t.clone(),
    }
}

fn subst_row(row: &Row, sub: &BTreeMap<String, Ty>) -> Row {
    match row {
        Row::Empty => Row::Empty,
        Row::Cons(ls, tail) => Row::Cons(
            ls.iter()
                .map(|l| EffLabel {
                    name: l.name.clone(),
                    args: l.args.iter().map(|a| subst_ty(a, sub)).collect(),
                })
                .collect(),
            tail.clone(),
        ),
    }
}
