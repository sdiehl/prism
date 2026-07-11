//! Row alias expansion.

use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use crate::error::{ErrKind, TypeError};
use crate::names;
use crate::syntax::ast::{Decl, EffLabel, Program, Row, Ty};

type AliasMap = BTreeMap<String, Vec<EffLabel>>;

// Row aliases are purely syntactic: each alias names a label set and expands
// transitively here, before checking, so the row machinery only sees real
// labels. The source (and the formatter) keep the alias name.
pub(super) fn expand_aliases(prog: &mut Program) -> Result<(), TypeError> {
    if prog.aliases.is_empty() {
        return Ok(());
    }
    let mut known: BTreeSet<String> = prog.effects.iter().map(|e| e.name.clone()).collect();
    known.extend([names::IO_EFFECT.into(), names::EXN_EFFECT.into()]);
    let mut map = AliasMap::new();
    for a in &prog.aliases {
        resolve_alias(&a.name, prog, &known, &mut map, &mut Vec::new())?;
    }
    for d in &mut prog.fns {
        expand_decl(d, &map);
    }
    for c in &mut prog.classes {
        for (_, t) in &mut c.methods {
            expand_ty(t, &map);
        }
    }
    for i in &mut prog.instances {
        expand_ty(&mut i.head, &map);
        for c in &mut i.context {
            expand_ty(&mut c.ty, &map);
        }
        for m in &mut i.methods {
            expand_decl(m, &map);
        }
    }
    for t in &mut prog.types {
        for c in &mut t.ctors {
            for a in &mut c.args {
                expand_ty(a, &map);
            }
            if let Some(fs) = &mut c.fields {
                for (_, ft) in fs {
                    expand_ty(ft, &map);
                }
            }
        }
    }
    for e in &mut prog.effects {
        for op in &mut e.ops {
            for p in &mut op.params {
                expand_ty(p, &map);
            }
            expand_ty(&mut op.ret, &map);
        }
    }
    Ok(())
}

fn resolve_alias(
    name: &str,
    prog: &Program,
    known: &BTreeSet<String>,
    map: &mut AliasMap,
    path: &mut Vec<String>,
) -> Result<Vec<EffLabel>, TypeError> {
    if let Some(ls) = map.get(name) {
        return Ok(ls.clone());
    }
    let a = prog
        .aliases
        .iter()
        .find(|a| a.name == name)
        .ok_or_else(|| ErrKind::UnknownAlias { name: name.into() }.at(Span::empty(0)))?;
    if path.iter().any(|p| p == name) {
        return Err(ErrKind::DefCycle {
            kind: "effect alias".into(),
            path: format!("{} -> {name}", path.join(" -> ")),
        }
        .at(a.span));
    }
    path.push(name.into());
    let mut out: Vec<EffLabel> = Vec::new();
    for l in &a.labels {
        let exp = if l.args.is_empty() && prog.aliases.iter().any(|b| b.name == l.name) {
            resolve_alias(&l.name, prog, known, map, path)?
        } else if known.contains(&l.name) {
            vec![l.clone()]
        } else {
            return Err(ErrKind::UnknownEffectInAlias {
                eff: l.name.clone(),
                alias: name.into(),
            }
            .at(a.span));
        };
        for x in exp {
            if !out.contains(&x) {
                out.push(x);
            }
        }
    }
    path.pop();
    map.insert(name.into(), out.clone());
    Ok(out)
}

fn expand_labels(ls: &mut Vec<EffLabel>, map: &AliasMap) {
    let mut out: Vec<EffLabel> = Vec::new();
    for l in ls.drain(..) {
        let exp = if l.args.is_empty() {
            map.get(&l.name).cloned().unwrap_or_else(|| vec![l])
        } else {
            vec![l]
        };
        for x in exp {
            if !out.contains(&x) {
                out.push(x);
            }
        }
    }
    *ls = out;
}

fn expand_ty(t: &mut Ty, map: &AliasMap) {
    // The node-specific work is expanding a row's label aliases, wherever a row
    // appears (a function's effect row, or a `{ MyAlias, .. }` `Row`-kinded
    // argument). Everything structural then recurses through the spine, so no
    // type position (including a label's own type arguments) is missed.
    match t {
        Ty::Fun(_, Row::Cons(ls, _), _) | Ty::RowLit(Row::Cons(ls, _)) => expand_labels(ls, map),
        _ => {}
    }
    t.each_child_mut(&mut |c| expand_ty(c, map));
}

fn expand_decl(d: &mut Decl, map: &AliasMap) {
    if let Some(effs) = &mut d.eff {
        expand_labels(effs, map);
    }
    for p in &mut d.params {
        if let Some(t) = &mut p.ty {
            expand_ty(t, map);
        }
    }
    if let Some(t) = &mut d.ret {
        expand_ty(t, map);
    }
    for c in &mut d.constraints {
        expand_ty(&mut c.ty, map);
    }
}
