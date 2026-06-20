//! Row alias expansion.

use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use crate::error::TypeError;
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
    known.extend(["IO".into(), "Exn".into()]);
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
        .ok_or_else(|| TypeError::Other {
            span: Span::empty(0),
            msg: format!("unknown effect alias `{name}`"),
        })?;
    if path.iter().any(|p| p == name) {
        return Err(TypeError::Other {
            span: a.span,
            msg: format!("effect alias cycle: {} -> {name}", path.join(" -> ")),
        });
    }
    path.push(name.into());
    let mut out: Vec<EffLabel> = Vec::new();
    for l in &a.labels {
        let exp = if l.args.is_empty() && prog.aliases.iter().any(|b| b.name == l.name) {
            resolve_alias(&l.name, prog, known, map, path)?
        } else if known.contains(&l.name) {
            vec![l.clone()]
        } else {
            return Err(TypeError::Other {
                span: a.span,
                msg: format!("unknown effect `{}` in alias `{name}`", l.name),
            });
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
    match t {
        Ty::Fun(args, row, ret) => {
            for a in args {
                expand_ty(a, map);
            }
            if let Row::Cons(ls, _) = row {
                expand_labels(ls, map);
            }
            expand_ty(ret, map);
        }
        Ty::Forall(_, b) => expand_ty(b, map),
        Ty::Con(_, args) | Ty::Tuple(args) => {
            for a in args {
                expand_ty(a, map);
            }
        }
        _ => {}
    }
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
