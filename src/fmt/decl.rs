//! Top-level declaration formatting: imports, effects, classes, instances,
//! data and pattern declarations, type/row/param rendering, and the function
//! definition printer. The expression and statement printers live in the
//! parent module; this layer calls back into them through `super::`.

use super::{
    fmt_block, fmt_expr, fmt_expr_break, fmt_expr_inline, forces_break, has_comments,
    is_trailing_call, Mode, INDENT, LINE_WIDTH,
};
use crate::syntax::ast::{
    ClassDecl, Constraint, Ctor, DataDecl, Decl, EffLabel, EffectDecl, Expr, Fip, ImportDecl,
    InstanceDecl, Param, PatternDecl, Row, Ty, S,
};

pub(super) fn fmt_import(i: &ImportDecl) -> String {
    use std::fmt::Write as _;
    let mut s = format!("import {}", i.path.join("."));
    if let Some(a) = &i.alias {
        write!(s, " as {a}").unwrap();
    }
    if let Some(names) = &i.names {
        write!(s, " ({})", names.join(", ")).unwrap();
    }
    s
}

pub(super) fn fmt_effect(e: &EffectDecl) -> String {
    let ops: Vec<String> = e
        .ops
        .iter()
        .map(|op| {
            let params: Vec<String> = op.params.iter().map(fmt_ty).collect();
            format!(
                "  ctl {}({}) : {}",
                op.name,
                params.join(", "),
                fmt_ty(&op.ret)
            )
        })
        .collect();
    let params = if e.params.is_empty() {
        String::new()
    } else {
        format!("({})", e.params.join(", "))
    };
    format!("effect {}{} {{\n{}\n}}", e.name, params, ops.join(",\n"))
}

pub(super) fn fmt_label(l: &EffLabel) -> String {
    if l.args.is_empty() {
        l.name.clone()
    } else {
        let args: Vec<String> = l.args.iter().map(fmt_ty).collect();
        format!("{}({})", l.name, args.join(", "))
    }
}

pub(super) fn fmt_labels(ls: &[EffLabel]) -> String {
    let parts: Vec<String> = ls.iter().map(fmt_label).collect();
    parts.join(", ")
}

pub(super) fn fmt_class(c: &ClassDecl) -> String {
    let sigs: Vec<String> = c
        .methods
        .iter()
        .map(|(n, t)| format!("  {n} : {}", fmt_ty(t)))
        .collect();
    let sup = if c.supers.is_empty() {
        String::new()
    } else {
        let parts: Vec<String> = c
            .supers
            .iter()
            .map(|s| format!("{s}({})", c.param))
            .collect();
        format!(" given {}", parts.join(", "))
    };
    format!(
        "class {}({}){sup} {{\n{}\n}}",
        c.name,
        c.param,
        sigs.join(",\n")
    )
}

pub(super) fn fmt_constraints(cs: &[Constraint]) -> String {
    let parts: Vec<String> = cs
        .iter()
        .map(|c| format!("{}({})", c.class, fmt_ty(&c.ty)))
        .collect();
    format!(" given {}", parts.join(", "))
}

pub(super) fn indent_block(s: &str) -> String {
    s.lines()
        .map(|l| {
            if l.is_empty() {
                String::new()
            } else {
                format!("{INDENT}{l}")
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

pub(super) fn fmt_instance(i: &InstanceDecl) -> String {
    let wh = if i.context.is_empty() {
        String::new()
    } else {
        fmt_constraints(&i.context)
    };
    let ms: Vec<String> = i
        .methods
        .iter()
        .map(|m| indent_block(&fmt_fn(m, Mode::Flat)))
        .collect();
    format!(
        "instance {} : {}({}){wh} {{\n{}\n}}",
        i.name,
        i.class,
        fmt_ty(&i.head),
        ms.join(",\n")
    )
}

pub(super) fn fmt_pattern_decl(p: &PatternDecl) -> String {
    let clause = |kw: &str, e: &S<Expr>| {
        let s = fmt_expr_inline(e, Mode::Flat).unwrap_or_else(|| fmt_expr_break(e, 1, Mode::Flat));
        format!("{INDENT}{kw} {s}")
    };
    let mut out = format!(
        "pattern {}({}) for {} =\n{}",
        p.name,
        p.params.join(", "),
        p.for_ty,
        clause("view", &p.view)
    );
    if let Some(mk) = &p.make {
        out.push('\n');
        out.push_str(&clause("make", mk));
    }
    out
}

pub(super) fn fmt_data(d: &DataDecl) -> String {
    let params = if d.params.is_empty() {
        String::new()
    } else {
        format!("({})", d.params.join(", "))
    };
    let ctors: Vec<String> = d.ctors.iter().map(fmt_ctor).collect();
    let der = if d.deriving.is_empty() {
        String::new()
    } else {
        let names: Vec<&str> = d.deriving.iter().map(|(n, _)| n.as_str()).collect();
        format!(" deriving ({})", names.join(", "))
    };
    let kw = if d.newtype { "newtype" } else { "type" };
    format!("{kw} {}{} = {}{der}", d.name, params, ctors.join(" | "))
}

pub(super) fn fmt_ctor(c: &Ctor) -> String {
    c.fields.as_ref().map_or_else(
        || {
            if c.args.is_empty() {
                c.name.clone()
            } else {
                let args: Vec<String> = c.args.iter().map(fmt_ty).collect();
                format!("{}({})", c.name, args.join(", "))
            }
        },
        |fields| {
            let fs: Vec<String> = fields
                .iter()
                .map(|(n, t)| format!("{n}: {}", fmt_ty(t)))
                .collect();
            format!("{} {{ {} }}", c.name, fs.join(", "))
        },
    )
}

pub(super) fn fmt_ty(t: &Ty) -> String {
    match t {
        Ty::Int => "Int".into(),
        Ty::I64 => "I64".into(),
        Ty::U64 => "U64".into(),
        Ty::Bool => "Bool".into(),
        Ty::Unit => "Unit".into(),
        Ty::Float => "Float".into(),
        Ty::Char => "Char".into(),
        Ty::Str => "String".into(),
        Ty::Var(x) => x.clone(),
        Ty::Forall(vs, t) => {
            let mut vs = vs.clone();
            let mut cur = t.as_ref();
            while let Ty::Forall(more, inner) = cur {
                vs.extend(more.iter().cloned());
                cur = inner;
            }
            format!("forall {}. {}", vs.join(" "), fmt_ty(cur))
        }
        Ty::Fun(args, row, ret) => {
            let args: Vec<String> = args.iter().map(fmt_ty).collect();
            format!("({}) -> {}{}", args.join(", "), fmt_ty(ret), fmt_row(row))
        }
        Ty::Con(name, args) if args.is_empty() => name.clone(),
        Ty::Con(name, args) => {
            let args: Vec<String> = args.iter().map(fmt_ty).collect();
            format!("{}({})", name, args.join(", "))
        }
        Ty::Tuple(ts) => {
            let ts: Vec<String> = ts.iter().map(fmt_ty).collect();
            format!("({})", ts.join(", "))
        }
        // Synthesized only by desugar and carries no span; the formatter only
        // ever sees source types. Should this marker leak this far, emit an inert
        // hole rather than fabricating identity text or aborting: a formatter
        // must never crash on or invent identity from its input.
        Ty::State(_) => "_".into(),
    }
}

pub(super) fn fmt_row(r: &Row) -> String {
    match r {
        Row::Empty => String::new(),
        Row::Cons(ls, tl) => {
            let body = match tl {
                Some(v) if ls.is_empty() => format!("| {v}"),
                Some(v) => format!("{} | {v}", fmt_labels(ls)),
                None => fmt_labels(ls),
            };
            format!(" ! {{{body}}}")
        }
    }
}

pub(super) fn fmt_param(p: &Param) -> String {
    let pre = if p.borrow { "borrow " } else { "" };
    let base = p.ty.as_ref().map_or_else(
        || format!("{pre}{}", p.name),
        |t| format!("{pre}{} : {}", p.name, fmt_ty(t)),
    );
    match &p.default {
        Some(d) => format!("{base} := {}", fmt_expr(d, 0, Mode::Flat)),
        None => base,
    }
}

pub(super) fn fmt_fn(d: &Decl, mode: Mode) -> String {
    if d.konst {
        let ann = d
            .ret
            .as_ref()
            .map_or_else(String::new, |t| format!(" : {}", fmt_ty(t)));
        let sig = format!("let {}{ann} =", d.name);
        let bodied = has_comments(d.span.start, d.body.span.end);
        if !bodied && (mode == Mode::Flat || !forces_break(&d.body)) {
            if let Some(body) = fmt_expr_inline(&d.body, mode) {
                let line = format!("{sig} {body}");
                if line.len() <= LINE_WIDTH {
                    return line;
                }
            }
        }
        return match mode {
            Mode::Layout => format!("{sig}\n{}", fmt_block(&d.body, 1, d.span.start)),
            Mode::Flat => format!(
                "{sig}\n{}{}",
                INDENT,
                fmt_expr_break(&d.body, 1, Mode::Flat)
            ),
        };
    }
    let params: Vec<String> = d.params.iter().map(fmt_param).collect();
    let ret_ann = match (&d.eff, &d.ret) {
        (None, None) => String::new(),
        (None, Some(t)) => format!(" : {}", fmt_ty(t)),
        (Some(effs), None) => {
            if effs.is_empty() {
                " : !".into()
            } else {
                format!(" : !{{{}}}", fmt_labels(effs))
            }
        }
        (Some(effs), Some(t)) => {
            if effs.is_empty() {
                format!(" : ! {}", fmt_ty(t))
            } else {
                format!(" : !{{{}}} {}", fmt_labels(effs), fmt_ty(t))
            }
        }
    };
    let wh = if d.constraints.is_empty() {
        String::new()
    } else {
        fmt_constraints(&d.constraints)
    };
    let kw = match d.fip {
        Fip::No => "fn",
        Fip::Fbip => "fbip fn",
        Fip::Fip => "fip fn",
    };
    let sig = format!("{kw} {}({}){}{} =", d.name, params.join(", "), ret_ann, wh);

    // A body carrying comments cannot collapse onto the signature line; only the
    // laid-out path has room to re-emit them.
    let bodied = has_comments(d.span.start, d.body.span.end);
    let trailing = mode == Mode::Layout && is_trailing_call(&d.body);
    let stay_inline = mode == Mode::Flat || !forces_break(&d.body);
    if !bodied && !trailing && stay_inline && d.wheres.is_empty() {
        if let Some(body) = fmt_expr_inline(&d.body, mode) {
            let line = format!("{sig} {body}");
            if line.len() <= LINE_WIDTH {
                return line;
            }
        }
    }

    // With a `where` block the body must indent deeper than the `where`
    // keyword, or the offside `=` block swallows the `where` line.
    let wheres = fmt_wheres(&d.wheres);
    let bi = if d.wheres.is_empty() { 1 } else { 2 };
    match mode {
        Mode::Layout => format!("{sig}\n{}{wheres}", fmt_block(&d.body, bi, d.span.start)),
        Mode::Flat => format!(
            "{sig}\n{}{}{wheres}",
            INDENT.repeat(bi),
            fmt_expr_break(&d.body, bi, Mode::Flat)
        ),
    }
}

// A trailing `where` block: `where` one level in, each binding two levels in, so
// the body (rendered a level deeper still) stays offside-nested under it.
pub(super) fn fmt_wheres(wheres: &[(String, S<Expr>)]) -> String {
    use std::fmt::Write as _;
    if wheres.is_empty() {
        return String::new();
    }
    let ind = INDENT.repeat(2);
    let mut s = format!("\n{INDENT}where");
    for (n, v) in wheres {
        if let Some(inl) = fmt_expr_inline(v, Mode::Layout) {
            let line = format!("{ind}{n} = {inl}");
            if line.len() <= LINE_WIDTH {
                write!(s, "\n{line}").unwrap();
                continue;
            }
        }
        write!(s, "\n{ind}{n} =\n{}", fmt_block(v, 3, v.span.start)).unwrap();
    }
    s
}
