//! Top-level declaration formatting: imports, effects, classes, instances,
//! data and pattern declarations, type/row/param rendering, and the function
//! definition printer. The expression and statement printers live in the
//! parent module; the body-bearing printers here are methods on `Fmt` so they
//! can call back into them, while the purely structural printers stay free.

use super::{block_trailing_call, forces_break, Fmt, Mode, INDENT, LINE_WIDTH};
use crate::kw;
use crate::syntax::ast::{
    ClassDecl, Constraint, Ctor, DataDecl, Decl, EffLabel, EffectDecl, Expr, Fip, ImportDecl,
    InstanceDecl, Param, PatternDecl, Row, Ty, S,
};

pub(super) fn fmt_import(i: &ImportDecl) -> String {
    use std::fmt::Write as _;
    let key = if i.reexport {
        format!("{} {}", kw::PUB, kw::IMPORT)
    } else {
        kw::IMPORT.to_string()
    };
    let mut s = format!("{key} {}", i.path.join("."));
    if let Some(a) = &i.alias {
        write!(s, " {} {a}", kw::AS).unwrap();
    }
    if i.glob {
        s.push_str(" (..)");
    } else if let Some(names) = &i.names {
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
                "  {} {}({}) : {}",
                kw::CTL,
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
    format!(
        "{} {}{} {{\n{}\n}}",
        kw::EFFECT,
        e.name,
        params,
        ops.join(",\n")
    )
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
        format!(" {} {}", kw::GIVEN, parts.join(", "))
    };
    format!(
        "{} {}({}){sup} {{\n{}\n}}",
        kw::CLASS,
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
    format!(" {} {}", kw::GIVEN, parts.join(", "))
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
        format!(" {} ({})", kw::DERIVING, names.join(", "))
    };
    let key = if d.newtype { kw::NEWTYPE } else { kw::TYPE };
    format!("{key} {}{} = {}{der}", d.name, params, ctors.join(" | "))
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
        Ty::Int => kw::TY_INT.into(),
        Ty::I64 => kw::TY_I64.into(),
        Ty::U64 => kw::TY_U64.into(),
        Ty::Bool => kw::TY_BOOL.into(),
        Ty::Unit => kw::TY_UNIT.into(),
        Ty::Float => kw::TY_FLOAT.into(),
        Ty::Char => kw::TY_CHAR.into(),
        Ty::Str => kw::TY_STRING.into(),
        Ty::Var(x) => x.clone(),
        Ty::App(v, args) => {
            let args: Vec<String> = args.iter().map(fmt_ty).collect();
            format!("{v}({})", args.join(", "))
        }
        Ty::Forall(vs, t) => {
            let mut vs = vs.clone();
            let mut cur = t.as_ref();
            while let Ty::Forall(more, inner) = cur {
                vs.extend(more.iter().cloned());
                cur = inner;
            }
            format!("{} {}. {}", kw::FORALL, vs.join(" "), fmt_ty(cur))
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

impl Fmt<'_> {
    pub(super) fn fmt_instance(&self, i: &InstanceDecl) -> String {
        let wh = if i.context.is_empty() {
            String::new()
        } else {
            fmt_constraints(&i.context)
        };
        let ms: Vec<String> = i
            .methods
            .iter()
            .map(|m| indent_block(&self.fmt_fn(m, Mode::Flat)))
            .collect();
        format!(
            "{} {} : {}({}){wh} {{\n{}\n}}",
            kw::INSTANCE,
            i.name,
            i.class,
            fmt_ty(&i.head),
            ms.join(",\n")
        )
    }

    pub(super) fn fmt_pattern_decl(&self, p: &PatternDecl) -> String {
        let clause = |key: &str, e: &S<Expr>| {
            let s = self
                .fmt_expr_inline(e, Mode::Flat)
                .unwrap_or_else(|| self.fmt_expr_break(e, 1, Mode::Flat));
            format!("{INDENT}{key} {s}")
        };
        let mut out = format!(
            "{} {}({}) {} {} =\n{}",
            kw::PATTERN,
            p.name,
            p.params.join(", "),
            kw::FOR,
            p.for_ty,
            clause("view", &p.view)
        );
        if let Some(mk) = &p.make {
            out.push('\n');
            out.push_str(&clause("make", mk));
        }
        out
    }

    pub(super) fn fmt_param(&self, p: &Param) -> String {
        let pre = if p.borrow {
            format!("{} ", kw::BORROW)
        } else {
            String::new()
        };
        let base = p.ty.as_ref().map_or_else(
            || format!("{pre}{}", p.name),
            |t| format!("{pre}{} : {}", p.name, fmt_ty(t)),
        );
        match &p.default {
            Some(d) => format!(
                "{base} {} {}",
                kw::COLON_EQ,
                self.fmt_expr(d, 0, Mode::Flat)
            ),
            None => base,
        }
    }

    pub(super) fn fmt_fn(&self, d: &Decl, mode: Mode) -> String {
        if d.konst {
            let ann = d
                .ret
                .as_ref()
                .map_or_else(String::new, |t| format!(" : {}", fmt_ty(t)));
            let sig = format!("{} {}{ann} =", kw::LET, d.name);
            let bodied = self.has_comments(d.span.start, d.body.span.end);
            if !bodied && (mode == Mode::Flat || !forces_break(&d.body)) {
                if let Some(body) = self.fmt_expr_inline(&d.body, mode) {
                    let line = format!("{sig} {body}");
                    if line.len() <= LINE_WIDTH {
                        return line;
                    }
                }
            }
            return match mode {
                Mode::Layout => format!("{sig}\n{}", self.fmt_block(&d.body, 1, d.span.start)),
                Mode::Flat => format!(
                    "{sig}\n{}{}",
                    INDENT,
                    self.fmt_expr_break(&d.body, 1, Mode::Flat)
                ),
            };
        }
        let params: Vec<String> = d.params.iter().map(|p| self.fmt_param(p)).collect();
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
        let key = match d.fip {
            Fip::No => kw::FN.to_string(),
            Fip::Fbip => format!("{} {}", kw::FBIP, kw::FN),
            Fip::Fip => format!("{} {}", kw::FIP, kw::FN),
        };
        let sig = format!("{key} {}({}){}{} =", d.name, params.join(", "), ret_ann, wh);

        // A body carrying comments cannot collapse onto the signature line; only the
        // laid-out path has room to re-emit them. A trailing-lambda call is tried
        // inline too: when its lambda body fits on the line it stays `f(\x -> e)`
        // rather than expanding to the `f() fn(x)` block form; a block-bodied lambda
        // does not fit inline, so it still falls through to the trailing layout.
        let bodied = self.has_comments(d.span.start, d.body.span.end);
        let block_trailing = mode == Mode::Layout && block_trailing_call(&d.body);
        let stay_inline = mode == Mode::Flat || !forces_break(&d.body);
        if !bodied && !block_trailing && stay_inline && d.wheres.is_empty() {
            if let Some(body) = self.fmt_expr_inline(&d.body, mode) {
                let line = format!("{sig} {body}");
                if line.len() <= LINE_WIDTH {
                    return line;
                }
            }
        }

        // With a `where` block the body must indent deeper than the `where`
        // keyword, or the offside `=` block swallows the `where` line.
        let wheres = self.fmt_wheres(&d.wheres);
        let bi = if d.wheres.is_empty() { 1 } else { 2 };
        match mode {
            Mode::Layout => format!(
                "{sig}\n{}{wheres}",
                self.fmt_block(&d.body, bi, d.span.start)
            ),
            Mode::Flat => format!(
                "{sig}\n{}{}{wheres}",
                INDENT.repeat(bi),
                self.fmt_expr_break(&d.body, bi, Mode::Flat)
            ),
        }
    }

    // A trailing `where` block: `where` one level in, each binding two levels in,
    // so the body (rendered a level deeper still) stays offside-nested under it.
    fn fmt_wheres(&self, wheres: &[(String, S<Expr>)]) -> String {
        use std::fmt::Write as _;
        if wheres.is_empty() {
            return String::new();
        }
        let ind = INDENT.repeat(2);
        let mut s = format!("\n{INDENT}{}", kw::WHERE);
        for (n, v) in wheres {
            if let Some(inl) = self.fmt_expr_inline(v, Mode::Layout) {
                let line = format!("{ind}{n} = {inl}");
                if line.len() <= LINE_WIDTH {
                    write!(s, "\n{line}").unwrap();
                    continue;
                }
            }
            write!(s, "\n{ind}{n} =\n{}", self.fmt_block(v, 3, v.span.start)).unwrap();
        }
        s
    }
}
