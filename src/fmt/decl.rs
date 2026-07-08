//! Top-level declaration formatting: imports, effects, classes, instances,
//! data and pattern declarations, type/row/param rendering, and the function
//! definition printer. The expression and statement printers live in the
//! parent module; the body-bearing printers here are methods on `Fmt` so they
//! can call back into them, while the purely structural printers stay free.

use std::fmt::Write as _;

use super::{block_trailing_call, forces_break, Fmt, Mode, INDENT, LINE_WIDTH};
use crate::coeffect::CoeffectFact;
use crate::kw;
use crate::syntax::ast::{
    ClassDecl, Constraint, Ctor, DataDecl, Decl, EffLabel, EffectDecl, Expr, Fip, ImportDecl,
    InstanceDecl, Kind, Param, PatternDecl, Row, Ty, S,
};

pub(super) fn fmt_import(i: &ImportDecl) -> String {
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

pub(crate) fn fmt_effect(e: &EffectDecl) -> String {
    let ops: Vec<String> = e
        .ops
        .iter()
        .map(|op| {
            let params: Vec<String> = op.params.iter().map(fmt_ty).collect();
            format!(
                "{INDENT}{} {}({}) : {}",
                op.grade.keyword(),
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
    format!("{} {}{}\n{}", kw::EFFECT, e.name, params, ops.join("\n"))
}

pub(super) fn fmt_label(l: &EffLabel) -> String {
    if l.args.is_empty() {
        l.name.clone()
    } else {
        let args: Vec<String> = l.args.iter().map(fmt_ty).collect();
        format!("{}({})", l.name, args.join(", "))
    }
}

pub(crate) fn fmt_labels(ls: &[EffLabel]) -> String {
    let parts: Vec<String> = ls.iter().map(fmt_label).collect();
    parts.join(", ")
}

pub(crate) fn fmt_class(c: &ClassDecl) -> String {
    let sigs: Vec<String> = c
        .methods
        .iter()
        .map(|(n, t)| format!("{INDENT}{n} : {}", fmt_ty(t)))
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
    let head = format!("{} {}({}){sup}", kw::CLASS, c.name, c.param);
    // A marker class with no methods is its bare head; anything else lays its
    // members out on the following indented lines.
    if sigs.is_empty() {
        head
    } else {
        format!("{head}\n{}", sigs.join("\n"))
    }
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

// Render a type declaration's parameters, restoring any written kind annotation
// (`type Cmd(a, e : Row)`, `type Vec(a, n : Nat)`). An unannotated parameter has
// kind `Type` and prints bare, so ordinary types are unchanged. The match is
// exhaustive over `Kind` on purpose: a silently dropped annotation is an
// AST-identity break (it once turned `Vec(a, n : Nat)` into `Vec(a, n)`), so a
// new kind must decide its rendering here to compile.
fn fmt_ty_params(names: &[String], kinds: &[Kind]) -> String {
    if names.is_empty() {
        return String::new();
    }
    let parts: Vec<String> = names
        .iter()
        .enumerate()
        .map(|(i, n)| match kinds.get(i) {
            Some(Kind::Row) => format!("{n} : {}", kw::KIND_ROW),
            Some(Kind::Nat) => format!("{n} : {}", kw::KIND_NAT),
            // A higher-kinded parameter's arrow kind is inferred, never written.
            Some(Kind::Type | Kind::Fun(..)) | None => n.clone(),
        })
        .collect();
    format!("({})", parts.join(", "))
}

pub(crate) fn fmt_data(d: &DataDecl) -> String {
    let params = fmt_ty_params(&d.params, &d.param_kinds);
    let head = format!(
        "{} {}{params}",
        if d.newtype { kw::NEWTYPE } else { kw::TYPE },
        d.name
    );
    let names: Vec<&str> = d.deriving.iter().map(|(n, _)| n.as_str()).collect();
    let der = if names.is_empty() {
        String::new()
    } else {
        format!(" {} ({})", kw::DERIVING, names.join(", "))
    };
    let ctors: Vec<String> = d.ctors.iter().map(fmt_ctor).collect();
    let flat = format!("{head} = {}{der}", ctors.join(" | "));
    // A type stays on one line only when it fits AND has at most three
    // constructors. A sum with more than three constructors is always stacked (the
    // canonical aligned form below), and any declaration over the width budget
    // wraps regardless of count.
    if flat.len() <= LINE_WIDTH && d.ctors.len() <= 3 {
        return flat;
    }
    // Two or more constructors stack one per line with the `=` and every `|`
    // aligned in a leading column under the head (the offside block form the
    // grammar reparses); a single constructor wraps its own fields or arguments in
    // place inside its brackets, which suppress layout. The split is a pure
    // function of the tree, so a short three-or-fewer type never reaches here and
    // formatting is idempotent.
    if d.ctors.len() >= 2 {
        let mut lines = vec![head, format!("{INDENT}= {}", ctors[0])];
        lines.extend(ctors[1..].iter().map(|c| format!("{INDENT}| {c}")));
        if !names.is_empty() {
            lines.push(format!("{INDENT}{} ({})", kw::DERIVING, names.join(", ")));
        }
        return lines.join("\n");
    }
    match d.ctors.first() {
        Some(c) => wrap_ctor(c).map_or(flat, |body| format!("{head} = {body}{der}")),
        None => flat,
    }
}

// A single constructor split across lines: record fields or positional arguments
// one per line, the closing delimiter back at the declaration's column. `None`
// when there is no member list worth wrapping, so the caller keeps the flat form.
fn wrap_ctor(c: &Ctor) -> Option<String> {
    match &c.fields {
        Some(fields) if fields.len() >= 2 => {
            let fs: Vec<String> = fields
                .iter()
                .map(|(n, t)| format!("{INDENT}{n}: {}", fmt_ty(t)))
                .collect();
            Some(format!("{} {{\n{}\n}}", c.name, fs.join(",\n")))
        }
        None if c.args.len() >= 2 => {
            let args: Vec<String> = c
                .args
                .iter()
                .map(|t| format!("{INDENT}{}", fmt_ty(t)))
                .collect();
            Some(format!("{}(\n{}\n)", c.name, args.join(",\n")))
        }
        _ => None,
    }
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

pub(crate) fn fmt_ty(t: &Ty) -> String {
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
            format!(
                "({}) {} {}{}",
                args.join(", "),
                kw::ARROW,
                fmt_ty(ret),
                fmt_row(row)
            )
        }
        Ty::Con(name, args) if args.is_empty() => name.clone(),
        Ty::Con(name, args) => {
            let args: Vec<String> = args.iter().map(fmt_ty).collect();
            format!("{}({})", name, args.join(", "))
        }
        // A usage row prints through the canonical `CoeffectRow` display
        // (singleton sugar, alphabetized braces). Arrow and forall types are
        // re-parenthesized: the row attaches to atoms only, so the parens are
        // what parsing required and round-tripping must restore.
        Ty::Coeffect(inner, row) => match inner.as_ref() {
            t @ (Ty::Fun(..) | Ty::Forall(..)) => format!("({}) {row}", fmt_ty(t)),
            t => format!("{} {row}", fmt_ty(t)),
        },
        Ty::Tuple(ts) => {
            let ts: Vec<String> = ts.iter().map(fmt_ty).collect();
            format!("({})", ts.join(", "))
        }
        // A row literal in argument position prints as `{ .. }` (no leading `!`,
        // which marks a function's effect row, not a row-kinded argument).
        Ty::RowLit(Row::Cons(ls, tl)) => {
            let body = match tl {
                Some(v) if ls.is_empty() => format!("| {v}"),
                Some(v) => format!("{} | {v}", fmt_labels(ls)),
                None => fmt_labels(ls),
            };
            format!("{{{body}}}")
        }
        Ty::RowLit(Row::Empty) => "{}".into(),
        // Synthesized only by desugar and carries no span; the formatter only
        // ever sees source types. Should this marker leak this far, emit an inert
        // hole rather than fabricating identity text or aborting: a formatter
        // must never crash on or invent identity from its input.
        Ty::State(_) => "_".into(),
        // A type-level natural literal in a dimension position (`Vec(Int, 3)`).
        Ty::Nat(n) => n.to_string(),
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
            .map(|m| indent_block(&self.fmt_fn(m, Mode::Layout)))
            .collect();
        let head = format!(
            "{} {} : {}({}){wh}",
            kw::INSTANCE,
            i.name,
            i.class,
            fmt_ty(&i.head)
        );
        // A marker-class instance carries no methods and is its bare head.
        if ms.is_empty() {
            head
        } else {
            format!("{head}\n{}", ms.join("\n"))
        }
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
        // A certified declaration re-parenthesizes a function return type: the
        // `@ noalloc` appended below must re-parse at the annotation's root, and
        // an unparenthesized arrow would capture the row on its codomain atom.
        let ret_ty = |t: &Ty| match t {
            t @ (Ty::Fun(..) | Ty::Forall(..)) if d.no_alloc => format!("({})", fmt_ty(t)),
            t => fmt_ty(t),
        };
        let ret_ann = match (&d.eff, &d.ret) {
            (None, None) => String::new(),
            (None, Some(t)) => format!(" : {}", ret_ty(t)),
            (Some(effs), None) => {
                if effs.is_empty() {
                    " : !".into()
                } else {
                    format!(" : !{{{}}}", fmt_labels(effs))
                }
            }
            (Some(effs), Some(t)) => {
                if effs.is_empty() {
                    format!(" : ! {}", ret_ty(t))
                } else {
                    format!(" : !{{{}}} {}", fmt_labels(effs), ret_ty(t))
                }
            }
        };
        let wh = if d.constraints.is_empty() {
            String::new()
        } else {
            fmt_constraints(&d.constraints)
        };
        let fip_key = match d.fip {
            Fip::No => kw::FN.to_string(),
            Fip::Fbip => format!("{} {}", kw::FBIP, kw::FN),
            Fip::Fip => format!("{} {}", kw::FIP, kw::FN),
        };
        let key = if d.replayable {
            format!("{} {fip_key}", kw::REPLAYABLE)
        } else {
            fip_key
        };
        // The allocation certificate `@ noalloc` is a postfix on the return
        // annotation (lifted onto the decl flag at parse), so it prints there,
        // not in the leading `key`.
        let na = if d.no_alloc {
            format!(" {} {}", kw::AT, CoeffectFact::Noalloc)
        } else {
            String::new()
        };
        // A signature over budget with two or more parameters puts each on its own
        // line inside the parens (which suppress layout), the closing `)` and the
        // return annotation placed back at the declaration's column. The wrap is
        // decided from the flat signature length, so it is idempotent and a short
        // signature stays on one line.
        let flat_sig = format!("{key} {}({}){ret_ann}{na}{wh} =", d.name, params.join(", "));
        let sig = if flat_sig.len() > LINE_WIDTH && params.len() >= 2 {
            let ps: Vec<String> = params.iter().map(|p| format!("{INDENT}{p}")).collect();
            format!(
                "{key} {}(\n{}\n){ret_ann}{na}{wh} =",
                d.name,
                ps.join(",\n")
            )
        } else {
            flat_sig
        };

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
