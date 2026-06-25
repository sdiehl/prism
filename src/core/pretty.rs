use std::fmt::Write;

use super::cbpv::{Comp, Core, CoreOp, CorePat, Value};
use crate::kw;
use crate::sym::Sym;

fn join_syms(syms: &[Sym]) -> String {
    syms.iter()
        .map(|s| s.as_str())
        .collect::<Vec<_>>()
        .join(", ")
}

#[must_use]
pub fn pp_core(core: &Core) -> String {
    let mut out = String::new();
    for f in &core.fns {
        writeln!(out, "{} {}({}) =", kw::FN, f.name, join_syms(&f.params)).unwrap();
        writeln!(out, "  {}", pp_comp(&f.body)).unwrap();
    }
    out
}

const STEP: &str = "  ";

// Multi-line rendering: one bind per line, indented `if`/`case`/`handle` blocks,
// unlike the single `;`-joined line `pp_core` emits for snapshots.
#[must_use]
pub fn pp_core_pretty(core: &Core) -> String {
    let mut out = String::new();
    for f in &core.fns {
        writeln!(out, "{} {}({}) =", kw::FN, f.name, join_syms(&f.params)).unwrap();
        out.push_str(&pp_block(&f.body, 1));
        out.push('\n');
    }
    out
}

fn pp_block(c: &Comp, depth: usize) -> String {
    pp_seq(c, depth, None)
}

// Render a computation as a stack of statement lines at `depth`. A bind flattens
// into its producer's statements followed by its body's, so an ANF chain reads
// top to bottom. `binder` is the name the whole sequence's result binds to (the
// last producer statement carries it), or `None` in tail position. Control-flow
// constructs recurse into nested blocks. One that appears as a bound producer
// (rare) falls back to the one-line form.
fn pp_seq(c: &Comp, depth: usize, binder: Option<&str>) -> String {
    let pad = STEP.repeat(depth);
    match c {
        Comp::Bind(m, x, n) => {
            let bx = (*x != "_").then_some(x.as_str());
            format!("{}\n{}", pp_seq(m, depth, bx), pp_seq(n, depth, binder))
        }
        Comp::If(v, t, e) if binder.is_none() => format!(
            "{pad}{} {} {}\n{}\n{pad}{}\n{}",
            kw::IF,
            pp_value(v),
            kw::THEN,
            pp_block(t, depth + 1),
            kw::ELSE,
            pp_block(e, depth + 1)
        ),
        Comp::Case(v, arms) if binder.is_none() => {
            let mut s = format!("{pad}case {} of", pp_value(v));
            for (p, b) in arms {
                write!(
                    s,
                    "\n{}{} =>\n{}",
                    STEP.repeat(depth + 1),
                    pp_pat(p),
                    pp_block(b, depth + 2)
                )
                .unwrap();
            }
            s
        }
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } if binder.is_none() => {
            let mut s = format!(
                "{pad}{}\n{}\n{pad}{}",
                kw::HANDLE,
                pp_block(body, depth + 1),
                kw::WITH
            );
            for op in ops {
                let mut ps = op.params.clone();
                ps.push(op.resume);
                write!(
                    s,
                    "\n{}{}({}) =>\n{}",
                    STEP.repeat(depth + 1),
                    op.name,
                    join_syms(&ps),
                    pp_block(&op.body, depth + 2)
                )
                .unwrap();
            }
            if let (Some(rv), Some(rb)) = (return_var, return_body) {
                write!(
                    s,
                    "\n{}{} {rv} =>\n{}",
                    STEP.repeat(depth + 1),
                    kw::RETURN,
                    pp_block(rb, depth + 2)
                )
                .unwrap();
            }
            s
        }
        Comp::Mask(ops, b) if binder.is_none() => {
            format!(
                "{pad}{}<{}>\n{}",
                kw::MASK,
                join_syms(ops),
                pp_block(b, depth + 1)
            )
        }
        // Flatten the scoped reuse like a bind: the token statement, then the
        // body's sequence carrying the same result binder.
        Comp::WithReuse { token, freed, body } => format!(
            "{pad}reuse_token {} to {token}\n{}",
            pp_value(freed),
            pp_seq(body, depth, binder)
        ),
        other => {
            let s = pp_comp(other);
            binder.map_or_else(|| format!("{pad}{s}"), |x| format!("{pad}{s} to {x}"))
        }
    }
}

pub fn pp_value(v: &Value) -> String {
    match v {
        Value::Var(x) => x.to_string(),
        Value::Int(n) => n.to_string(),
        Value::I64(n) => format!("{n}i64"),
        Value::U64(n) => format!("{n}u64"),
        Value::Float(f) => format!("{f}"),
        Value::Bool(b) => b.to_string(),
        Value::Unit => "()".into(),
        Value::Str(s) => format!("{s:?}"),
        Value::Thunk(c) => format!("thunk {{ {} }}", pp_comp(c)),
        Value::Ctor(name, _, vs) if vs.is_empty() => name.to_string(),
        Value::Ctor(name, _, vs) => {
            let vs: Vec<_> = vs.iter().map(pp_value).collect();
            format!("{name}({})", vs.join(", "))
        }
        Value::Tuple(vs) if vs.is_empty() => "()".into(),
        Value::Tuple(vs) => {
            let vs: Vec<_> = vs.iter().map(pp_value).collect();
            format!("({})", vs.join(", "))
        }
    }
}

pub fn pp_comp(c: &Comp) -> String {
    match c {
        Comp::Return(v) => format!("{} {}", kw::RETURN, pp_value(v)),
        Comp::Bind(m, x, n) => format!("{} to {x}; {}", pp_comp(m), pp_comp(n)),
        Comp::Force(v) => format!("force {}", pp_value(v)),
        Comp::Lam(ps, b) => format!(
            "\\{}. {}",
            ps.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(" "),
            pp_comp(b)
        ),
        Comp::App(m, args) => {
            let args: Vec<_> = args.iter().map(pp_value).collect();
            format!("({})({})", pp_comp(m), args.join(", "))
        }
        Comp::If(v, t, e) => {
            format!(
                "{} {} {} ({}) {} ({})",
                kw::IF,
                pp_value(v),
                kw::THEN,
                pp_comp(t),
                kw::ELSE,
                pp_comp(e)
            )
        }
        Comp::Prim(op, a, b) => format!("{} {} {}", pp_value(a), pp_op(*op), pp_value(b)),
        Comp::Call(name, args) => {
            let args: Vec<_> = args.iter().map(pp_value).collect();
            format!("{name}({})", args.join(", "))
        }
        Comp::StrBuiltin(b, args) => {
            let args: Vec<_> = args.iter().map(pp_value).collect();
            format!("{}({})", b.name(), args.join(", "))
        }
        Comp::Print(v) => format!("print {}", pp_value(v)),
        Comp::PrintF(v) => format!("printf {}", pp_value(v)),
        Comp::PrintS(v) => format!("prints {}", pp_value(v)),
        Comp::PrintNl => "print_nl".into(),
        Comp::ReadInt => "read_int()".into(),
        Comp::ReadLine => "read_line()".into(),
        Comp::Rand => "rand()".into(),
        Comp::Srand(v) => format!("srand {}", pp_value(v)),
        Comp::Error(v) => format!("error {}", pp_value(v)),
        Comp::Case(v, arms) => {
            let arms: Vec<_> = arms
                .iter()
                .map(|(p, b)| format!("{} => {}", pp_pat(p), pp_comp(b)))
                .collect();
            format!("case {} {{ {} }}", pp_value(v), arms.join(" | "))
        }
        Comp::FloatBuiltin(op, v) => format!("{}({})", op.name(), pp_value(v)),
        Comp::Dup(v) => format!("dup {}", pp_value(v)),
        Comp::Drop(v) => format!("drop {}", pp_value(v)),
        Comp::WithReuse { token, freed, body } => {
            format!(
                "reuse_token {} to {token}; {}",
                pp_value(freed),
                pp_comp(body)
            )
        }
        Comp::Reuse(tok, v) => format!("reuse {tok} as {}", pp_value(v)),
        Comp::Do(op, args) => {
            let args: Vec<_> = args.iter().map(pp_value).collect();
            format!("do {op}({})", args.join(", "))
        }
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => {
            let mut arms: Vec<String> = ops
                .iter()
                .map(|op| {
                    let mut ps = op.params.clone();
                    ps.push(op.resume);
                    format!("{}({}) => {}", op.name, join_syms(&ps), pp_comp(&op.body))
                })
                .collect();
            if let (Some(rv), Some(rb)) = (return_var, return_body) {
                arms.push(format!("{} {rv} => {}", kw::RETURN, pp_comp(rb)));
            }
            format!(
                "{} {{ {} }} {} {{ {} }}",
                kw::HANDLE,
                pp_comp(body),
                kw::WITH,
                arms.join(", ")
            )
        }
        Comp::Mask(ops, b) => format!("{}<{}> {{ {} }}", kw::MASK, join_syms(ops), pp_comp(b)),
    }
}

fn pp_pat(p: &CorePat) -> String {
    let field = |b: &Option<Sym>| b.map_or_else(|| "_".to_string(), |s| s.as_str().to_string());
    match p {
        CorePat::Wild => "_".into(),
        CorePat::Var(x) => x.as_str().to_string(),
        CorePat::Ctor(name, fields) if fields.is_empty() => name.as_str().to_string(),
        CorePat::Ctor(name, fields) => {
            let fs: Vec<_> = fields.iter().map(field).collect();
            format!("{}({})", name.as_str(), fs.join(", "))
        }
        CorePat::Tuple(fields) => {
            let fs: Vec<_> = fields.iter().map(field).collect();
            format!("({})", fs.join(", "))
        }
    }
}

const fn pp_op(op: CoreOp) -> &'static str {
    match op {
        CoreOp::Add => kw::PLUS,
        CoreOp::Sub => kw::MINUS,
        CoreOp::Mul => kw::STAR,
        CoreOp::Div => kw::SLASH,
        CoreOp::Rem => kw::PERCENT,
        CoreOp::Addf => kw::PLUS_DOT,
        CoreOp::Subf => kw::MINUS_DOT,
        CoreOp::Mulf => kw::STAR_DOT,
        CoreOp::Divf => kw::SLASH_DOT,
        CoreOp::Eq => kw::EQ_EQ,
        CoreOp::Ne => kw::NE,
        CoreOp::Lt => kw::LT,
        CoreOp::Le => kw::LE,
        CoreOp::Gt => kw::GT,
        CoreOp::Ge => kw::GE,
        CoreOp::Eqf => kw::EQ_DOT,
        CoreOp::Nef => kw::NE_DOT,
        CoreOp::Ltf => kw::LT_DOT,
        CoreOp::Lef => kw::LE_DOT,
        CoreOp::Gtf => kw::GT_DOT,
        CoreOp::Gef => kw::GE_DOT,
    }
}
