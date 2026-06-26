//! JSON serialization of the CBPV core, in the tagged schema the Lean model's
//! decoder (`models/Json.lean`) reads. `prism dump core-json <file>` emits this
//! so the formally-verified CEK oracle (`models/`) can be fed the exact core the
//! compiler builds, for differential checking against the interpreter.
//!
//! The shape mirrors `pp_core_pretty` but as data: each node is a JSON object
//! tagged by `"c"` (computations), `"v"` (values), or `"p"` (patterns). `Sym`s
//! resolve to their interned name. IO/builtin/ref nodes are tagged faithfully;
//! the Lean side maps the ones it models to their erased forms and rejects the
//! rest, so only the pure + effects fragment round-trips.

use serde_json::{json, Map, Value as J};

use super::cbpv::{Comp, Core, CoreFn, CoreOp, CorePat, HandleOp, Value};
use crate::sym::Sym;

fn syms(ss: &[Sym]) -> J {
    J::Array(ss.iter().map(|s| json!(s.as_str())).collect())
}

fn op_name(op: CoreOp) -> &'static str {
    use CoreOp::{
        Add, Addf, Div, Divf, Eq, Eqf, Ge, Gef, Gt, Gtf, Le, Lef, Lt, Ltf, Mul, Mulf, Ne, Nef, Rem,
        Sub, Subf,
    };
    match op {
        Add => "add",
        Sub => "sub",
        Mul => "mul",
        Div => "div",
        Rem => "rem",
        Eq => "eq",
        Ne => "ne",
        Lt => "lt",
        Le => "le",
        Gt => "gt",
        Ge => "ge",
        Addf => "addf",
        Subf => "subf",
        Mulf => "mulf",
        Divf => "divf",
        Eqf => "eqf",
        Nef => "nef",
        Ltf => "ltf",
        Lef => "lef",
        Gtf => "gtf",
        Gef => "gef",
    }
}

fn value(v: &Value) -> J {
    match v {
        Value::Var(x) => json!({"v": "var", "x": x.as_str()}),
        Value::Int(n) | Value::I64(n) => json!({"v": "int", "n": n}),
        Value::U64(n) => json!({"v": "int", "n": n}),
        Value::Float(f) => json!({"v": "float", "f": f}),
        Value::Bool(b) => json!({"v": "bool", "b": b}),
        Value::Unit => json!({"v": "unit"}),
        Value::Str(s) => json!({"v": "str", "s": s}),
        Value::Thunk(c) => json!({"v": "thunk", "c": comp(c)}),
        Value::Ctor(n, tag, args) => {
            json!({"v": "ctor", "name": n.as_str(), "tag": tag, "args": values(args)})
        }
        Value::Tuple(args) => json!({"v": "tuple", "args": values(args)}),
    }
}

fn values(vs: &[Value]) -> J {
    J::Array(vs.iter().map(value).collect())
}

// A core ctor/tuple pattern binder list: `Some(x)` binds, `None` is a wildcard.
fn binders(args: &[Option<Sym>]) -> J {
    J::Array(
        args.iter()
            .map(|o| match o {
                Some(x) => json!({"p": "var", "x": x.as_str()}),
                None => json!({"p": "wild"}),
            })
            .collect(),
    )
}

fn pat(p: &CorePat) -> J {
    match p {
        CorePat::Wild => json!({"p": "wild"}),
        CorePat::Var(x) => json!({"p": "var", "x": x.as_str()}),
        CorePat::Ctor(n, args) => json!({"p": "ctor", "name": n.as_str(), "args": binders(args)}),
        CorePat::Tuple(args) => json!({"p": "tuple", "args": binders(args)}),
    }
}

fn handle_op(h: &HandleOp) -> J {
    json!({"name": h.name.as_str(), "params": syms(&h.params), "resume": h.resume.as_str(), "body": comp(&h.body)})
}

fn comp(c: &Comp) -> J {
    match c {
        Comp::Return(v) => json!({"c": "ret", "v": value(v)}),
        Comp::Bind(m, x, n) => json!({"c": "bind", "m": comp(m), "x": x.as_str(), "n": comp(n)}),
        Comp::Force(v) => json!({"c": "force", "v": value(v)}),
        Comp::Lam(xs, b) => json!({"c": "lam", "xs": syms(xs), "body": comp(b)}),
        Comp::App(f, args) => json!({"c": "app", "f": comp(f), "args": values(args)}),
        Comp::If(v, t, e) => json!({"c": "ite", "cond": value(v), "t": comp(t), "e": comp(e)}),
        Comp::Prim(op, a, b) => {
            json!({"c": "prim", "op": op_name(*op), "a": value(a), "b": value(b)})
        }
        Comp::Call(n, args) => json!({"c": "call", "name": n.as_str(), "args": values(args)}),
        Comp::Case(v, arms) => json!({"c": "case", "scrut": value(v),
            "arms": J::Array(arms.iter().map(|(p, b)| json!({"pat": pat(p), "body": comp(b)})).collect())}),
        Comp::Do(op, args) => json!({"c": "doOp", "name": op.as_str(), "args": values(args)}),
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => {
            let mut m = Map::new();
            m.insert("c".into(), json!("handle"));
            m.insert("body".into(), comp(body));
            m.insert("ops".into(), J::Array(ops.iter().map(handle_op).collect()));
            if let Some(rv) = return_var {
                m.insert("retVar".into(), json!(rv.as_str()));
            }
            if let Some(rb) = return_body {
                m.insert("retBody".into(), comp(rb));
            }
            J::Object(m)
        }
        Comp::Mask(ops, b) => json!({"c": "mask", "ops": syms(ops), "body": comp(b)}),
        // IO / builtins / ref: tagged faithfully; the Lean model erases or rejects these.
        Comp::Print(v) => json!({"c": "print", "v": value(v)}),
        Comp::PrintF(v) => json!({"c": "printf", "v": value(v)}),
        Comp::PrintS(v) => json!({"c": "prints", "v": value(v)}),
        Comp::PrintNl => json!({"c": "printNl"}),
        Comp::ReadInt => json!({"c": "readInt"}),
        Comp::ReadLine => json!({"c": "readLine"}),
        Comp::Rand => json!({"c": "rand"}),
        Comp::Srand(v) => json!({"c": "srand", "v": value(v)}),
        Comp::Error(v) => json!({"c": "err", "v": value(v)}),
        Comp::FloatBuiltin(op, v) => {
            json!({"c": "floatBuiltin", "name": format!("{op:?}"), "v": value(v)})
        }
        Comp::StrBuiltin(b, args) => {
            json!({"c": "strBuiltin", "name": format!("{b:?}"), "args": values(args)})
        }
        Comp::Dup(v) => json!({"c": "dup", "v": value(v)}),
        Comp::Drop(v) => json!({"c": "drop", "v": value(v)}),
        Comp::WithReuse { token, freed, body } => {
            json!({"c": "withReuse", "tok": token.as_str(), "freed": value(freed), "body": comp(body)})
        }
        Comp::Reuse(tok, v) => json!({"c": "reuse", "tok": tok.as_str(), "v": value(v)}),
        Comp::RefNew(v) => json!({"c": "refNew", "v": value(v)}),
        Comp::RefGet(v) => json!({"c": "refGet", "v": value(v)}),
        Comp::RefSet(a, b) => json!({"c": "refSet", "a": value(a), "b": value(b)}),
    }
}

fn core_fn(f: &CoreFn) -> J {
    json!({"name": f.name.as_str(), "params": syms(&f.params), "body": comp(&f.body)})
}

/// Serialize a whole core program to the Lean-readable JSON schema.
#[must_use]
pub fn core_to_json(core: &Core) -> String {
    json!({"fns": J::Array(core.fns.iter().map(core_fn).collect())}).to_string()
}
