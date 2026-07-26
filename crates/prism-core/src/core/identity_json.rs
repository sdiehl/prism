//! The identity export: the exact inputs [`super::hash`] folds into a
//! definition's content hash, as deterministic JSON.
//!
//! [`json`](super::json) already serializes Core, but for a different consumer
//! and from a different point in the pipeline: it renders *optimized* Core in the
//! Lean model's tag vocabulary, and it omits the two facts the hash commits to
//! that Core does not carry (a definition's dictionary arity and its out-of-Core
//! elaboration metadata). A program that reads it therefore cannot reproduce a
//! content hash. This module exports the identity surface instead: pre-optimizer
//! Core, every node tagged by the *same* identifier the hasher commits to
//! (`Comp::kind`, and the `hash_tag` of each operator family), plus the
//! dictionary arity, the metadata string, and the content hashes of the
//! definitions the exported group depends on.
//!
//! Two facts travel as data rather than as a name a reader would have to parse
//! back. A generated `var` operation carries its verb and State slot in separate
//! fields, so a consumer performs the hasher's rename-and-reorder
//! canonicalization without re-implementing the `get@x@n` spelling; and a
//! numeric literal carries its exact decimal (or, for a float, its bit pattern)
//! as a string, so a consumer splices the same bytes the hasher writes rather
//! than round-tripping through a JSON number.

use serde_json::{json, Map, Value as J};

use super::cbpv::{Comp, CoreFn, CorePat, HandleOp, Value};
use prism_common::digest::Digest;
use prism_common::sym::Sym;
use prism_syntax::names::{parse_var_get, parse_var_set};

/// The versioned schema tag of the identity export.
pub const IDENTITY_SCHEMA: &str = "prism-core-identity-v1";

/// The two generated-`var` verbs, the canonical spelling the hasher renumbers.
const VAR_VERB_GET: &str = "get";
const VAR_VERB_SET: &str = "set";

fn syms(ss: &[Sym]) -> J {
    J::Array(ss.iter().map(|s| json!(s.as_str())).collect())
}

// A core ctor/tuple pattern binder list: a name binds, `null` is a wildcard.
fn binders(args: &[Option<Sym>]) -> J {
    J::Array(
        args.iter()
            .map(|o| o.as_ref().map_or(J::Null, |x| json!(x.as_str())))
            .collect(),
    )
}

fn pat(p: &CorePat) -> J {
    match p {
        CorePat::Wild => json!({"p": "Wild"}),
        CorePat::Var(x) => json!({"p": "Var", "x": x.as_str()}),
        CorePat::Ctor(n, args) => json!({"p": "Ctor", "name": n.as_str(), "fields": binders(args)}),
        CorePat::Tuple(args) => json!({"p": "Tuple", "fields": binders(args)}),
    }
}

fn values(vs: &[Value]) -> J {
    J::Array(vs.iter().map(value).collect())
}

fn value(v: &Value) -> J {
    match v {
        Value::Var(x) => json!({"v": "Var", "x": x.as_str()}),
        // Exact decimal, as a string: the same bytes the hasher writes, with no
        // JSON-number round trip in between.
        Value::Int(n) => json!({"v": "Int", "n": n.to_string()}),
        Value::I64(n) => json!({"v": "I64", "n": n.to_string()}),
        Value::U64(n) => json!({"v": "U64", "n": n.to_string()}),
        // The bit pattern, so a NaN payload and a signed zero survive exactly.
        Value::Float(f) => json!({"v": "Float", "bits": f.to_bits().to_string()}),
        Value::Bool(b) => json!({"v": "Bool", "b": b}),
        Value::Unit => json!({"v": "Unit"}),
        Value::Str(s) => json!({"v": "Str", "s": s}),
        Value::Thunk(c) => json!({"v": "Thunk", "c": comp(c)}),
        Value::Ctor(n, tag, args) => {
            json!({"v": "Ctor", "name": n.as_str(), "tag": tag, "args": values(args)})
        }
        Value::Tuple(args) => json!({"v": "Tuple", "args": values(args)}),
        Value::UnboxedTuple(args) => json!({"v": "UnboxedTuple", "args": values(args)}),
        Value::UnboxedRecord(fs) => json!({
            "v": "UnboxedRecord",
            "fields": fs.iter().map(|(n, x)| json!({"name": n.as_str(), "val": value(x)})).collect::<Vec<_>>(),
        }),
    }
}

// The generated-`var` decomposition of an effect-operation name, as the fields a
// consumer needs to renumber it: the verb and the State slot. `None` for a
// user-declared operation, which the hash commits to verbatim.
fn var_op_fields(name: &str) -> Option<(&'static str, String)> {
    parse_var_get(name)
        .map(|(_, n)| (VAR_VERB_GET, n.to_string()))
        .or_else(|| parse_var_set(name).map(|(_, n)| (VAR_VERB_SET, n.to_string())))
}

// Insert the generated-`var` fields when `name` is one, leaving the object
// untouched when it is a user-declared operation.
fn put_var_fields(m: &mut Map<String, J>, name: &str) {
    if let Some((verb, slot)) = var_op_fields(name) {
        m.insert("varVerb".into(), json!(verb));
        m.insert("varSlot".into(), json!(slot));
    }
}

fn handle_op(h: &HandleOp) -> J {
    let mut m = Map::new();
    m.insert("name".into(), json!(h.name.as_str()));
    put_var_fields(&mut m, h.name.as_str());
    m.insert("params".into(), syms(&h.params));
    m.insert("resume".into(), json!(h.resume.as_str()));
    m.insert("body".into(), comp(&h.body));
    J::Object(m)
}

#[allow(clippy::too_many_lines)]
fn comp(c: &Comp) -> J {
    // Every node is tagged by `Comp::kind`, the same identifier the hasher writes
    // between angle brackets, so the export and the hash can never disagree about
    // which node a reader is looking at.
    let k = c.kind();
    match c {
        Comp::Return(v)
        | Comp::Force(v)
        | Comp::Error(v)
        | Comp::Dup(v)
        | Comp::Drop(v)
        | Comp::RefNew(v)
        | Comp::RefGet(v) => json!({"k": k, "v": value(v)}),
        Comp::Io(_, args) => json!({"k": k, "args": values(args)}),
        Comp::FloatBuiltin(op, v) => json!({"k": k, "tag": op.hash_tag(), "v": value(v)}),
        Comp::Neg(lane, v) => json!({"k": k, "tag": lane.hash_tag(), "v": value(v)}),
        Comp::UnboxedProject(v, field) => {
            json!({"k": k, "v": value(v), "field": field.as_str()})
        }
        Comp::Bind(m, x, n) => json!({"k": k, "m": comp(m), "x": x.as_str(), "n": comp(n)}),
        Comp::Lam(xs, b) => json!({"k": k, "xs": syms(xs), "body": comp(b)}),
        Comp::App(f, args) => json!({"k": k, "f": comp(f), "args": values(args)}),
        Comp::If(v, t, e) => json!({"k": k, "cond": value(v), "t": comp(t), "e": comp(e)}),
        Comp::Prim(op, a, b) => {
            json!({"k": k, "tag": op.hash_tag(), "a": value(a), "b": value(b)})
        }
        Comp::Call(n, args) => json!({"k": k, "name": n.as_str(), "args": values(args)}),
        Comp::Do(op, args) => {
            let mut m = Map::new();
            m.insert("k".into(), json!(k));
            m.insert("op".into(), json!(op.as_str()));
            put_var_fields(&mut m, op.as_str());
            m.insert("args".into(), values(args));
            J::Object(m)
        }
        Comp::Case(v, arms) => json!({"k": k, "scrut": value(v),
            "arms": J::Array(arms.iter().map(|(p, b)| json!({"pat": pat(p), "body": comp(b)})).collect())}),
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => {
            let mut m = Map::new();
            m.insert("k".into(), json!(k));
            m.insert("body".into(), comp(body));
            if let Some(rv) = return_var {
                m.insert("retVar".into(), json!(rv.as_str()));
            }
            if let Some(rb) = return_body {
                m.insert("retBody".into(), comp(rb));
            }
            m.insert("ops".into(), J::Array(ops.iter().map(handle_op).collect()));
            J::Object(m)
        }
        Comp::Mask(ops, b) => json!({"k": k, "ops": syms(ops), "body": comp(b)}),
        Comp::StrBuiltin(b, args) => json!({"k": k, "tag": b.hash_tag(), "args": values(args)}),
        Comp::WithReuse { token, freed, body } => {
            json!({"k": k, "token": token.as_str(), "freed": value(freed), "body": comp(body)})
        }
        Comp::Reuse(tok, v) => json!({"k": k, "token": tok.as_str(), "v": value(v)}),
        Comp::RefSet(a, b) | Comp::InitAt(a, b) => json!({"k": k, "a": value(a), "b": value(b)}),
    }
}

/// One definition's identity inputs: the Core the hasher walks, the dictionary
/// arity it prefixes, and the out-of-Core metadata it folds in.
fn def(f: &CoreFn, meta: &str) -> J {
    json!({
        "name": f.name.as_str(),
        "params": syms(&f.params),
        "dictArity": f.dict_arity,
        "meta": meta,
        "body": comp(&f.body),
    })
}

/// Serialize the identity inputs of `defs`, with the recursive-group partition
/// they are hashed in and the content hashes of the external definitions they
/// reference.
///
/// `meta_of` supplies each definition's metadata string (the rendering
/// [`super::hash::hash_program`] receives). `groups` is the strongly-connected
/// partition in callee-before-caller order, the unit
/// [`super::hash::hash_group`] hashes and therefore an identity input in its own
/// right, not something a reader is expected to re-derive. `deps` maps every
/// referenced symbol defined outside `defs` to its content hash; a symbol in
/// neither list is a leaf the hash commits to by name, exactly as the encoder
/// treats it.
pub fn core_identity_json(
    defs: &[&CoreFn],
    meta_of: impl Fn(Sym) -> String,
    groups: &[Vec<Sym>],
    deps: &[(Sym, Digest)],
    compiler: &str,
) -> String {
    let doc = json!({
        "schema": IDENTITY_SCHEMA,
        "compiler": compiler,
        "defs": J::Array(defs.iter().map(|f| def(f, &meta_of(f.name))).collect()),
        "groups": J::Array(groups.iter().map(|g| syms(g)).collect()),
        "deps": J::Array(
            deps.iter()
                .map(|(s, h)| json!({"name": s.as_str(), "hash": h.to_string()}))
                .collect(),
        ),
    });
    serde_json::to_string_pretty(&doc).unwrap_or_default()
}
