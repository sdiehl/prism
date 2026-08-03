//! Frozen Rust `TypeSigParser` direct-entry adapter.
//!
//! This file is both included by the integration test and compiled as a tiny
//! standalone binary by the acceptance driver against the detached oracle's
//! already-built `prism_syntax` rlib. Its output is the existing
//! surface-syntax type-subtree vocabulary, never `Debug` text.

use std::fs;
use std::path::Path;

use prism_syntax::ast::{EffLabel, Row, Ty};
use prism_syntax::lex::lex_raw;
use prism_syntax::TypeSigParser;
use serde_json::{json, Map, Value};

fn put(map: &mut Map<String, Value>, key: &str, value: Value) {
    map.insert(key.to_string(), value);
}

fn put_list(map: &mut Map<String, Value>, key: &str, values: Vec<Value>) {
    if !values.is_empty() {
        put(map, key, Value::Array(values));
    }
}

fn object(kind: &str) -> Map<String, Value> {
    let mut map = Map::new();
    put(&mut map, "kind", json!(kind));
    map
}

fn effect_label(label: &EffLabel) -> Value {
    let mut map = Map::new();
    put(&mut map, "name", json!(label.name));
    put_list(
        &mut map,
        "args",
        label.args.iter().map(type_projection).collect(),
    );
    Value::Object(map)
}

fn row_projection(row: &Row) -> Value {
    let mut map = Map::new();
    match row {
        Row::Empty => put(&mut map, "labels", json!([])),
        Row::Cons(labels, tail) => {
            put(
                &mut map,
                "labels",
                Value::Array(labels.iter().map(effect_label).collect()),
            );
            if let Some(tail) = tail {
                put(&mut map, "tail", json!(tail));
            }
        }
    }
    Value::Object(map)
}

pub(crate) fn type_projection(ty: &Ty) -> Value {
    match ty {
        Ty::Int => json!({"kind": "int"}),
        Ty::I64 => json!({"kind": "i64"}),
        Ty::U64 => json!({"kind": "u64"}),
        Ty::Bool => json!({"kind": "bool"}),
        Ty::Unit => json!({"kind": "unit"}),
        Ty::Float => json!({"kind": "float"}),
        Ty::Char => json!({"kind": "char"}),
        Ty::Str => json!({"kind": "str"}),
        Ty::Var(name) => json!({"kind": "var", "name": name}),
        Ty::App(head, args) => {
            let mut map = object("app");
            put(&mut map, "head", json!(head));
            put_list(&mut map, "args", args.iter().map(type_projection).collect());
            Value::Object(map)
        }
        Ty::State(cell) => json!({"kind": "state", "cell": cell}),
        Ty::Forall(vars, body) => {
            json!({"kind": "forall", "vars": vars, "ty": type_projection(body)})
        }
        Ty::Fun(params, effects, ret) => {
            let mut map = object("fun");
            put_list(
                &mut map,
                "params",
                params.iter().map(type_projection).collect(),
            );
            put(&mut map, "effects", row_projection(effects));
            put(&mut map, "ret", type_projection(ret));
            Value::Object(map)
        }
        Ty::Con(name, args) => {
            let mut map = object("con");
            put(&mut map, "name", json!(name));
            put_list(&mut map, "args", args.iter().map(type_projection).collect());
            Value::Object(map)
        }
        Ty::Tuple(items) => {
            json!({"kind": "tuple", "items": items.iter().map(type_projection).collect::<Vec<_>>()})
        }
        Ty::UnboxedTuple(items) => {
            json!({"kind": "unboxed-tuple", "items": items.iter().map(type_projection).collect::<Vec<_>>()})
        }
        Ty::UnboxedRecord(fields) => json!({
            "kind": "unboxed-record",
            "fields": fields
                .iter()
                .map(|(name, ty)| json!({"name": name, "ty": type_projection(ty)}))
                .collect::<Vec<_>>(),
        }),
        Ty::RowLit(row) => json!({"kind": "row", "row": row_projection(row)}),
        Ty::Nat(value) => json!({"kind": "nat", "value": value}),
        Ty::Coeffect(body, row) => json!({
            "kind": "usage",
            "ty": type_projection(body),
            "facts": row.facts().iter().map(|fact| fact.name()).collect::<Vec<_>>(),
        }),
    }
}

pub(crate) fn parse_projection(fragment: &str) -> Value {
    let (tokens, _) = lex_raw(fragment).expect("direct TypeSig fragment must lex");
    let ty = TypeSigParser::new()
        .parse(tokens)
        .expect("direct TypeSig fragment must parse completely");
    type_projection(&ty)
}

pub(crate) fn check_committed_receipt(root: &Path) {
    let path = root.join("tests/fixtures/parser/compaction/entries/rust-typesig.receipt.json");
    let receipt: Value =
        serde_json::from_str(&fs::read_to_string(&path).expect("read Rust entry receipt"))
            .expect("decode Rust entry receipt");
    assert_eq!(
        receipt["schema"],
        "prism-parser-compaction-entry-receipt-v1"
    );
    assert_eq!(receipt["entry_id"], "rust.TypeSigParser");
    let fragment = receipt["fragment"].as_str().expect("receipt fragment");
    assert_eq!(
        parse_projection(fragment),
        receipt["value_projection"],
        "Rust TypeSig direct-entry projection drifted"
    );
    assert_eq!(receipt["outcome"], "accepted");
    assert_eq!(
        receipt["unconsumed_position"],
        receipt["token_slice"]
            .as_array()
            .expect("token slice")
            .len()
    );
}

pub(crate) fn main() {
    let fragment = std::env::args()
        .nth(1)
        .expect("usage: parser-compaction-entry-adapter TYPE");
    println!(
        "{}",
        serde_json::to_string_pretty(&parse_projection(&fragment))
            .expect("encode direct type projection")
    );
}
