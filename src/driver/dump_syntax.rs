//! The two versioned syntax seams: `dump syntax-tokens` and `dump surface-syntax`.
//!
//! Each is a deterministic, self-contained JSON export of what the lexer and
//! parser produce for one source file, the boundary a Prism-written lexer,
//! layout pass, or parser is diffed against. `syntax-tokens` carries the raw
//! token stream (post interpolation splitting, trivia stripped), the
//! post-layout stream the grammar actually consumes (virtual `v{`/`v}`/`v;`
//! tokens included, the synthetic head opener already spent), and the trivia
//! events. `surface-syntax` carries the semantic surface AST as one ordered
//! item list, reconstructed by declaration span so the internal family-vector
//! organization of [`Program`] never becomes public schema.
//!
//! Both envelopes embed the exact source text and its digest; every span is a
//! half-open byte range into that embedded text, so a persisted artifact needs
//! no external file. Token kinds use [`Token::wire_name`], the one canonical
//! vocabulary shared with the grammar's terminal aliases. Empty collections and
//! default flags are omitted, so a plain program stays small and a reader
//! treats absence as empty/default. Node ids are identity, not content, and are
//! never emitted; the parse-sugar bit is emitted as `synth` only when set.

use marginalia::{BuiltinKind, Trivia, TriviaTable};
use serde::Serialize;
use serde_json::{json, Map, Value};

use crate::core::hash::hex;
use crate::error::{Error, LexError, ParseError, SourceMap};
use crate::lex::{lex, lex_raw, LexSpanned};
use crate::parse::parse;
use crate::syntax::ast::{
    AliasDecl, Arm, CanonicalDecl, CatchArm, ClassDecl, Constraint, ConvDir, Converter, Ctor,
    CtorShape, DataDecl, Decl, EffLabel, EffOp, EffectDecl, ErrorDecl, Expr, HandlerArm,
    HandlerMode, ImportDecl, InstanceDecl, Kind, Marker, Migration, MigrationDir, MigrationRoute,
    PathOp, PathStep, Pattern, PatternDecl, Program, Qualifier, Row, Rung, RungField, SExpr, Span,
    StableDecl, Suffix, Sugar, SugarArm, SynonymDecl, Total, Ty, S,
};

use super::dump::COMPILER_VERSION;

// The versioned schema tags heading the two syntax seams. Self-describing and
// versioned like the front-end seams; bump on any incompatible shape change.
pub(super) const SYNTAX_TOKENS_SCHEMA: &str = "prism-syntax-tokens-v1";
pub(super) const SURFACE_SYNTAX_SCHEMA: &str = "prism-surface-syntax-v1";

// The token-stream envelope: the embedded source, the raw and post-layout
// streams, and the trivia events, in stream order.
#[derive(Serialize)]
struct SyntaxTokens {
    schema: &'static str,
    compiler: &'static str,
    source: SourceInfo,
    raw: Vec<TokenRow>,
    parse: Vec<TokenRow>,
    trivia: Vec<TriviaRow>,
}

// The surface-AST envelope: the embedded source and the ordered item list.
#[derive(Serialize)]
struct SurfaceSyntax {
    schema: &'static str,
    compiler: &'static str,
    source: SourceInfo,
    items: Vec<Value>,
}

// The embedded source: exact text plus its digest, the identity every span
// indexes into.
#[derive(Serialize)]
struct SourceInfo {
    digest: String,
    text: String,
}

#[derive(Serialize)]
struct TokenRow {
    kind: &'static str,
    span: [usize; 2],
    #[serde(skip_serializing_if = "Option::is_none")]
    value: Option<String>,
}

#[derive(Serialize)]
struct TriviaRow {
    kind: &'static str,
    span: [usize; 2],
}

/// Render the `syntax-tokens` seam for one source file. The input may carry
/// the prepended prelude; the artifact commits to the user's own file, so
/// spans are user-relative and no prelude text enters the bytes.
///
/// # Errors
/// Fails on lex errors: a malformed input refuses the whole export rather than
/// yielding a partial artifact.
pub(super) fn syntax_tokens(src: &str) -> Result<String, Error> {
    let base = SourceMap::new(src).prelude_len();
    let src = &src[base..];
    let (raw, trivia) = lex_raw(src).map_err(|e| rebase_lex(&e, base))?;
    let (post, _) = lex(src).map_err(|e| rebase_lex(&e, base))?;
    let doc = SyntaxTokens {
        schema: SYNTAX_TOKENS_SCHEMA,
        compiler: COMPILER_VERSION,
        source: source_info(src),
        raw: token_rows(&raw),
        parse: token_rows(&post),
        trivia: trivia_rows(&trivia),
    };
    Ok(serde_json::to_string_pretty(&doc).unwrap_or_default())
}

/// Render the `surface-syntax` seam for one source file. The input may carry
/// the prepended prelude; the artifact commits to the user's own file, so
/// spans are user-relative and no prelude declarations enter the item list.
///
/// # Errors
/// Fails on lex or parse errors: a malformed input refuses the whole export
/// rather than yielding a partial artifact.
pub(super) fn surface_syntax(src: &str) -> Result<String, Error> {
    let base = SourceMap::new(src).prelude_len();
    let src = &src[base..];
    let program = parse(src).map_err(|e| rebase_parse(e, base))?.program;
    let doc = SurfaceSyntax {
        schema: SURFACE_SYNTAX_SCHEMA,
        compiler: COMPILER_VERSION,
        source: source_info(src),
        items: items(&program),
    };
    Ok(serde_json::to_string_pretty(&doc).unwrap_or_default())
}

// The seams lex/parse the user slice, so their error spans are user-relative;
// the caller renders errors against the full prelude-prefixed input. Rebase the
// span onto the full input so the rendered snippet points at the right bytes
// (the message text is already user-relative and stays correct).
const fn rebase_lex(e: &LexError, base: usize) -> LexError {
    match *e {
        LexError::Invalid { offset } => LexError::Invalid {
            offset: offset + base,
        },
        LexError::EmptyHole { offset } => LexError::EmptyHole {
            offset: offset + base,
        },
        LexError::UnterminatedHole { offset } => LexError::UnterminatedHole {
            offset: offset + base,
        },
        LexError::UnterminatedString { offset } => LexError::UnterminatedString {
            offset: offset + base,
        },
        LexError::NumberSeparator { offset } => LexError::NumberSeparator {
            offset: offset + base,
        },
    }
}

fn rebase_parse(e: ParseError, base: usize) -> ParseError {
    match e {
        ParseError::Syntax { span, msg } => ParseError::Syntax {
            span: Span::new(span.start + base, span.end + base),
            msg,
        },
        ParseError::UnexpectedEof => ParseError::UnexpectedEof,
    }
}

fn source_info(src: &str) -> SourceInfo {
    SourceInfo {
        digest: hex(src).to_string(),
        text: src.to_string(),
    }
}

fn token_rows(tokens: &[LexSpanned]) -> Vec<TokenRow> {
    tokens
        .iter()
        .map(|(lo, t, hi)| TokenRow {
            kind: t.wire_name(),
            span: [*lo, *hi],
            value: t.wire_value(),
        })
        .collect()
}

fn trivia_rows(table: &TriviaTable) -> Vec<TriviaRow> {
    table
        .events()
        .iter()
        .map(|e| TriviaRow {
            kind: match &e.trivia {
                Trivia::Comment {
                    kind: BuiltinKind::Line,
                    ..
                } => "comment",
                Trivia::Comment {
                    kind: BuiltinKind::Block,
                    ..
                } => "block-comment",
                Trivia::BlankLine => "blank",
            },
            span: [e.span.start, e.span.end],
        })
        .collect()
}

// -------------------------------------------------------------------------
// Surface items
// -------------------------------------------------------------------------

// The ordered item list. `parse` distributes items into per-family vectors, so
// written order is reconstructed by sorting on each declaration's span start
// (top-level spans are disjoint). Visibility and deprecation live in the
// program's name-keyed side sets and are re-attached to the owning item here.
fn items(p: &Program) -> Vec<Value> {
    let mut rows: Vec<(usize, Value)> = Vec::new();
    for i in &p.imports {
        rows.push((i.span.start, import_item(i)));
    }
    for d in &p.types {
        rows.push((d.span.start, named(p, &d.name, data_item(d))));
    }
    for d in &p.effects {
        rows.push((d.span.start, named(p, &d.name, effect_item(d))));
    }
    for d in &p.errors {
        rows.push((d.span.start, named(p, &d.name, error_item(d))));
    }
    for d in &p.aliases {
        rows.push((d.span.start, named(p, &d.name, alias_item(d))));
    }
    for d in &p.synonyms {
        rows.push((d.span.start, named(p, &d.name, synonym_item(d))));
    }
    for d in &p.classes {
        rows.push((d.span.start, named(p, &d.name, class_item(d))));
    }
    for d in &p.instances {
        rows.push((d.span.start, instance_item(d)));
    }
    for d in &p.canonicals {
        rows.push((d.span.start, canonical_item(d)));
    }
    for d in &p.patterns {
        rows.push((d.span.start, named(p, &d.name, pattern_item(d))));
    }
    for d in &p.stable {
        rows.push((d.span.start, named(p, &d.name, stable_item(d))));
    }
    for d in &p.fns {
        let kind = if d.konst { "const" } else { "fn" };
        rows.push((d.span.start, named(p, &d.name, decl_value(d, kind))));
    }
    for d in &p.logic_fns {
        rows.push((d.span.start, named(p, &d.name, decl_value(d, "logic-fn"))));
    }
    rows.sort_by_key(|(lo, _)| *lo);
    rows.into_iter().map(|(_, v)| v).collect()
}

// Re-attach a named item's visibility and deprecation suggestion.
fn named(p: &Program, name: &str, mut v: Value) -> Value {
    let Some(o) = v.as_object_mut() else {
        return v;
    };
    if p.opaques.contains(name) {
        o.insert("vis".into(), json!("opaque"));
    } else if p.exports.contains(name) {
        o.insert("vis".into(), json!("pub"));
    }
    if let Some(msg) = p.deprecated.get(name) {
        o.insert("deprecated".into(), json!(msg));
    }
    v
}

// An object carrying its node kind; every AST encoder starts here.
fn obj(kind: &str) -> Map<String, Value> {
    let mut m = Map::new();
    m.insert("kind".into(), json!(kind));
    m
}

fn sp(s: Span) -> Value {
    json!([s.start, s.end])
}

fn put(m: &mut Map<String, Value>, key: &str, v: Value) {
    m.insert(key.into(), v);
}

// Insert a list field, omitted when empty.
fn put_list(m: &mut Map<String, Value>, key: &str, vs: Vec<Value>) {
    if !vs.is_empty() {
        put(m, key, Value::Array(vs));
    }
}

fn put_strs(m: &mut Map<String, Value>, key: &str, ss: &[String]) {
    if !ss.is_empty() {
        put(m, key, json!(ss));
    }
}

fn put_flag(m: &mut Map<String, Value>, key: &str, set: bool) {
    if set {
        put(m, key, json!(true));
    }
}

fn import_item(i: &ImportDecl) -> Value {
    let mut m = obj("import");
    put(&mut m, "path", json!(i.path));
    if let Some(a) = &i.alias {
        put(&mut m, "alias", json!(a));
    }
    if let Some(ns) = &i.names {
        put(&mut m, "names", json!(ns));
    }
    put_flag(&mut m, "glob", i.glob);
    put_flag(&mut m, "reexport", i.reexport);
    put(&mut m, "span", sp(i.span));
    Value::Object(m)
}

fn data_item(d: &DataDecl) -> Value {
    let mut m = obj(if d.newtype { "newtype" } else { "data" });
    put(&mut m, "name", json!(d.name));
    put_strs(&mut m, "params", &d.params);
    put_list(
        &mut m,
        "param_kinds",
        d.param_kinds.iter().map(kind_value).collect(),
    );
    put_list(&mut m, "ctors", d.ctors.iter().map(ctor_value).collect());
    put_list(
        &mut m,
        "deriving",
        d.deriving
            .iter()
            .map(|(name, span)| json!({"name": name, "span": sp(*span)}))
            .collect(),
    );
    put(&mut m, "span", sp(d.span));
    Value::Object(m)
}

fn ctor_value(c: &Ctor) -> Value {
    let mut m = Map::new();
    put(&mut m, "name", json!(c.name));
    match c.shape() {
        CtorShape::Positional(args) => {
            put_list(&mut m, "args", args.iter().map(ty_value).collect());
        }
        CtorShape::Record(fields) => {
            put(
                &mut m,
                "fields",
                Value::Array(
                    fields
                        .iter()
                        .map(|(name, t)| json!({"name": name, "ty": ty_value(t)}))
                        .collect(),
                ),
            );
        }
    }
    Value::Object(m)
}

fn effect_item(d: &EffectDecl) -> Value {
    let mut m = obj("effect");
    put(&mut m, "name", json!(d.name));
    put_strs(&mut m, "params", &d.params);
    put_list(&mut m, "ops", d.ops.iter().map(eff_op).collect());
    put(&mut m, "span", sp(d.span));
    Value::Object(m)
}

fn eff_op(op: &EffOp) -> Value {
    let mut m = Map::new();
    put(&mut m, "name", json!(op.name));
    put_list(&mut m, "params", op.params.iter().map(ty_value).collect());
    put(&mut m, "ret", ty_value(&op.ret));
    if !op.grade.is_default() {
        put(&mut m, "grade", json!(op.grade.word()));
    }
    Value::Object(m)
}

fn error_item(d: &ErrorDecl) -> Value {
    let mut m = obj("error");
    put(&mut m, "name", json!(d.name));
    put_list(&mut m, "params", d.params.iter().map(ty_value).collect());
    put(&mut m, "span", sp(d.span));
    Value::Object(m)
}

fn alias_item(d: &AliasDecl) -> Value {
    let mut m = obj("effect-alias");
    put(&mut m, "name", json!(d.name));
    put_list(&mut m, "labels", d.labels.iter().map(eff_label).collect());
    put(&mut m, "span", sp(d.span));
    Value::Object(m)
}

fn synonym_item(d: &SynonymDecl) -> Value {
    let mut m = obj("type-synonym");
    put(&mut m, "name", json!(d.name));
    put_strs(&mut m, "params", &d.params);
    put(&mut m, "ty", ty_value(&d.ty));
    put(&mut m, "span", sp(d.span));
    Value::Object(m)
}

fn class_item(d: &ClassDecl) -> Value {
    let mut m = obj("class");
    put(&mut m, "name", json!(d.name));
    put(&mut m, "param", json!(d.param));
    put_strs(&mut m, "supers", &d.supers);
    put_list(
        &mut m,
        "methods",
        d.methods
            .iter()
            .map(|(name, t)| json!({"name": name, "ty": ty_value(t)}))
            .collect(),
    );
    put(&mut m, "span", sp(d.span));
    Value::Object(m)
}

fn instance_item(d: &InstanceDecl) -> Value {
    let mut m = obj("instance");
    put(&mut m, "name", json!(d.name));
    put(&mut m, "class", json!(d.class));
    put(&mut m, "head", ty_value(&d.head));
    put_list(
        &mut m,
        "context",
        d.context.iter().map(constraint_value).collect(),
    );
    put_list(
        &mut m,
        "methods",
        d.methods.iter().map(|f| decl_value(f, "fn")).collect(),
    );
    put(&mut m, "span", sp(d.span));
    Value::Object(m)
}

fn canonical_item(d: &CanonicalDecl) -> Value {
    let mut m = obj("canonical");
    put(&mut m, "class", json!(d.class));
    put(&mut m, "head", ty_value(&d.head));
    put(&mut m, "name", json!(d.name));
    put(&mut m, "span", sp(d.span));
    Value::Object(m)
}

fn pattern_item(d: &PatternDecl) -> Value {
    let mut m = obj("pattern");
    put(&mut m, "name", json!(d.name));
    put_strs(&mut m, "params", &d.params);
    put(&mut m, "for", json!(d.for_ty));
    put(&mut m, "view", expr_value(&d.view));
    if let Some(make) = &d.make {
        put(&mut m, "make", expr_value(make));
    }
    put(&mut m, "span", sp(d.span));
    Value::Object(m)
}

fn stable_item(d: &StableDecl) -> Value {
    let mut m = obj("stable");
    put(&mut m, "name", json!(d.name));
    put_list(&mut m, "rungs", d.rungs.iter().map(rung_value).collect());
    put_list(
        &mut m,
        "converters",
        d.converters.iter().map(converter_value).collect(),
    );
    put_list(
        &mut m,
        "migrations",
        d.migrations.iter().map(migration_value).collect(),
    );
    put(&mut m, "span", sp(d.span));
    Value::Object(m)
}

fn rung_value(r: &Rung) -> Value {
    let mut m = Map::new();
    put(&mut m, "name", json!(r.name));
    if let Some(base) = &r.base {
        put(&mut m, "base", json!(base));
    }
    put_list(&mut m, "fields", r.fields.iter().map(rung_field).collect());
    if let Some(frozen) = &r.frozen {
        put(&mut m, "frozen", json!(frozen));
    }
    put(&mut m, "span", sp(r.span));
    Value::Object(m)
}

fn rung_field(f: &RungField) -> Value {
    let mut m = Map::new();
    put(&mut m, "name", json!(f.name));
    put(&mut m, "ty", ty_value(&f.ty));
    if let Some(default) = &f.default {
        put(&mut m, "default", expr_value(default));
    }
    Value::Object(m)
}

fn converter_value(c: &Converter) -> Value {
    let mut m = Map::new();
    put(
        &mut m,
        "dir",
        json!(match c.dir {
            ConvDir::Upgrade => "upgrade",
            ConvDir::Downgrade => "downgrade",
        }),
    );
    put(&mut m, "from", json!(c.from));
    put(&mut m, "to", json!(c.to));
    put(&mut m, "base", expr_value(&c.base));
    put_list(
        &mut m,
        "overrides",
        c.overrides
            .iter()
            .map(|(name, e)| json!({"name": name, "value": expr_value(e)}))
            .collect(),
    );
    put_strs(&mut m, "drop_loss", &c.drop_loss);
    put(&mut m, "span", sp(c.span));
    Value::Object(m)
}

fn migration_value(mig: &Migration) -> Value {
    let mut m = Map::new();
    put(&mut m, "from", json!(mig.from));
    put(&mut m, "to", json!(mig.to));
    put(
        &mut m,
        "route",
        match &mig.route {
            MigrationRoute::Auto => json!("auto"),
            MigrationRoute::Version(v) => json!({
                "upgrade": migration_dir(&v.upgrade),
                "downgrade": migration_dir(&v.downgrade),
            }),
        },
    );
    put(&mut m, "span", sp(mig.span));
    Value::Object(m)
}

fn migration_dir(d: &MigrationDir) -> Value {
    match d {
        MigrationDir::Auto => json!("auto"),
        MigrationDir::Expr(e) => expr_value(e),
    }
}

// -------------------------------------------------------------------------
// Declarations
// -------------------------------------------------------------------------

fn decl_value(d: &Decl, kind: &str) -> Value {
    let mut m = obj(kind);
    put(&mut m, "name", json!(d.name));
    put_list(&mut m, "params", d.params.iter().map(param_value).collect());
    if let Some(ret) = &d.ret {
        put(&mut m, "ret", ty_value(ret));
    }
    if let Some(labels) = &d.eff {
        let mut row = Map::new();
        put(
            &mut row,
            "labels",
            Value::Array(labels.iter().map(eff_label).collect()),
        );
        if let Some(tail) = &d.eff_tail {
            put(&mut row, "tail", json!(tail));
        }
        put(&mut m, "effects", Value::Object(row));
    }
    put_list(
        &mut m,
        "constraints",
        d.constraints.iter().map(constraint_value).collect(),
    );
    put(&mut m, "body", expr_value(&d.body));
    put_list(
        &mut m,
        "wheres",
        d.wheres
            .iter()
            .map(|(name, e)| json!({"name": name, "value": expr_value(e)}))
            .collect(),
    );
    put_list(
        &mut m,
        "requires",
        d.requires.iter().map(expr_value).collect(),
    );
    put_list(
        &mut m,
        "ensures",
        d.ensures
            .iter()
            .map(|(binder, e)| json!({"binder": binder, "expr": expr_value(e)}))
            .collect(),
    );
    if let Some(measure) = &d.decreases {
        put(&mut m, "decreases", expr_value(measure));
    }
    put_flag(&mut m, "test", d.test);
    match d.total {
        Total::No => {}
        Total::Prove => put(&mut m, "total", json!("prove")),
        Total::Assume => put(&mut m, "total", json!("assume")),
    }
    if let Some(word) = d.fip.keyword() {
        put(&mut m, "fip", json!(word));
    }
    put_flag(&mut m, "replayable", d.replayable);
    put_flag(&mut m, "no_alloc", d.no_alloc);
    put(&mut m, "span", sp(d.span));
    Value::Object(m)
}

fn param_value(p: &crate::syntax::ast::Param) -> Value {
    let mut m = Map::new();
    put(&mut m, "name", json!(p.name));
    if let Some(t) = &p.ty {
        put(&mut m, "ty", ty_value(t));
    }
    put_flag(&mut m, "borrow", p.borrow);
    if let Some(default) = &p.default {
        put(&mut m, "default", expr_value(default));
    }
    Value::Object(m)
}

fn constraint_value(c: &Constraint) -> Value {
    json!({"class": c.class, "ty": ty_value(&c.ty), "span": sp(c.span)})
}

// -------------------------------------------------------------------------
// Types
// -------------------------------------------------------------------------

fn kind_value(k: &Kind) -> Value {
    match k {
        Kind::Type => json!("type"),
        Kind::Row => json!("row"),
        Kind::Nat => json!("nat"),
        Kind::Fun(a, b) => json!({"from": kind_value(a), "to": kind_value(b)}),
    }
}

fn eff_label(l: &EffLabel) -> Value {
    let mut m = Map::new();
    put(&mut m, "name", json!(l.name));
    put_list(&mut m, "args", l.args.iter().map(ty_value).collect());
    Value::Object(m)
}

fn row_value(r: &Row) -> Value {
    let mut m = Map::new();
    match r {
        Row::Empty => put(&mut m, "labels", json!([])),
        Row::Cons(labels, tail) => {
            put(
                &mut m,
                "labels",
                Value::Array(labels.iter().map(eff_label).collect()),
            );
            if let Some(t) = tail {
                put(&mut m, "tail", json!(t));
            }
        }
    }
    Value::Object(m)
}

fn ty_value(t: &Ty) -> Value {
    match t {
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
            let mut m = obj("app");
            put(&mut m, "head", json!(head));
            put_list(&mut m, "args", args.iter().map(ty_value).collect());
            Value::Object(m)
        }
        // Desugar-internal; can never appear in a parse-time type, encoded for
        // totality so a walker over this function needs no unreachable arm.
        Ty::State(n) => json!({"kind": "state", "cell": n}),
        Ty::Forall(vars, body) => {
            json!({"kind": "forall", "vars": vars, "ty": ty_value(body)})
        }
        Ty::Fun(params, row, ret) => {
            let mut m = obj("fun");
            put_list(&mut m, "params", params.iter().map(ty_value).collect());
            put(&mut m, "effects", row_value(row));
            put(&mut m, "ret", ty_value(ret));
            Value::Object(m)
        }
        Ty::Con(name, args) => {
            let mut m = obj("con");
            put(&mut m, "name", json!(name));
            put_list(&mut m, "args", args.iter().map(ty_value).collect());
            Value::Object(m)
        }
        Ty::Tuple(items) => {
            json!({"kind": "tuple", "items": items.iter().map(ty_value).collect::<Vec<_>>()})
        }
        Ty::UnboxedTuple(items) => {
            json!({"kind": "unboxed-tuple", "items": items.iter().map(ty_value).collect::<Vec<_>>()})
        }
        Ty::UnboxedRecord(fields) => json!({
            "kind": "unboxed-record",
            "fields": fields
                .iter()
                .map(|(name, ty)| json!({"name": name, "ty": ty_value(ty)}))
                .collect::<Vec<_>>(),
        }),
        Ty::RowLit(row) => json!({"kind": "row", "row": row_value(row)}),
        Ty::Nat(n) => json!({"kind": "nat", "value": n}),
        Ty::Coeffect(body, row) => json!({
            "kind": "usage",
            "ty": ty_value(body),
            "facts": row.facts().iter().map(|f| f.name()).collect::<Vec<_>>(),
        }),
    }
}

// -------------------------------------------------------------------------
// Expressions
// -------------------------------------------------------------------------

// The spanned wrapper: every expression object carries its span; the
// parse-sugar bit appears as `synth` only when set. Node ids never appear.
fn expr_value(e: &SExpr) -> Value {
    let mut v = expr_node(&e.node);
    if let Some(o) = v.as_object_mut() {
        o.insert("span".into(), sp(e.span));
        if e.synth {
            o.insert("synth".into(), json!(true));
        }
    }
    v
}

#[allow(clippy::too_many_lines)] // one arm per expression form; splitting would scatter the node vocabulary
fn expr_node(e: &Expr) -> Value {
    match e {
        Expr::Int(i) => {
            let mut m = obj("int");
            put(&mut m, "value", json!(i.value.to_string()));
            match i.suffix {
                Suffix::None => {}
                Suffix::I64 => put(&mut m, "suffix", json!("i64")),
                Suffix::U64 => put(&mut m, "suffix", json!("u64")),
            }
            Value::Object(m)
        }
        // The shortest round-trip rendering, as a string: JSON numbers cannot
        // carry every f64 (non-finite values have no literal), and the decoded
        // value must be deterministic byte-for-byte.
        Expr::Float(x) => json!({"kind": "float", "value": format!("{x:?}")}),
        Expr::Char(c) => json!({"kind": "char", "value": c.to_string()}),
        Expr::Bool(b) => json!({"kind": "bool", "value": b}),
        Expr::Unit => json!({"kind": "unit"}),
        Expr::Str(s) => json!({"kind": "str", "value": s}),
        Expr::Var(name) => json!({"kind": "var", "name": name}),
        Expr::Hole(name) => json!({"kind": "hole", "name": name}),
        Expr::Bin(op, lhs, rhs) => json!({
            "kind": "bin",
            "op": op.spelling(),
            "lhs": expr_value(lhs),
            "rhs": expr_value(rhs),
        }),
        Expr::Neg(a) => json!({"kind": "neg", "expr": expr_value(a)}),
        Expr::If(c, t, f) => json!({
            "kind": "if",
            "cond": expr_value(c),
            "then": expr_value(t),
            "else": expr_value(f),
        }),
        Expr::Let(name, value, body) => json!({
            "kind": "let",
            "name": name,
            "value": expr_value(value),
            "body": expr_value(body),
        }),
        Expr::Lam(params, body) => {
            let mut m = obj("lam");
            put_list(&mut m, "params", params.iter().map(param_value).collect());
            put(&mut m, "body", expr_value(body));
            Value::Object(m)
        }
        Expr::Call(head, args) => {
            let mut m = obj("call");
            put(&mut m, "head", expr_value(head));
            put_list(&mut m, "args", args.iter().map(expr_value).collect());
            Value::Object(m)
        }
        Expr::Pipe(lhs, rhs) => {
            json!({"kind": "pipe", "lhs": expr_value(lhs), "rhs": expr_value(rhs)})
        }
        Expr::Match(scrut, arms) => json!({
            "kind": "match",
            "scrutinee": expr_value(scrut),
            "arms": arms.iter().map(arm_value).collect::<Vec<_>>(),
        }),
        Expr::List(items) => json!({
            "kind": "list",
            "items": items.iter().map(expr_value).collect::<Vec<_>>(),
        }),
        Expr::Tuple(items) => json!({
            "kind": "tuple",
            "items": items.iter().map(expr_value).collect::<Vec<_>>(),
        }),
        Expr::FieldAccess(base, name) => {
            json!({"kind": "field", "expr": expr_value(base), "name": name})
        }
        Expr::UnboxedTuple(items) => json!({
            "kind": "unboxed-tuple",
            "items": items.iter().map(expr_value).collect::<Vec<_>>(),
        }),
        Expr::UnboxedRecord(fields) => json!({
            "kind": "unboxed-record",
            "fields": named_exprs(fields),
        }),
        Expr::UnboxedField(base, name) => {
            json!({"kind": "unboxed-field", "expr": expr_value(base), "name": name})
        }
        Expr::RecordCreate(name, fields) => json!({
            "kind": "record",
            "name": name,
            "fields": named_exprs(fields),
        }),
        Expr::RecordUpdate(base, name, fields) => json!({
            "kind": "record-update",
            "base": expr_value(base),
            "name": name,
            "fields": named_exprs(fields),
        }),
        Expr::RecordUpdatePath(base, updates) => json!({
            "kind": "path-update",
            "base": expr_value(base),
            "updates": updates
                .iter()
                .map(|(steps, op)| json!({
                    "path": steps.iter().map(path_step).collect::<Vec<_>>(),
                    "op": path_op(op),
                }))
                .collect::<Vec<_>>(),
        }),
        Expr::Handle(body, arms, mode) => {
            let mut m = obj("handle");
            put(&mut m, "body", expr_value(body));
            put_list(&mut m, "arms", arms.iter().map(handler_arm).collect());
            put_flag(&mut m, "partial", *mode == HandlerMode::Partial);
            Value::Object(m)
        }
        Expr::Mask(effect, body) => {
            json!({"kind": "mask", "effect": effect, "body": expr_value(body)})
        }
        Expr::Inst(base, args) => {
            json!({"kind": "inst", "expr": expr_value(base), "args": args})
        }
        Expr::Index(base, index) => {
            json!({"kind": "index", "expr": expr_value(base), "index": expr_value(index)})
        }
        Expr::IndexSet(base, index, value) => json!({
            "kind": "index-set",
            "expr": expr_value(base),
            "index": expr_value(index),
            "value": expr_value(value),
        }),
        Expr::Ann(base, ty) => {
            json!({"kind": "ann", "expr": expr_value(base), "ty": ty_value(ty)})
        }
        Expr::Marker(m) => json!({
            "kind": "marker",
            "marker": match m {
                Marker::With => "with",
                Marker::Try => "try",
                Marker::Interp => "interp",
            },
        }),
        Expr::Sugar(s) => sugar_node(s),
    }
}

fn named_exprs(fields: &[(String, SExpr)]) -> Vec<Value> {
    fields
        .iter()
        .map(|(name, e)| json!({"name": name, "value": expr_value(e)}))
        .collect()
}

#[allow(clippy::too_many_lines)] // one arm per sugar form; splitting would scatter the node vocabulary
fn sugar_node(s: &Sugar<crate::syntax::ast::Surface>) -> Value {
    match s {
        Sugar::NamedHandle(name, body, arms) => {
            let mut m = obj("named-handle");
            put(&mut m, "name", json!(name));
            put(&mut m, "body", expr_value(body));
            put_list(&mut m, "arms", arms.iter().map(handler_arm).collect());
            Value::Object(m)
        }
        Sugar::VarDecl(name, value, body) => json!({
            "kind": "var-decl",
            "name": name,
            "value": expr_value(value),
            "body": expr_value(body),
        }),
        Sugar::Assign(name, value) => {
            json!({"kind": "assign", "name": name, "value": expr_value(value)})
        }
        Sugar::IndexAssign(base, index, value) => json!({
            "kind": "index-assign",
            "expr": expr_value(base),
            "index": expr_value(index),
            "value": expr_value(value),
        }),
        Sugar::Throw(name, args) => {
            let mut m = obj("throw");
            put(&mut m, "name", json!(name));
            put_list(&mut m, "args", args.iter().map(expr_value).collect());
            Value::Object(m)
        }
        Sugar::TryCatch(body, arms) => json!({
            "kind": "try-catch",
            "body": expr_value(body),
            "arms": arms.iter().map(catch_arm).collect::<Vec<_>>(),
        }),
        Sugar::For(binder, seq, quals, body) => {
            let mut m = obj("for");
            put(&mut m, "binder", json!(binder));
            put(&mut m, "seq", expr_value(seq));
            put_list(&mut m, "quals", quals.iter().map(qualifier).collect());
            put(&mut m, "body", expr_value(body));
            Value::Object(m)
        }
        Sugar::While(Some(cond), body) => json!({
            "kind": "while",
            "cond": expr_value(cond),
            "body": expr_value(body),
        }),
        Sugar::While(None, body) => json!({"kind": "loop", "body": expr_value(body)}),
        Sugar::Break => json!({"kind": "break"}),
        Sugar::Continue => json!({"kind": "continue"}),
        Sugar::Return(value) => json!({"kind": "return", "value": expr_value(value)}),
        Sugar::Comp(head, binder, seq, quals) => {
            let mut m = obj("comprehension");
            put(&mut m, "head", expr_value(head));
            put(&mut m, "binder", json!(binder));
            put(&mut m, "seq", expr_value(seq));
            put_list(&mut m, "quals", quals.iter().map(qualifier).collect());
            Value::Object(m)
        }
        Sugar::Default(body, fallback) => json!({
            "kind": "default",
            "expr": expr_value(body),
            "fallback": expr_value(fallback),
        }),
        Sugar::Transact(body, fallback) => json!({
            "kind": "transact",
            "body": expr_value(body),
            "fallback": expr_value(fallback),
        }),
        Sugar::Probe(name, body) => {
            json!({"kind": "probe", "name": name, "body": expr_value(body)})
        }
        Sugar::OptChain(base, name) => {
            json!({"kind": "opt-chain", "expr": expr_value(base), "name": name})
        }
        Sugar::Range(prefix, end) => json!({
            "kind": "range",
            "prefix": prefix.iter().map(expr_value).collect::<Vec<_>>(),
            "end": expr_value(end),
        }),
        Sugar::Compose(forward, lhs, rhs) => json!({
            "kind": "compose",
            "dir": if *forward { "forward" } else { "backward" },
            "lhs": expr_value(lhs),
            "rhs": expr_value(rhs),
        }),
        Sugar::ReadPath(base, steps) => json!({
            "kind": "read-path",
            "base": expr_value(base),
            "path": steps.iter().map(path_step).collect::<Vec<_>>(),
        }),
    }
}

fn arm_value(a: &Arm) -> Value {
    let mut m = Map::new();
    put(&mut m, "pat", pattern_value(&a.pat));
    if let Some(g) = &a.guard {
        put(&mut m, "guard", expr_value(g));
    }
    put(&mut m, "body", expr_value(&a.body));
    Value::Object(m)
}

fn handler_arm(a: &HandlerArm) -> Value {
    match a {
        HandlerArm::Return(binder, body) => json!({
            "kind": "return",
            "binder": binder,
            "body": expr_value(body),
        }),
        HandlerArm::Op(op, params, resume, body) => json!({
            "kind": "op",
            "op": op,
            "params": params,
            "resume": resume,
            "body": expr_value(body),
        }),
        HandlerArm::Sugar(SugarArm::Once(op, params, body)) => json!({
            "kind": "once",
            "op": op,
            "params": params,
            "body": expr_value(body),
        }),
        HandlerArm::Sugar(SugarArm::Val(name, body)) => json!({
            "kind": "val",
            "name": name,
            "body": expr_value(body),
        }),
        HandlerArm::Sugar(SugarArm::Never(op, params, body)) => json!({
            "kind": "never",
            "op": op,
            "params": params,
            "body": expr_value(body),
        }),
    }
}

fn catch_arm(a: &CatchArm) -> Value {
    let mut m = Map::new();
    put(&mut m, "name", json!(a.name));
    put_strs(&mut m, "binders", &a.binders);
    put(&mut m, "body", expr_value(&a.body));
    put(&mut m, "span", sp(a.span));
    Value::Object(m)
}

fn qualifier(q: &Qualifier) -> Value {
    match q {
        Qualifier::Guard(e) => json!({"kind": "guard", "expr": expr_value(e)}),
        Qualifier::Bind(name, e) => {
            json!({"kind": "bind", "name": name, "value": expr_value(e)})
        }
    }
}

fn path_step(s: &PathStep) -> Value {
    match s {
        PathStep::Field(name) => json!({"kind": "field", "name": name}),
        PathStep::Each => json!({"kind": "each"}),
        PathStep::Case(name) => json!({"kind": "case", "name": name}),
        PathStep::Index(e) => json!({"kind": "index", "expr": expr_value(e)}),
        PathStep::Where(e) => json!({"kind": "where", "expr": expr_value(e)}),
    }
}

fn path_op(op: &PathOp) -> Value {
    match op {
        PathOp::Set(e) => json!({"kind": "set", "expr": expr_value(e)}),
        PathOp::Modify(e) => json!({"kind": "modify", "expr": expr_value(e)}),
    }
}

// -------------------------------------------------------------------------
// Patterns
// -------------------------------------------------------------------------

fn pattern_value(p: &S<Pattern>) -> Value {
    let mut v = pattern_node(&p.node);
    if let Some(o) = v.as_object_mut() {
        o.insert("span".into(), sp(p.span));
        if p.synth {
            o.insert("synth".into(), json!(true));
        }
    }
    v
}

fn pattern_node(p: &Pattern) -> Value {
    match p {
        Pattern::Wild => json!({"kind": "wild"}),
        Pattern::Var(name) => json!({"kind": "var", "name": name}),
        Pattern::Int(i) => {
            let mut m = obj("int");
            put(&mut m, "value", json!(i.value.to_string()));
            match i.suffix {
                Suffix::None => {}
                Suffix::I64 => put(&mut m, "suffix", json!("i64")),
                Suffix::U64 => put(&mut m, "suffix", json!("u64")),
            }
            Value::Object(m)
        }
        Pattern::Float(x) => json!({"kind": "float", "value": format!("{x:?}")}),
        Pattern::Char(c) => json!({"kind": "char", "value": c.to_string()}),
        Pattern::Bool(b) => json!({"kind": "bool", "value": b}),
        Pattern::Ctor(name, args) => {
            let mut m = obj("ctor");
            put(&mut m, "name", json!(name));
            put_list(&mut m, "args", args.iter().map(pattern_value).collect());
            Value::Object(m)
        }
        Pattern::Tuple(items) => json!({
            "kind": "tuple",
            "items": items.iter().map(pattern_value).collect::<Vec<_>>(),
        }),
        Pattern::Record(name, fields, rest) => {
            let mut m = obj("record");
            put(&mut m, "name", json!(name));
            put_list(
                &mut m,
                "fields",
                fields
                    .iter()
                    .map(|(field, pat)| json!({"name": field, "pat": pattern_value(pat)}))
                    .collect(),
            );
            put_flag(&mut m, "rest", *rest);
            Value::Object(m)
        }
    }
}
