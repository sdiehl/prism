use std::fs;
use std::path::Path;

const SOURCE: &str = "tests/fixtures/typespans/basic.pr";
const GOLDEN: &str = "tests/fixtures/typespans/basic.typespans.json";

fn repo(path: &str) -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(path)
}

fn extract(source: &str) -> prism::TypeSpans {
    let full = prism::with_prelude(source);
    let json = prism::dump("typespans", &full).expect("dump typespans");
    prism::TypeSpans::from_json(&json).expect("valid shared schema")
}

fn span_at<'a>(
    payload: &'a prism::TypeSpans,
    start: usize,
    text: &str,
    level: &str,
) -> &'a prism::TypeSpan {
    payload
        .spans
        .iter()
        .find(|span| {
            span.start == start && span.end == start + text.len() && span.level.tag() == level
        })
        .unwrap_or_else(|| panic!("missing {level} span for `{text}` at byte {start}"))
}

#[test]
fn typespans_fixture_is_canonical_and_semantic() {
    let source = fs::read_to_string(repo(SOURCE)).expect("read typespans source");
    let full = prism::with_prelude(&source);
    let actual = prism::dump("typespans", &full).expect("dump typespans");
    let expected = fs::read_to_string(repo(GOLDEN)).expect("read typespans golden");
    assert_eq!(format!("{actual}\n"), expected);

    let payload = prism::TypeSpans::from_json(&actual).expect("valid shared schema");
    assert_eq!(payload.format, prism::TYPESPANS_FORMAT);
    // Pure spans elide the empty row entirely; only genuinely effectful
    // renderings carry a `!` row.
    assert!(payload
        .spans
        .iter()
        .all(|span| !span.rendered.ends_with("! {}")));
    assert!(payload
        .spans
        .iter()
        .any(|span| span.rendered == "Int ! {Ask}"));
    let plus_one = source.find("plus_one").expect("function name in fixture");
    assert!(payload.spans.iter().any(|span| {
        span.start == plus_one
            && &source[span.start..span.end] == "plus_one"
            && span.rendered == "(Int) -> Int"
    }));
    let parameter = source.find("x : Int").expect("parameter in fixture");
    assert!(payload.spans.iter().any(|span| {
        span.start == parameter && &source[span.start..span.end] == "x" && span.rendered == "Int"
    }));
    assert!(payload
        .spans
        .windows(2)
        .any(|pair| { pair[0].start <= pair[1].start && pair[0].end >= pair[1].end }));

    let again = prism::dump("typespans", &full).expect("second typespans dump");
    assert_eq!(again, actual, "typespans extraction must be byte-stable");
}

#[test]
fn typespans_decoder_refuses_crossing_ranges() {
    let crossing = r#"{"format":"prism-typespans-v1","spans":[{"start":0,"end":4,"type":"Int ! {}"},{"start":2,"end":6,"type":"Int ! {}"}]}"#;
    let error = prism::TypeSpans::from_json(crossing).expect_err("crossing ranges must fail");
    assert!(error.contains("crossing typespans"));
}

#[test]
fn handler_and_catch_clause_lhs_are_independently_pointable() {
    let state = fs::read_to_string(repo("docs/examples/eff_state.pr")).expect("read state example");
    let state_spans = extract(&state);

    let get = state.find("get() resume k").expect("get clause");
    assert_eq!(
        span_at(&state_spans, get, "get()", "effect").rendered,
        "get() : Int"
    );
    let get_k = get + "get() resume ".len();
    let get_k_span = span_at(&state_spans, get_k, "k", "coeffect");
    assert!(get_k_span.rendered.starts_with("(Int) ->"));
    assert!(get_k_span.rendered.ends_with("declared resumption: many"));
    let state_param = state.find("\\(_s)").expect("unused lambda parameter") + 2;
    assert_eq!(span_at(&state_spans, state_param, "_s", "").rendered, "Int");

    let put = state.find("put(s2) resume k").expect("put clause");
    let put_head = span_at(&state_spans, put, "put(s2)", "effect");
    assert_eq!(put_head.rendered, "put(Int) : Unit");
    let s2 = put + "put(".len();
    assert_eq!(
        span_at(&state_spans, s2, "s2", "patternvar").rendered,
        "Int"
    );
    let put_k = put + "put(s2) resume ".len();
    assert!(span_at(&state_spans, put_k, "k", "coeffect")
        .rendered
        .starts_with("(Unit) ->"));

    let return_arm = state.find("return r =>").expect("return clause");
    assert_eq!(
        span_at(
            &state_spans,
            return_arm + "return ".len(),
            "r",
            "patternvar"
        )
        .rendered,
        "Int"
    );

    let errors =
        fs::read_to_string(repo("docs/examples/failure_stack.pr")).expect("read errors example");
    let error_spans = extract(&errors);
    for (head, binder, ty) in [
        ("NotFound(_k)", "_k", "String"),
        ("Malformed(_s)", "_s", "String"),
        ("Timeout(_ms)", "_ms", "Int"),
    ] {
        let start = errors.find(head).expect("catch clause");
        let effect = span_at(&error_spans, start, head, "effect");
        assert!(effect.rendered.starts_with("never "));
        assert_eq!(
            span_at(
                &error_spans,
                start + head.find(binder).expect("binder in clause"),
                binder,
                "patternvar"
            )
            .rendered,
            ty
        );
    }
}

#[test]
fn builtin_io_effect_annotation_is_pointable() {
    let source = fs::read_to_string(repo("examples/os.pr")).expect("read IO example");
    let spans = extract(&source);
    let annotation = source.find("! {IO}").expect("IO effect annotation");
    assert_eq!(
        span_at(&spans, annotation + "! {".len(), "IO", "effect").rendered,
        "IO; builtin effect"
    );
}

#[test]
fn pattern_synonyms_wildcards_and_prefixed_binders_are_pointable() {
    let source = fs::read_to_string(repo("docs/examples/pattern_syn_sugar.pr"))
        .expect("read pattern synonym example");
    let spans = extract(&source);

    let declaration = source
        .find("pattern OnXAxis(x)")
        .expect("pattern declaration");
    assert_eq!(
        span_at(&spans, declaration + "pattern ".len(), "OnXAxis", "").rendered,
        "(Int) -> Vec2"
    );
    assert_eq!(
        span_at(
            &spans,
            declaration + "pattern OnXAxis(".len(),
            "x",
            "patternvar"
        )
        .rendered,
        "Int"
    );

    let use_site = source.rfind("OnXAxis(x)").expect("pattern use");
    assert_eq!(
        span_at(&spans, use_site, "OnXAxis", "").rendered,
        "(Int) -> Vec2"
    );
    let wildcard = source.find("    _ =>").expect("wildcard pattern") + 4;
    assert_eq!(
        span_at(&spans, wildcard, "_", "patternvar").rendered,
        "Vec2"
    );
}

#[test]
fn stable_ladder_surface_and_unused_pattern_binder_are_pointable() {
    let source = fs::read_to_string(repo("docs/examples/stable.pr")).expect("read stable example");
    let spans = extract(&source);

    let stable = source.find("stable Save").expect("stable declaration");
    assert_eq!(
        span_at(&spans, stable + "stable ".len(), "Save", "typelevel").rendered,
        "Save : Type"
    );
    let v1 = source.find("V1 =").expect("V1 rung");
    assert_eq!(
        span_at(&spans, v1, "V1", "typelevel").rendered,
        "Save.V1 : Type"
    );
    let fog = source.find("fog: Int").expect("stable field");
    assert_eq!(span_at(&spans, fog, "fog", "").rendered, "Int");
    let default = source.find("30 }").expect("stable default");
    assert_eq!(span_at(&spans, default, "30", "").rendered, "Int");

    let rest = source.find("_rest").expect("unused prefixed binder");
    assert_eq!(
        span_at(&spans, rest, "_rest", "patternvar").rendered,
        "Wire.Bytes"
    );
}

#[test]
fn stable_migration_rung_references_are_pointable() {
    let source =
        fs::read_to_string(repo("docs/examples/player_manual.pr")).expect("read player manual");
    let spans = extract(&source);

    // A predecessor rung named in a migration row hovers as its dotted rung type.
    let row = source.find("V1 -> V2").expect("migration row");
    assert_eq!(
        span_at(&spans, row, "V1", "typelevel").rendered,
        "PlayerManual.V1 : Type"
    );
    // The current rung named as a route target hovers as the bare type name.
    let to_current = source.find("V2 -> V3").expect("route to current");
    let target = to_current + "V2 -> ".len();
    assert_eq!(
        span_at(&spans, target, "V3", "typelevel").rendered,
        "PlayerManual : Type"
    );
}

#[test]
fn logic_expression_spans_are_a_distinct_level() {
    // Contract and `logic fn` subexpressions are sort-checked separately and
    // erased before Core, so they carry the dedicated `logic` level. `extract`
    // validates the whole document through `from_json`, so this also proves the
    // logic spans nest cleanly with the body spans and never cross them.
    let source = "\
logic fn nonneg(x : Int) : Bool = x >= 0

fn f(x : Int) : Int
  requires x >= 0
  ensures |r| nonneg(r)
  = x + 1
";
    let spans = extract(source);
    assert!(
        spans.spans.iter().any(|s| s.level.tag() == "logic"),
        "a contract program has logic-level spans"
    );
    // The `logic fn` body `x >= 0` is a Bool logical expression.
    let body = source.find("x >= 0").expect("logic fn body");
    assert_eq!(span_at(&spans, body, "x >= 0", "logic").rendered, "Bool");
    // The `requires` clause is Bool; its `x` operand is an Int logical value.
    let clause = source.find("requires x >= 0").expect("requires clause") + "requires ".len();
    assert_eq!(span_at(&spans, clause, "x >= 0", "logic").rendered, "Bool");
    // The runtime body keeps its ordinary value spans, unaffected.
    let rt = source.find("= x + 1").expect("body") + "= ".len();
    assert_eq!(span_at(&spans, rt, "x + 1", "").rendered, "Int");
}
