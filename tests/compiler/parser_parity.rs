// The parser differential gate: the Prism-owned parser must agree with the
// Rust one on every byte of the surface AST, spans and synth bits included.
//
// The oracle is produced here rather than frozen. `dump surface-syntax` runs
// the Rust parser over a source file, `tests/fixtures/parser/parity.pr` decodes
// that artifact, re-parses the embedded source through `Syntax.Parse`, and
// re-encodes; the witness prints `ok` only when both encodings match exactly.
// Generating the oracle each run means it tracks the tree instead of a pinned
// commit, so the gate cannot certify a parser against a stale grammar.
//
// Three corpora: the committed syntax fixtures, which are the same sources the
// artifact round trip already pins; a focused file of grammar edges that are
// easy to lose in handwritten maintenance; and four deterministic mutation
// matrices generated live, so a parser shaped only around fixtures cannot pass.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::{env, fs, process};

use prism::{
    default_roots, dump_on, interpret_io_on_with_args, step_ruler_on, with_prelude, Config, Root,
};
use serde_json::Value;

use super::fixture_stems;

const SYNTAX_FIXTURES: &str = "tests/fixtures/syntax";
const PARSER_FIXTURES: &str = "tests/fixtures/parser";
const WITNESS: &str = "parity.pr";
const EDGES: &str = "edge_parity.pr";
const SELF_PARSE: &str = "self_parse.pr";
const SURFACE_PHASE: &str = "surface-syntax";
const OK: &str = "ok";

// Every syntax-fixture stem whose source the Prism parser is expected to accept
// whole, kept sorted. `parity_covers_every_stem` pins this against the fixture
// directory so a new corpus file cannot silently skip the gate.
const STEMS: [&str; 10] = [
    "classes",
    "contracts",
    "decls",
    "effects",
    "exprs",
    "interp",
    "patterns",
    "roundtrip",
    "stable",
    "types",
];

fn root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

fn fixture(dir: &str) -> PathBuf {
    root().join(dir)
}

fn roots() -> Vec<Root> {
    default_roots(root())
}

// Run the differential witness under an explicit search path, returning its
// output lines or the run's own failure. The search path is a parameter rather
// than a constant because which one the witness runs under is itself something
// the gate has to pin: the modules it imports are shadowable by any directory
// root ahead of the standard library.
fn run_witness(roots: &[Root], args: Vec<String>) -> Result<Vec<String>, String> {
    let src = fs::read_to_string(fixture(PARSER_FIXTURES).join(WITNESS))
        .expect("differential witness source");
    let full = with_prelude(&src);
    let mut sink = Vec::new();
    interpret_io_on_with_args(
        &full,
        roots,
        &mut sink,
        &mut &b""[..],
        &Config::from_env(),
        args,
    )
    .map_err(|error| error.to_string())?;
    Ok(String::from_utf8(sink)
        .expect("utf8 witness output")
        .lines()
        .filter(|line| !line.is_empty())
        .map(str::to_string)
        .collect())
}

// The argument vector the witness reads: one surface artifact and one mismatch
// path per comparison, in order.
fn witness_args(pairs: &[(&Path, &Path)]) -> Vec<String> {
    pairs
        .iter()
        .flat_map(|(artifact, mismatch)| {
            [
                artifact.display().to_string(),
                mismatch.display().to_string(),
            ]
        })
        .collect()
}

// Run the differential witness once over surface-artifact/mismatch-path pairs.
// One verdict line is returned per pair, in argument order.
fn parity_pairs(pairs: &[(&Path, &Path)]) -> Vec<String> {
    run_witness(&roots(), witness_args(pairs))
        .unwrap_or_else(|error| panic!("differential witness run: {error}"))
}

// Run the differential witness over one surface artifact and return its verdict
// line. The second path receives the Prism encoding on a mismatch.
fn parity(artifact: &Path, mismatch: &Path) -> String {
    let mut verdicts = parity_pairs(&[(artifact, mismatch)]);
    assert_eq!(verdicts.len(), 1, "one verdict for one surface artifact");
    verdicts.pop().expect("one differential verdict")
}

// Assert that re-parsing a source through the Prism parser reproduces the Rust
// parser's artifact byte for byte.
fn assert_parses_identically(label: &str, artifact: &Path) {
    let mismatch = env::temp_dir().join(format!("prism-parity-{label}.json"));
    let _ = fs::remove_file(&mismatch);
    let verdict = parity(artifact, &mismatch);
    assert_eq!(
        verdict, OK,
        "{label}: the Prism parser must reproduce the Rust parser's surface bytes\n\
         witness said: {verdict}"
    );
}

// The committed goldens are the Rust parser's own output, so they serve as the
// oracle directly.
fn assert_stem_parses_identically(stem: &str) {
    let artifact = fixture(SYNTAX_FIXTURES).join(format!("{stem}.{SURFACE_PHASE}.json"));
    assert!(
        artifact.is_file(),
        "{stem}: missing committed surface golden at {}",
        artifact.display()
    );
    assert_parses_identically(stem, &artifact);
}

macro_rules! stem_parity {
    ($($name:ident => $stem:literal),+ $(,)?) => {
        $(#[test]
        fn $name() {
            assert_stem_parses_identically($stem);
        })+
    };
}

stem_parity! {
    parity_classes => "classes",
    parity_contracts => "contracts",
    parity_decls => "decls",
    parity_effects => "effects",
    parity_exprs => "exprs",
    parity_interp => "interp",
    parity_patterns => "patterns",
    parity_roundtrip => "roundtrip",
    parity_stable => "stable",
    parity_types => "types",
}

// Grammar edges the Rust parser accepts: numeric limits, trailing separators,
// open `elif` chains, and every `?` propagation shape. The oracle is generated
// from the source here, so this file needs no committed artifact beside it.
#[test]
fn parity_grammar_edges() {
    let source_path = fixture(PARSER_FIXTURES).join(EDGES);
    let source = fs::read_to_string(&source_path).expect("edge-case source");
    let artifact = dump_on(SURFACE_PHASE, &source, &roots(), &Config::from_env())
        .expect("Rust parser must accept the edge-case source");
    let path = env::temp_dir().join("prism-parity-edges.surface-syntax.json");
    fs::write(&path, artifact).expect("write generated oracle");
    assert_parses_identically("edge_parity", &path);
}

// A generated lane carries several independently keyed source mutations in one
// program. One witness invocation per lane keeps this a cheap parser gate while
// item-count and key checks prevent an empty or duplicate generator from going
// green.
struct GeneratedLane {
    source: String,
    cases: usize,
    // How many of this lane's cases the parser is expected to tell apart once
    // spans and generated names are folded away. It equals the case count for a
    // lane that varies structure on every axis, and is smaller for one that also
    // varies layout, because indentation is not allowed to reach the tree.
    shapes: usize,
}

fn aggregate_lane(
    label: &str,
    base_key: &str,
    cases: Vec<(String, String)>,
    expected: usize,
    shapes: usize,
) -> GeneratedLane {
    assert_eq!(cases.len(), expected, "{label}: mutation count drift");
    assert!(expected > 1, "{label}: mutation lane is vacuous");

    let keys: BTreeSet<&str> = cases.iter().map(|(key, _)| key.as_str()).collect();
    assert_eq!(keys.len(), expected, "{label}: duplicate mutation key");
    assert!(
        !keys.contains(base_key),
        "{label}: the unmutated base leaked into the lane"
    );
    let sources: BTreeSet<&str> = cases.iter().map(|(_, source)| source.as_str()).collect();
    assert_eq!(
        sources.len(),
        expected,
        "{label}: duplicate source mutation"
    );

    assert!(
        shapes > 0 && shapes <= expected,
        "{label}: {shapes} distinct shapes is not a bound {expected} cases can meet"
    );

    GeneratedLane {
        source: cases.into_iter().map(|(_, source)| source).collect(),
        cases: expected,
        shapes,
    }
}

fn type_mutations() -> GeneratedLane {
    let heads = [
        "Int",
        "List(Int)",
        "(Int, Float)",
        "#(I64, U64)",
        "#{ w : Int, h : Float }",
    ];
    let rows = ["{}", "{Tick}", "{Emit(Int)}", "{Tick, Emit(Int) | e}"];
    let mut cases = Vec::new();
    for head in heads {
        for row in rows {
            let ty = format!("({head}) -> {head} ! {row}");
            let index = cases.len();
            cases.push((ty.clone(), format!("alias TypeMutation{index} = {ty}\n")));
        }
    }
    aggregate_lane("type", "Bool", cases, 20, 20)
}

fn pattern_mutations() -> GeneratedLane {
    let atoms = ["x", "_", "0", "'a'"];
    let shells = ["ctor", "tuple", "list", "record", "or"];
    let mut cases = Vec::new();
    for atom in atoms {
        for shell in shells {
            let pat = match shell {
                "ctor" => format!("Some({atom})"),
                "tuple" => format!("({atom}, _)"),
                "list" => format!("[{atom}, _]"),
                "record" => format!("Point {{ x = {atom}, .. }}"),
                "or" => format!("Some({atom}) | None"),
                _ => unreachable!("closed pattern shell matrix"),
            };
            let index = cases.len();
            cases.push((
                format!("{shell}:{atom}"),
                format!(
                    "fn pattern_mutation_{index}(v) =\n  match v of\n    {pat} => 0\n    _ => 1\n"
                ),
            ));
        }
    }
    aggregate_lane("pattern", "ctor:None", cases, 20, 20)
}

fn vertical_mutations() -> GeneratedLane {
    let mut cases = Vec::new();
    for width in [2, 4, 6] {
        let one = " ".repeat(width);
        let two = " ".repeat(width * 2);
        for shape in ["closed-if", "open-if", "match", "try"] {
            let index = cases.len();
            let body = match shape {
                "closed-if" => {
                    format!("{one}if x then\n{two}1\n{one}else\n{two}0\n")
                }
                "open-if" => {
                    format!("{one}if x > 0 then\n{two}1\n{one}elif x < 0 then\n{two}2\n{one}0\n")
                }
                "match" => {
                    format!("{one}match x of\n{two}0 => 1\n{two}_ => 2\n")
                }
                "try" => format!("{one}let y = r?\n{one}y\n"),
                _ => unreachable!("closed vertical shape matrix"),
            };
            cases.push((
                format!("{width}:{shape}"),
                format!("fn vertical_mutation_{index}(x, r) =\n{body}"),
            ));
        }
    }
    aggregate_lane("vertical", "0:inline", cases, 12, 4)
}

fn cross_mutations() -> GeneratedLane {
    let mut cases = Vec::new();
    for ty in ["Int", "List(Int)"] {
        for pat in ["Some(x)", "(x, _)", "Pair(x, _)"] {
            for width in [2, 4] {
                let indent = " ".repeat(width);
                let index = cases.len();
                cases.push((
                    format!("{ty}|{pat}|{width}"),
                    format!(
                        "fn cross_mutation_{index}(v : {ty}, r) : {ty} =\n\
                         {indent}let {pat} = r?\n{indent}v\n"
                    ),
                ));
            }
        }
    }
    aggregate_lane("cross", "Int|_|0", cases, 12, 6)
}

fn json_span(node: &Value, context: &str) -> (usize, usize) {
    let span = node["span"]
        .as_array()
        .unwrap_or_else(|| panic!("{context}: span is not an array"));
    assert_eq!(span.len(), 2, "{context}: span width");
    let bound = |index: usize| {
        let raw = span[index]
            .as_u64()
            .unwrap_or_else(|| panic!("{context}: span[{index}]"));
        usize::try_from(raw).unwrap_or_else(|_| panic!("{context}: span[{index}] overflows"))
    };
    (bound(0), bound(1))
}

fn assert_span_bounds(node: &Value, source_len: usize, path: &str) -> usize {
    match node {
        Value::Object(fields) => {
            let own = usize::from(fields.contains_key("span"));
            if own == 1 {
                let (lo, hi) = json_span(node, path);
                assert!(lo <= hi, "{path}: inverted span [{lo}, {hi})");
                assert!(
                    hi <= source_len,
                    "{path}: span [{lo}, {hi}) exceeds {source_len} bytes"
                );
            }
            own + fields
                .iter()
                .map(|(key, child)| assert_span_bounds(child, source_len, &format!("{path}.{key}")))
                .sum::<usize>()
        }
        Value::Array(items) => items
            .iter()
            .enumerate()
            .map(|(index, child)| {
                assert_span_bounds(child, source_len, &format!("{path}[{index}]"))
            })
            .sum(),
        Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) => 0,
    }
}

// The stand-in for a generated declaration name in a shape comparison.
const LANE_NAME_HOLE: &str = "<lane-name>";

// Whether a string is one of the declaration names a lane generates. Each case
// numbers its own declaration, so the name differs between any two cases of a
// lane whatever the encoder wrote about the construct under test. Folding the
// name away is what keeps the shape comparison from passing on the index alone.
fn is_lane_name(text: &str) -> bool {
    let stem = text.trim_end_matches(|c: char| c.is_ascii_digit());
    stem.len() < text.len() && (stem.ends_with("mutation_") || stem.ends_with("Mutation"))
}

// The encoded node reduced to its structure: spans erased, generated names
// folded. Two cases of one lane sit at different offsets and carry different
// declaration names, so comparing encodings verbatim would hold no matter what
// the encoder recorded. What survives here is only what the parser understood.
fn lane_shape(node: &Value) -> Value {
    match node {
        Value::Object(fields) => Value::Object(
            fields
                .iter()
                .filter(|(key, _)| key.as_str() != "span")
                .map(|(key, child)| (key.clone(), lane_shape(child)))
                .collect(),
        ),
        Value::Array(items) => Value::Array(items.iter().map(lane_shape).collect()),
        Value::String(text) if is_lane_name(text) => Value::String(String::from(LANE_NAME_HOLE)),
        other => other.clone(),
    }
}

fn synth_count(node: &Value) -> usize {
    match node {
        Value::Object(fields) => {
            usize::from(fields.get("synth").and_then(Value::as_bool) == Some(true))
                + fields.values().map(synth_count).sum::<usize>()
        }
        Value::Array(items) => items.iter().map(synth_count).sum(),
        Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) => 0,
    }
}

fn generated_lane_artifact(
    label: &str,
    lane: &GeneratedLane,
    expect_sugar: bool,
) -> (PathBuf, PathBuf) {
    let artifact = dump_on(SURFACE_PHASE, &lane.source, &roots(), &Config::from_env())
        .unwrap_or_else(|error| panic!("{label}: Rust parser rejected a generated lane: {error}"));
    let doc: Value = serde_json::from_str(&artifact)
        .unwrap_or_else(|error| panic!("{label}: generated surface JSON: {error}"));
    assert_eq!(
        doc["source"]["text"].as_str(),
        Some(lane.source.as_str()),
        "{label}: artifact source envelope"
    );
    let items = doc["items"]
        .as_array()
        .unwrap_or_else(|| panic!("{label}: items array"));
    assert_eq!(items.len(), lane.cases, "{label}: one item per mutation");
    let span_count = assert_span_bounds(&doc, lane.source.len(), "$");
    assert!(
        span_count >= lane.cases,
        "{label}: recursive span walk found only {span_count} spans"
    );
    let mut previous = 0;
    for (index, item) in items.iter().enumerate() {
        let (lo, _hi) = json_span(item, &format!("{label}.items[{index}]"));
        assert!(
            lo >= previous,
            "{label}: items leave source order at byte {lo}"
        );
        previous = lo;
    }
    if expect_sugar {
        assert!(
            synth_count(&doc) > 0,
            "{label}: sugar lane contains no synthesized node"
        );
    }

    // What the encoding keeps, counted. Erasing spans and folding the generated
    // declaration names leaves only what the parser understood about each case,
    // so the number of distinct shapes says exactly which axes of the lane are
    // structural. The check fails in both directions and both are real defects:
    // fewer shapes than expected means the encoder dropped a field two cases
    // differed in, and an encoding that loses a field cannot stand in for the
    // tree it encodes; more shapes than expected means indentation reached the
    // tree, and layout must not survive parsing.
    let shapes: BTreeSet<String> = items
        .iter()
        .map(|item| lane_shape(item).to_string())
        .collect();
    assert_eq!(
        shapes.len(),
        lane.shapes,
        "{label}: {} cases encode to {} distinct shapes, expected {}",
        lane.cases,
        shapes.len(),
        lane.shapes
    );

    let path = env::temp_dir().join(format!(
        "prism-parity-{label}-{}.surface-syntax.json",
        process::id()
    ));
    let mismatch = env::temp_dir().join(format!(
        "prism-parity-{label}-{}.mismatch.json",
        process::id()
    ));
    let _ = fs::remove_file(&mismatch);
    fs::write(&path, artifact).expect("write generated mutation oracle");
    (path, mismatch)
}

#[test]
fn parity_generated_mutation_lanes() {
    let labels = [
        "mutation-type",
        "mutation-pattern",
        "mutation-vertical",
        "mutation-cross",
    ];
    let files = [
        generated_lane_artifact(labels[0], &type_mutations(), false),
        generated_lane_artifact(labels[1], &pattern_mutations(), false),
        generated_lane_artifact(labels[2], &vertical_mutations(), true),
        generated_lane_artifact(labels[3], &cross_mutations(), true),
    ];
    let pairs: Vec<(&Path, &Path)> = files
        .iter()
        .map(|(artifact, mismatch)| (artifact.as_path(), mismatch.as_path()))
        .collect();
    let verdicts = parity_pairs(&pairs);

    for (artifact, mismatch) in &files {
        let _ = fs::remove_file(artifact);
        let _ = fs::remove_file(mismatch);
    }
    assert_eq!(
        verdicts.len(),
        labels.len(),
        "one verdict per mutation lane"
    );
    for (label, verdict) in labels.into_iter().zip(verdicts) {
        assert_eq!(
            verdict, OK,
            "{label}: the Prism parser must reproduce the Rust surface bytes"
        );
    }
}

// The bootstrap smoke: `Syntax.Parse` accepts the parser fixtures themselves,
// its own harness included, without the artifact round trip in the way. One
// verdict line per file, each of which must lead with the ok token.
#[test]
fn parity_self_parse() {
    let src = fs::read_to_string(fixture(PARSER_FIXTURES).join(SELF_PARSE))
        .expect("self-parse harness source");
    let full = with_prelude(&src);
    let mut sink = Vec::new();
    let args: Vec<String> = [WITNESS, EDGES, SELF_PARSE]
        .iter()
        .map(|name| fixture(PARSER_FIXTURES).join(name).display().to_string())
        .collect();
    let expected = args.len();
    interpret_io_on_with_args(
        &full,
        &roots(),
        &mut sink,
        &mut &b""[..],
        &Config::from_env(),
        args,
    )
    .unwrap_or_else(|e| panic!("self-parse run: {e}"));
    let out = String::from_utf8(sink).expect("utf8 self-parse output");
    let verdicts: Vec<&str> = out.lines().filter(|l| !l.is_empty()).collect();
    assert_eq!(verdicts.len(), expected, "one verdict per fixture:\n{out}");
    for line in &verdicts {
        assert!(
            line.starts_with(OK),
            "Syntax.Parse rejected a parser fixture: {line}"
        );
    }
}

// The static stem list matches the fixture directory exactly, so adding a
// corpus file without extending the gate is a test failure, not a silent skip.
#[test]
fn parity_covers_every_stem() {
    let suffix = format!(".{SURFACE_PHASE}.json");
    let found = fixture_stems(&fixture(SYNTAX_FIXTURES), &suffix, "mismatch");
    assert_eq!(
        found, STEMS,
        "fixture stems and the static parity list have drifted apart"
    );
}

// Whose parser the gate is actually judging.
//
// Module resolution is first-hit and a directory root precedes the embedded
// standard library, so a file at `<root>/Syntax/Parse.pr` supplies that module
// to everything resolving under that root. The witness imports the front end by
// name, which means the search path it runs under decides which front end the
// comparison certifies. A harness that ever derived its roots from the tree it
// compares would let a file ship the parser that judges it, and the gate would
// be comparing a parser against itself while still printing `ok`.
//
// Two halves, because either alone proves nothing. The substitution is live,
// shown by performing it. And the harness does not expose it, shown by the
// search path it really uses.
const HOSTILE_FIXTURES: &str = "tests/fixtures/parser/hostile";

// One directory per module of the shadow front end, each supplying that module
// and nothing else, so a run that survives names which module failed to matter.
const SHADOWED: [(&str, &str); 3] = [
    ("layout", "Syntax.Layout"),
    ("lex", "Syntax.Lex"),
    ("parse", "Syntax.Parse"),
];

// The family the shadow front end lives in. Guarding the subtree rather than a
// list of module names covers a parser module added later on the day it exists,
// with no second list to keep in step.
const SHADOW_FAMILY: &str = "Syntax";

#[test]
fn parity_front_end_is_compiler_owned() {
    let artifact = fixture(SYNTAX_FIXTURES).join(format!("types.{SURFACE_PHASE}.json"));
    let mismatch = env::temp_dir().join("prism-parity-shadowed.json");
    let _ = fs::remove_file(&mismatch);
    let args = witness_args(&[(artifact.as_path(), mismatch.as_path())]);

    for (dir, module) in SHADOWED {
        let shadowed = default_roots(&fixture(HOSTILE_FIXTURES).join(dir));
        let outcome = run_witness(&shadowed, args.clone());
        assert!(
            outcome.is_err(),
            "a root supplying {module} must decide which front end the witness \
             runs, and this one did not: {outcome:?}"
        );
    }

    for root in roots() {
        let Root::Dir(dir) = root else { continue };
        let family = dir.join(SHADOW_FAMILY);
        assert!(
            !family.exists(),
            "{} would supply the shadow front end ahead of the standard library, \
             so the parser under test could be chosen by the tree it is run over",
            family.display()
        );
    }
}

// What the front end costs, asserted as a shape rather than as a number.
//
// The measured Prism-to-Rust parse figure is wall clock from a dedicated
// harness, and wall clock on a loaded machine is not something a gate can stand
// on. Machine steps are: the count is a pure function of the program and its
// input. Even so, a pinned count is the wrong pin. It reseats on every ordinary
// parser edit, and having reseated it says nothing about the shape of the cost,
// which is the only part a budget is really protecting. So the assertion is the
// shape directly: doubling the input doubles the work.
//
// A run pays to load the front end before it parses anything, and that part does
// not grow with the input. Comparing two sizes directly would fold it into the
// answer and drift the ratio toward one, so the comparison is taken between
// three sizes instead: the difference of the differences cancels any cost that
// does not grow, whatever it is, and needs no separate run to measure it.
const COST_UNITS: usize = 12;
const COST_DECLS_PER_UNIT: usize = 3;

// The subject is identical repetitions, so a parser linear in its input lands on
// two exactly, and the measured value is two to the digit. The band is therefore
// kept narrow enough to mean something rather than widened to whatever passes: a
// pass that added one log factor over the whole input would land at 2.36 and is
// meant to fail here, because a parser acquiring one is a change worth stating
// out loud and widening this band deliberately.
const COST_RATIO_LOW: f64 = 1.85;
const COST_RATIO_HIGH: f64 = 2.30;

// One repetition of the subject: a signature, a sum declaration, and a match
// over it, each named for its index so no two repetitions are the same text.
// Every spelling here avoids the quote, brace, and backslash that would need
// escaping on the way into the Prism string literal that carries it.
fn cost_unit(index: usize) -> String {
    format!(
        "fn fa{index}(a : Int, b : Int) : Int = a + b * 2 - 1\n\
         type Tb{index} = Ca{index}(Int) | Cb{index}(String, Bool)\n\
         fn fc{index}(x : Tb{index}) : Int =\n\
         \x20 match x of\n\
         \x20   Ca{index}(n) => n + fa{index}(n, 1)\n\
         \x20   Cb{index}(s, p) => if p then 1 else 0\n"
    )
}

// The cost harness: parse a subject of `units` repetitions through the shadow
// front end and report how many declarations came back. Everything the run does
// besides parsing is one walk of the result and one printed line, both linear in
// the input and both dwarfed by the parse, so the machine steps the run takes
// track the parser's own cost on that subject.
fn cost_program(units: usize) -> String {
    let subject: String = (0..units).map(cost_unit).collect();
    let literal = subject.replace('\n', "\\n");
    format!(
        "import Syntax.Parse (..)\n\
         \n\
         fn subject() : String = \"{literal}\"\n\
         \n\
         fn declared(items, n) =\n\
         \x20 match items of\n\
         \x20   Nil => n\n\
         \x20   Cons(_, rest) => declared(rest, n + 1)\n\
         \n\
         fn main() =\n\
         \x20 match parse_source(subject()) of\n\
         \x20   Ok(items) => println(\"parsed {{declared(items, 0)}}\")\n\
         \x20   Err(_) => println(\"refused\")\n"
    )
}

// Machine steps and the reported line for one subject size.
fn cost_run(units: usize) -> (usize, String) {
    let src = with_prelude(&cost_program(units));
    let mut sink = Vec::new();
    let ruler = step_ruler_on(
        &src,
        &roots(),
        &mut sink,
        &mut &b""[..],
        &Config::from_env(),
    )
    .unwrap_or_else(|error| panic!("cost harness at {units} units: {error}"));
    let out = String::from_utf8(sink).expect("utf8 cost harness output");
    (ruler.total_steps, out.trim().to_string())
}

#[test]
fn parity_front_end_cost_stays_linear() {
    let sizes = [COST_UNITS, 2 * COST_UNITS, 4 * COST_UNITS];
    let runs = sizes.map(cost_run);

    // The parser parsed, and parsed all of it. A run that refused, or that
    // dropped declarations, would otherwise satisfy any ratio at all.
    for (units, (_, line)) in sizes.iter().zip(&runs) {
        assert_eq!(
            *line,
            format!("parsed {}", units * COST_DECLS_PER_UNIT),
            "the subject at {units} units"
        );
    }

    let [small, mid, large] = runs.map(|(steps, _)| steps);
    assert!(
        small < mid && mid < large,
        "parsing more must cost more: {small}, {mid}, {large}"
    );

    #[expect(
        clippy::cast_precision_loss,
        reason = "a step count large enough to lose precision here is already \
                  orders of magnitude outside the band"
    )]
    let ratio = (large - mid) as f64 / (mid - small) as f64;
    assert!(
        (COST_RATIO_LOW..=COST_RATIO_HIGH).contains(&ratio),
        "doubling the subject moved the front end's step count by {ratio:.2}x \
         ({small}, {mid}, {large} at {sizes:?} units); linear is 2 and quadratic is 4"
    );
}

// Recursion-depth refusal is exercised across every nesting axis, including
// direct let-pattern entries. Each axis is probed one point below the recursion
// budget, where the witness must accept, and one point beyond, where
// `Syntax.Parse` must answer its structured E7102 depth diagnostic and never
// abort. The per-axis probes run under an explicit small budget through
// `parse_source_budgeted`: the refusal machinery is identical at every
// budget, and probing at the default 2048 costs minutes per axis because the
// interpreted parser is super-linear on several nesting classes. One
// full-depth witness below pins the default budget's magnitude on the cheapest
// linear axis.
const DEPTH_BUDGET: usize = 64;
const DEPTH_OK: usize = 24;
const DEPTH_BEYOND: usize = 80;
const DEPTH_FULL: usize = 2100;
const DEPTH_CODE: &str = "E7102";

fn nested(prefix: &str, open: &str, seed: &str, close: &str, depth: usize, suffix: &str) -> String {
    let mut source = String::with_capacity(prefix.len() + depth * (open.len() + close.len()) + 64);
    source.push_str(prefix);
    for _ in 0..depth {
        source.push_str(open);
    }
    source.push_str(seed);
    for _ in 0..depth {
        source.push_str(close);
    }
    source.push_str(suffix);
    source.push('\n');
    source
}

fn open_if_blocks(depth: usize) -> String {
    let mut source = String::from("fn f(a : Bool) : Int =\n");
    for level in 0..depth {
        for _ in 0..=level {
            source.push_str("  ");
        }
        source.push_str("if a then\n");
    }
    for _ in 0..=depth {
        source.push_str("  ");
    }
    source.push_str("1\n");
    source
}

fn depth_axes(depth: usize) -> Vec<(&'static str, String)> {
    vec![
        (
            "forall-bodies",
            nested("fn f(x : ", "forall a. ", "Int", "", depth, ") : Int = 1"),
        ),
        (
            "right-arrows",
            nested("fn f(g : ", "(Int) -> ", "Int", "", depth, ") : Int = 1"),
        ),
        (
            "type-list",
            nested("fn f(x : ", "List(", "Int", ")", depth, ") : Int = 1"),
        ),
        (
            "type-tuple",
            nested("fn f(x : ", "(Int, ", "Int", ")", depth, ") : Int = 1"),
        ),
        (
            "type-ctor",
            nested("fn f(x : ", "Wrap(", "Int", ")", depth, ") : Int = 1"),
        ),
        (
            "effect-label-args",
            nested(
                "fn f(k : (Int) -> Int ! {Emit(",
                "List(",
                "Int",
                ")",
                depth,
                ")}) : Int = 1",
            ),
        ),
        (
            "pattern-ctor",
            nested(
                "fn f(x : Int) : Int =\n  match x of\n    ",
                "Wrap(",
                "y",
                ")",
                depth,
                " => 1\n    _ => 0",
            ),
        ),
        (
            "pattern-list",
            nested(
                "fn f(x : Int) : Int =\n  match x of\n    ",
                "[",
                "y",
                "]",
                depth,
                " => 1\n    _ => 0",
            ),
        ),
        (
            "pattern-tuple",
            nested(
                "fn f(x : Int) : Int =\n  match x of\n    ",
                "(",
                "y",
                ", 1)",
                depth,
                " => 1\n    _ => 0",
            ),
        ),
        (
            "pattern-record",
            nested(
                "fn f(x : Int) : Int =\n  match x of\n    ",
                "Wrap { field = ",
                "y",
                " }",
                depth,
                " => 1\n    _ => 0",
            ),
        ),
        (
            "expr-parens",
            nested("fn f() : Int = ", "(", "1", ")", depth, ""),
        ),
        (
            "right-assoc-caret",
            nested("fn f(a : Int) : Int = a", " ^ a", "", "", depth, ""),
        ),
        ("open-if-layout", open_if_blocks(depth)),
        (
            "let-pattern-entry",
            nested(
                "fn f(x : Int) : Int =\n  let ",
                "(",
                "y",
                ", 1)",
                depth,
                " = x\n  1",
            ),
        ),
    ]
}

fn depth_probe(axis: &'static str) -> (String, String) {
    let all_ok = depth_axes(DEPTH_OK);
    let all_beyond = depth_axes(DEPTH_BEYOND);
    let ok = &all_ok
        .iter()
        .find(|(a, _s)| *a == axis)
        .expect("known axis")
        .1;
    let beyond = &all_beyond
        .iter()
        .find(|(a, _s)| *a == axis)
        .expect("known axis")
        .1;
    (ok.clone(), beyond.clone())
}

fn assert_depth_axis(axis: &'static str) {
    let harness = fs::read_to_string(fixture(PARSER_FIXTURES).join(SELF_PARSE))
        .expect("self-parse harness source");
    let full = with_prelude(&harness);
    let dir = env::temp_dir().join("prism-depth-ledger");
    fs::create_dir_all(&dir).expect("depth scratch dir");
    let (ok_src, beyond_src) = depth_probe(axis);
    let ok_path = dir.join(format!("{axis}-ok.pr"));
    let beyond_path = dir.join(format!("{axis}-beyond.pr"));
    fs::write(&ok_path, ok_src).expect("write shallow probe");
    fs::write(&beyond_path, beyond_src).expect("write beyond probe");
    let mut sink = Vec::new();
    interpret_io_on_with_args(
        &full,
        &roots(),
        &mut sink,
        &mut &b""[..],
        &Config::from_env(),
        vec![
            format!("budget={DEPTH_BUDGET}"),
            ok_path.display().to_string(),
            beyond_path.display().to_string(),
        ],
    )
    .unwrap_or_else(|e| panic!("{axis}: depth witness run: {e}"));
    let out = String::from_utf8(sink).expect("utf8 depth output");
    let verdicts: Vec<&str> = out.lines().filter(|l| !l.is_empty()).collect();
    assert_eq!(verdicts.len(), 2, "{axis}: one verdict per probe:\n{out}");
    assert!(
        verdicts[0].starts_with(OK),
        "{axis}: a shallow probe must parse, witness said: {}",
        verdicts[0]
    );
    assert!(
        verdicts[1].contains(DEPTH_CODE),
        "{axis}: a beyond-budget probe must answer the structured depth \
         diagnostic, witness said: {}",
        verdicts[1]
    );
}

macro_rules! depth_axis {
    ($($name:ident => $axis:literal),+ $(,)?) => {
        $(#[test]
        fn $name() {
            assert_depth_axis($axis);
        })+
    };
}

// The magnitude witness: the default budget really is deep enough for two
// thousand nesting levels and really does refuse past them, proven once on
// the cheapest linear axis rather than fourteen times.
#[test]
fn depth_default_budget_magnitude() {
    let harness = fs::read_to_string(fixture(PARSER_FIXTURES).join(SELF_PARSE))
        .expect("self-parse harness source");
    let full = with_prelude(&harness);
    let dir = env::temp_dir().join("prism-depth-ledger");
    fs::create_dir_all(&dir).expect("depth scratch dir");
    let ok_src = nested("fn f() : Int = ", "(", "1", ")", DEPTH_OK, "");
    let beyond_src = nested("fn f() : Int = ", "(", "1", ")", DEPTH_FULL, "");
    let ok_path = dir.join("default-budget-ok.pr");
    let beyond_path = dir.join("default-budget-beyond.pr");
    fs::write(&ok_path, ok_src).expect("write shallow probe");
    fs::write(&beyond_path, beyond_src).expect("write beyond probe");
    let mut sink = Vec::new();
    interpret_io_on_with_args(
        &full,
        &roots(),
        &mut sink,
        &mut &b""[..],
        &Config::from_env(),
        vec![
            ok_path.display().to_string(),
            beyond_path.display().to_string(),
        ],
    )
    .unwrap_or_else(|e| panic!("default-budget witness run: {e}"));
    let out = String::from_utf8(sink).expect("utf8 default-budget output");
    let verdicts: Vec<&str> = out.lines().filter(|l| !l.is_empty()).collect();
    assert_eq!(verdicts.len(), 2, "one verdict per probe:\n{out}");
    assert!(verdicts[0].starts_with(OK), "shallow: {}", verdicts[0]);
    assert!(
        verdicts[1].contains(DEPTH_CODE),
        "beyond the default budget: {}",
        verdicts[1]
    );
}

depth_axis! {
    depth_forall_bodies => "forall-bodies",
    depth_right_arrows => "right-arrows",
    depth_type_list => "type-list",
    depth_type_tuple => "type-tuple",
    depth_type_ctor => "type-ctor",
    depth_effect_label_args => "effect-label-args",
    depth_pattern_ctor => "pattern-ctor",
    depth_pattern_list => "pattern-list",
    depth_pattern_tuple => "pattern-tuple",
    depth_pattern_record => "pattern-record",
    depth_expr_parens => "expr-parens",
    depth_right_assoc_caret => "right-assoc-caret",
    depth_open_if_layout => "open-if-layout",
    depth_let_pattern_entry => "let-pattern-entry",
}

// Negative-corpus parity: the committed malformed artifacts are the oracle,
// and the witness compares the refusal's semantic projection (code, phase,
// span, canonical expected set, related spans; message prose excluded as
// renderer-owned). Every case agrees exactly, expected sets included, so no
// stem carries an exception.
//
// The expression-at-EOF case is the one that reaches the expected sets, and
// neither side of that comparison is authored for the test: the oracle's set is
// the grammar's own first set for an operand, surfaced by `canonical_expected`,
// and the shadow's is whatever the cursor noted where it refused. Requiring
// equality there is what keeps the two parsers agreeing on which tokens can
// begin an operand, and the witness reports the difference as tokens rather
// than as an offset, so a regression names what it added or dropped.
const NEGATIVE_WITNESS: &str = "negative_parity.pr";

const NEGATIVE_STEMS: [(&str, &str); 8] = [
    ("malformed_empty_hole", OK),
    ("malformed_invalid", OK),
    ("malformed_lex", OK),
    ("malformed_number_sep", OK),
    ("malformed_parse", OK),
    ("malformed_parse_eof", OK),
    ("malformed_parse_flip", OK),
    ("malformed_unterm_hole", OK),
];

#[test]
fn negative_corpus_parity() {
    let witness = fs::read_to_string(fixture(PARSER_FIXTURES).join(NEGATIVE_WITNESS))
        .expect("negative witness source");
    let full = with_prelude(&witness);
    for (stem, want) in NEGATIVE_STEMS {
        let artifact = fixture(SYNTAX_FIXTURES).join(format!("{stem}.syntax-diagnostics.json"));
        assert!(artifact.is_file(), "{stem}: missing committed oracle");
        let mut sink = Vec::new();
        interpret_io_on_with_args(
            &full,
            &roots(),
            &mut sink,
            &mut &b""[..],
            &Config::from_env(),
            vec![artifact.display().to_string()],
        )
        .unwrap_or_else(|e| panic!("{stem}: negative witness run: {e}"));
        let out = String::from_utf8(sink).expect("utf8 negative output");
        let verdict = out.trim();
        assert_eq!(
            verdict, want,
            "{stem}: the refusal projection must match the oracle exactly \
             (or its one named exception exactly)"
        );
    }
}
