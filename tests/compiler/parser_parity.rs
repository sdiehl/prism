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
// Two corpora: the committed syntax fixtures, which are the same sources the
// artifact round trip already pins, and a focused file of grammar edges that
// are easy to lose in handwritten maintenance.

use std::path::{Path, PathBuf};
use std::{env, fs};

use prism::{default_roots, dump_on, interpret_io_on_with_args, with_prelude, Config, Root};

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

// Run the differential witness over one surface artifact and return its verdict
// line. `arg(1)` names where the witness dumps its own encoding on a mismatch,
// which is the artifact to diff when this fails.
fn parity(artifact: &Path, mismatch: &Path) -> String {
    let src = fs::read_to_string(fixture(PARSER_FIXTURES).join(WITNESS))
        .expect("differential witness source");
    let full = with_prelude(&src);
    let mut sink = Vec::new();
    let args = vec![
        artifact.display().to_string(),
        mismatch.display().to_string(),
    ];
    interpret_io_on_with_args(
        &full,
        &roots(),
        &mut sink,
        &mut &b""[..],
        &Config::from_env(),
        args,
    )
    .unwrap_or_else(|e| panic!("{}: witness run: {e}", artifact.display()));
    String::from_utf8(sink)
        .expect("utf8 witness output")
        .trim()
        .to_string()
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
// renderer-owned). One case is a named, watched exception: the
// expression-at-EOF expected set still diverges because the atom noteset is
// incomplete, and this test fails the moment it starts agreeing so the
// exception cannot outlive its cause.
const NEGATIVE_WITNESS: &str = "negative_parity.pr";
const NEGATIVE_STEMS: [(&str, &str); 8] = [
    ("malformed_empty_hole", OK),
    ("malformed_invalid", OK),
    ("malformed_lex", OK),
    ("malformed_number_sep", OK),
    ("malformed_parse", OK),
    ("malformed_parse_eof", "expected-set divergence at 362"),
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
