// The differential gate for `Syntax.Report`, the Prism-side caret renderer.
//
// Diagnostics are bytes. The compiler renders a refused source through ariadne
// with color off, and any Prism front end whose refusals print differently
// fails a negative test even when it classifies the fault perfectly. This gate
// pins the Prism renderer against the compiler's own output, so the layout is
// specified by a passing test rather than by a description of it.
//
// Each corpus source under `tests/fixtures/report/` is refused by the compiler.
// The gate computes the oracle the same way the driver does (lex, then parse,
// then `Error::render_plain` against `<source>`), feeds the same source's
// `prism-syntax-diagnostics-v1` artifact to
// `tests/fixtures/report/render_check.pr`, and compares the two byte for byte.
//
// The corpus records which shapes `Syntax.Report` draws. A span crossing a line
// boundary gets the compiler's multi-line form, which the module does not draw;
// those cases must print the decline marker, and the oracle must actually carry
// the multi-line arrow, so the boundary is pinned from both sides instead of
// asserted in a comment.

use std::fs;
use std::path::{Path, PathBuf};

use prism::lex::lex;
use prism::parse::parse;
use prism::{default_roots, interpret_io_on_with_args, with_prelude, Config, Error};

const FIXTURE_DIR: &str = "tests/fixtures/report";
const HARNESS: &str = "render_check.pr";
const PHASE: &str = "syntax-diagnostics";

// The source name the driver stamps into the location line when reporting on a
// single file.
const SOURCE_NAME: &str = "<source>";

// What the harness prints for a diagnostic outside the shape the module draws.
const DECLINED: &str = "declined\n";

// The head of the compiler's multi-line report form: the arrow that runs from
// the margin into the opening line of a span that crosses a line boundary. Its
// presence is what puts a diagnostic outside the drawn shape.
const MULTILINE_MARK: &str = "─▶";

// The negative corpus. The flag is whether `Syntax.Report` draws the shape; the
// note says which part of the layout the case exercises.
//
// Between them the drawn cases cover both span shapes the syntax boundary
// raises (a zero-width lexical caret and a parse token's range), a caret at the
// line terminator, a caret at the very end of the text, a caret in an empty
// text, a stem landing inside a wide span, tab expansion to four-column stops,
// trailing whitespace dropped from the source line, both line terminators, and
// a two-digit gutter.
const CORPUS: [(&str, bool); 15] = [
    ("lex_unterminated_string", true),
    ("lex_invalid_escape", true),
    ("lex_empty_hole", true),
    ("lex_unterminated_hole", true),
    ("lex_number_separator", true),
    ("parse_token", true),
    ("parse_keyword", true),
    ("parse_end_of_block", true),
    ("parse_no_trailing_newline", true),
    ("parse_empty_source", true),
    ("tab_indent", true),
    ("trailing_space", true),
    ("crlf", true),
    ("gutter_two_digits", true),
    ("multiline_span", false),
];

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE_DIR)
}

fn read(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

fn source(stem: &str) -> String {
    read(&fixture_dir().join(format!("{stem}.pr")))
}

// The bytes the compiler prints for the source's first syntax fault, built the
// way `driver::report` builds them: the lexer runs first, the parser second,
// and whichever refuses is rendered without color against `<source>`.
fn oracle(stem: &str, src: &str) -> String {
    let err: Error = match lex(src) {
        Err(e) => e.into(),
        Ok(_) => match parse(src) {
            Err(e) => e.into(),
            Ok(_) => panic!("{stem}: the corpus is negative, but this source is accepted"),
        },
    };
    err.render_plain(src, SOURCE_NAME)
}

// Run the Prism harness over the source's diagnostics artifact and return
// everything it printed.
fn rendered(stem: &str, src: &str) -> String {
    let artifact = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("{stem}.{PHASE}.json"));
    let document = prism::dump(PHASE, src).unwrap_or_else(|e| panic!("{stem}: dump: {e}"));
    fs::write(&artifact, &document).unwrap_or_else(|e| panic!("write {}: {e}", artifact.display()));

    let full = with_prelude(&read(&fixture_dir().join(HARNESS)));
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut sink = Vec::new();
    let cfg = Config::from_env();
    let args = vec![artifact.display().to_string()];
    interpret_io_on_with_args(
        &full,
        &default_roots(root),
        &mut sink,
        &mut &b""[..],
        &cfg,
        args,
    )
    .unwrap_or_else(|e| panic!("{stem}: harness run: {e}"));
    String::from_utf8(sink).expect("utf8 harness output")
}

fn assert_case(stem: &str, drawn: bool) {
    let src = source(stem);
    let want = oracle(stem, &src);
    let got = rendered(stem, &src);
    if drawn {
        assert!(
            !want.contains(MULTILINE_MARK),
            "{stem}: the compiler now draws this in its multi-line form, so the \
             corpus entry is stale"
        );
        assert_eq!(
            got, want,
            "{stem}: the Prism renderer diverged from the compiler's own bytes"
        );
    } else {
        assert!(
            want.contains(MULTILINE_MARK),
            "{stem}: this case is recorded as undrawn because the compiler draws \
             it in its multi-line form, and it no longer does"
        );
        assert_eq!(
            got, DECLINED,
            "{stem}: an undrawn shape must decline, never approximate"
        );
    }
}

macro_rules! report_gate {
    ($($name:ident => ($stem:literal, $drawn:literal)),+ $(,)?) => {
        $(#[test]
        fn $name() {
            assert_case($stem, $drawn);
        })+
    };
}

report_gate! {
    report_lex_unterminated_string => ("lex_unterminated_string", true),
    report_lex_invalid_escape => ("lex_invalid_escape", true),
    report_lex_empty_hole => ("lex_empty_hole", true),
    report_lex_unterminated_hole => ("lex_unterminated_hole", true),
    report_lex_number_separator => ("lex_number_separator", true),
    report_parse_token => ("parse_token", true),
    report_parse_keyword => ("parse_keyword", true),
    report_parse_end_of_block => ("parse_end_of_block", true),
    report_parse_no_trailing_newline => ("parse_no_trailing_newline", true),
    report_parse_empty_source => ("parse_empty_source", true),
    report_tab_indent => ("tab_indent", true),
    report_trailing_space => ("trailing_space", true),
    report_crlf => ("crlf", true),
    report_gutter_two_digits => ("gutter_two_digits", true),
    report_multiline_span => ("multiline_span", false),
}

// Every corpus source is gated, and every gate entry has a source: a fixture
// added without an entry (or an entry left behind by a deleted fixture) fails
// here rather than silently going unrendered.
#[test]
fn report_covers_every_fixture() {
    let mut found: Vec<String> = fs::read_dir(fixture_dir())
        .expect("fixture dir")
        .filter_map(Result::ok)
        .filter_map(|e| {
            let name = e.file_name().into_string().ok()?;
            let stem = name.strip_suffix(".pr")?;
            (name != HARNESS).then(|| stem.to_string())
        })
        .collect();
    found.sort_unstable();

    let mut expected: Vec<String> = CORPUS.iter().map(|(s, _)| (*s).to_string()).collect();
    expected.sort_unstable();

    assert_eq!(
        found, expected,
        "the report fixtures and the corpus table have drifted apart"
    );
}

// The corpus is only a parity claim if it holds both kinds of case: at least one
// shape the module draws, and at least one it declines.
#[test]
fn report_corpus_spans_the_boundary() {
    assert!(
        CORPUS.iter().any(|(_, drawn)| *drawn),
        "the corpus must exercise a shape the renderer draws"
    );
    assert!(
        CORPUS.iter().any(|(_, drawn)| !*drawn),
        "the corpus must exercise a shape the renderer declines, so the boundary \
         stays pinned"
    );
}
