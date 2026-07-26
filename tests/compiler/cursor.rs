// The `Syntax.Cursor` gates: the module's binding powers are the compiler's, and
// its expectation set is the one held at the furthest position a parse reached.
//
// Both are differential rather than declarative. The precedence gate never reads
// a table: it dumps the live `prism-surface-syntax-v1` parse of a corpus of
// expressions, hands the same source to the Prism-side Pratt driver, and renders
// both trees fully parenthesized. Grouping is the only thing the two parsers can
// disagree about on that corpus, and the parentheses record exactly that, so
// equal strings mean the driver's levels and associativities reproduce the
// grammar's for every entry. Dumping live is the point: a change to the
// compiler's precedence ladder that the stdlib table does not follow fails here.
//
// The expectation gate runs a deliberately alternative-shaped grammar over a
// corpus of malformed inputs. Each input sends one alternative some distance into
// the stream before it fails and the parse rewinds, which is the situation a
// hand-written parser gets wrong: it reports the expectations of the position it
// retreated to rather than of the position it died at. The committed golden pins
// every reported record, and a second test re-states the furthest-position
// property directly, so a golden blessed with a wrong record still fails.

use std::fs;
use std::path::{Path, PathBuf};

use prism::{default_roots, dump, interpret_io_on_with_args, with_prelude, Config};

const FIXTURE_DIR: &str = "tests/fixtures/cursor";
const PRECEDENCE_CORPUS: &str = "precedence.pr";
const PRATT_HARNESS: &str = "pratt_check.pr";
const EXPECT_CORPUS: &str = "expectations.txt";
const EXPECT_HARNESS: &str = "expect_check.pr";
const EXPECT_GOLDEN: &str = "expectations.golden";
const SURFACE_PHASE: &str = "surface-syntax";
const ACCEPT: &str = "PRISM_ACCEPT_CURSOR_FIXTURES";

// The precedence corpus is a corpus: a gate that agreed about four expressions
// would prove nothing about a ladder ten levels deep.
const PRECEDENCE_FLOOR: usize = 30;

// The report separator, and the label the merged expectation set is printed
// under. The set is last on the line, so lifting it out is a split at the label
// however many commas, brackets, or operator spellings it holds.
const VERDICT: &str = " => ";
const WANT: &str = " want=";

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE_DIR)
}

fn read(name: &str) -> String {
    let path = fixture_dir().join(name);
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

// Run one harness over one argument file and capture its stdout.
fn harness(name: &str, arg: &Path) -> String {
    let src = with_prelude(&read(name));
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut sink = Vec::new();
    let cfg = Config::from_env();
    interpret_io_on_with_args(
        &src,
        &default_roots(root),
        &mut sink,
        &mut &b""[..],
        &cfg,
        vec![arg.display().to_string()],
    )
    .unwrap_or_else(|e| panic!("{name}: harness run: {e}"));
    String::from_utf8(sink).expect("utf8 harness output")
}

// The Pratt driver's parse of every corpus body, diffed against the compiler's
// own parse of the same source, dumped live rather than committed.
#[test]
fn cursor_binding_powers_are_the_compilers() {
    let src = read(PRECEDENCE_CORPUS);
    let artifact = std::env::temp_dir().join("prism_cursor_precedence.surface-syntax.json");
    let dump = dump(SURFACE_PHASE, &src).expect("surface-syntax dump");
    fs::write(&artifact, &dump).expect("write the dumped artifact");

    let report = harness(PRATT_HARNESS, &artifact);
    let lines: Vec<&str> = report.lines().filter(|l| !l.is_empty()).collect();
    assert!(
        lines.len() >= PRECEDENCE_FLOOR,
        "the precedence corpus reported only {} verdicts; the harness is not \
         reading the corpus",
        lines.len()
    );
    assert_eq!(
        lines.len(),
        src.lines().filter(|l| l.starts_with("fn ")).count(),
        "every corpus declaration must produce exactly one verdict"
    );
    let disagreements: Vec<&&str> = lines
        .iter()
        .filter(|l| l.split_whitespace().nth(1).is_none_or(|w| w != "ok"))
        .collect();
    assert!(
        disagreements.is_empty(),
        "the Pratt driver's binding powers diverge from the compiler's parse:\n{}\n\n\
         Each line is `name compiler=<grouping> pratt=<grouping>`. The compiler's \
         parse is authoritative: fix the tables in lib/std/Syntax/Cursor.pr.",
        disagreements
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n")
    );
}

// The full refusal record of every malformed input, against its committed
// golden: code, span, message, and merged expectation set.
#[test]
fn cursor_expectation_report_matches_the_golden() {
    let report = harness(EXPECT_HARNESS, &fixture_dir().join(EXPECT_CORPUS));
    if std::env::var_os(ACCEPT).is_some() {
        fs::write(fixture_dir().join(EXPECT_GOLDEN), &report).expect("write golden");
        eprintln!("accepted {EXPECT_GOLDEN}");
        return;
    }
    assert_eq!(
        report,
        read(EXPECT_GOLDEN),
        "the expectation report drifted from its golden (regenerate with {ACCEPT}=1 \
         and review every changed span and set)"
    );
}

// One reported refusal: the byte offset it points at and its merged expectation
// set, lifted back out of the report line for that input.
fn refusal(report: &str, input: &str) -> (usize, String) {
    let line = report
        .lines()
        .find(|l| l.starts_with(&format!("{input}{VERDICT}")))
        .unwrap_or_else(|| panic!("no report line for {input:?}"));
    let body = line.split_once(VERDICT).expect("verdict separator").1;
    let (head, want) = body.split_once(WANT).expect("expectation-set label");
    let span = head.split_whitespace().nth(1).expect("span field");
    let lo = span.split_once(':').expect("lo:hi span").0;
    (lo.parse().expect("decimal offset"), want.to_string())
}

// The property the whole module exists for, stated directly rather than only
// pinned as bytes: a refusal names the furthest position the parse reached and
// carries exactly the expectations recorded there.
//
// The first four inputs each drive one alternative several tokens in before it
// fails, while the alternatives tried after it fail at the first token. The
// report must name the deep offset and hold only the deep expectation: the
// shallow ones are recorded behind the mark and dropped. The last three fail
// every alternative at one position, and the report must hold all of them, in
// the order they were tried.
#[test]
fn cursor_expectations_are_the_furthest_positions() {
    let report = harness(EXPECT_HARNESS, &fixture_dir().join(EXPECT_CORPUS));
    let shallow = "(, [, int, ident";
    for (input, offset, want) in [
        ("[1 + 2", 6, "]"),
        ("(1 + 2", 6, ")"),
        ("1 + [2", 6, "]"),
        ("[1 + 2)", 6, "]"),
        ("*", 0, shallow),
        ("1 +", 3, shallow),
        ("[)", 1, shallow),
    ] {
        let (got_offset, got_want) = refusal(&report, input);
        assert_eq!(
            (got_offset, got_want.as_str()),
            (offset, want),
            "{input:?}: the refusal must be reported at the furthest position \
             reached, carrying exactly the expectations recorded there"
        );
    }

    // The negative half: a deep refusal must not carry what the alternatives
    // tried afterwards wanted at the position the parse rewound to. Reporting
    // the union over all positions, or the last alternative's set, would pass
    // the offset check above while making the message useless.
    for input in ["[1 + 2", "(1 + 2", "[1 + 2)"] {
        let (_, want) = refusal(&report, input);
        assert!(
            !want.contains("int"),
            "{input:?}: the refusal carries expectations from an earlier \
             position ({want}); the record must not merge across positions"
        );
    }
}
