#!/usr/bin/env python3
"""The compaction scoreboard: what each component costs on each side.

Regenerates `docs/internal/SCOREBOARD.md` from the sources themselves, so the
size half of the ledger cannot drift from the tree. `--check` reproduces the
file and fails if the committed copy differs, the way the Standard Library
Reference is checked.

Two halves, with different standing:

- Size is computed here, from the files named below, under one counting rule.
  It is deterministic, so CI checks it.
- Cost is measured with `just lexperf` on a developer machine and recorded here
  by hand, carrying the date and the machine. It is not reproducible on another
  host, so CI does not check it.

A pair is listed whether or not it flattered the claim. A threshold that failed
stays on the board as failed, and a threshold that stopped describing its module
is retired in writing, because a threshold quietly dropped is a threshold gamed.
"""

import argparse
import subprocess
import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REPORT = ROOT / "docs" / "internal" / "SCOREBOARD.md"

# The line-comment marker per language. One rule, three suffixes; see `count`.
MARKERS = {".rs": "//", ".lalrpop": "//", ".pr": "--"}


def count(patterns):
    """`(raw, code, [paths])` over every file matching `patterns`.

    The counting rule, defined once and applied to both sides: a line is code
    when its stripped form is non-empty and does not begin with its language's
    line-comment marker. Raw is every line.
    """
    raw = code = 0
    paths = []
    for pattern in patterns:
        matches = sorted(ROOT.glob(pattern))
        if not matches:
            sys.exit(f"scoreboard: no file matches {pattern}")
        for path in matches:
            paths.append(path.relative_to(ROOT).as_posix())
            marker = MARKERS[path.suffix]
            for line in path.read_text().splitlines():
                raw += 1
                bare = line.strip()
                if bare and not bare.startswith(marker):
                    code += 1
    return raw, code, paths


class Row:
    """One pre-registered component pair.

    `verdict` receives the code-line ratio, or `None` when a side is missing and
    there is nothing to divide. `cost` says where that pair stands on the cost
    half, since a pair nobody has timed and a pair that is free are different
    claims and must not render the same.
    """

    def __init__(self, name, rust, prism, threshold, verdict, cost):
        self.name = name
        self.rust = rust
        self.prism = prism
        self.threshold = threshold
        self.verdict = verdict
        self.cost = cost


# The ratio the Prism parser has to beat to count as evidence. Registered before
# that parser exists, which is the only thing separating a threshold from a
# description of whatever ends up getting built.
PARSER_RATIO = 0.5

# The ratio the Prism checker has to beat once its coverage reaches the whole
# language. Registered while it checks a first-order subset, for the same
# reason the parser's number was registered before that parser existed.
CHECKER_RATIO = 0.5

ROWS = [
    Row(
        name="lexer and layout",
        rust=["crates/prism-syntax/src/lex/*.rs"],
        prism=["lib/std/Syntax/Lex.pr", "lib/std/Syntax/Layout.pr"],
        threshold="control, recorded rather than judged",
        verdict=lambda ratio: (
            f"recorded at {ratio:.2f}. The Prism side was deliberately written to"
            " track the Rust side token for token so the two can be diffed, so"
            " what this row measures is that decision and not the language"
        ),
        cost="measured, in the table above",
    ),
    Row(
        name="parser",
        rust=[
            "crates/prism-syntax/src/grammar.lalrpop",
            "crates/prism-syntax/src/sugar.rs",
        ],
        prism=[
            "lib/std/Syntax/Parse.pr",
            "lib/std/Syntax/Parse/*.pr",
        ],
        threshold=f"ratio {PARSER_RATIO:.2f} or lower",
        verdict=lambda ratio: (
            "registered and unmet. The Prism parser is not written, so this is"
            " neither passed nor failed; the number it has to beat is on the"
            " board first so it cannot be set afterwards"
            if ratio is None
            else f"{'met' if ratio <= PARSER_RATIO else 'FAILED'} at {ratio:.2f}."
            " The pre-registered bet was that the library floor had absorbed the"
            " plumbing. The first judgment decomposed the gap into three named"
            " causes, and the two that were compiler work have landed: the"
            " sequencing rewrite and the `let ... else` early-return binding"
            " form, which the parser now uses throughout. Rewriting the parser"
            " onto them removed 1,002 code lines, fourteen percent, while the"
            " same release grew the Rust side by 279 lines of new surface"
            " syntax, so the ratio fell from 4.31 at v0.17.0. It has since risen"
            " from 3.21, and the cause is worth naming because it is not a"
            " regression in the language: closing the last four gaps between the"
            " two parsers put 288 code lines onto the shadow and none onto the"
            " oracle, which already derived those productions. Coverage catching"
            " up moves this row the unfavorable way by construction, which is"
            " what a board measuring lines rather than capability will do. The"
            " residual gap stands on the remaining cause, that the generated"
            " side never pays line by line for the productions its tables"
            " derive. No further compiler work is pre-registered against this"
            " row; it stays failed rather than re-excused, and the rise is"
            " recorded rather than netted against the earlier fall"
        ),
        cost="measured, in the table above, from the one run that table"
        " transcribes; the duplicate receipt that backed the earlier reading of"
        " this layer was not repeated, so these rates carry a single receipt",
    ),
    Row(
        name="surface AST",
        rust=["crates/prism-syntax/src/ast.rs"],
        prism=["lib/std/Syntax/Ast.pr"],
        threshold="not evidence for the claim",
        verdict=lambda ratio: (
            f"not evidence at {ratio:.2f}. The Rust file carries derives and"
            " hand-written trait impls alongside the declarations and the Prism"
            " file carries declarations only, so most of the gap is a difference"
            " in what the two files hold. It becomes a comparison when the impls"
            " are separated out, and it stays on the board unseparated so that"
            " the favorable number is not quotable on its own"
        ),
        cost="declarations, so nothing executes and there is no cost to report",
    ),
    Row(
        name="syntax codecs",
        rust=[],
        prism=["lib/std/Syntax/Codec.pr"],
        threshold="derivable from the schema rather than written",
        verdict=lambda _ratio: (
            "FALSIFIED. Under the pinned wire schema the encoders and decoders"
            " were written out by hand, one arm per constructor, which is the"
            " finding this row exists to record. There is no Rust counterpart to"
            " divide by because that side is derived and occupies no lines, and"
            " that asymmetry is exactly the gap"
        ),
        cost="executes, but no paired driver runs the same bytes through both"
        " sides, so the ratio is unmeasured rather than favorable",
    ),
    Row(
        name="checker",
        rust=["src/tc/*.rs", "src/tc/infer/*.rs"],
        prism=["packages/tc/src/Tc.pr", "packages/tc/src/Bootstrap.pr"],
        threshold=f"ratio {CHECKER_RATIO:.2f} or lower at full coverage",
        verdict=lambda ratio: (
            f"recorded, not judged, at {ratio:.2f}. The Prism side checks the"
            " subset the bootstrap workbench supports, so the number says what a"
            " subset costs, not what the full checker will. That subset is no"
            " longer the pure first-order one it was: this release added written"
            " effect rows, parameterized effect labels, shared handler effect"
            " evidence, and generalization of local types, and the Prism side"
            " nearly doubled paying for them while the ratio rose from 0.24."
            " That is the curve this row exists to publish and it is moving"
            " against the claim, which is the expected shape, since the cheapest"
            " part of a checker is the part written first. Both counting"
            " asymmetries push the ratio up rather than down: the Prism files"
            " carry their own type definitions and the artifact decoding, while"
            " the Rust side counts the inference engine alone. The threshold"
            " binds when the shadow's coverage reaches the whole language, and"
            " every subset number stays recorded so the curve from subset to"
            " full checker is public"
        ),
        cost="the reproducible figure is end to end: the shipped workbench, which"
        " is `just tc` on the committed bootstrap fixture with the release binary"
        " hosting the interpreter, takes 2.29 s median of 20 on an Apple M5"
        " measured 2026-08-23, against 1.9 s for the same fixture on 2026-08-14,"
        " the workbench having grown the effect-row and local-generalization"
        " coverage named above in between. The pair that produced the 54x, 625 ms"
        " for the checker compiled to a native binary and run to full parity on"
        " the fixture's exported artifacts against 11.6 ms for the Rust typecheck"
        " phase on the same 270-definition universe, was measured 2026-08-14 on an"
        " apparatus that was never committed, with artifact decode inside the"
        " Prism figure and outside the Rust one. It is carried here as vintage"
        " rather than as a number this tree can re-derive, and a committed driver"
        " that isolates the Rust phase and the compiled checker over one universe"
        " is what would make that ratio quotable again",
    ),
]

# Cost readings, transcribed by hand from one `just lexperf` run. Machine
# dependent, hence the provenance line and hence CI leaving this half alone.
COST_PROVENANCE = (
    "Measured 2026-08-23, all three layers in one `just lexperf` run, on an Apple"
    " M5 running macOS 26.3, release profile, the Prism side compiled to a native"
    " binary. The absolute rates belong to that machine; the ratio is the figure"
    " that carries across hosts, and `just lexperf` reprints all of it. Each class"
    " climbs a doubling ladder until the Prism side crosses two seconds, so a row"
    " is measured at whatever size that ladder reached and the `at KiB` column"
    " carries it: the two peak columns compare to each other within a row and to"
    " nothing across rows."
)

# Transcribed verbatim from the harness, ratio included rather than recomputed:
# the rates here are already rounded for printing, so dividing them back out
# would quietly disagree with the tool this table claims to be a copy of.
# workload, layer, size reached, Rust MB/s, Prism MB/s, ratio, and the two peaks.
COST_ROWS = [
    ("stdlib", "raw", "4096", "210.6", "7.396", "28x", "130.8M", "164.3M"),
    ("example", "raw", "4095", "175.6", "5.210", "34x", "135.6M", "233.1M"),
    ("flat", "raw", "4096", "147.1", "4.102", "36x", "184.7M", "328.0M"),
    ("comments", "raw", "4096", "1024.1", "29.956", "34x", "30.0M", "15.5M"),
    ("nesting", "raw", "4096", "75.7", "3.019", "25x", "476.7M", "871.8M"),
    ("interp", "raw", "4096", "59.0", "1.534", "38x", "173.3M", "307.9M"),
    ("corpus", "raw", "1282", "206.0", "7.648", "27x", "35.9M", "52.5M"),
    ("stdlib", "layout", "4096", "62.1", "4.264", "15x", "214.3M", "242.7M"),
    ("example", "layout", "4095", "47.0", "2.993", "16x", "201.3M", "355.7M"),
    ("flat", "layout", "4096", "43.6", "2.304", "19x", "274.7M", "493.8M"),
    ("comments", "layout", "4096", "824.0", "29.753", "28x", "30.1M", "15.5M"),
    ("nesting", "layout", "4096", "9.9", "1.265", "8x", "709.1M", "1272.4M"),
    ("interp", "layout", "4096", "31.7", "1.187", "27x", "254.6M", "456.1M"),
    ("corpus", "layout", "1282", "59.9", "4.036", "15x", "61.6M", "76.9M"),
    ("stdlib", "parse", "4109", "26.7", "2.685", "10x", "298.9M", "276.8M"),
    ("example", "parse", "4102", "19.0", "1.848", "10x", "323.5M", "414.3M"),
    ("flat", "parse", "4096", "15.6", "1.359", "11x", "577.9M", "616.8M"),
    ("comments", "parse", "4096", "673.3", "14.743", "46x", "25.9M", "15.7M"),
    ("nesting", "parse", "2048", "3.9", "0.535", "7x", "359.7M", "669.1M"),
    ("interp", "parse", "2048", "12.5", "0.798", "16x", "254.7M", "286.5M"),
    ("corpus", "parse", "1282", "25.2", "2.554", "10x", "88.3M", "85.9M"),
]

COST_NOTES = [
    "Every workload class the harness offers is above except `modules`, which it"
    " flagged on all three layers as launch dominated: most of the Prism wall"
    " clock was process startup, subtracted rather than measured. Its ratio would"
    " be an artifact of that subtraction, so it is named here instead of quoted."
    " The `corpus` class is the one input that is not synthetic, being the 110"
    " committed modules concatenated whole, which is why its ladder stops at the"
    " size the tree actually is rather than at a doubling.",
    "Log-log slopes of time against input size came back between 0.91 and 1.07 on"
    " both sides, which is to say linear on both. The Prism lexer is a constant"
    " factor behind rather than asymptotically worse, and the size of that"
    " constant is the thing to keep reporting.",
    "Peak resident set is the other half of the cost, and it does not track"
    " throughput: the Prism side peaks higher on most classes and lower on the"
    " comment-heavy one, where it allocates less per byte of input than the token"
    " stream the Rust side materializes. Read it against `at KiB` and never"
    " against the previous reading of this table, which carried no such column: a"
    " class that got faster climbs further up the ladder before the two-second cut"
    " and reports a larger peak for that reason alone.",
    "Against the readings this table replaces, the two structured layers closed"
    " most of the way and the raw layer barely moved. Layout went from 21x to 15x"
    " on the standard library and from 126x to 8x on the deeply nested class;"
    " parse went from 13x to 10x and from 59x to 7x on the same two. The"
    " comment-heavy class is the one that went the other way, 40x to 46x at parse."
    " This run measured the tree, not the cause: nothing here attributes the move"
    " to a particular change, and the earlier figures were taken on two separate"
    " days against a table that did not record the size each row reached.",
]

# Thresholds that stopped describing their module. Retired in writing, never
# deleted, since a board only means something if leaving it requires a sentence.
RETIREMENTS = [
    (
        "`Syntax.Walk` under 60 lines once the arm table is derived",
        "Moot rather than failed. The module grew to cover more sorts, and it"
        " keeps one hand-written layer for a reason that is documented at the"
        " definition: a derived instance on the spanned wrapper yields no"
        " children, one at the unwrapped sort loses the spans, and the instance"
        " that would be correct sits at an instantiation `deriving` cannot"
        " currently name. The premise of the threshold no longer describes the"
        " module, so the number is withdrawn rather than quietly missed.",
    ),
]

BANNER = "<!-- Generated by scripts/scoreboard.py. Run `just scoreboard` to regenerate. -->"

# Matches the markdown width in dprint.json, so the committed file reads the way
# the hand-written docs beside it do.
WIDTH = 80


def wrap(text, **kwargs):
    """Wrap to `WIDTH`, never inside a word.

    Hyphens and long words are kept whole because the text is full of paths in
    backticks, and a code span split across two lines is no longer a code span.
    """
    return textwrap.wrap(
        text, WIDTH, break_long_words=False, break_on_hyphens=False, **kwargs
    )


def para(text):
    """One prose paragraph, wrapped."""
    return wrap(text)


def bullet(text):
    """One list item, wrapped and hung under its marker."""
    return wrap(text, initial_indent="- ", subsequent_indent="  ")


def table(header, aligns, rows):
    """A markdown table with padded cells, so the committed file reads as text.

    `aligns` is one character per column, `r` for right and anything else left.
    """
    widths = [max(len(cell) for cell in col) for col in zip(header, *rows)]

    def line(cells):
        padded = [
            cell.rjust(width) if align == "r" else cell.ljust(width)
            for cell, width, align in zip(cells, widths, aligns)
        ]
        return "| " + " | ".join(padded) + " |"

    rule = [
        "-" * (width - 1) + ":" if align == "r" else "-" * width
        for width, align in zip(widths, aligns)
    ]
    return [line(header), line(rule), *(line(row) for row in rows)]


def cell(side, index):
    """One count, or `none` where a pair has no file on that side at all."""
    return f"{side[index]:,}" if side else "none"


def size_section():
    rows = []
    ratios = {}
    for row in ROWS:
        rust = count(row.rust) if row.rust else None
        prism = count(row.prism) if row.prism else None
        ratio = prism[1] / rust[1] if rust and prism and rust[1] else None
        ratios[row.name] = ratio
        rows.append(
            [
                row.name,
                cell(rust, 0),
                cell(rust, 1),
                cell(prism, 0),
                cell(prism, 1),
                "n/a" if ratio is None else f"{ratio:.2f}",
            ]
        )
    header = ["component", "Rust raw", "Rust code", "Prism raw", "Prism code", "ratio"]
    return table(header, "lrrrrr", rows), ratios


def sources_section():
    out = []
    for row in ROWS:
        sides = []
        for label, patterns in (("Rust", row.rust), ("Prism", row.prism)):
            if patterns:
                sides.append(f"{label} `{'`, `'.join(count(patterns)[2])}`")
            else:
                sides.append(f"{label} none")
        out += bullet(f"**{row.name}**: {'; '.join(sides)}.")
    return out


def cost_table():
    header = [
        "workload",
        "layer",
        "at KiB",
        "Rust MB/s",
        "Prism MB/s",
        "ratio",
        "Rust peak",
        "Prism peak",
    ]
    return table(header, "llrrrrrr", [list(row) for row in COST_ROWS])


def render():
    size, ratios = size_section()
    lines = [
        "# Compaction scoreboard",
        "",
        BANNER,
        "",
        *para(
            "The claim on trial is that a compiler component written in Prism is"
            " smaller than the same component written in Rust. This file is the"
            " ledger. Every pair that was registered appears here, including the"
            " ones that went the wrong way, because a board you are free to leave"
            " selectively measures nothing."
        ),
        "",
        "## Counting rule",
        "",
        *para(
            "One rule, applied to both sides. A line is **code** when, after"
            " stripping the surrounding whitespace, it is non-empty and does not"
            " begin with its language's line-comment marker: `//` for Rust and for"
            " the grammar, `--` for Prism. **Raw** is every line. The rule keeps a"
            " comment trailing a code line and does not understand Rust block"
            " comments. It is crude deliberately. What matters is that it is the"
            " same rule on both sides, not that it is the fairest available rule"
            " for either one."
        ),
        "",
        *para(
            "The `ratio` column is Prism code lines over Rust code lines. Below"
            " 1.00 is compaction, above it is not."
        ),
        "",
        "## Size",
        "",
        *size,
        "",
        "What each row counts:",
        "",
        *sources_section(),
        "",
        "## Verdicts",
        "",
    ]
    for row in ROWS:
        lines += bullet(
            f"**{row.name}**, threshold {row.threshold}:"
            f" {row.verdict(ratios[row.name])}."
        )
    lines += [
        "",
        "## Cost",
        "",
        *para(
            "Agreement is never reported without cost. A component that matches"
            " its Rust counterpart line for line and runs orders of magnitude"
            " slower has not replaced it, and a scoreboard printing only the"
            " flattering half of that pair is advertising. The size half above is"
            " computed from the tree and checked by CI. This half is not: it is"
            " measured by hand and carries its provenance instead."
        ),
        "",
        *para(COST_PROVENANCE),
        "",
        *cost_table(),
        "",
    ]
    for note in COST_NOTES:
        lines += [*para(note), ""]
    lines += ["Where the other pairs stand on cost:", ""]
    for row in ROWS:
        lines += bullet(f"**{row.name}**: {row.cost}.")
    lines += ["", "## Retirements", ""]
    for name, why in RETIREMENTS:
        lines += bullet(f"{name}. {why}")
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser(description="Regenerate the compaction scoreboard.")
    ap.add_argument(
        "--check",
        action="store_true",
        help="fail if the committed report differs from a freshly generated one",
    )
    args = ap.parse_args()
    fresh = render()
    rel = REPORT.relative_to(ROOT)
    if not args.check:
        REPORT.write_text(fresh)
        print(f"wrote {rel}")
        return
    if not REPORT.exists():
        sys.exit(f"{rel} is missing; run `just scoreboard`")
    if REPORT.read_text() == fresh:
        print(f"{rel} is current")
        return
    subprocess.run(
        ["git", "--no-pager", "diff", "--no-index", "--", str(rel), "-"],
        cwd=ROOT,
        input=fresh,
        text=True,
        check=False,
    )
    sys.exit(f"{rel} is stale; run `just scoreboard`")


if __name__ == "__main__":
    main()
