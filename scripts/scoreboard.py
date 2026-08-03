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
            " plumbing; the measured gap says it has not, and it decomposes into"
            " named causes rather than standing as an adjective: every"
            " sequencing point is a spelled-out three-way match because the"
            " effect-styled formulation measurably lowers the whole program at"
            " the free-monad tier (the thunk-evidence gap), the language has no"
            " early-return binding form to collapse that threading, and the"
            " generated side never pays line by line for the productions its"
            " tables derive. The first two are compiler work with this parser as"
            " their first customer; the row is re-judged when they land"
        ),
        cost="measured, in the table above; a second receipt reproduced every ratio within noise",
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
]

# Cost readings, transcribed by hand from one `just lexperf` run. Machine
# dependent, hence the provenance line and hence CI leaving this half alone.
COST_PROVENANCE = (
    "Lex layers measured 2026-07-28 and the parse layer 2026-08-01 with `just"
    " lexperf` on an Apple M5 running macOS 26.3, release profile, the Prism"
    " side compiled to a native binary. The absolute"
    " rates belong to that machine; the ratio is the figure that carries across"
    " hosts, and `just lexperf` reprints all of it."
)

# Transcribed verbatim from the harness, ratio included rather than recomputed:
# the rates here are already rounded for printing, so dividing them back out
# would quietly disagree with the tool this table claims to be a copy of.
# workload, layer, Rust MB/s, Prism MB/s, ratio, Rust peak RSS, Prism peak RSS.
COST_ROWS = [
    ("stdlib", "raw", "217.6", "8.223", "26x", "126.2M", "154.7M"),
    ("example", "raw", "174.0", "5.280", "33x", "134.7M", "233.4M"),
    ("flat", "raw", "143.7", "4.063", "35x", "184.6M", "327.9M"),
    ("comments", "raw", "1127.0", "32.292", "35x", "29.9M", "15.4M"),
    ("nesting", "raw", "67.4", "2.873", "23x", "476.6M", "871.7M"),
    ("interp", "raw", "58.7", "1.325", "44x", "173.1M", "313.6M"),
    ("stdlib", "layout", "63.8", "3.083", "21x", "202.0M", "183.0M"),
    ("example", "layout", "45.6", "2.065", "22x", "200.3M", "287.4M"),
    ("flat", "layout", "43.6", "1.499", "29x", "274.5M", "406.3M"),
    ("comments", "layout", "853.1", "31.914", "27x", "25.1M", "15.4M"),
    ("nesting", "layout", "10.5", "0.084", "126x", "48.3M", "68.9M"),
    ("interp", "layout", "31.0", "0.857", "36x", "129.7M", "193.4M"),
    ("stdlib", "parse", "22.4", "1.667", "13x", "299.0M", "231.4M"),
    ("example", "parse", "16.5", "1.207", "14x", "322.9M", "346.9M"),
    ("flat", "parse", "13.8", "0.890", "16x", "294.6M", "269.4M"),
    ("comments", "parse", "631.4", "15.867", "40x", "30.7M", "15.6M"),
    ("nesting", "parse", "3.8", "0.065", "59x", "27.0M", "37.9M"),
    ("interp", "parse", "11.8", "0.569", "21x", "254.7M", "278.6M"),
]

COST_NOTES = [
    "Every workload class the harness offers is above except `modules`, which it"
    " flagged on both layers as launch dominated: most of the Prism wall clock"
    " was process startup, subtracted rather than measured. Its ratio would be an"
    " artifact of that subtraction, so it is named here instead of quoted.",
    "Log-log slopes of time against input size came back between 0.94 and 1.07 on"
    " both sides, which is to say linear on both. The Prism lexer is a constant"
    " factor behind rather than asymptotically worse, and the size of that"
    " constant is the thing to keep reporting.",
    "Peak resident set is the other half of the cost, and it does not track"
    " throughput: the Prism side peaks higher on most classes and lower on the"
    " comment-heavy one, where it allocates less per byte of input than the token"
    " stream the Rust side materializes.",
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
        "Rust MB/s",
        "Prism MB/s",
        "ratio",
        "Rust peak",
        "Prism peak",
    ]
    return table(header, "llrrrrr", [list(row) for row in COST_ROWS])


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
