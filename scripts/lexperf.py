#!/usr/bin/env python3
"""Prism-to-Rust syntax-pipeline throughput, peak memory, and growth exponent.

Times two single-shot drivers over byte-identical frozen inputs: the compiler's
own front end (`benches/lexbench.rs`) and the Prism-language twin
(`benches/lexbench.pr`, compiled natively), each reading one file and running
one layer over it. Counts are the cross-implementation correctness control.
Only Prism-to-Prism baseline/candidate samples judge parser adoption speed:
the Rust parse path additionally distributes items into `Program`.

The Rust driver reports its own elapsed time, because a whole run there is
microseconds and process startup would swamp it. The Prism driver cannot:
reading a clock from Prism means installing an effect handler around the
measured region, and a handler changes the tier the whole program lowers at, so
an internally timed run would measure the handler instead of the lexer. That
side is timed from the outside with process startup subtracted, and a point is
kept only once the run is several times its own launch cost.

Every class is measured at a doubling ladder of input sizes, growing until the
Prism side exceeds a wall-clock budget. A constant factor is a cost; a ratio that
grows with input size is an algorithmic defect, so the fitted log-log slope of
time against bytes is reported beside the throughput. A slope near 1.0 is linear;
near 2.0 is quadratic and is the failure this exists to catch.

Peak resident set is the whole process, startup included, and is reported raw.
"""
import argparse
import datetime
import hashlib
import json
import math
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PARSER_ORACLE_COMMIT = "46886c1fa7064e4809020c1b788b3ee3531d6a63"
# Exact Ledger-B parser boundary from scripts/parser_baseline.py. Keep paths
# explicit: directory expansion would let a receipt silently omit a moved file.
PARSER_SOURCE_PATHS = (
    "crates/prism-syntax/src/coeffect.rs",
    "crates/prism-syntax/src/error/parse.rs",
    "crates/prism-syntax/src/grammar.lalrpop",
    "crates/prism-syntax/src/parse/mod.rs",
    "crates/prism-syntax/src/sugar.rs",
    "lib/std/Syntax/Cursor.pr",
    "lib/std/Syntax/Parse.pr",
    "lib/std/Syntax/Parse/Build.pr",
    "lib/std/Syntax/Parse/Decl.pr",
    "lib/std/Syntax/Parse/DeclClass.pr",
    "lib/std/Syntax/Parse/DeclStable.pr",
    "lib/std/Syntax/Parse/Expr.pr",
    "lib/std/Syntax/Parse/Pattern.pr",
    "lib/std/Syntax/Parse/Support.pr",
    "lib/std/Syntax/Parse/Type.pr",
)
LAYERS = ("raw", "layout", "parse")
KIB = 1024
# The committed corpus row reads these trees from the current checkout.
CORPUS_TREES = ("lib/std", "packages")
# A walk smaller than this is a broken enumeration, not a small corpus.
CORPUS_MIN_FILES = 100
# The doubling ladder, in bytes. A class stops climbing when the Prism side
# passes the budget, so the pathological layers report at the size they reach.
SIZES = [8 * KIB << i for i in range(10)]
# `/usr/bin/time -l` (BSD) reports peak RSS in bytes on this line.
MAXRSS_RE = re.compile(r"^\s*(\d+)\s+maximum resident set size", re.M)
# GNU `/usr/bin/time -v` spells the same number in kilobytes.
MAXRSS_GNU_RE = re.compile(r"Maximum resident set size \(kbytes\):\s*(\d+)")
# A fit needs enough points to mean anything.
MIN_FIT_POINTS = 3
# An externally timed run counts only once it is this many times its own process
# startup, below which the subtraction is mostly measuring the launch.
FLOOR_FACTOR = 3.0


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, text=True, capture_output=True, **kw)


def bytes_identity(data, path):
    return {
        "path": path,
        "bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def file_identity(path):
    """Stable identity for one source or executable used by a receipt."""
    path = Path(path)
    digest = hashlib.sha256()
    with path.open("rb") as src:
        for chunk in iter(lambda: src.read(1024 * 1024), b""):
            digest.update(chunk)
    try:
        shown = str(path.resolve().relative_to(ROOT))
    except ValueError:
        shown = str(path.resolve())
    return {
        "path": shown,
        "bytes": path.stat().st_size,
        "sha256": digest.hexdigest(),
    }


def parser_source_identities():
    """Every handwritten/Rust parser source pinned by the identity oracle."""
    if len(PARSER_SOURCE_PATHS) != len(set(PARSER_SOURCE_PATHS)):
        sys.exit("duplicate path in exact Ledger-B parser boundary")
    return [file_identity(ROOT / rel) for rel in PARSER_SOURCE_PATHS]


def git_text(commit, rel):
    result = run(["git", "show", f"{commit}:{rel}"])
    if result.returncode:
        sys.exit(result.stderr.strip() or f"cannot read {commit}:{rel}")
    return result.stdout


def frozen_corpus():
    """Source corpus read only from the frozen oracle tree.

    Returning named units lets the module workload preserve file boundaries
    while every candidate sees byte-identical inputs.
    """
    result = run(["git", "ls-tree", "-r", "--name-only", PARSER_ORACLE_COMMIT])
    if result.returncode:
        sys.exit(result.stderr.strip() or "cannot enumerate parser oracle tree")
    paths = result.stdout.splitlines()
    stdlib_paths = sorted(
        p for p in paths if p.startswith("lib/std/") and p.endswith(".pr")
    )
    example_paths = sorted(
        p for p in paths
        if p.startswith("examples/")
        and p.endswith(".pr")
        and "/" not in p.removeprefix("examples/")
    )
    if not stdlib_paths or not example_paths:
        sys.exit("frozen syntax benchmark corpus is empty")
    stdlib = [(p, git_text(PARSER_ORACLE_COMMIT, p)) for p in stdlib_paths]
    examples = [(p, git_text(PARSER_ORACLE_COMMIT, p)) for p in example_paths]
    return stdlib, examples


def committed_corpus():
    """Every committed `.pr` under the current tree's corpus roots, from disk.

    Enumerated with `git ls-files` so the row measures exactly what is
    committed; the bytes come from the working tree, and any local drift is
    already visible in the receipt's `worktree_changes`.
    """
    result = run(["git", "ls-files", "--", *CORPUS_TREES])
    if result.returncode:
        sys.exit(result.stderr.strip() or "cannot enumerate the committed corpus")
    paths = sorted(p for p in result.stdout.splitlines() if p.endswith(".pr"))
    if len(paths) < CORPUS_MIN_FILES:
        sys.exit(f"committed corpus walk found only {len(paths)} files; "
                 f"the enumeration is broken")
    return [(p, (ROOT / p).read_text()) for p in paths]


def host_identity():
    """Best-effort machine and timer identity; unavailable fields stay visible."""
    def probe(cmd):
        result = run(cmd)
        return result.stdout.strip() if result.returncode == 0 else None

    cpu = platform.processor() or platform.machine()
    memory = None
    power = None
    if sys.platform == "darwin":
        cpu = probe(["sysctl", "-n", "machdep.cpu.brand_string"]) or cpu
        memory = probe(["sysctl", "-n", "hw.memsize"])
        power = probe(["pmset", "-g", "custom"])
    elif Path("/proc/cpuinfo").exists():
        for line in Path("/proc/cpuinfo").read_text().splitlines():
            if line.lower().startswith("model name"):
                cpu = line.split(":", 1)[-1].strip()
                break
        if Path("/proc/meminfo").exists():
            memory = Path("/proc/meminfo").read_text().splitlines()[0]
        power = probe(["sh", "-c",
                       "cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor"])
    clock = time.get_clock_info("perf_counter")
    return {
        "platform": platform.platform(),
        "machine": platform.machine(),
        "cpu": cpu,
        "logical_cpus": os.cpu_count(),
        "memory": memory,
        "power": power,
        "timer": {
            "implementation": clock.implementation,
            "monotonic": clock.monotonic,
            "adjustable": clock.adjustable,
            "resolution_seconds": clock.resolution,
        },
    }


def command_version(cmd):
    result = run(cmd)
    return {
        "command": cmd,
        "status": result.returncode,
        "stdout": result.stdout.strip(),
        "stderr": result.stderr.strip(),
    }


def build_drivers(quiet):
    """Build both drivers, returning (rust_driver, prism_cli) paths."""
    if not quiet:
        print("building the compiler and both drivers...", file=sys.stderr)
    # Build the compiler binary in the same invocation as the Rust driver. A
    # pre-existing target/release/prism may belong to another tree, which would
    # make an otherwise well-identified receipt compile the Prism twin with a
    # stale compiler.
    r = run([
        "cargo", "build", "--release", "--bin", "prism", "--bench", "lexbench",
        "--message-format=json",
    ])
    if r.returncode != 0:
        sys.exit(f"cargo build failed:\n{r.stderr}")
    rust = None
    for line in r.stdout.splitlines():
        try:
            msg = json.loads(line)
        except ValueError:
            continue
        if msg.get("reason") != "compiler-artifact":
            continue
        if msg.get("target", {}).get("name") == "lexbench" and msg.get("executable"):
            rust = Path(msg["executable"])
    if rust is None:
        sys.exit("could not locate the lexbench executable in cargo's output")
    prism_cli = ROOT / "target" / "release" / "prism"
    if not prism_cli.exists():
        sys.exit(f"{prism_cli} is missing; run `just build-release` first")
    return rust, prism_cli


def compile_prism_driver(prism_cli, out):
    r = run([str(prism_cli), "benches/lexbench.pr", "-o", str(out)])
    if r.returncode != 0:
        sys.exit(f"compiling benches/lexbench.pr failed:\n{r.stdout}{r.stderr}")
    return out


def sources(pattern):
    return sorted(p for p in ROOT.glob(pattern) if p.is_file())


def repeat_to(text, size):
    """`text` repeated and cut on a line boundary to about `size` bytes."""
    while len(text) < size:
        text += text
    cut = text.rfind("\n", 0, size)
    return text[:cut + 1] if cut >= 0 else text[:size]


def lines_to(make, size):
    """Lines from `make(i)` accumulated to about `size` bytes."""
    out = []
    total = 0
    i = 0
    while total < size:
        line = make(i)
        out.append(line)
        total += len(line)
        i += 1
    return "".join(out)


def complete_to(units, size):
    """Whole source units accumulated to at least `size` bytes.

    Parser benchmarks cannot cut arbitrary source text at a byte or line
    boundary: a line can still be the middle of a declaration. Cycling complete
    units keeps every point syntactically closed.
    """
    out = []
    total = 0
    i = 0
    while total < size:
        unit = units[i % len(units)]
        out.append(unit)
        total += len(unit)
        i += 1
    return "".join(out)


def classes(layer, corpus=None):
    """(name, description, size -> text) for every corpus class."""
    stdlib_named, example_named = corpus or frozen_corpus()
    stdlib_texts = [text for _, text in stdlib_named]
    stdlib = "".join(stdlib_texts)
    stdlib_units = [text.rstrip() + "\n" for text in stdlib_texts]
    biggest_name, example = max(
        example_named, key=lambda pair: len(pair[1].encode("utf-8"))
    )
    example_unit = example.rstrip() + "\n"
    biggest_name = Path(biggest_name).name
    nest = "(" * 500 + "1" + ")" * 500
    if layer == "parse":
        comment_sentinel = "fn comments_sentinel() : Int = 0\n"
        return [
            ("stdlib", "complete standard-library source units",
             lambda n: complete_to(stdlib_units, n)),
            ("example", f"complete copies of largest example ({biggest_name})",
             lambda n: complete_to([example_unit], n)),
            ("flat", "wide flat generated definitions",
             lambda n: lines_to(
                 lambda i: f"fn f{i}(x : Int) : Int = x + {i}\n", n)),
            ("comments", "comment-dominated source with one declaration",
             lambda n: lines_to(
                 lambda i: (
                     f"-- line {i}: ordinary words carrying no tokens at all\n"
                 ),
                 max(0, n - len(comment_sentinel))) + comment_sentinel),
            ("nesting", "500-deep bracket nesting per definition",
             lambda n: lines_to(lambda i: f"fn n{i}() : Int = {nest}\n", n)),
            ("interp", "nested string interpolation",
             lambda n: lines_to(
                 lambda i: (
                     f'fn s{i}() : String = "a{{"c{{show_int(1)}}d"}}b"\n'
                 ),
                 n)),
        ]
    return [
        ("stdlib", "standard-library sources",
         lambda n: repeat_to(stdlib, n)),
        ("example", f"largest example ({biggest_name})",
         lambda n: repeat_to(example, n)),
        ("flat", "wide flat generated definitions",
         lambda n: lines_to(lambda i: f"fn f{i}(x : Int) : Int = x + {i}\n", n)),
        ("comments", "comment-dominated source",
         lambda n: lines_to(
             lambda i: f"-- line {i}: ordinary words carrying no tokens at all\n",
             n)),
        ("nesting", "500-deep bracket nesting per definition",
         lambda n: lines_to(lambda i: f"fn n{i}() : Int = {nest}\n", n)),
        ("interp", "nested string interpolation",
         lambda n: lines_to(
             lambda i: f'fn s{i}() : String = "a{{"c{{show_int(1)}}d"}}b"\n', n)),
    ]


def peak_rss(cmd):
    """Peak RSS in bytes for one run of `cmd`, or None if unmeasurable."""
    timer = shutil.which("gtime") or shutil.which("time", path="/usr/bin")
    if timer is None:
        return None
    for flag, pattern, scale in (("-l", MAXRSS_RE, 1), ("-v", MAXRSS_GNU_RE, 1024)):
        r = run([timer, flag] + cmd)
        m = pattern.search(r.stderr)
        if m:
            return int(m.group(1)) * scale
    return None


def measure(driver, paths, layer, reps):
    """Best-of-`reps` timing and raw samples over `paths`.

    Returns `(wall, inner, count, samples)`. `wall` is the whole process,
    launch included. `inner` is what the driver reports for the layer itself,
    or None when it does not report one.
    """
    best = None
    samples = []
    tokens = 0
    for _ in range(reps):
        wall = 0.0
        inner = 0.0
        timed = True
        tokens = 0
        for path in paths:
            t0 = time.perf_counter()
            r = subprocess.run([str(driver), str(path), layer], cwd=ROOT,
                               text=True, capture_output=True)
            wall += time.perf_counter() - t0
            if r.returncode != 0:
                return (None, None,
                        f"{path.name}: {r.stderr.strip() or 'died'}", samples)
            fields = r.stdout.split()
            tokens += int(fields[0])
            if len(fields) > 1:
                inner += int(fields[1]) / 1e9
            else:
                timed = False
        here = (wall, inner if timed else None)
        samples.append({"wall_seconds": here[0], "inner_seconds": here[1]})
        if best is None or (here[1] or here[0]) < (best[1] or best[0]):
            best = here
    if best is None:
        return None, None, "no repetitions requested", samples
    return best[0], best[1], tokens, samples


def slope(points):
    """Log-log least-squares slope of time against bytes."""
    if len(points) < MIN_FIT_POINTS:
        return None
    xs = [math.log(b) for b, _ in points]
    ys = [math.log(t) for _, t in points]
    mx = sum(xs) / len(xs)
    my = sum(ys) / len(ys)
    denom = sum((x - mx) ** 2 for x in xs)
    if denom == 0:
        return None
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / denom


class Bench:
    def __init__(self, rust, prism, startup, reps, budget, quiet):
        self.drivers = {"rust": rust, "prism": prism}
        self.startup = startup
        self.reps = reps
        self.budget = budget
        self.quiet = quiet

    def one(self, side, paths, layer):
        """`(seconds, tokens, solid)` for one input, or `(None, message, _)`.

        A driver that reports its own elapsed time is taken at its word. One that
        does not is timed from the outside with process startup subtracted, and
        the point is `solid` only when the run is long enough that the
        subtraction cannot dominate it.
        """
        wall, inner, tokens, raw_samples = measure(
            self.drivers[side], paths, layer, self.reps)
        if wall is None:
            return None, tokens, False, raw_samples
        if inner is not None:
            samples = [sample["inner_seconds"] for sample in raw_samples]
            return inner, tokens, True, samples
        launch = self.startup[side] * len(paths)
        samples = [
            max(sample["wall_seconds"] - launch, 1e-9)
            for sample in raw_samples
        ]
        return (max(wall - launch, 1e-9), tokens,
                wall >= FLOOR_FACTOR * launch, samples)

    def launch_share(self, side, count, secs):
        """Fraction of an externally timed wall clock that was process launch."""
        launch = self.startup[side] * count
        return launch / (launch + secs)

    def floor_note(self):
        return (f"nothing measurable: no run reached {FLOOR_FACTOR:g}x its "
                f"{self.startup['prism'] * 1e3:.1f} ms process launch before the "
                f"{self.budget:g}s budget stopped the climb")

    def ladder(self, name, layer, make, tmp):
        """Climb the size ladder until the Prism side passes the budget."""
        row = {"class": name, "layer": layer, "points": {}, "note": "",
               "caveat": "", "samples": {}, "inputs": {}, "gate": "timing",
               "quotable": True}
        widest_path = None
        for size in SIZES:
            # The layer belongs in the cache key. `classes` hands the parse
            # layer different generators from the lex layers for exactly the
            # reason `complete_to` documents, so a name keyed on class and size
            # alone lets whichever layer runs first serve its input to the rest:
            # the parse layer then measured a line-boundary cut through the
            # middle of a declaration and reported the resulting rejection as a
            # driver failure.
            path = tmp / f"{name}-{layer}-{size}.pr"
            if not path.exists():
                path.write_text(make(size))
            actual = path.stat().st_size
            row["inputs"][actual] = bytes_identity(
                path.read_bytes(), f"{name}-{size}.pr"
            )
            if not self.quiet:
                print(f"  {name:<9} {layer:<6} {actual // KIB:>5} KiB",
                      file=sys.stderr)
            here = {}
            solid = True
            for side in ("rust", "prism"):
                secs, tokens, ok, samples = self.one(side, [path], layer)
                if secs is None:
                    row["note"] = f"{side} failed at {actual} bytes: {tokens}"
                    return row
                here[side] = (secs, tokens)
                row["samples"].setdefault(actual, {})[side] = samples
                solid = solid and ok
            if here["rust"][1] != here["prism"][1]:
                row["note"] = (f"count mismatch at {actual} bytes: "
                               f"rust={here['rust'][1]} prism={here['prism'][1]}")
                return row
            # Sizes a process launch could dominate are climbed through, not
            # recorded: a noise-floor point would bend the fitted slope.
            if solid:
                row["points"][actual] = here
                row["tokens"] = here["rust"][1]
                widest_path = path
            if here["prism"][0] > self.budget:
                break
        if not row["points"]:
            row["note"] = self.floor_note()
        if widest_path is not None:
            for side in ("rust", "prism"):
                row[f"{side}_rss"] = peak_rss(
                    [str(self.drivers[side]), str(widest_path), layer])
        return row

    def modules(self, layer, paths, corpus_inputs):
        """Many small frozen modules, one process per source file.

        This class pays one process launch per module by construction, so unlike
        the ladder it cannot climb out of the startup floor by growing its input.
        It remains a correctness/count and operational-cost report, never a hard
        timing gate.
        """
        size = sum(p.stat().st_size for p in paths)
        row = {"class": "modules", "layer": layer, "points": {}, "note": "",
               "caveat": "", "files": len(paths), "samples": {},
               "inputs": corpus_inputs, "gate": "report-only",
               "quotable": True}
        if not self.quiet:
            print(f"  {'modules':<9} {layer:<6} {len(paths)} files",
                  file=sys.stderr)
        here = {}
        solid = True
        for side in ("rust", "prism"):
            secs, tokens, ok, samples = self.one(side, paths, layer)
            if secs is None:
                row["note"] = f"{side} failed: {tokens}"
                return row
            here[side] = (secs, tokens)
            row["samples"].setdefault(size, {})[side] = samples
            solid = solid and ok
            row[f"{side}_rss"] = None
        if here["rust"][1] != here["prism"][1]:
            row["note"] = (f"count mismatch: rust={here['rust'][1]} "
                           f"prism={here['prism'][1]}")
            return row
        if not solid:
            share = self.launch_share("prism", len(paths), here["prism"][0])
            row["quotable"] = False
            row["caveat"] = (f"launch-dominated: {share:.0%} of the Prism wall clock "
                             f"was process startup, subtracted rather than "
                             f"measured; timing is report-only")
        elif not row["caveat"]:
            row["caveat"] = (
                "one process per module; timing is report-only even above the "
                "launch floor"
            )
        row["points"][size] = here
        row["tokens"] = here["rust"][1]
        return row

    def whole_corpus(self, layer, path, files):
        """The entire committed tree as one closed input, a single solid point.

        The ladder classes repeat a fragment to size, so a fragment that is
        unrepresentative of real modules can report a flattering throughput.
        This row runs every committed corpus module through one process as one
        concatenated input, so the number beside the sampled rows is the
        corpus's own.
        """
        size = path.stat().st_size
        row = {"class": "corpus", "layer": layer, "points": {}, "note": "",
               "caveat": f"{files} committed modules concatenated whole",
               "files": files, "samples": {},
               "inputs": {size: bytes_identity(path.read_bytes(), path.name)},
               "gate": "timing", "quotable": True}
        if not self.quiet:
            print(f"  {'corpus':<9} {layer:<6} {size // KIB:>5} KiB",
                  file=sys.stderr)
        here = {}
        solid = True
        for side in ("rust", "prism"):
            secs, tokens, ok, samples = self.one(side, [path], layer)
            if secs is None:
                row["note"] = f"{side} failed: {tokens}"
                return row
            here[side] = (secs, tokens)
            row["samples"].setdefault(size, {})[side] = samples
            solid = solid and ok
            row[f"{side}_rss"] = peak_rss(
                [str(self.drivers[side]), str(path), layer])
        if here["rust"][1] != here["prism"][1]:
            row["note"] = (f"count mismatch: rust={here['rust'][1]} "
                           f"prism={here['prism'][1]}")
            return row
        if not solid:
            share = self.launch_share("prism", 1, here["prism"][0])
            row["quotable"] = False
            row["caveat"] = (f"launch-dominated: {share:.0%} of the Prism wall "
                             f"clock was process startup; timing is report-only")
            row["gate"] = "report-only"
        row["points"][size] = here
        row["tokens"] = here["rust"][1]
        return row


def report(rows, budget):
    head = (f"{'class':<9} {'layer':<7} {'at KiB':>7} {'rust MB/s':>10} "
            f"{'prism MB/s':>11} {'ratio':>8} {'rust n':>7} {'prism n':>8} "
            f"{'rust RSS':>9} {'prism RSS':>10}")
    print(head)
    print("-" * len(head))
    for r in rows:
        if not r["points"]:
            print(f"{r['class']:<9} {r['layer']:<7} "
                  f"{r['note'] or 'no point recorded'}")
            continue
        widest = max(r["points"])
        rust_s, _ = r["points"][widest]["rust"]
        prism_s, _ = r["points"][widest]["prism"]
        fits = {
            side: slope([(b, p[side][0]) for b, p in sorted(r["points"].items())])
            for side in ("rust", "prism")
        }
        cell = {s: f"{fits[s]:>7.2f}" if fits[s] is not None else f"{'-':>7}"
                for s in fits}
        rss = {}
        for side in ("rust", "prism"):
            v = r.get(f"{side}_rss")
            rss[side] = f"{v / 1e6:>8.1f}M" if v else f"{'-':>9}"
        # A row whose wall clock was mostly process startup has already been
        # declared an artifact of the subtraction, so it does not also get to
        # print the artifact as a throughput: a near-zero denominator renders as
        # a spectacular rate and a 0x ratio, and a number in a receipt gets
        # quoted whatever the footnote beside it says.
        if r.get("quotable", True):
            rates = (f"{widest / rust_s / 1e6:>10.1f} "
                     f"{widest / prism_s / 1e6:>11.3f} "
                     f"{prism_s / rust_s:>7.0f}x")
        else:
            rates = f"{'-':>10} {'-':>11} {'-':>8}"
        print(f"{r['class']:<9} {r['layer']:<7} {widest // KIB:>7} {rates} "
              f"{cell['rust']} {cell['prism']:>8} {rss['rust']} {rss['prism']:>10}")
        for kind in ("note", "caveat"):
            if r[kind]:
                print(f"{'':>9} {'':>7} {kind}: {r[kind]}")
    print()
    print("`rust n`/`prism n` are log-log slopes of time against bytes; "
          "1.0 is linear, 2.0 quadratic.")
    print(f"Each class climbs an 8 KiB doubling ladder until the Prism side "
          f"passes {budget:.1f}s, so `at KiB` differs by row.")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--reps", type=int, default=3,
                    help="timed runs per point; the best is reported (default 3)")
    ap.add_argument("--budget", type=float, default=2.0,
                    help="stop growing a class past this many Prism seconds")
    ap.add_argument("--layer", choices=LAYERS,
                    help="measure only one layer (default: all)")
    ap.add_argument("--quiet", action="store_true", help="no progress on stderr")
    ap.add_argument("--json", type=Path, metavar="PATH",
                    help="also write a machine-readable receipt with raw samples")
    ap.add_argument("--arm", choices=("baseline", "candidate"),
                    help="receipt arm (required with --json for gate evidence)")
    ap.add_argument("--pair", type=int,
                    help="one-based alternating run pair (required with --json)")
    args = ap.parse_args()
    if args.json and (args.arm is None or args.pair is None or args.pair < 1):
        ap.error("--json gate receipts require --arm and positive --pair")
    layers = (args.layer,) if args.layer else LAYERS

    rust, prism_cli = build_drivers(args.quiet)
    with tempfile.TemporaryDirectory(prefix="prism-lexperf-") as td:
        tmp = Path(td)
        corpus = frozen_corpus()
        frozen_modules = tmp / "frozen-modules"
        module_paths = []
        module_inputs = []
        for rel, text in corpus[0]:
            path = frozen_modules / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            module_paths.append(path)
            module_inputs.append(bytes_identity(text.encode("utf-8"), rel))
        prism = compile_prism_driver(prism_cli, tmp / "lexbench-prism")
        empty = tmp / "empty.pr"
        empty.write_text("")
        startup = {}
        startup_samples = {}
        for side, driver in (("rust", rust), ("prism", prism)):
            # One warm-up first: a cold first launch would set the floor every
            # later row is judged against.
            measure(driver, [empty], LAYERS[0], 1)
            wall, _inner, _tokens, samples = measure(
                driver, [empty], LAYERS[0], args.reps)
            startup[side] = wall
            startup_samples[side] = samples
        if not args.quiet:
            print(f"startup: rust {startup['rust'] * 1e3:.1f} ms, "
                  f"prism {startup['prism'] * 1e3:.1f} ms", file=sys.stderr)

        corpus_units = committed_corpus()
        corpus_file = tmp / "committed-corpus.pr"
        corpus_file.write_text(
            "".join(text.rstrip() + "\n" for _, text in corpus_units)
        )

        bench = Bench(rust, prism, startup, args.reps, args.budget, args.quiet)
        rows = []
        for layer in layers:
            for name, _desc, make in classes(layer, corpus):
                rows.append(bench.ladder(name, layer, make, tmp))
            rows.append(bench.modules(layer, module_paths, module_inputs))
            rows.append(
                bench.whole_corpus(layer, corpus_file, len(corpus_units))
            )
        report(rows, args.budget)
        if args.json:
            status = run([
                "git", "status", "--short", "--untracked-files=normal",
            ]).stdout.splitlines()
            oracle_changes = run([
                "git", "diff", "--name-only", PARSER_ORACLE_COMMIT, "--",
                *PARSER_SOURCE_PATHS,
            ]).stdout.splitlines()
            receipt = {
                "schema": "prism-lexperf-v1",
                "generated_at": (
                    datetime.datetime.now(datetime.timezone.utc).isoformat()
                ),
                "commit": run(["git", "rev-parse", "HEAD"]).stdout.strip(),
                "tree": run(["git", "rev-parse", "HEAD^{tree}"]).stdout.strip(),
                "worktree_changes": status,
                "parser_oracle_commit": PARSER_ORACLE_COMMIT,
                "parser_source_changes_from_oracle": oracle_changes,
                "host": host_identity(),
                "build_profile": "release",
                "arm": args.arm,
                "pair": args.pair,
                "required_pair_order": (
                    ["baseline", "candidate"]
                    if args.pair % 2 == 1
                    else ["candidate", "baseline"]
                ),
                "toolchain": {
                    "cargo": command_version(["cargo", "--version"]),
                    "rustc": command_version(["rustc", "-Vv"]),
                },
                "source_identities": [
                    file_identity(ROOT / "scripts" / "lexperf.py"),
                    file_identity(ROOT / "benches" / "lexbench.rs"),
                    file_identity(ROOT / "benches" / "lexbench.pr"),
                    *parser_source_identities(),
                ],
                "binary_identities": {
                    "rust_driver": file_identity(rust),
                    "prism_compiler": file_identity(prism_cli),
                    "prism_driver": file_identity(prism),
                },
                "layers": list(layers),
                "repetitions": args.reps,
                "budget_seconds": args.budget,
                "corpus": {
                    "commit": PARSER_ORACLE_COMMIT,
                    "stdlib": module_inputs,
                    "examples": [
                        bytes_identity(text.encode("utf-8"), rel)
                        for rel, text in corpus[1]
                    ],
                },
                "startup_seconds": startup,
                "startup_samples": startup_samples,
                "rows": rows,
            }
            args.json.parent.mkdir(parents=True, exist_ok=True)
            args.json.write_text(json.dumps(receipt, indent=2, sort_keys=True)
                                 + "\n")
        if any(r["note"] for r in rows):
            sys.exit(1)


if __name__ == "__main__":
    main()
