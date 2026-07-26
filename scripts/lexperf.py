#!/usr/bin/env python3
"""Prism-to-Rust lexer throughput, peak memory, and growth exponent.

Times two single-shot drivers that do the same work in the same shape: the
compiler's own lexer (`benches/lexbench.rs`) and the Prism-language lexer
(`benches/lexbench.pr`, compiled natively), each reading one file and running
one layer over it.

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
import json
import math
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LAYERS = ("raw", "layout")
KIB = 1024
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


def build_drivers(quiet):
    """Build both drivers, returning (rust_driver, prism_cli) paths."""
    if not quiet:
        print("building the compiler and both drivers...", file=sys.stderr)
    r = run(["cargo", "build", "--release", "--bench", "lexbench",
             "--message-format=json"])
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


def classes():
    """(name, description, size -> text) for every corpus class."""
    stdlib = "".join(p.read_text() for p in sources("lib/std/**/*.pr"))
    biggest = max(sources("examples/*.pr"), key=lambda p: p.stat().st_size)
    example = biggest.read_text()
    nest = "(" * 500 + "1" + ")" * 500
    return [
        ("stdlib", "standard-library sources",
         lambda n: repeat_to(stdlib, n)),
        ("example", f"largest example ({biggest.name})",
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
    """Best-of-`reps` timing over `paths`, or `(None, message)` on failure.

    Returns `(wall, inner, tokens)`. `wall` is the whole process, launch
    included. `inner` is what the driver reports for the layer itself, or None
    when it does not report one.
    """
    best = None
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
                return None, None, f"{path.name}: {r.stderr.strip() or 'died'}"
            fields = r.stdout.split()
            tokens += int(fields[0])
            if len(fields) > 1:
                inner += int(fields[1]) / 1e9
            else:
                timed = False
        here = (wall, inner if timed else None)
        if best is None or (here[1] or here[0]) < (best[1] or best[0]):
            best = here
    if best is None:
        return None, None, "no repetitions requested"
    return best[0], best[1], tokens


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
        wall, inner, tokens = measure(self.drivers[side], paths, layer, self.reps)
        if wall is None:
            return None, tokens, False
        if inner is not None:
            return inner, tokens, True
        launch = self.startup[side] * len(paths)
        return max(wall - launch, 1e-9), tokens, wall >= FLOOR_FACTOR * launch

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
               "caveat": ""}
        widest_path = None
        for size in SIZES:
            path = tmp / f"{name}-{size}.pr"
            if not path.exists():
                path.write_text(make(size))
            actual = path.stat().st_size
            if not self.quiet:
                print(f"  {name:<9} {layer:<6} {actual // KIB:>5} KiB",
                      file=sys.stderr)
            here = {}
            solid = True
            for side in ("rust", "prism"):
                secs, tokens, ok = self.one(side, [path], layer)
                if secs is None:
                    row["note"] = f"{side} failed at {actual} bytes: {tokens}"
                    return row
                here[side] = (secs, tokens)
                solid = solid and ok
            if here["rust"][1] != here["prism"][1]:
                row["note"] = (f"token mismatch at {actual} bytes: "
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

    def modules(self, layer):
        """Many small modules: one process per file over the real sources.

        This class pays one process launch per module by construction, so unlike
        the ladder it cannot climb out of the startup floor by growing its input.
        A launch-dominated result is therefore disclosed rather than dropped: the
        corpus class is required, and the note says how much of the wall clock
        was subtracted instead of measured.
        """
        paths = sources("lib/std/**/*.pr")
        size = sum(p.stat().st_size for p in paths)
        row = {"class": "modules", "layer": layer, "points": {}, "note": "",
               "caveat": "", "files": len(paths)}
        if not self.quiet:
            print(f"  {'modules':<9} {layer:<6} {len(paths)} files",
                  file=sys.stderr)
        here = {}
        solid = True
        for side in ("rust", "prism"):
            secs, tokens, ok = self.one(side, paths, layer)
            if secs is None:
                row["note"] = f"{side} failed: {tokens}"
                return row
            here[side] = (secs, tokens)
            solid = solid and ok
            row[f"{side}_rss"] = None
        if here["rust"][1] != here["prism"][1]:
            row["note"] = (f"token mismatch: rust={here['rust'][1]} "
                           f"prism={here['prism'][1]}")
            return row
        if not solid:
            share = self.launch_share("prism", len(paths), here["prism"][0])
            row["caveat"] = (f"launch-dominated: {share:.0%} of the Prism wall clock "
                             f"was process startup, subtracted rather than "
                             f"measured, so this throughput is approximate")
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
        print(f"{r['class']:<9} {r['layer']:<7} {widest // KIB:>7} "
              f"{widest / rust_s / 1e6:>10.1f} {widest / prism_s / 1e6:>11.3f} "
              f"{prism_s / rust_s:>7.0f}x "
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
    ap.add_argument("--layer", choices=LAYERS, help="measure only one layer")
    ap.add_argument("--quiet", action="store_true", help="no progress on stderr")
    args = ap.parse_args()
    layers = (args.layer,) if args.layer else LAYERS

    rust, prism_cli = build_drivers(args.quiet)
    with tempfile.TemporaryDirectory(prefix="prism-lexperf-") as td:
        tmp = Path(td)
        prism = compile_prism_driver(prism_cli, tmp / "lexbench-prism")
        empty = tmp / "empty.pr"
        empty.write_text("")
        startup = {}
        for side, driver in (("rust", rust), ("prism", prism)):
            # One warm-up first: a cold first launch would set the floor every
            # later row is judged against.
            measure(driver, [empty], LAYERS[0], 1)
            wall, _inner, _tokens = measure(driver, [empty], LAYERS[0], args.reps)
            startup[side] = wall
        if not args.quiet:
            print(f"startup: rust {startup['rust'] * 1e3:.1f} ms, "
                  f"prism {startup['prism'] * 1e3:.1f} ms", file=sys.stderr)

        bench = Bench(rust, prism, startup, args.reps, args.budget, args.quiet)
        rows = []
        for layer in layers:
            for name, _desc, make in classes():
                rows.append(bench.ladder(name, layer, make, tmp))
            rows.append(bench.modules(layer))
        report(rows, args.budget)
        if any(r["note"] for r in rows):
            sys.exit(1)


if __name__ == "__main__":
    main()
