#!/usr/bin/env python3
"""Reseat every golden family from one cold run and print a categorized diff.

The family-specific reseat commands (snapshot regeneration, the seam fixtures,
the tier and cost manifests, the HIR fixtures, the optimizer baseline, the
stdlib and package references, the book figures, the Lean fixture manifest)
each rerun most of the same cold compile work. This task stacks every accept
knob onto one cold pass over the golden-bearing test targets, follows it with
the generated-artifact stages, and ends with one diff grouped by family so the
review reads as "which gates moved" rather than a flat file list.

The run is deliberately canonical: the compiler cache is off, sharding and the
gate cache and the sentinel subset are refused, and every inherited PRISM_*
knob except the C compiler override is dropped so a stray experiment flag
cannot be baked into a golden.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Callable, Sequence

ROOT = Path(__file__).resolve().parent.parent
TEST_RESULTS = re.compile(r"test result:|error\[|error:|panicked|regenerated")

# The golden-bearing test targets of the one cold pass.
GOLDEN_TARGETS = ("compiler", "tooling", "snapshots", "native")

# Every accept knob the cold pass stacks. Each is read by exactly one gate;
# unrelated gates ignore the others, so stacking them is safe by construction.
ACCEPT_KNOBS = (
    "PRISM_ACCEPT_FRONTEND_FIXTURES",
    "PRISM_ACCEPT_SYNTAX_FIXTURES",
    "PRISM_ACCEPT_RESOLVED_FIXTURES",
    "PRISM_ACCEPT_CURSOR_FIXTURES",
    "PRISM_ACCEPT_TEST_FIXTURES",
    "PRISM_ACCEPT_HIR_FIXTURES",
    "PRISM_ACCEPT_TIER_MANIFEST",
    "PRISM_ACCEPT_COST_MANIFEST",
    "PRISM_ACCEPT_OPTIMIZER_BASELINE",
)

# Inherited environment that would make the run partial or non-canonical. The
# cost-manifest gate refuses a partial run on its own; refusing here names the
# cause before half an hour of work.
REFUSED_ENV = ("PRISM_GATE_CACHE", "PRISM_SHARD_TOTAL", "PRISM_SENTINEL_CORPUS")
# The one PRISM_* knob that must survive scrubbing: native builds need the
# matching clang when the ambient one is a different LLVM.
KEPT_ENV = ("PRISM_CC",)

PACKAGES = ("tzdb", "typst", "spectra", "tc")


def base_env() -> dict[str, str]:
    env = {
        key: value
        for key, value in os.environ.items()
        if not key.startswith(("PRISM_", "INSTA_")) or key in KEPT_ENV
    }
    return env


def run(command: Sequence[str], *, env: dict[str, str], cwd: Path = ROOT) -> int:
    return subprocess.run(command, cwd=cwd, env=env, check=False).returncode


def run_filtered(command: Sequence[str], *, env: dict[str, str]) -> int:
    result = subprocess.run(
        command,
        cwd=ROOT,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    lines = [line for line in result.stdout.splitlines() if TEST_RESULTS.search(line)]
    if lines:
        print(*lines, sep="\n")
    return result.returncode


def git_lines(arguments: Sequence[str]) -> list[str]:
    result = subprocess.run(
        ["git", *arguments],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        text=True,
        check=False,
    )
    return [line for line in result.stdout.splitlines() if line]


def clear_pending_snapshots() -> int:
    """A pending .snap.new masks the matching update; drop them first."""
    for pending in (ROOT / "tests" / "snapshots").rglob("*.snap.new"):
        pending.unlink()
    return 0


def golden_test_pass(env: dict[str, str]) -> int:
    pass_env = dict(env)
    pass_env["PRISM_COMPILER_CACHE"] = "0"
    pass_env["INSTA_UPDATE"] = "always"
    for knob in ACCEPT_KNOBS:
        pass_env[knob] = "1"
    selectors = [item for target in GOLDEN_TARGETS for item in ("--test", target)]
    # --no-fail-fast so one genuine failure cannot leave later families stale
    # while the task looks done; with INSTA_UPDATE=always a non-zero status is
    # a real failure, never the drift this task exists to absorb.
    return run_filtered(
        ["cargo", "test", "--release", "--no-fail-fast", *selectors], env=pass_env
    )


def rebuild_release(env: dict[str, str]) -> int:
    """No-op when nothing changed; after a docstring bless it re-embeds lib/."""
    return run(["cargo", "build", "--release", "--features", "native"], env=env)


def stdlib_reference(env: dict[str, str]) -> int:
    prism = str(ROOT / "target" / "release" / "prism")
    status = run([prism, "docs", "--stdlib", "--test", "--accept"], env=env)
    if status:
        return status
    if status := rebuild_release(env):
        return status
    return run([prism, "docs", "--stdlib", "--out", "docs/src/stdlib"], env=env)


def package_references(env: dict[str, str]) -> int:
    prism = str(ROOT / "target" / "release" / "prism")
    for package in PACKAGES:
        path = f"packages/{package}"
        for arguments in (
            [prism, "docs", path, "--test", "--accept"],
            [prism, "docs", path, "--out", f"docs/src/packages/{package}"],
            [prism, "docs", path, "--out", f"{path}/docs"],
        ):
            if status := run(arguments, env=env):
                return status
    return 0


def stdlib_digests(env: dict[str, str]) -> int:
    """Re-run after the docs stages so blessed sources feed the digests."""
    digest_env = dict(env)
    digest_env["PRISM_COMPILER_CACHE"] = "0"
    digest_env["INSTA_UPDATE"] = "always"
    return run_filtered(
        ["cargo", "test", "--release", "--test", "snapshots", "shape_digests"],
        env=digest_env,
    )


def book_figures(env: dict[str, str]) -> int:
    figure_env = dict(env)
    figure_env["PRISM_BIN"] = str(ROOT / "target" / "release" / "prism")
    return run(["bash", "docs/scripts/gen-core.sh"], env=figure_env)


def lean_fixture_manifest(env: dict[str, str]) -> int:
    if shutil.which("lake") is None:
        print("lean fixture manifest: skipped, `lake` is not installed")
        return 0
    # The manifest pins the debug binary's output, matching its CI job.
    if status := run(["cargo", "build"], env=env):
        return status
    return run(["./gen_fixtures.sh"], env=env, cwd=ROOT / "models")


def frozen_parser_corpus(env: dict[str, str]) -> int:
    """Check only: the compaction corpus is frozen against a pinned oracle, so
    drift here is investigated, never blanket-accepted."""
    return run(["just", "parser-corpus", "check"], env=env)


# The families of the categorized diff, first match wins.
FAMILIES: tuple[tuple[str, Callable[[str], bool]], ...] = (
    ("insta snapshots", lambda p: p.startswith("tests/snapshots/")),
    ("HIR fixtures", lambda p: p.startswith("tests/fixtures/hir/")),
    ("seam fixtures", lambda p: p.startswith("tests/fixtures/")),
    (
        "tier manifest and ratchet",
        lambda p: p in ("tests/tier_manifest.txt", "tests/tier_ratchet.txt"),
    ),
    ("cost manifest", lambda p: p == "tests/cost_manifest.txt"),
    ("optimizer baseline", lambda p: p == "tests/optimizer_baseline.txt"),
    ("stdlib reference", lambda p: p.startswith("docs/src/stdlib/")),
    (
        "package references",
        lambda p: p.startswith("docs/src/packages/")
        or (p.startswith("packages/") and "/docs/" in p),
    ),
    (
        "doctest expectations",
        lambda p: p.endswith(".pr") and p.startswith(("lib/", "packages/")),
    ),
    ("book figures", lambda p: p.startswith("docs/examples/")),
    ("Lean fixture manifest", lambda p: p.startswith("models/fixtures/")),
)
OUTSIDE = "outside every family (review by hand)"


def categorized_diff(start_head: str, dirty_at_start: set[str]) -> None:
    changed = git_lines(["diff", "--name-only", start_head])
    changed += git_lines(["ls-files", "--others", "--exclude-standard"])
    grouped: dict[str, list[str]] = {}
    for path in sorted(set(changed)):
        for label, member in FAMILIES:
            if member(path):
                break
        else:
            label = OUTSIDE
        grouped.setdefault(label, []).append(path)

    print("\n== accept: categorized diff ==")
    if not grouped:
        print("every golden family is already current")
        return
    order = [label for label, _ in FAMILIES] + [OUTSIDE]
    for label in order:
        paths = grouped.get(label)
        if not paths:
            continue
        print(f"{label}: {len(paths)} file(s)")
        for path in paths:
            marker = "  (dirty before the run)" if path in dirty_at_start else ""
            print(f"  {path}{marker}")
    untouched = [label for label, _ in FAMILIES if label not in grouped]
    if untouched:
        print(f"unchanged: {', '.join(untouched)}")


def main() -> int:
    for name in REFUSED_ENV:
        if os.environ.get(name):
            print(
                f"accept: refusing to run with {name} set; the reseat must come "
                "from one cold, unsharded, full-corpus run",
                file=sys.stderr,
            )
            return 2

    env = base_env()
    start_head = git_lines(["rev-parse", "HEAD"])[0]
    dirty_at_start = set(git_lines(["diff", "--name-only", "HEAD"]))
    dirty_at_start |= set(git_lines(["ls-files", "--others", "--exclude-standard"]))

    stages: tuple[tuple[str, Callable[[], int]], ...] = (
        ("clear pending snapshots", clear_pending_snapshots),
        ("release build", lambda: rebuild_release(env)),
        ("golden test pass (cold)", lambda: golden_test_pass(env)),
        ("stdlib doctests and reference", lambda: stdlib_reference(env)),
        ("package doctests and references", lambda: package_references(env)),
        ("stdlib digests", lambda: stdlib_digests(env)),
        ("book figures", lambda: book_figures(env)),
        ("Lean fixture manifest", lambda: lean_fixture_manifest(env)),
        ("frozen parser corpus (check only)", lambda: frozen_parser_corpus(env)),
    )
    failures: list[str] = []
    for label, stage in stages:
        print(f"== {label}")
        if stage():
            failures.append(label)

    categorized_diff(start_head, dirty_at_start)
    if failures:
        print(
            "\naccept: {} stage(s) reported genuine failures (not drift):\n  {}".format(
                len(failures), "\n  ".join(failures)
            ),
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
