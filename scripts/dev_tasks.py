#!/usr/bin/env python3
"""Small development workflows used by the just recipes.

Keep process control, output filtering, and temporary files here instead of in
shell-heavy just recipes. Run ``dev_tasks.py --help`` for the supported tasks.
"""

from __future__ import annotations

import argparse
import os
import re
import shlex
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Sequence


ROOT = Path(__file__).resolve().parent.parent
JUSTFILES = (ROOT / "justfile", *sorted((ROOT / "just").glob("*.just")))
DIAGNOSTICS = re.compile(r"error|warning")
TEST_RESULTS = re.compile(r"test result:|FAILED|error\[|error:|panicked")
SNAPSHOT_RESULTS = re.compile(r"test result:|error\[|error:")


def run(command: Sequence[str], *, env: dict[str, str] | None = None) -> int:
    """Run a command at the repository root and return its status."""
    return subprocess.run(command, cwd=ROOT, env=env, check=False).returncode


def run_filtered(
    command: Sequence[str], pattern: re.Pattern[str], *, clean: str | None = None,
    env: dict[str, str] | None = None,
) -> int:
    """Run a command, print matching combined output, and preserve its status."""
    result = subprocess.run(
        command,
        cwd=ROOT,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    matches = [line for line in result.stdout.splitlines() if pattern.search(line)]
    if matches:
        print(*matches, sep="\n")
    elif clean:
        print(clean)
    return result.returncode


def cache_disabled() -> dict[str, str]:
    env = os.environ.copy()
    env["PRISM_COMPILER_CACHE"] = "0"
    return env


def cargo_filtered(arguments: list[str], clean: str) -> int:
    return run_filtered(["cargo", *arguments], DIAGNOSTICS, clean=clean)


def filtered_test(filter_text: str) -> int:
    arguments = shlex.split(filter_text)
    return run_filtered(
        ["cargo", "test", *arguments], TEST_RESULTS, env=cache_disabled()
    )


def update_snapshots(filter_text: str) -> int:
    env = cache_disabled()
    env["INSTA_UPDATE"] = "always"
    # `always` rewrites a drifted snapshot and lets the assertion pass, so a
    # non-zero status here is a genuine failure rather than the drift this task
    # exists to absorb, and reporting it is what keeps a red suite visible.
    # Without `--no-fail-fast` the first such failure also stops cargo before the
    # later targets run, leaving their snapshots stale while the task looks done.
    status = run_filtered(
        ["cargo", "test", "--no-fail-fast", *shlex.split(filter_text)],
        SNAPSHOT_RESULTS,
        env=env,
    )
    # Snapshot review is the point of this task, so show the drift either way.
    run(["git", "status", "--short", "tests/snapshots"])
    return status


def smoke(source: str) -> int:
    with tempfile.TemporaryDirectory(prefix="prism-smoke-") as directory:
        binary = Path(directory) / "program"
        status = run(
            ["cargo", "run", "--quiet", "--", source, "-o", str(binary)]
        )
        return status or run([str(binary)])


def lean_fuzz() -> int:
    status = subprocess.run(
        ["lake", "build"], cwd=ROOT / "models", check=False
    ).returncode
    if status:
        return status
    return run(
        [
            "cargo",
            "test",
            "--test",
            "differential",
            "lean_fuzz::generated_programs_match_lean_final_values",
            "--",
            "--ignored",
            "--exact",
            "--nocapture",
        ]
    )


def format_justfiles(*, check: bool) -> int:
    """Run just's formatter over the root file and every imported fragment."""
    for path in JUSTFILES:
        command = ["just", "--fmt"]
        if check:
            command.append("--check")
        command.extend(("--justfile", str(path)))
        status = run(command)
        if status:
            return status
    return 0


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    subcommands = command.add_subparsers(dest="task", required=True)

    subcommands.add_parser("build", help="build and show diagnostics only")

    check = subcommands.add_parser("check", help="check and show diagnostics only")
    check.add_argument(
        "scope", nargs="?", choices=("all", "core", "syntax"), default="all"
    )

    test = subcommands.add_parser("test", help="run one filtered cargo test")
    test.add_argument("filter")

    snapshots = subcommands.add_parser("snapshots", help="regenerate snapshots")
    snapshots.add_argument("filter", nargs="?", default="")

    smoke_parser = subcommands.add_parser("smoke", help="compile and run one file")
    smoke_parser.add_argument("source")

    subcommands.add_parser("lean-fuzz", help="run the Lean differential oracle")

    justfiles = subcommands.add_parser(
        "format-justfiles", help="format every justfile fragment"
    )
    justfiles.add_argument("--check", action="store_true")
    return command


def main() -> int:
    arguments = parser().parse_args()
    if arguments.task == "build":
        return cargo_filtered(["build"], "build clean")
    if arguments.task == "check":
        scopes = {
            "all": ["check", "--all-targets"],
            "core": ["check", "-p", "prism-core"],
            "syntax": ["check", "-p", "prism-syntax"],
        }
        return cargo_filtered(scopes[arguments.scope], "check clean")
    if arguments.task == "test":
        return filtered_test(arguments.filter)
    if arguments.task == "snapshots":
        return update_snapshots(arguments.filter)
    if arguments.task == "smoke":
        return smoke(arguments.source)
    if arguments.task == "lean-fuzz":
        return lean_fuzz()
    if arguments.task == "format-justfiles":
        return format_justfiles(check=arguments.check)
    raise AssertionError(f"unhandled task: {arguments.task}")


if __name__ == "__main__":
    sys.exit(main())
