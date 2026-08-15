#!/usr/bin/env python3
"""Run Prism's local correctness gates without embedding shell in the justfile."""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Sequence


ROOT = Path(__file__).resolve().parent.parent
FAILURES = re.compile(r"test result:|FAILED|error\[")
ORACLE_TARGETS = ("native", "snapshots", "compiler")


def run(command: Sequence[str], *, env: dict[str, str] | None = None) -> int:
    return subprocess.run(command, cwd=ROOT, env=env, check=False).returncode


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
    lines = [line for line in result.stdout.splitlines() if FAILURES.search(line)]
    if lines:
        print(*lines, sep="\n")
    return result.returncode


def test_targets(
    targets: Sequence[str],
    *,
    env: dict[str, str],
    cargo_flags: Sequence[str] = (),
    name_filter: str | None = None,
) -> int:
    selectors = [item for target in targets for item in ("--test", target)]
    filters = [name_filter] if name_filter else []
    if shutil.which("cargo-nextest"):
        return run(
            [
                "cargo",
                "nextest",
                "run",
                "--profile",
                "ci",
                *cargo_flags,
                *selectors,
                *filters,
            ],
            env=env,
        )
    return run_filtered(
        ["cargo", "test", *cargo_flags, *selectors, *filters], env=env
    )


def oracles(cargo_flags: Sequence[str]) -> int:
    env = os.environ.copy()
    env["PRISM_COMPILER_CACHE"] = "0"
    # Core lint bypasses the typed-SCC cache exercised by cache-specific tests;
    # opt-equiv provides denser, cache-free inter-pass lint coverage separately.
    return test_targets(ORACLE_TARGETS, env=env, cargo_flags=cargo_flags)


def development() -> int:
    print(
        "gate-dev: development subset; 'just gate' remains authoritative",
        flush=True,
    )
    commands = (
        ["cargo", "check", "--all-targets"],
        ["cargo", "fmt", "--all", "--check"],
    )
    for command in commands:
        status = run(command)
        if status:
            return status

    stats_env = os.environ.copy()
    stats_env["PRISM_COMPILER_STATS"] = "1"
    status = run(
        ["cargo", "run", "--quiet", "--", "check", "examples/accum.pr"],
        env=stats_env,
    )
    if status:
        return status

    test_env = os.environ.copy()
    test_env["PRISM_COMPILER_CACHE"] = "0"
    return test_targets(("snapshots", "compiler"), env=test_env)


def native_slice() -> int:
    with tempfile.TemporaryDirectory(prefix="prism-gate-dev-") as directory:
        binary = Path(directory) / "program"
        build_env = os.environ.copy()
        build_env.update(PRISM_COMPILER_STATS="1", PRISM_EXPLAIN_CACHE="1")
        status = run(
            [
                "cargo",
                "run",
                "--quiet",
                "--",
                "examples/accum.pr",
                "-o",
                str(binary),
            ],
            env=build_env,
        )
        if status:
            return status

    test_env = os.environ.copy()
    test_env.update(
        PRISM_COMPILER_CACHE="0", PRISM_SHARD_TOTAL="8", PRISM_SHARD_INDEX="0"
    )
    return test_targets(("native",), env=test_env, name_filter="parity::")


def usage() -> None:
    print("usage: gate.py {oracles [CARGO_FLAG...]|development|native-slice}")


def main(arguments: list[str]) -> int:
    if arguments and arguments[0] in {"-h", "--help"}:
        usage()
        return 0
    if not arguments:
        usage()
        return 2
    task, *rest = arguments
    if task == "oracles":
        return oracles(rest)
    if task == "development" and not rest:
        return development()
    if task == "native-slice" and not rest:
        return native_slice()
    usage()
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
