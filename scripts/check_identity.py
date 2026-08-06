#!/usr/bin/env python3
"""Check that one binary emits the same identity manifest twice."""

from __future__ import annotations

import difflib
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Sequence


ROOT = Path(__file__).resolve().parent.parent


def run(command: Sequence[str], *, env: dict[str, str] | None = None) -> int:
    return subprocess.run(command, cwd=ROOT, env=env, check=False).returncode


def main() -> int:
    status = run(["cargo", "build", "--release", "--features", "native"])
    if status:
        return status

    env = os.environ.copy()
    env["PRISM_BIN"] = "target/release/prism"
    with tempfile.TemporaryDirectory(prefix="prism-identity-") as directory:
        first = Path(directory) / "first.tsv"
        second = Path(directory) / "second.tsv"
        for output in (first, second):
            status = run(
                ["bash", "scripts/identity-manifest.sh", "--out", str(output)],
                env=env,
            )
            if status:
                return status
        first_text = first.read_text()
        second_text = second.read_text()

    if first_text != second_text:
        sys.stdout.writelines(
            difflib.unified_diff(
                first_text.splitlines(keepends=True),
                second_text.splitlines(keepends=True),
                fromfile="first manifest",
                tofile="second manifest",
            )
        )
        print("identity: manifest is nondeterministic", file=sys.stderr)
        return 1

    print("identity: manifest is deterministic across two runs")
    print(first_text, end="")
    return 0


if __name__ == "__main__":
    sys.exit(main())
