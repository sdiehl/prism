#!/usr/bin/env python3
"""Count the public items each workspace crate leaves undocumented.

`missing_docs` is not in the workspace lint table: the pre-commit clippy run
denies every warning, so a warn-level lint there would block every commit until
the debt reached zero. This script measures the debt instead, by checking each
library with `-W missing_docs` in a target directory of its own (the changed
flags would otherwise invalidate the ordinary build cache), and prints one count
per crate. The counts are transcribed into `scripts/scoreboard.py`.
"""

import json
import os
import subprocess
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def main():
    env = dict(
        os.environ,
        RUSTFLAGS="-W missing_docs",
        CARGO_TARGET_DIR=str(ROOT / "target" / "docs-debt"),
    )
    out = subprocess.run(
        ["cargo", "check", "--workspace", "--lib", "--message-format=json"],
        cwd=ROOT,
        env=env,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    counts = Counter()
    for line in out.splitlines():
        msg = json.loads(line)
        if msg.get("reason") != "compiler-message":
            continue
        if not {"lib", "rlib"} & set(msg["target"]["kind"]):
            continue
        code = (msg["message"].get("code") or {}).get("code")
        if code == "missing_docs":
            counts[msg["target"]["name"].replace("_", "-")] += 1
    for name, n in sorted(counts.items()):
        print(f"{name}\t{n}")
    print(f"total\t{sum(counts.values())}")


if __name__ == "__main__":
    main()
