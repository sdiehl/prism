#!/usr/bin/env python3
"""Reject placeholder markers in production Rust sources."""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MARKER = re.compile(r"todo!|unimplemented!|FIXME|XXX|allow\(dead_code\)")


def main() -> int:
    matches = 0
    for source_root in ("src", "bin", "crates"):
        for path in sorted((ROOT / source_root).rglob("*")):
            if not path.is_file():
                continue
            try:
                lines = path.read_text().splitlines()
            except UnicodeDecodeError:
                continue
            for number, line in enumerate(lines, start=1):
                if MARKER.search(line):
                    print(f"{path.relative_to(ROOT)}:{number}:{line}")
                    matches += 1
    if matches:
        print(f"stub markers found: {matches}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
