#!/usr/bin/env python3
"""Fail if README.md's prism version references don't match Cargo.toml."""
import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parent.parent
cargo = (root / "Cargo.toml").read_text()
pkg = re.search(r"\[package\](.*?)(\n\[|\Z)", cargo, re.S)
m = re.search(r'(?m)^\s*version\s*=\s*"([^"]+)"', pkg.group(1)) if pkg else None
if not m:
    sys.exit("could not find [package] version in Cargo.toml")
want = m.group(1)

readme = (root / "README.md").read_text()
refs = re.findall(r"releases/download/v(\d+\.\d+\.\d+)", readme)
refs += re.findall(r"prism[-_](\d+\.\d+\.\d+)", readme)
if not refs:
    sys.exit("no prism version references found in README.md install commands")

bad = sorted({v for v in refs if v != want})
if bad:
    sys.exit(f"README.md references {bad} but Cargo.toml is {want}; bump the README install commands")
print(f"README.md version references match Cargo.toml ({want})")
