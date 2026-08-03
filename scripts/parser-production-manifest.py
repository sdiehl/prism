#!/usr/bin/env python3
"""Validate the frozen Phase-1B parser production classification manifest."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import NoReturn


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs" / "internal" / "PARSER_PRODUCTION_MANIFEST.json"
EXPECTED_SCHEMA = "prism-parser-production-manifest-v1"
EXPECTED_ORACLE = "46886c1fa7064e4809020c1b788b3ee3531d6a63"
GRAMMAR_PATH = "crates/prism-syntax/src/grammar.lalrpop"
SUGAR_PATH = "crates/prism-syntax/src/sugar.rs"
COEFFECT_PATH = "crates/prism-syntax/src/coeffect.rs"
EXPECTED_PRODUCTION_COUNT = 133

PARSER_PATHS = (
    "lib/std/Syntax/Parse/Type.pr",
    "lib/std/Syntax/Parse/Pattern.pr",
    "lib/std/Syntax/Parse/Expr.pr",
    "lib/std/Syntax/Parse/Decl.pr",
    "lib/std/Syntax/Parse/DeclClass.pr",
    "lib/std/Syntax/Parse/DeclStable.pr",
)

CLASSES = {"predictive", "trial/cut", "Pratt", "escaped"}
OWNERS = {"shared", "types", "patterns", "exprs", "decls"}
FAMILIES = {"types", "patterns", "exprs", "decls"}
HOOK_EFFECTS = {"cursor", "fault", "span", "synth", "value"}
CONTROL_HOOK_EFFECTS = {"cursor", "fault", "span", "synth"}
DEPTH_ENTRIES = {"spend", "nonspend"}
DEPTH_SHAPES = {
    "leaf",
    "siblings-nonspending",
    "child-spends",
    "self-spends",
    "mixed",
}
FROZEN_SPENDING_ENTRIES = {
    "parse_program",
    "parse_type",
    "parse_type_head",
    "parse_type_arg",
    "parse_arrow_nested",
    "parse_pattern",
    "parse_let_pattern",
    "parse_expr",
    "parse_bp",
    "parse_pattern_decl",
    "parse_stable_decl",
}

PRODUCTION_HEAD = re.compile(
    r"^(?:pub\s+)?([A-Za-z][A-Za-z0-9_]*)(?:<[^>]+>)?\s*:"
)
FUNCTION_HEAD = re.compile(r"^(?:pub\s+)?fn\s+([A-Za-z_][A-Za-z0-9_]*)")
RUST_DEFINITION_HEAD = re.compile(
    r"^\s*(?:pub(?:\([^)]*\))?\s+)?"
    r"(?:(?:const|async|unsafe)\s+)*"
    r"(?:fn|const|static|enum|struct|type)\s+"
    r"([A-Za-z_][A-Za-z0-9_]*)"
)


def fail(message: str) -> NoReturn:
    raise SystemExit(f"parser production manifest: {message}")


def git(*args: str) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    if result.returncode:
        fail(result.stderr.strip() or f"git {' '.join(args)} failed")
    return result.stdout


def oracle_blob(oracle: str, path: str) -> str:
    return git("show", f"{oracle}:{path}")


def oracle_oid(oracle: str, path: str) -> str:
    oid = git("rev-parse", f"{oracle}:{path}").strip()
    if git("cat-file", "-t", oid).strip() != "blob":
        fail(f"{path} does not resolve to a blob at {oracle}")
    return oid


def production_inventory(text: str) -> dict[str, int]:
    result: dict[str, int] = {}
    for line_number, line in enumerate(text.splitlines(), 1):
        match = PRODUCTION_HEAD.match(line)
        if not match:
            continue
        name = match.group(1)
        if name in result:
            fail(f"duplicate oracle production {name}")
        result[name] = line_number
    if len(result) != EXPECTED_PRODUCTION_COUNT:
        fail(
            f"expected {EXPECTED_PRODUCTION_COUNT} oracle productions, "
            f"found {len(result)}"
        )
    return result


def parser_inventory(
    oracle: str,
) -> tuple[dict[str, set[str]], set[str], set[str]]:
    by_path: dict[str, set[str]] = {}
    functions: set[str] = set()
    spends: set[str] = set()
    for path in PARSER_PATHS:
        path_functions: set[str] = set()
        current: str | None = None
        for line in oracle_blob(oracle, path).splitlines():
            match = FUNCTION_HEAD.match(line)
            if match:
                current = match.group(1)
                functions.add(current)
                path_functions.add(current)
            if re.search(r"\bdescend\s*\(", line):
                if current is None:
                    fail(f"descend outside a recognized function in {path}")
                spends.add(current)
        by_path[path] = path_functions
    return by_path, functions, spends


def rust_symbol_inventory(oracle: str, path: str) -> set[str]:
    symbols: set[str] = set()
    for line in oracle_blob(oracle, path).splitlines():
        match = RUST_DEFINITION_HEAD.match(line)
        if match:
            symbols.add(match.group(1))
    return symbols


def require_text(row: dict[str, object], field: str, name: str) -> str:
    value = row.get(field)
    if not isinstance(value, str) or not value.strip():
        fail(f"{name} has missing/empty {field}")
    return value


def require_string_list(
    row: dict[str, object], field: str, name: str
) -> list[str]:
    value = row.get(field)
    if (
        not isinstance(value, list)
        or any(not isinstance(item, str) or not item for item in value)
    ):
        fail(f"{name} has invalid {field}; expected a string list")
    if len(value) != len(set(value)):
        fail(f"{name} has duplicate {field}")
    return value


def validate() -> tuple[Counter[str], Counter[str]]:
    try:
        document = json.loads(MANIFEST.read_text())
    except (OSError, json.JSONDecodeError) as error:
        fail(f"cannot read {MANIFEST.relative_to(ROOT)}: {error}")
    if not isinstance(document, dict):
        fail("top level must be an object")
    if document.get("schema") != EXPECTED_SCHEMA:
        fail(f"schema must be {EXPECTED_SCHEMA}")
    oracle = document.get("oracle_commit")
    if oracle != EXPECTED_ORACLE:
        fail(f"oracle_commit must be {EXPECTED_ORACLE}")

    sources = document.get("sources")
    if not isinstance(sources, dict) or set(sources) != {
        GRAMMAR_PATH,
        SUGAR_PATH,
        COEFFECT_PATH,
        *PARSER_PATHS,
    }:
        fail(
            "sources must contain exactly grammar, sugar, coeffect, "
            "and six parser blobs"
        )
    for path, recorded_oid in sources.items():
        if not isinstance(recorded_oid, str):
            fail(f"non-string blob OID for {path}")
        actual_oid = oracle_oid(oracle, path)
        if recorded_oid != actual_oid:
            fail(
                f"blob OID mismatch for {path}: recorded {recorded_oid}, "
                f"oracle has {actual_oid}"
            )

    grammar = production_inventory(oracle_blob(oracle, GRAMMAR_PATH))
    parser_by_path, parser_functions, spending_entries = parser_inventory(oracle)
    if spending_entries != FROZEN_SPENDING_ENTRIES:
        fail(
            "handwritten direct descend inventory drifted: "
            f"missing={sorted(FROZEN_SPENDING_ENTRIES - spending_entries)}, "
            f"new={sorted(spending_entries - FROZEN_SPENDING_ENTRIES)}"
        )

    hooks = document.get("hooks")
    if not isinstance(hooks, dict):
        fail("hooks must be an object")
    symbols_by_path = {
        GRAMMAR_PATH: set(grammar),
        SUGAR_PATH: rust_symbol_inventory(oracle, SUGAR_PATH),
        COEFFECT_PATH: rust_symbol_inventory(oracle, COEFFECT_PATH),
        **parser_by_path,
    }
    for hook_name, hook in hooks.items():
        if not isinstance(hook_name, str) or not hook_name:
            fail("hook names must be nonempty strings")
        if not isinstance(hook, dict):
            fail(f"hook {hook_name} must be an object")
        require_text(hook, "purpose", f"hook {hook_name}")
        symbols = require_string_list(hook, "symbols", f"hook {hook_name}")
        if not symbols:
            fail(f"hook {hook_name} has no frozen symbol references")
        sides: set[str] = set()
        for reference in symbols:
            if reference.count("#") != 1:
                fail(
                    f"hook {hook_name} symbol {reference!r} must be path#name"
                )
            path, symbol = reference.split("#")
            if path not in symbols_by_path:
                fail(f"hook {hook_name} references untracked source {path}")
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", symbol):
                fail(f"hook {hook_name} has invalid symbol name {symbol!r}")
            if symbol not in symbols_by_path[path]:
                fail(
                    f"hook {hook_name} symbol {symbol} is absent from "
                    f"frozen {path}"
                )
            sides.add("prism" if path.startswith("lib/std/") else "rust")
        if sides != {"rust", "prism"}:
            fail(
                f"hook {hook_name} must cite frozen Rust and Prism symbols; "
                f"found {sorted(sides)}"
            )
        effects = require_string_list(hook, "effects", f"hook {hook_name}")
        unknown_effects = set(effects) - HOOK_EFFECTS
        if unknown_effects:
            fail(f"hook {hook_name} has unknown effects {sorted(unknown_effects)}")

    cuts = document.get("cuts")
    if not isinstance(cuts, dict):
        fail("cuts must be an object")

    productions = document.get("productions")
    if not isinstance(productions, list):
        fail("productions must be an array")
    if len(productions) != EXPECTED_PRODUCTION_COUNT:
        fail(
            f"expected {EXPECTED_PRODUCTION_COUNT} manifest rows, "
            f"found {len(productions)}"
        )

    seen: dict[str, int] = {}
    hook_references: set[str] = set()
    cut_references: set[str] = set()
    depth_text: list[str] = []
    class_counts: Counter[str] = Counter()
    owner_counts: Counter[str] = Counter()

    for index, row in enumerate(productions):
        label = f"production row {index}"
        if not isinstance(row, dict):
            fail(f"{label} must be an object")
        name = require_text(row, "name", label)
        label = f"production {name}"
        if name in seen:
            fail(f"{name} appears in rows {seen[name]} and {index}")
        seen[name] = index
        if name not in grammar:
            fail(f"{name} is not an oracle grammar production")
        line = row.get("line")
        if line != grammar[name]:
            fail(f"{name} line is {line}; oracle line is {grammar[name]}")

        owner = require_text(row, "owner", label)
        if owner not in OWNERS:
            fail(f"{name} has unknown owner {owner}")
        owner_counts[owner] += 1
        consumers = row.get("consumers")
        if owner == "shared":
            consumer_list = require_string_list(row, "consumers", label)
            if not consumer_list or not set(consumer_list) <= FAMILIES:
                fail(f"{name} has invalid shared consumers {consumer_list}")
        elif consumers is not None:
            fail(f"{name} is not shared but declares consumers")

        classification = require_text(row, "class", label)
        if classification not in CLASSES:
            fail(f"{name} has unknown class {classification}")
        class_counts[classification] += 1
        decision = require_text(row, "decision", label)
        if len(decision) < 20:
            fail(f"{name} decision is too short to be auditable")

        production_hooks = require_string_list(row, "hooks", label)
        unknown_hooks = set(production_hooks) - set(hooks)
        if unknown_hooks:
            fail(f"{name} references unknown hooks {sorted(unknown_hooks)}")
        hook_references.update(production_hooks)

        production_cuts = require_string_list(row, "cuts", label)
        unknown_cuts = set(production_cuts) - set(cuts)
        if unknown_cuts:
            fail(f"{name} references unknown cuts {sorted(unknown_cuts)}")
        cut_references.update(production_cuts)
        if classification == "trial/cut" and not production_cuts:
            fail(f"{name} is trial/cut but has no named cut/ambiguity identity")
        if classification != "trial/cut" and production_cuts:
            fail(f"{name} names a cut but is classified {classification}")

        if classification == "escaped":
            control_effects = {
                effect
                for hook_name in production_hooks
                for effect in hooks[hook_name]["effects"]
                if effect in CONTROL_HOOK_EFFECTS
            }
            if not control_effects:
                fail(
                    f"{name} is escaped but has no cursor/fault/span/synth hook"
                )

        depth = row.get("depth")
        if not isinstance(depth, dict):
            fail(f"{name} depth must be an object")
        entry = require_text(depth, "entry", f"{name} depth")
        shape = require_text(depth, "shape", f"{name} depth")
        detail = require_text(depth, "detail", f"{name} depth")
        if entry not in DEPTH_ENTRIES:
            fail(f"{name} has invalid depth entry {entry}")
        if shape not in DEPTH_SHAPES:
            fail(f"{name} has invalid depth shape {shape}")
        if len(detail) < 20:
            fail(f"{name} depth detail is too short to be auditable")
        depth_text.append(detail)

        handwritten = require_string_list(row, "handwritten", label)
        if not handwritten:
            fail(f"{name} has no handwritten correspondence")
        missing_functions = set(handwritten) - parser_functions
        if missing_functions:
            fail(
                f"{name} names absent frozen handwritten functions "
                f"{sorted(missing_functions)}"
            )

    manifest_names = set(seen)
    oracle_names = set(grammar)
    if manifest_names != oracle_names:
        fail(
            "production coverage mismatch: "
            f"missing={sorted(oracle_names - manifest_names)}, "
            f"unknown={sorted(manifest_names - oracle_names)}"
        )
    unused_hooks = set(hooks) - hook_references
    if unused_hooks:
        fail(f"unreferenced hooks {sorted(unused_hooks)}")
    unused_cuts = set(cuts) - cut_references
    if unused_cuts:
        fail(f"unreferenced cuts {sorted(unused_cuts)}")

    joined_depth = "\n".join(depth_text)
    undocumented_spends = {
        name
        for name in FROZEN_SPENDING_ENTRIES
        if re.search(rf"\b{re.escape(name)}\b", joined_depth) is None
    }
    if undocumented_spends:
        fail(
            "depth summaries omit frozen spending entries "
            f"{sorted(undocumented_spends)}"
        )
    return class_counts, owner_counts


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command",
        nargs="?",
        choices=("check", "summary"),
        default="check",
    )
    args = parser.parse_args()
    class_counts, owner_counts = validate()
    if args.command == "summary":
        print(
            json.dumps(
                {
                    "schema": EXPECTED_SCHEMA,
                    "oracle": EXPECTED_ORACLE,
                    "productions": EXPECTED_PRODUCTION_COUNT,
                    "classes": dict(sorted(class_counts.items())),
                    "owners": dict(sorted(owner_counts.items())),
                },
                indent=2,
                sort_keys=True,
            )
        )
    else:
        classes = ", ".join(
            f"{name}={count}" for name, count in sorted(class_counts.items())
        )
        owners = ", ".join(
            f"{name}={count}" for name, count in sorted(owner_counts.items())
        )
        print(
            f"parser production manifest: ok "
            f"({EXPECTED_PRODUCTION_COUNT} productions; {classes}; {owners})"
        )


if __name__ == "__main__":
    main()
