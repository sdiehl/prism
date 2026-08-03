#!/usr/bin/env python3
"""Freeze, replay, and extend the independent parser-compaction corpus.

`check` validates every byte and every coverage claim that exists.  Curated
tranche 2 closes the declared structural inventory and three direct-entry
receipts while keeping exact depth and mutation work visibly pending.  It
never upgrades incomplete evidence to a parity gate.

`accept` is noisy and guarded.  It builds the Rust oracle from a clean detached
worktree at the literal frozen commit, writes complete versioned dump bytes,
then replays those bytes through one natively compiled handwritten-Prism
harness.  The current worktree's parser is a differential subject only.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import resource
import shutil
import struct
import subprocess
import sys
import tempfile
import time
from collections import defaultdict
from pathlib import Path
from typing import Any


ORACLE_COMMIT = "46886c1fa7064e4809020c1b788b3ee3531d6a63"
ORACLE_TREE = "cd110efef00d124b955cb6648724887e8e5517f4"
ACCEPT_ENV = "PRISM_ACCEPT_PARSER_COMPACTION"
ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "tests/fixtures/parser/compaction"
MANIFEST = CORPUS / "manifest.json"
VERTICAL = CORPUS / "vertical-inventory.json"
STATUS = CORPUS / "handwritten-status.json"
MUTATIONS = CORPUS / "mutation-seeds.json"
MUTATION_SAMPLE = CORPUS / "mutation-sample.json"
COVERAGE = CORPUS / "coverage.json"
HARNESS = ROOT / "tests/fixtures/parser/compaction_check.pr"
DEPTH_HARNESS = ROOT / "tests/fixtures/parser/compaction_depth_check.pr"
RUST_ENTRY_ADAPTER = ROOT / "tests/compiler/parser_compaction_entry_adapter.rs"
ENTRIES = CORPUS / "entries"
DEPTH = CORPUS / "depth"
DEPTH_INDEX = DEPTH / "index.json"
BYTE_REPLAY = CORPUS / "self-parse-byte-replay.json"
MUTATION_RETAINED = CORPUS / "mutations/retained"
MUTATION_ORACLE = CORPUS / "mutations/oracle-full"
MUTATION_FAILURES = CORPUS / "mutations/failures.json"
FIXED_STACK_KIB = 65536
PROBE_TIMEOUT_SECONDS = 180
MUTATION_LANES = [
    ("type", 0x5459504556310001),
    ("pattern", 0x5041545656310001),
    ("vertical", 0x5645525456310001),
    ("cross", 0x43524F5356310001),
]
MUTATORS = [
    "delete-token",
    "truncate-token-boundary",
    "replace-closer",
    "edit-comma-or-bar",
    "insert-closer-at-separator",
    "edit-or-splice-prefix",
    "replace-payload-same-lexer-class",
    "edit-newline-or-indentation",
]
DEPTH_AXES = [
    "effect-label-args",
    "expression-parens",
    "forall",
    "open-if",
    "pattern-constructor",
    "pattern-list",
    "pattern-record",
    "pattern-tuple",
    "pow-right",
    "right-arrow",
    "type-constructor",
    "type-list",
    "type-tuple",
]

SCHEMAS = {
    "manifest": "prism-parser-compaction-manifest-v1",
    "vertical": "prism-parser-compaction-vertical-inventory-v1",
    "coverage": "prism-parser-compaction-coverage-v1",
    "status": "prism-parser-compaction-handwritten-status-v1",
    "mutations": "prism-parser-compaction-mutation-seeds-v1",
    "mutation_sample": "prism-parser-compaction-mutation-sample-v1",
    "surface": "prism-surface-syntax-v1",
    "diagnostics": "prism-syntax-diagnostics-v1",
    "tokens": "prism-syntax-tokens-v1",
}

# Minimal, dependency-free BLAKE3.  Keeping this here makes a clean checkout's
# `check` independent of a Python wheel or a platform-specific b3sum command.
_IV = [
    0x6A09E667,
    0xBB67AE85,
    0x3C6EF372,
    0xA54FF53A,
    0x510E527F,
    0x9B05688C,
    0x1F83D9AB,
    0x5BE0CD19,
]
_PERM = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
_CHUNK_START = 1
_CHUNK_END = 2
_PARENT = 4
_ROOT = 8
_MASK = 0xFFFFFFFF


def _rotr(value: int, count: int) -> int:
    return ((value >> count) | (value << (32 - count))) & _MASK


def _g(
    state: list[int],
    a: int,
    b: int,
    c: int,
    d: int,
    mx: int,
    my: int,
) -> None:
    state[a] = (state[a] + state[b] + mx) & _MASK
    state[d] = _rotr(state[d] ^ state[a], 16)
    state[c] = (state[c] + state[d]) & _MASK
    state[b] = _rotr(state[b] ^ state[c], 12)
    state[a] = (state[a] + state[b] + my) & _MASK
    state[d] = _rotr(state[d] ^ state[a], 8)
    state[c] = (state[c] + state[d]) & _MASK
    state[b] = _rotr(state[b] ^ state[c], 7)


def _round(state: list[int], words: list[int]) -> None:
    _g(state, 0, 4, 8, 12, words[0], words[1])
    _g(state, 1, 5, 9, 13, words[2], words[3])
    _g(state, 2, 6, 10, 14, words[4], words[5])
    _g(state, 3, 7, 11, 15, words[6], words[7])
    _g(state, 0, 5, 10, 15, words[8], words[9])
    _g(state, 1, 6, 11, 12, words[10], words[11])
    _g(state, 2, 7, 8, 13, words[12], words[13])
    _g(state, 3, 4, 9, 14, words[14], words[15])


def _compress(
    cv: list[int],
    block_words: list[int],
    counter: int,
    block_len: int,
    flags: int,
) -> list[int]:
    state = cv[:] + _IV[:4] + [
        counter & _MASK,
        (counter >> 32) & _MASK,
        block_len,
        flags,
    ]
    words = block_words[:]
    for round_index in range(7):
        _round(state, words)
        if round_index != 6:
            words = [words[i] for i in _PERM]
    return [
        *(state[i] ^ state[i + 8] for i in range(8)),
        *(state[i + 8] ^ cv[i] for i in range(8)),
    ]


class _Output:
    def __init__(
        self,
        input_cv: list[int],
        block_words: list[int],
        counter: int,
        block_len: int,
        flags: int,
    ) -> None:
        self.input_cv = input_cv
        self.block_words = block_words
        self.counter = counter
        self.block_len = block_len
        self.flags = flags

    def chaining_value(self) -> list[int]:
        return _compress(
            self.input_cv,
            self.block_words,
            self.counter,
            self.block_len,
            self.flags,
        )[:8]

    def root_bytes(self) -> bytes:
        words = _compress(
            self.input_cv,
            self.block_words,
            0,
            self.block_len,
            self.flags | _ROOT,
        )
        return struct.pack("<16I", *words)[:32]


def _block_words(block: bytes) -> list[int]:
    return list(struct.unpack("<16I", block.ljust(64, b"\0")))


def _chunk_output(chunk: bytes, index: int) -> _Output:
    blocks = [chunk[i : i + 64] for i in range(0, len(chunk), 64)] or [b""]
    cv = _IV[:]
    for block_index, block in enumerate(blocks[:-1]):
        flags = _CHUNK_START if block_index == 0 else 0
        cv = _compress(cv, _block_words(block), index, len(block), flags)[:8]
    last = blocks[-1]
    flags = _CHUNK_END
    if len(blocks) == 1:
        flags |= _CHUNK_START
    return _Output(cv, _block_words(last), index, len(last), flags)


def _parent_output(left: list[int], right: list[int]) -> _Output:
    return _Output(_IV[:], left + right, 0, 64, _PARENT)


def blake3_bytes(data: bytes) -> str:
    chunks = [data[i : i + 1024] for i in range(0, len(data), 1024)] or [b""]
    stack: list[list[int]] = []
    for index, chunk in enumerate(chunks[:-1]):
        cv = _chunk_output(chunk, index).chaining_value()
        total = index + 1
        while total & 1 == 0:
            cv = _parent_output(stack.pop(), cv).chaining_value()
            total >>= 1
        stack.append(cv)
    output = _chunk_output(chunks[-1], len(chunks) - 1)
    while stack:
        output = _parent_output(stack.pop(), output.chaining_value())
    return output.root_bytes().hex()


def fail(message: str) -> None:
    raise RuntimeError(message)


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        fail(f"{path.relative_to(ROOT)}: {error}")
    if not isinstance(value, dict):
        fail(f"{path.relative_to(ROOT)}: root must be an object")
    return value


def write_json(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + ".tmp")
    temp.write_text(
        json.dumps(value, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    temp.replace(path)


def run(
    argv: list[str],
    *,
    cwd: Path = ROOT,
    check: bool = True,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[bytes]:
    result = subprocess.run(
        argv,
        cwd=cwd,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=env,
    )
    if check and result.returncode != 0:
        command = " ".join(argv)
        stderr = result.stderr.decode("utf-8", errors="replace")
        fail(f"`{command}` failed ({result.returncode}):\n{stderr}")
    return result


def run_fixed_stack(
    argv: list[str],
    *,
    stack_kib: int = FIXED_STACK_KIB,
    timeout_seconds: int = PROBE_TIMEOUT_SECONDS,
) -> dict[str, Any]:
    """Run one probe as an independently limited child and retain its receipt.

    `/usr/bin/time -lp` is intentionally outside the subject process.  The
    stack rlimit is installed before it execs, inherited by the subject, and
    the time utility gives us a per-process-tree peak RSS rather than Python's
    cumulative RUSAGE_CHILDREN high-water mark.
    """

    stack_bytes = stack_kib * 1024

    started = time.monotonic()
    timed_out = False
    try:
        # macOS launches Python with an 8 MiB soft stack and refuses a
        # pre-exec raise of that hard limit.  A shell child can raise its
        # inherited soft limit up to the process hard limit before execing
        # the subject, giving every probe the same fixed 64 MiB stack.
        subject = [
            "/bin/sh",
            "-c",
            f"ulimit -s {stack_kib}; exec \"$@\"",
            "prism-depth-child",
            *argv,
        ]
        result = subprocess.run(
            ["/usr/bin/time", "-lp", *subject],
            cwd=ROOT,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_seconds,
        )
        returncode = result.returncode
        stdout = result.stdout
        stderr = result.stderr
    except subprocess.TimeoutExpired as error:
        timed_out = True
        returncode = None
        stdout = error.stdout or b""
        stderr = error.stderr or b""
    elapsed_ms = round((time.monotonic() - started) * 1000)
    stderr_text = stderr.decode("utf-8", errors="replace")
    rss_match = re.search(r"^\s*(\d+)\s+maximum resident set size\s*$", stderr_text, re.M)
    signal = -returncode if isinstance(returncode, int) and returncode < 0 else None
    aborted = signal is not None or returncode in {134, 139}
    return {
        "argv": argv,
        "stack_kib": stack_kib,
        "timeout_seconds": timeout_seconds,
        "elapsed_ms": elapsed_ms,
        "peak_rss_bytes": int(rss_match.group(1)) if rss_match else None,
        "returncode": returncode,
        "signal": signal,
        "timed_out": timed_out,
        "aborted": aborted,
        "stdout": stdout,
        "stderr": stderr,
    }


def diagnostic_projection(doc: dict[str, Any], kind: str) -> dict[str, Any]:
    rows = doc.get("diagnostics")
    if not isinstance(rows, list) or len(rows) != 1 or not isinstance(rows[0], dict):
        fail("malformed result must carry exactly one diagnostic")
    row = rows[0]
    projection: dict[str, Any] = {
        "code": row.get("code"),
        "phase": row.get("phase"),
        "span": row.get("span"),
        "expected": sorted(row.get("expected", [])),
        "related": row.get("related"),
    }
    if kind == "deliberate":
        projection["message"] = row.get("message")
    return projection


def projection_digest(doc: dict[str, Any], kind: str) -> str:
    projection = diagnostic_projection(doc, kind)
    encoded = json.dumps(
        projection, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode()
    return blake3_bytes(encoded)


def artifact_paths(case: dict[str, Any]) -> tuple[Path, Path]:
    artifacts = case.get("artifacts")
    if not isinstance(artifacts, dict):
        fail(f"{case.get('id')}: no accepted artifact metadata")
    result = artifacts.get("result")
    tokens = artifacts.get("tokens")
    if not isinstance(result, str) or not isinstance(tokens, str):
        fail(f"{case.get('id')}: incomplete artifact paths")
    return CORPUS / result, CORPUS / tokens


def validate_source(case: dict[str, Any]) -> bytes:
    case_id = case.get("id", "<missing>")
    source_name = case.get("source")
    if not isinstance(source_name, str):
        fail(f"{case_id}: source path must be a string")
    source_path = CORPUS / source_name
    data = source_path.read_bytes()
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        fail(f"{case_id}: source is not UTF-8: {error}")
    if b"\r" in data or not data.endswith(b"\n"):
        fail(f"{case_id}: source must be LF-only with one terminal newline")
    if data.endswith(b"\n\n"):
        fail(f"{case_id}: source has more than one terminal newline")
    digest = blake3_bytes(data)
    if digest != case.get("source_blake3"):
        fail(f"{case_id}: source BLAKE3 drift ({digest})")
    fragment = case.get("fragment")
    if not isinstance(fragment, str) or text.count(fragment) != 1:
        fail(f"{case_id}: fragment must occur exactly once")
    character_start = text.index(fragment)
    start = len(text[:character_start].encode())
    if case.get("fragment_span") != [start, start + len(fragment.encode())]:
        fail(f"{case_id}: fragment span drift")
    return data


def validate_artifact(
    case: dict[str, Any],
    path: Path,
    schema: str,
    source: bytes,
) -> dict[str, Any]:
    raw = path.read_bytes()
    if not raw.endswith(b"\n") or raw.endswith(b"\n\n"):
        fail(f"{path.relative_to(ROOT)}: artifact needs exactly one terminal newline")
    doc = load_json(path)
    if doc.get("schema") != schema:
        fail(f"{path.relative_to(ROOT)}: schema is not {schema}")
    source_row = doc.get("source")
    if not isinstance(source_row, dict):
        fail(f"{path.relative_to(ROOT)}: source envelope missing")
    if source_row.get("text", "").encode() != source:
        fail(f"{path.relative_to(ROOT)}: embedded source differs")
    if source_row.get("digest") != case.get("source_blake3"):
        fail(f"{path.relative_to(ROOT)}: embedded source digest differs")
    return doc


def build_coverage(manifest: dict[str, Any], vertical: dict[str, Any]) -> dict[str, Any]:
    type_pattern_ids = manifest["rust_inventory"]["ids"]
    vertical_ids = vertical["alternatives"]
    inventory = sorted(type_pattern_ids + vertical_ids)
    if len(inventory) != len(set(inventory)):
        fail("inventory contains duplicate coverage IDs")
    by_id: dict[str, list[str]] = defaultdict(list)
    hooks: dict[str, list[str]] = defaultdict(list)
    cuts: dict[str, list[str]] = defaultdict(list)
    separators: dict[str, list[str]] = defaultdict(list)
    recursion: dict[str, list[str]] = defaultdict(list)
    for case in manifest["cases"]:
        case_id = case["id"]
        for coverage_id in case["coverage_ids"]:
            if coverage_id not in inventory:
                fail(f"{case_id}: unknown coverage ID {coverage_id}")
            by_id[coverage_id].append(case_id)
        for name in case["hooks"]:
            hooks[name].append(case_id)
        for name in case["cuts"]:
            cuts[name].append(case_id)
        for name in case["separator_boundaries"]:
            separators[name].append(case_id)
        for name in case["recursion_families"]:
            recursion[name].append(case_id)
    entries = [
        {
            "id": coverage_id,
            "curated_cases": sorted(by_id[coverage_id]),
            "mutations": [],
        }
        for coverage_id in inventory
    ]
    uncovered = [row["id"] for row in entries if not row["curated_cases"]]
    return {
        "schema": SCHEMAS["coverage"],
        "oracle_commit": ORACLE_COMMIT,
        "corpus_version": manifest["corpus_version"],
        "scope": "declared Type/Pattern/narrow-vertical structural inventory only",
        "semantic_matrix_complete": False,
        "gate_ready": not uncovered and not any(manifest["pending"].values()),
        "entries": entries,
        "hooks": [
            {"id": name, "curated_cases": sorted(cases), "mutations": []}
            for name, cases in sorted(hooks.items())
        ],
        "cuts": [
            {"id": name, "curated_cases": sorted(cases), "mutations": []}
            for name, cases in sorted(cuts.items())
        ],
        "separator_boundaries": [
            {"id": name, "curated_cases": sorted(cases), "mutations": []}
            for name, cases in sorted(separators.items())
        ],
        "recursion_families": [
            {"id": name, "curated_cases": sorted(cases), "mutations": []}
            for name, cases in sorted(recursion.items())
        ],
        "uncovered": uncovered,
        "pending": manifest["pending"],
    }


def mutation_document(manifest: dict[str, Any]) -> dict[str, Any]:
    ids = [case["id"] for case in manifest["cases"]]
    preview_by_lane = {
        row["lane"]: row for row in mutation_schedule_preview(manifest)["lanes"]
    }
    return {
        "schema": SCHEMAS["mutations"],
        "oracle_commit": ORACLE_COMMIT,
        "corpus_version": manifest["corpus_version"],
        "status": "reviewed-local-micro-sample-full-oracle-execution-pending",
        "prng": "SplitMix64-v1",
        "implementation_blake3": blake3_bytes(Path(__file__).read_bytes()),
        "schedule": {
            "mutators": MUTATORS,
            "draws_per_mutator": 64,
            "candidates_per_lane": 512,
            "retained_cap_per_lane": 128,
        },
        "fixed_micro_sample": {
            "path": "mutation-sample.json",
            "draws_per_mutator": 1,
            "scheduled": 32,
            "applicable": 24,
            "oracle_accepted": 6,
            "oracle_rejected": 18,
            "handwritten_exact": 21,
            "handwritten_mismatch": 3,
            "unique_minimized_witnesses": 6,
            "resolved_exact_witnesses": 3,
            "pending_expected_deltas": 3,
            "status": "reviewed-local-reproduction-non-gating",
        },
        "lanes": [
            {
                "lane": name,
                "seed": seed,
                "case_ids": [
                    case_id
                    for case_id in ids
                    if name == "cross"
                    or next(
                        case["slice"]
                        for case in manifest["cases"]
                        if case["id"] == case_id
                    ).startswith(name)
                ],
                "generated": 0,
                "preview_generated": preview_by_lane[name]["generated"],
                "preview_applicable": preview_by_lane[name]["applicable"],
                "preview_inapplicable": preview_by_lane[name]["inapplicable"],
                "preview_plan_blake3": preview_by_lane[name][
                    "candidate_plan_blake3"
                ],
                "accepted": 0,
                "inapplicable": None,
                "lex_failed": None,
                "discarded": None,
                "retained": [],
            }
            for name, seed in (
                (lane, f"0x{seed:016x}") for lane, seed in MUTATION_LANES
            )
        ],
        "pending_reason": "The deterministic 2,048-candidate plan is implemented and known-answer tested. A fixed 32-draw micro-sample was reproduced by a local Rust binary against all 45 curated receipts; three of its six minimized witnesses are now exact and three remain expected deltas, but it is not content-addressed acceptance. The complete lanes have not yet been run, novelty-selected, retained, or minimized.",
    }


def splitmix64_next(state: int) -> tuple[int, int]:
    """Return the next SplitMix64-v1 state and output word."""
    state = (state + 0x9E3779B97F4A7C15) & 0xFFFFFFFFFFFFFFFF
    value = state
    value = ((value ^ (value >> 30)) * 0xBF58476D1CE4E5B9) & 0xFFFFFFFFFFFFFFFF
    value = ((value ^ (value >> 27)) * 0x94D049BB133111EB) & 0xFFFFFFFFFFFFFFFF
    return state, (value ^ (value >> 31)) & 0xFFFFFFFFFFFFFFFF


def lane_case_ids(manifest: dict[str, Any], lane: str) -> list[str]:
    return [
        case["id"]
        for case in manifest["cases"]
        if lane == "cross" or case["slice"].startswith(lane)
    ]


def case_raw_tokens(case: dict[str, Any]) -> list[dict[str, Any]]:
    _, tokens_path = artifact_paths(case)
    tokens = load_json(tokens_path).get("raw")
    if not isinstance(tokens, list):
        fail(f"{case['id']}: token artifact has no raw stream")
    return [token for token in tokens if isinstance(token, dict)]


def mutate_bytes(source: bytes, lo: int, hi: int, replacement: bytes) -> bytes:
    if lo < 0 or hi < lo or hi > len(source):
        fail(f"invalid mutation span [{lo}, {hi}) for {len(source)} bytes")
    return source[:lo] + replacement + source[hi:]


def terminal_newline(source: bytes) -> bytes:
    return source.rstrip(b"\n") + b"\n"


def fragment_tokens(
    case: dict[str, Any],
    tokens: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    lo, hi = case["fragment_span"]
    selected = [
        token
        for token in tokens
        if token["span"][0] >= lo and token["span"][1] <= hi
    ]
    return selected or tokens


def mutation_candidate(
    manifest: dict[str, Any],
    cases: dict[str, dict[str, Any]],
    lane_ids: list[str],
    case: dict[str, Any],
    mutator: str,
    draw: int,
) -> tuple[bytes, dict[str, Any]] | None:
    source = (CORPUS / case["source"]).read_bytes()
    tokens = case_raw_tokens(case)
    focus = fragment_tokens(case, tokens)
    if not focus:
        return None

    if mutator == "delete-token":
        token = focus[(draw >> 8) % len(focus)]
        lo, hi = token["span"]
        result = mutate_bytes(source, lo, hi, b"")
        operation = {"token_index": tokens.index(token), "span": [lo, hi]}

    elif mutator == "truncate-token-boundary":
        token = focus[(draw >> 8) % len(focus)]
        lo = token["span"][0]
        result = terminal_newline(source[:lo])
        operation = {"boundary": lo}

    elif mutator == "replace-closer":
        closers = [token for token in focus if token.get("kind") in {")", "]", "}"}]
        if not closers:
            return None
        token = closers[(draw >> 8) % len(closers)]
        alternatives = [closer for closer in (")", "]", "}") if closer != token["kind"]]
        replacement = alternatives[(draw >> 16) % len(alternatives)].encode()
        lo, hi = token["span"]
        result = mutate_bytes(source, lo, hi, replacement)
        operation = {
            "span": [lo, hi],
            "from": token["kind"],
            "to": replacement.decode(),
        }

    elif mutator == "edit-comma-or-bar":
        separators = [token for token in focus if token.get("kind") in {",", "|"}]
        if not separators:
            return None
        token = separators[(draw >> 8) % len(separators)]
        lo, hi = token["span"]
        spelling = source[lo:hi]
        edit = (draw >> 16) % 3
        if edit == 0:
            result = mutate_bytes(source, lo, hi, b"")
            action = "delete"
        elif edit == 1:
            result = mutate_bytes(source, lo, hi, spelling + spelling)
            action = "duplicate"
        else:
            destinations = [
                row["span"][0]
                for row in focus
                if row is not token and row["span"][0] != lo
            ]
            if not destinations:
                return None
            destination = destinations[(draw >> 24) % len(destinations)]
            without = mutate_bytes(source, lo, hi, b"")
            if destination > hi:
                destination -= hi - lo
            result = mutate_bytes(without, destination, destination, spelling)
            action = "move"
        operation = {"span": [lo, hi], "action": action}

    elif mutator == "insert-closer-at-separator":
        separators = [token for token in focus if token.get("kind") in {",", "|"}]
        if not separators:
            return None
        token = separators[(draw >> 8) % len(separators)]
        closer = (")", "]", "}")[(draw >> 16) % 3].encode()
        before = ((draw >> 24) & 1) == 0
        at = token["span"][0] if before else token["span"][1]
        result = mutate_bytes(source, at, at, closer)
        operation = {
            "separator_span": token["span"],
            "closer": closer.decode(),
            "side": "before" if before else "after",
        }

    elif mutator == "edit-or-splice-prefix":
        prefix = focus[: min(3, len(focus))]
        if not prefix:
            return None
        edit = (draw >> 16) % 3
        if edit == 0:
            token = prefix[(draw >> 8) % len(prefix)]
            lo, hi = token["span"]
            spelling = source[lo:hi]
            result = mutate_bytes(source, hi, hi, b" " + spelling)
            operation = {"action": "duplicate", "span": [lo, hi]}
        elif edit == 1:
            if len(prefix) < 2:
                return None
            index = (draw >> 8) % (len(prefix) - 1)
            left, right = prefix[index], prefix[index + 1]
            lo, hi = left["span"][0], right["span"][1]
            left_bytes = source[left["span"][0] : left["span"][1]]
            right_bytes = source[right["span"][0] : right["span"][1]]
            result = mutate_bytes(source, lo, hi, right_bytes + b" " + left_bytes)
            operation = {"action": "swap", "spans": [left["span"], right["span"]]}
        else:
            donors = [
                cases[case_id]
                for case_id in lane_ids
                if case_id != case["id"] and cases[case_id]["wrapper"] == case["wrapper"]
            ]
            if not donors:
                return None
            donor = donors[(draw >> 24) % len(donors)]
            donor_source = (CORPUS / donor["source"]).read_bytes()
            donor_focus = fragment_tokens(donor, case_raw_tokens(donor))
            width = min(len(prefix), len(donor_focus), 1 + ((draw >> 32) % 3))
            if width == 0:
                return None
            lo, hi = prefix[0]["span"][0], prefix[width - 1]["span"][1]
            donor_lo = donor_focus[0]["span"][0]
            donor_hi = donor_focus[width - 1]["span"][1]
            result = mutate_bytes(source, lo, hi, donor_source[donor_lo:donor_hi])
            operation = {
                "action": "splice",
                "donor_case": donor["id"],
                "width": width,
                "span": [lo, hi],
            }

    elif mutator == "replace-payload-same-lexer-class":
        payloads = [token for token in focus if isinstance(token.get("value"), str)]
        if not payloads:
            return None
        token = payloads[(draw >> 8) % len(payloads)]
        donors: list[tuple[dict[str, Any], dict[str, Any]]] = []
        for case_id in lane_ids:
            donor_case = cases[case_id]
            for donor_token in case_raw_tokens(donor_case):
                if (
                    donor_token.get("kind") == token.get("kind")
                    and donor_token.get("value") != token.get("value")
                ):
                    donors.append((donor_case, donor_token))
        if not donors:
            return None
        donor_case, donor_token = donors[(draw >> 24) % len(donors)]
        donor_source = (CORPUS / donor_case["source"]).read_bytes()
        donor_lo, donor_hi = donor_token["span"]
        lo, hi = token["span"]
        result = mutate_bytes(source, lo, hi, donor_source[donor_lo:donor_hi])
        operation = {
            "span": [lo, hi],
            "kind": token["kind"],
            "donor_case": donor_case["id"],
            "donor_span": [donor_lo, donor_hi],
        }

    elif mutator == "edit-newline-or-indentation":
        if not case.get("layout"):
            return None
        newlines = [
            index
            for index, byte in enumerate(source[:-1])
            if byte == ord("\n")
        ]
        if not newlines:
            return None
        newline = newlines[(draw >> 8) % len(newlines)]
        edit = (draw >> 16) % 3
        if edit == 0:
            result = mutate_bytes(source, newline, newline + 1, b" ")
            operation = {"action": "delete-newline", "offset": newline}
        elif edit == 1:
            result = mutate_bytes(source, newline, newline, b"\n")
            operation = {"action": "insert-newline", "offset": newline}
        else:
            line_start = newline + 1
            indent_end = line_start
            while indent_end < len(source) and source[indent_end] == ord(" "):
                indent_end += 1
            if ((draw >> 24) & 1) == 0 or indent_end - line_start < 2:
                result = mutate_bytes(source, line_start, line_start, b"  ")
                action = "indent"
            else:
                result = mutate_bytes(source, line_start, line_start + 2, b"")
                action = "dedent"
            operation = {"action": action, "line_start": line_start}
    else:
        fail(f"unknown mutator {mutator}")

    if result == source:
        return None
    return terminal_newline(result), operation


def mutation_schedule_preview(manifest: dict[str, Any]) -> dict[str, Any]:
    cases = {case["id"]: case for case in manifest["cases"]}
    lane_rows = []
    for lane, seed in MUTATION_LANES:
        state = seed
        lane_ids = lane_case_ids(manifest, lane)
        applicable = []
        inapplicable = 0
        for mutator in MUTATORS:
            for draw_index in range(64):
                state, draw = splitmix64_next(state)
                case = cases[lane_ids[draw % len(lane_ids)]]
                candidate = mutation_candidate(
                    manifest,
                    cases,
                    lane_ids,
                    case,
                    mutator,
                    draw,
                )
                schedule_index = MUTATORS.index(mutator) * 64 + draw_index
                if candidate is None:
                    inapplicable += 1
                    continue
                source, operation = candidate
                applicable.append(
                    {
                        "schedule_index": schedule_index,
                        "mutator": mutator,
                        "case_id": case["id"],
                        "draw": f"0x{draw:016x}",
                        "source_blake3": blake3_bytes(source),
                        "operation": operation,
                    }
                )
        encoded = json.dumps(
            applicable,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        ).encode()
        lane_rows.append(
            {
                "lane": lane,
                "seed": f"0x{seed:016x}",
                "generated": 512,
                "applicable": len(applicable),
                "inapplicable": inapplicable,
                "candidate_plan_blake3": blake3_bytes(encoded),
                "first_applicable": applicable[:3],
            }
        )
    return {
        "schema": "prism-parser-compaction-mutation-plan-preview-v1",
        "oracle_commit": ORACLE_COMMIT,
        "corpus_version": manifest["corpus_version"],
        "status": "preview-only-not-oracled",
        "lanes": lane_rows,
    }


def fixed_mutation_sample_preview(manifest: dict[str, Any]) -> dict[str, Any]:
    """Reconstruct the one-draw-per-mutator sample without invoking a parser."""
    cases = {case["id"]: case for case in manifest["cases"]}
    lanes = []
    candidates = []
    for lane, seed in MUTATION_LANES:
        state = seed
        lane_ids = lane_case_ids(manifest, lane)
        applicable = 0
        inapplicable = 0
        for mutator_index, mutator in enumerate(MUTATORS):
            for draw_index in range(64):
                state, draw = splitmix64_next(state)
                if draw_index != 0:
                    continue
                case = cases[lane_ids[draw % len(lane_ids)]]
                candidate = mutation_candidate(
                    manifest,
                    cases,
                    lane_ids,
                    case,
                    mutator,
                    draw,
                )
                if candidate is None:
                    inapplicable += 1
                    continue
                applicable += 1
                source, _ = candidate
                schedule_index = mutator_index * 64
                digest = blake3_bytes(source)
                candidates.append(
                    {
                        "id": f"{lane}-{schedule_index:03d}-{digest[:12]}",
                        "lane": lane,
                        "schedule_index": schedule_index,
                        "mutator": mutator,
                        "base_case": case["id"],
                        "source_blake3": digest,
                        "source_bytes": len(source),
                    }
                )
        lanes.append(
            {
                "lane": lane,
                "seed": f"0x{seed:016x}",
                "scheduled": len(MUTATORS),
                "applicable": applicable,
                "inapplicable": inapplicable,
            }
        )
    return {"lanes": lanes, "candidates": candidates}


def validate_mutation_sample(manifest: dict[str, Any]) -> None:
    sample = load_json(MUTATION_SAMPLE)
    if sample.get("schema") != SCHEMAS["mutation_sample"]:
        fail("mutation sample schema drift")
    if sample.get("oracle_commit") != ORACLE_COMMIT:
        fail("mutation sample oracle drift")
    if (
        sample.get("status")
        != "reviewed-local-rust-reproduction-not-content-addressed"
    ):
        fail("mutation sample must not claim full-lane completion")
    if sample.get("draw_cap_per_mutator") != 1:
        fail("mutation sample draw cap drift")
    provenance = sample.get("oracle_provenance")
    if not isinstance(provenance, dict):
        fail("mutation sample oracle provenance missing")
    if provenance != {
        "executable_path": "target/release/prism",
        "executable_blake3": (
            "f18f9baf5818c83ad95ee1a87eba269c86521b2b3629b7f130032c5f9bbe9c71"
        ),
        "manifest_executable_blake3": (
            "6a1e6b2c0e6c1cb9621c653714f96321563cb7ff26e3cb73ebc1fdc46c49141a"
        ),
        "curated_receipts_exact": 45,
        "curated_receipts_total": 45,
        "content_addressed": False,
    }:
        fail("mutation sample local reproduction provenance drift")

    preview = fixed_mutation_sample_preview(manifest)
    actual_lanes = sample.get("lanes")
    if not isinstance(actual_lanes, list):
        fail("mutation sample lanes missing")
    if len(actual_lanes) != len(preview["lanes"]):
        fail("mutation sample lane count drift")
    lane_by_name: dict[str, dict[str, Any]] = {}
    for actual, expected in zip(actual_lanes, preview["lanes"]):
        for field in (
            "lane",
            "seed",
            "scheduled",
            "applicable",
            "inapplicable",
        ):
            if actual.get(field) != expected[field]:
                fail(f"mutation sample {expected['lane']} {field} drift")
        lane_by_name[actual["lane"]] = actual

    actual_candidates = sample.get("candidates")
    if not isinstance(actual_candidates, list):
        fail("mutation sample candidates missing")
    expected_candidates = preview["candidates"]
    if len(actual_candidates) != len(expected_candidates):
        fail("mutation sample applicable candidate count drift")
    candidate_by_id: dict[str, dict[str, Any]] = {}
    source_bytes_by_id: dict[str, int] = {}
    identity_fields = (
        "id",
        "lane",
        "schedule_index",
        "mutator",
        "base_case",
        "source_blake3",
    )
    for actual, expected in zip(actual_candidates, expected_candidates):
        if {field: actual.get(field) for field in identity_fields} != {
            field: expected[field] for field in identity_fields
        }:
            fail(f"mutation sample candidate drift at {expected['id']}")
        candidate_id = actual["id"]
        if candidate_id in candidate_by_id:
            fail(f"duplicate mutation sample candidate {candidate_id}")
        candidate_by_id[candidate_id] = actual
        source_bytes_by_id[candidate_id] = expected["source_bytes"]

    totals = sample.get("totals")
    if not isinstance(totals, dict):
        fail("mutation sample totals missing")
    count_fields = (
        "scheduled",
        "applicable",
        "inapplicable",
        "oracle_accepted",
        "oracle_rejected",
        "handwritten_exact",
        "handwritten_mismatch",
    )
    for field in count_fields:
        lane_sum = sum(int(lane.get(field, -1)) for lane in actual_lanes)
        if totals.get(field) != lane_sum:
            fail(f"mutation sample {field} total drift")
    if totals.get("lex_failed") != 0 or totals.get("discarded") != 0:
        fail("mutation sample unexpectedly lost a candidate")
    if totals.get("novel") != totals.get("applicable"):
        fail("mutation sample novelty count drift")
    statuses = [candidate.get("handwritten_status") for candidate in actual_candidates]
    kinds = [candidate.get("oracle_result_kind") for candidate in actual_candidates]
    if statuses.count("exact") != totals["handwritten_exact"]:
        fail("mutation sample exact status count drift")
    if statuses.count("mismatch") != totals["handwritten_mismatch"]:
        fail("mutation sample mismatch status count drift")
    if kinds.count("surface") != totals["oracle_accepted"]:
        fail("mutation sample accepted count drift")
    if kinds.count("diagnostics") != totals["oracle_rejected"]:
        fail("mutation sample rejected count drift")
    if sample.get("edit_classes_exercised") != [
        "delete-name",
        "delete-punctuation",
        "insert-punctuation",
        "substitute-name",
        "substitute-punctuation",
    ]:
        fail("mutation sample edit-class receipt drift")

    mismatch_ids = {
        candidate["id"]
        for candidate in actual_candidates
        if candidate["handwritten_status"] == "mismatch"
    }
    witnesses = sample.get("witnesses")
    if not isinstance(witnesses, list) or not witnesses:
        fail("mutation sample witnesses missing")
    pending_witnessed: set[str] = set()
    resolved_witnessed: set[str] = set()
    all_witnessed: set[str] = set()
    source_paths: set[str] = set()
    oracle_paths: set[str] = set()
    for witness in witnesses:
        status = witness.get("status")
        handwritten_result = witness.get("handwritten_result")
        pending = status == "expected-delta" and handwritten_result == "mismatch"
        resolved = status == "exact" and handwritten_result == "exact"
        if witness.get("oracle_status") != "rejected" or not (pending or resolved):
            fail("mutation witness must be an explicit pending delta or exact result")
        origins = witness.get("origins")
        provenance = witness.get("provenance")
        if (
            not isinstance(origins, list)
            or not origins
            or not isinstance(provenance, list)
            or len(provenance) != len(origins)
        ):
            fail("mutation witness provenance is incomplete")
        if all_witnessed.intersection(origins):
            fail("mutation origin is witnessed more than once")
        all_witnessed.update(origins)
        if pending:
            pending_witnessed.update(origins)
        else:
            resolved_witnessed.update(origins)
        for origin, row in zip(origins, provenance):
            candidate = candidate_by_id.get(origin)
            expected_status = "mismatch" if pending else "exact"
            if (
                candidate is None
                or candidate.get("handwritten_status") != expected_status
            ):
                fail(
                    f"mutation witness origin {origin} is not {expected_status}"
                )
            lane = lane_by_name[candidate["lane"]]
            expected_provenance = {
                "origin": origin,
                "lane": candidate["lane"],
                "seed": lane["seed"],
                "mutator": candidate["mutator"],
                "parent": candidate["base_case"],
            }
            if row != expected_provenance:
                fail(f"{origin}: mutation provenance drift")

        source_name = witness.get("source")
        oracle_name = witness.get("oracle")
        if (
            not isinstance(source_name, str)
            or not source_name.startswith("mutations/minimized/")
            or not isinstance(oracle_name, str)
            or not oracle_name.startswith("mutations/oracle/")
        ):
            fail("mutation witness paths escape their registered directories")
        if source_name in source_paths or oracle_name in oracle_paths:
            fail("mutation witness file reused without origin deduplication")
        source_paths.add(source_name)
        oracle_paths.add(oracle_name)
        source_path = CORPUS / source_name
        oracle_path = CORPUS / oracle_name
        source = source_path.read_bytes()
        if not source.endswith(b"\n") or source.endswith(b"\n\n"):
            fail(f"{source_name}: minimized source terminal newline drift")
        oracle = load_json(oracle_path)
        if oracle.get("schema") != SCHEMAS["diagnostics"]:
            fail(f"{oracle_name}: diagnostic schema drift")
        source_row = oracle.get("source")
        if not isinstance(source_row, dict):
            fail(f"{oracle_name}: source envelope missing")
        if source_row.get("text", "").encode() != source:
            fail(f"{oracle_name}: minimized source differs from oracle")
        if source_row.get("digest") != blake3_bytes(source):
            fail(f"{oracle_name}: minimized source digest drift")
        diagnostic = diagnostic_projection(oracle, "generic")
        rust_expected = sorted(witness.get("rust_expected", []))
        handwritten_expected = sorted(witness.get("handwritten_expected", []))
        if diagnostic["code"] != "E7100" or diagnostic["phase"] != "parse":
            fail(f"{oracle_name}: expected an E7100 parse diagnostic")
        if diagnostic["expected"] != rust_expected:
            fail(f"{oracle_name}: Rust expected-set receipt drift")
        if pending and rust_expected == handwritten_expected:
            fail(f"{oracle_name}: expected-delta witness became equal")
        if resolved and rust_expected != handwritten_expected:
            fail(f"{oracle_name}: exact witness retains an expected-set delta")

        minimization = witness.get("minimization")
        if not isinstance(minimization, dict):
            fail(f"{source_name}: minimization receipt missing")
        original_bytes = [source_bytes_by_id[origin] for origin in origins]
        if minimization.get("original_bytes") != original_bytes:
            fail(f"{source_name}: minimization parent sizes drift")
        if minimization.get("minimized_bytes") != len(source):
            fail(f"{source_name}: minimized byte count drift")
        if not all(len(source) < size for size in original_bytes):
            fail(f"{source_name}: witness was not reduced")
        if minimization.get("deduplicated_origins") != (len(origins) > 1):
            fail(f"{source_name}: deduplication receipt drift")
    if pending_witnessed != mismatch_ids:
        fail(
            "mutation sample mismatch witness set drift: "
            f"missing={sorted(mismatch_ids - pending_witnessed)}, "
            f"extra={sorted(pending_witnessed - mismatch_ids)}"
        )
    if pending_witnessed.intersection(resolved_witnessed):
        fail("mutation origin is both pending and resolved")


def syntax_shape(value: Any, tags: list[Any]) -> None:
    if isinstance(value, dict):
        if isinstance(value.get("kind"), str):
            tags.append(["kind", value["kind"]])
        if value.get("synth") is True:
            tags.append(["synth", True])
        for key, child in value.items():
            if key not in {
                "schema",
                "compiler",
                "source",
                "span",
                "name",
                "value",
                "cell",
            }:
                syntax_shape(child, tags)
    elif isinstance(value, list):
        tags.append(["list", len(value)])
        for child in value:
            syntax_shape(child, tags)


def mutation_novelty(
    case: dict[str, Any],
    kind: str,
    document: dict[str, Any],
    tokens: dict[str, Any],
) -> str:
    if kind == "surface":
        tags: list[Any] = []
        syntax_shape(document.get("items", []), tags)
        projection: dict[str, Any] = {
            "entry": case["wrapper"],
            "shape": tags,
            "coverage_ids": case["coverage_ids"],
        }
    else:
        diagnostic = diagnostic_projection(
            document,
            case["diagnostic"]["kind"],
        )
        span = diagnostic["span"]
        offending = None
        if isinstance(span, list) and len(span) == 2:
            for token in tokens.get("raw", []):
                token_span = token.get("span")
                if (
                    isinstance(token_span, list)
                    and len(token_span) == 2
                    and token_span[0] <= span[0] <= token_span[1]
                ):
                    offending = token.get("kind")
                    break
        projection = {
            "entry": case["wrapper"],
            "diagnostic_kind": case["diagnostic"]["kind"],
            "diagnostic": diagnostic,
            "offending_token_kind": offending,
            "coverage_ids": case["coverage_ids"],
        }
        projection["diagnostic"].pop("span", None)
    return projection_blake3(projection)


def bounded_mutation_run(
    manifest: dict[str, Any],
    oracle: Path,
    harness: Path,
    draw_cap: int,
    lane_filter: str | None = None,
) -> dict[str, Any]:
    if draw_cap < 1 or draw_cap > 64:
        fail("bounded mutation draw cap must be between 1 and 64")
    cases = {case["id"]: case for case in manifest["cases"]}
    lanes = []
    with tempfile.TemporaryDirectory(prefix="prism-mutation-bounded-") as name:
        directory = Path(name)
        for lane, seed in MUTATION_LANES:
            if lane_filter is not None and lane != lane_filter:
                continue
            state = seed
            lane_ids = lane_case_ids(manifest, lane)
            counts = {
                "scheduled": len(MUTATORS) * draw_cap,
                "applicable": 0,
                "inapplicable": 0,
                "lex_failed": 0,
                "oracle_accepted": 0,
                "oracle_rejected": 0,
                "discarded": 0,
                "novel": 0,
                "handwritten_exact": 0,
                "handwritten_mismatch": 0,
            }
            novelty_seen: set[str] = set()
            mismatches = []
            useful = []
            for mutator_index, mutator in enumerate(MUTATORS):
                for draw_index in range(64):
                    state, draw = splitmix64_next(state)
                    if draw_index >= draw_cap:
                        continue
                    case = cases[lane_ids[draw % len(lane_ids)]]
                    candidate = mutation_candidate(
                        manifest,
                        cases,
                        lane_ids,
                        case,
                        mutator,
                        draw,
                    )
                    schedule_index = mutator_index * 64 + draw_index
                    if candidate is None:
                        counts["inapplicable"] += 1
                        continue
                    counts["applicable"] += 1
                    source_bytes, operation = candidate
                    candidate_id = (
                        f"{lane}-{schedule_index:03d}-"
                        f"{blake3_bytes(source_bytes)[:12]}"
                    )
                    source = directory / f"{candidate_id}.pr"
                    tokens_path = directory / f"{candidate_id}.tokens.json"
                    result_path = directory / f"{candidate_id}.result.json"
                    source.write_bytes(source_bytes)
                    token_result = run(
                        [str(oracle), "dump", "syntax-tokens", str(source)],
                        check=False,
                    )
                    if token_result.returncode != 0:
                        counts["lex_failed"] += 1
                        continue
                    tokens_bytes = token_result.stdout.rstrip(b"\n") + b"\n"
                    tokens_path.write_bytes(tokens_bytes)
                    tokens_doc = json.loads(tokens_bytes)
                    surface = run(
                        [str(oracle), "dump", "surface-syntax", str(source)],
                        check=False,
                    )
                    if surface.returncode == 0:
                        kind = "surface"
                        result_bytes = surface.stdout.rstrip(b"\n") + b"\n"
                        counts["oracle_accepted"] += 1
                    else:
                        diagnostics = run(
                            [
                                str(oracle),
                                "dump",
                                "syntax-diagnostics",
                                str(source),
                            ],
                            check=False,
                        )
                        if diagnostics.returncode != 0:
                            counts["discarded"] += 1
                            continue
                        kind = "diagnostics"
                        result_bytes = diagnostics.stdout.rstrip(b"\n") + b"\n"
                        counts["oracle_rejected"] += 1
                    result_path.write_bytes(result_bytes)
                    oracle_doc = json.loads(result_bytes)
                    novelty = mutation_novelty(
                        case,
                        kind,
                        oracle_doc,
                        tokens_doc,
                    )
                    is_novel = novelty not in novelty_seen
                    if is_novel:
                        novelty_seen.add(novelty)
                        counts["novel"] += 1
                    replay = run(
                        [str(harness), kind, str(result_path)],
                        check=False,
                    )
                    if replay.returncode != 0 or replay.stdout.startswith(
                        b"HARNESS_ERROR"
                    ):
                        exact = False
                    elif kind == "surface":
                        exact = replay.stdout == result_bytes
                    else:
                        try:
                            exact = diagnostic_projection(
                                json.loads(replay.stdout),
                                case["diagnostic"]["kind"],
                            ) == diagnostic_projection(
                                oracle_doc,
                                case["diagnostic"]["kind"],
                            )
                        except (json.JSONDecodeError, RuntimeError):
                            exact = False
                    if exact:
                        counts["handwritten_exact"] += 1
                    else:
                        counts["handwritten_mismatch"] += 1
                        mismatches.append(candidate_id)
                    if is_novel or not exact:
                        useful.append(
                            {
                                "candidate_id": candidate_id,
                                "schedule_index": schedule_index,
                                "mutator": mutator,
                                "base_case": case["id"],
                                "source": source_bytes.decode(
                                    "utf-8",
                                    errors="strict",
                                ),
                                "source_blake3": blake3_bytes(source_bytes),
                                "operation": operation,
                                "oracle_result_kind": kind,
                                "novelty_blake3": novelty,
                                "handwritten_status": (
                                    "exact" if exact else "mismatch"
                                ),
                            }
                        )
            lanes.append(
                {
                    "lane": lane,
                    "seed": f"0x{seed:016x}",
                    "draw_cap_per_mutator": draw_cap,
                    "counts": counts,
                    "mismatches": mismatches,
                    "useful": useful[:16],
                    "useful_total": len(useful),
                }
            )
    return {
        "schema": "prism-parser-compaction-bounded-mutation-run-v1",
        "oracle_commit": ORACLE_COMMIT,
        "oracle_executable_path": str(oracle),
        "handwritten_harness_path": str(harness),
        "draw_cap_per_mutator": draw_cap,
        "status": "bounded-review-run-not-full-lane-acceptance",
        "lanes": lanes,
    }


def depth_fragment(axis: str, layers: int) -> str:
    if layers < 0:
        fail(f"{axis}: negative depth layer count")
    if axis == "effect-label-args":
        label = "Io" if layers == 0 else "Io(" * layers + "Int" + ")" * layers
        return f"() -> Int ! {{{label}}}"
    if axis == "forall":
        return "".join(f"forall a{index}. " for index in range(layers)) + "Int"
    if axis == "right-arrow":
        return "Int -> " * layers + "Int"
    if axis == "type-constructor":
        return "Box(" * layers + "Int" + ")" * layers
    if axis == "type-list":
        return "[" * layers + "Int" + "]" * layers
    if axis == "type-tuple":
        return "(" * layers + "Int" + ",)" * layers
    if axis == "pattern-constructor":
        return "A(" * layers + "x" + ")" * layers
    if axis == "pattern-list":
        return "[" * layers + "x" + "]" * layers
    if axis == "pattern-record":
        return "A {x = " * layers + "x" + "}" * layers
    if axis == "pattern-tuple":
        return "(" * layers + "x" + ",)" * layers
    if axis == "expression-parens":
        return "(" * layers + "0" + ")" * layers
    if axis == "pow-right":
        return "0 ^ " * layers + "0"
    fail(f"unknown depth axis {axis}")


def depth_source(axis: str, layers: int) -> bytes:
    if axis == "open-if":
        if layers == 0:
            return b"fn corpus() = 0\n"
        lines = ["fn corpus() ="]
        for level in range(layers):
            lines.append("  " * (level + 1) + "if true then")
        lines.append("  " * (layers + 1) + "0")
        return ("\n".join(lines) + "\n").encode()
    fragment = depth_fragment(axis, layers)
    if axis.startswith("pattern-"):
        return (
            "fn corpus(v) = match v of\n"
            f"  {fragment} => 0\n"
            "  _ => 1\n"
        ).encode()
    if axis in {"expression-parens", "pow-right"}:
        return f"fn corpus() = {fragment}\n".encode()
    return f"fn corpus(x : {fragment}) = x\n".encode()


def depth_schedule_preview(
    manifest: dict[str, Any],
    probe_compiler: Path | None,
) -> dict[str, Any]:
    declared = manifest["pending"]["depth_axes"]
    if declared != DEPTH_AXES:
        fail(
            "frozen depth-axis ledger drift: "
            f"declared={declared}, implemented={DEPTH_AXES}"
        )
    rows = []
    for axis in DEPTH_AXES:
        sample = depth_source(axis, 3)
        probe_status = "not-run"
        if probe_compiler is not None:
            with tempfile.TemporaryDirectory(prefix=f"prism-depth-{axis}-") as name:
                source = Path(name) / f"{axis}.pr"
                source.write_bytes(sample)
                result = run(
                    [str(probe_compiler), "dump", "surface-syntax", str(source)],
                    check=False,
                )
                probe_status = (
                    "accepted"
                    if result.returncode == 0
                    else f"failed-exit-{result.returncode}"
                )
                if result.returncode != 0:
                    fail(
                        f"{axis}: depth generator sample failed:\n"
                        + result.stderr.decode("utf-8", errors="replace")
                    )
        below_probe = depth_source(axis, 2047)
        above_probe = depth_source(axis, 2048)
        rows.append(
            {
                "axis": axis,
                "entry": "parse_source",
                "sample_layers": 3,
                "sample_source_blake3": blake3_bytes(sample),
                "sample_probe": probe_status,
                "uncalibrated_2047": {
                    "bytes": len(below_probe),
                    "source_blake3": blake3_bytes(below_probe),
                },
                "uncalibrated_2048": {
                    "bytes": len(above_probe),
                    "source_blake3": blake3_bytes(above_probe),
                },
                "boundary_status": "uncalibrated",
                "ordered_spend_trace_status": "instrumentation-required",
            }
        )
    return {
        "schema": "prism-parser-compaction-depth-plan-preview-v1",
        "oracle_commit": ORACLE_COMMIT,
        "corpus_version": manifest["corpus_version"],
        "declared_axis_count": len(DEPTH_AXES),
        "status": "generators-implemented-boundaries-unmeasured",
        "unledgered_followups": manifest["pending"].get("depth_followups", []),
        "axes": rows,
    }


def depth_probe(
    axis: str,
    layers: int,
    compiler: Path,
    harness: Path,
    directory: Path,
    budget: int = 2048,
) -> dict[str, Any]:
    source_bytes = depth_source(axis, layers)
    source = directory / f"{axis}-{layers}.pr"
    tokens = directory / f"{axis}-{layers}.syntax-tokens.json"
    if not tokens.is_file():
        source.write_bytes(source_bytes)
        token_result = run_fixed_stack(
            [str(compiler), "dump", "syntax-tokens", str(source)]
        )
        if (
            token_result["returncode"] != 0
            or token_result["timed_out"]
            or token_result["aborted"]
        ):
            fail(
                f"{axis}@{layers}: token dump failed: "
                f"return={token_result['returncode']} "
                f"signal={token_result['signal']}\n"
                + token_result["stderr"].decode("utf-8", errors="replace")[-4000:]
            )
        tokens.write_bytes(token_result["stdout"].rstrip(b"\n") + b"\n")
    result = run_fixed_stack(
        [
            str(harness),
            "program",
            str(tokens),
            "0",
            str(len(source_bytes)),
            str(len(source_bytes)),
            str(budget),
        ]
    )
    if result["returncode"] != 0 or result["timed_out"] or result["aborted"]:
        fail(
            f"{axis}@{layers}: depth harness failed: return={result['returncode']} "
            f"signal={result['signal']} timeout={result['timed_out']}\n"
            + result["stderr"].decode("utf-8", errors="replace")[-4000:]
        )
    try:
        outcome = json.loads(result["stdout"])
    except json.JSONDecodeError as error:
        fail(f"{axis}@{layers}: invalid depth harness JSON: {error}")
    if not isinstance(outcome, dict):
        fail(f"{axis}@{layers}: depth harness result is not an object")
    outcome["layers"] = layers
    outcome["source_bytes"] = len(source_bytes)
    outcome["source_blake3"] = blake3_bytes(source_bytes)
    outcome["budget"] = budget
    return outcome


def depth_probe_class(outcome: dict[str, Any]) -> str:
    if outcome.get("outcome") == "accepted" and outcome.get("complete") is True:
        return "accepted"
    diagnostic = outcome.get("diagnostic")
    if (
        outcome.get("outcome") == "fault"
        and isinstance(diagnostic, dict)
        and diagnostic.get("code") == "E7102"
        and diagnostic.get("phase") == "parse"
        and diagnostic.get("message")
        == "nesting exceeds the parser's depth budget"
        and diagnostic.get("expected") == []
        and diagnostic.get("related") == []
    ):
        return "depth-fault"
    return "unexpected"


def calibrate_depth_axis(
    axis: str,
    compiler: Path,
    harness: Path,
) -> dict[str, Any]:
    if axis not in DEPTH_AXES:
        fail(f"unknown frozen depth axis {axis}")
    with tempfile.TemporaryDirectory(prefix=f"prism-depth-calibrate-{axis}-") as name:
        directory = Path(name)
        cache: dict[int, dict[str, Any]] = {}

        def probe(layers: int) -> dict[str, Any]:
            if layers not in cache:
                cache[layers] = depth_probe(
                    axis,
                    layers,
                    compiler,
                    harness,
                    directory,
                )
            return cache[layers]

        below = 0
        if depth_probe_class(probe(below)) != "accepted":
            fail(f"{axis}: zero-layer base did not accept")
        above = 1
        while above <= 8192 and depth_probe_class(probe(above)) == "accepted":
            below = above
            above *= 2
        if above > 8192:
            fail(f"{axis}: no E7102 boundary through 8192 layers")
        above_class = depth_probe_class(probe(above))
        if above_class != "depth-fault":
            fail(f"{axis}@{above}: expected E7102, got {probe(above)}")
        while above - below > 1:
            middle = (below + above) // 2
            classification = depth_probe_class(probe(middle))
            if classification == "accepted":
                below = middle
            elif classification == "depth-fault":
                above = middle
            else:
                fail(f"{axis}@{middle}: unexpected outcome {probe(middle)}")

        below_result = probe(below)
        above_result = probe(above)
        return {
            "schema": "prism-parser-compaction-depth-calibration-v1",
            "oracle_commit": ORACLE_COMMIT,
            "axis": axis,
            "budget": 2048,
            "entry": "parse_program",
            "status": "boundary-calibrated-trace-and-stack-receipts-pending",
            "below": below_result,
            "above": above_result,
            "probe_count": len(cache),
            "compiler_path": str(compiler),
            "harness_source_blake3": blake3_bytes(DEPTH_HARNESS.read_bytes()),
            "harness_executable_path": str(harness),
            "ordered_spend_trace_status": "instrumentation-required",
            "fixed_stack_status": "not-run",
            "peak_rss_status": "not-run",
        }


def minimum_depth_budget(
    axis: str,
    layers: int,
    compiler: Path,
    harness: Path,
    directory: Path,
) -> int:
    """Measure the exact number of successful `descend` calls on one path."""

    low = -1
    high = 1
    while high <= 256:
        classification = depth_probe_class(
            depth_probe(axis, layers, compiler, harness, directory, high)
        )
        if classification == "accepted":
            break
        if classification != "depth-fault":
            fail(f"{axis}@{layers}/budget={high}: unexpected depth result")
        low = high
        high *= 2
    if high > 256:
        fail(f"{axis}@{layers}: base path spends more than 256 units")
    while high - low > 1:
        middle = (low + high) // 2
        classification = depth_probe_class(
            depth_probe(axis, layers, compiler, harness, directory, middle)
        )
        if classification == "accepted":
            high = middle
        elif classification == "depth-fault":
            low = middle
        else:
            fail(f"{axis}@{layers}/budget={middle}: unexpected depth result")
    return high


def depth_boundary(
    axis: str,
    compiler: Path,
    harness: Path,
    directory: Path,
) -> tuple[int, int, dict[str, Any]]:
    """Calibrate a linear spending axis cheaply, then verify D-/D+ at 2048."""

    requirements = [
        minimum_depth_budget(axis, layers, compiler, harness, directory)
        for layers in range(5)
    ]
    slopes = [requirements[index] - requirements[index - 1] for index in range(2, 5)]
    if not slopes or slopes[0] <= 0 or any(slope != slopes[0] for slope in slopes):
        fail(f"{axis}: non-linear ordered spend calibration {requirements}")
    per_layer = slopes[0]
    intercept = requirements[1] - per_layer
    if any(
        requirements[layers] != intercept + per_layer * layers
        for layers in range(1, 5)
    ):
        fail(f"{axis}: unstable ordered spend calibration {requirements}")
    below = (2048 - intercept) // per_layer
    if below < 1:
        fail(f"{axis}: no positive below-budget nesting point")

    # The affine calibration is evidence, not an assumption: verify the exact
    # transition at the release budget before any fixed-stack arm is accepted.
    while depth_probe_class(
        depth_probe(axis, below, compiler, harness, directory, 2048)
    ) == "depth-fault":
        below -= 1
    while depth_probe_class(
        depth_probe(axis, below + 1, compiler, harness, directory, 2048)
    ) == "accepted":
        below += 1
    above = below + 1
    below_outcome = depth_probe(axis, below, compiler, harness, directory, 2048)
    above_outcome = depth_probe(axis, above, compiler, harness, directory, 2048)
    if depth_probe_class(below_outcome) != "accepted":
        fail(f"{axis}@{below}: D- did not accept")
    if depth_probe_class(above_outcome) != "depth-fault":
        fail(f"{axis}@{above}: D+ did not produce E7102")
    calibration = {
        "method": "minimum-budget-affine-calibration-plus-release-boundary-verification",
        "sample_layers": [0, 1, 2, 3, 4],
        "minimum_budgets": requirements,
        "base_spends": intercept,
        "spends_per_layer": per_layer,
        "below_spends": intercept + per_layer * below,
        "above_attempted_spend": intercept + per_layer * above,
    }
    return below, above, calibration


def fixed_depth_arm(
    arm: str,
    compiler: Path,
    harness: Path,
    tokens: Path,
    source_bytes: int,
) -> dict[str, Any]:
    arguments = [
        "program",
        str(tokens),
        "0",
        str(source_bytes),
        str(source_bytes),
        "2048",
    ]
    if arm == "native":
        argv = [str(harness), *arguments]
    elif arm == "interpreted":
        argv = [str(compiler), "run", str(DEPTH_HARNESS), "--", *arguments]
    else:
        fail(f"unknown depth execution arm {arm}")
    measured = run_fixed_stack(argv)
    stdout = measured.pop("stdout")
    stderr = measured.pop("stderr")
    if (
        measured["returncode"] != 0
        or measured["timed_out"]
        or measured["aborted"]
    ):
        fail(
            f"{arm} depth child failed: return={measured['returncode']} "
            f"signal={measured['signal']} timeout={measured['timed_out']}\n"
            + stderr.decode("utf-8", errors="replace")[-4000:]
        )
    try:
        document = json.loads(stdout)
    except json.JSONDecodeError as error:
        fail(f"{arm} depth child emitted truncated/invalid JSON: {error}")
    if not isinstance(document, dict):
        fail(f"{arm} depth child result is not an object")
    measured.pop("argv")
    return {
        "arm": arm,
        **measured,
        "stdout_blake3": blake3_bytes(stdout),
        "stderr_blake3": blake3_bytes(stderr),
        "result": document,
        "classification": depth_probe_class(document),
    }


def run_depth_axis_receipts(
    axis: str,
    compiler: Path,
    harness: Path,
) -> list[dict[str, Any]]:
    with tempfile.TemporaryDirectory(prefix=f"prism-depth-receipt-{axis}-") as name:
        directory = Path(name)
        below, above, calibration = depth_boundary(
            axis, compiler, harness, directory
        )
        rows = []
        for side, layers, required_class in (
            ("below", below, "accepted"),
            ("above", above, "depth-fault"),
        ):
            source = directory / f"{axis}-{layers}.pr"
            tokens = directory / f"{axis}-{layers}.syntax-tokens.json"
            # Boundary calibration has already materialized this exact source
            # and token stream; assert that rather than quietly regenerating it.
            if not source.is_file() or not tokens.is_file():
                fail(f"{axis}-{side}: calibrated source/token pair is missing")
            source_data = source.read_bytes()
            arms = [
                fixed_depth_arm(
                    arm,
                    compiler,
                    harness,
                    tokens,
                    len(source_data),
                )
                for arm in ("interpreted", "native")
            ]
            if any(row["classification"] != required_class for row in arms):
                fail(f"{axis}-{side}: wrong interpreted/native classification")
            if arms[0]["result"] != arms[1]["result"]:
                fail(f"{axis}-{side}: interpreted/native result bytes disagree")
            rows.append(
                {
                    "schema": "prism-parser-compaction-depth-receipt-v1",
                    "oracle_commit": ORACLE_COMMIT,
                    "axis": axis,
                    "side": side,
                    "entry": "parse_program",
                    "depth_budget": 2048,
                    "layers": layers,
                    "source_bytes": len(source_data),
                    "source_blake3": blake3_bytes(source_data),
                    "token_document_blake3": blake3_bytes(tokens.read_bytes()),
                    "stack_kib": FIXED_STACK_KIB,
                    "required_classification": required_class,
                    "calibration": calibration,
                    "arms": arms,
                    "status": "exact-fixed-stack-interpreted-native",
                }
            )
        return rows


def materialize_depth_receipts(compiler: Path, harness: Path) -> dict[str, Any]:
    receipts = []
    for axis in DEPTH_AXES:
        axis_rows = run_depth_axis_receipts(axis, compiler, harness)
        for row in axis_rows:
            write_json(DEPTH / f"{axis}-{row['side']}.receipt.json", row)
            receipts.append(
                {
                    "axis": axis,
                    "side": row["side"],
                    "layers": row["layers"],
                    "source_blake3": row["source_blake3"],
                    "receipt": f"depth/{axis}-{row['side']}.receipt.json",
                }
            )
    index = {
        "schema": "prism-parser-compaction-depth-index-v1",
        "oracle_commit": ORACLE_COMMIT,
        "depth_budget": 2048,
        "stack_kib": FIXED_STACK_KIB,
        "axis_count": len(DEPTH_AXES),
        "probe_count": len(receipts),
        "execution_arms": ["interpreted", "native"],
        "receipts": receipts,
        "unledgered_followup": (
            "direct parse_let_pattern remains visibly outside the frozen "
            "13-axis ledger and is not claimed by this index"
        ),
        "status": "complete",
    }
    write_json(DEPTH_INDEX, index)
    return index


def validate_manifest(manifest: dict[str, Any], oracle: str) -> None:
    if manifest.get("schema") != SCHEMAS["manifest"]:
        fail("manifest schema drift")
    oracle_row = manifest.get("oracle")
    if not isinstance(oracle_row, dict):
        fail("manifest oracle is missing")
    if oracle != ORACLE_COMMIT or oracle_row.get("commit") != ORACLE_COMMIT:
        fail(f"oracle must be the literal frozen commit {ORACLE_COMMIT}")
    if oracle_row.get("tree") != ORACLE_TREE:
        fail("oracle tree drift")
    cases = manifest.get("cases")
    if not isinstance(cases, list) or not cases:
        fail("manifest has no cases")
    ids = [case.get("id") for case in cases]
    pending = manifest.get("pending")
    if not isinstance(pending, dict):
        fail("manifest pending ledger is missing")
    if pending.get("depth_axes") != DEPTH_AXES:
        fail("manifest frozen 13-axis depth ledger drift")
    followups = pending.get("depth_followups")
    if not isinstance(followups, list) or len(followups) != 1:
        fail("manifest direct parse_let_pattern depth follow-up is missing")
    if ids != sorted(ids) or len(ids) != len(set(ids)):
        fail("manifest case IDs must be unique and sorted")
    if manifest.get("gate_ready") is not False:
        fail("tranche 1 must not claim gate readiness")


def is_blake3(value: Any) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def validate_status(
    status: dict[str, Any],
    manifest: dict[str, Any],
) -> None:
    if status.get("schema") != SCHEMAS["status"]:
        fail("handwritten status schema drift")
    if status.get("oracle_commit") != ORACLE_COMMIT:
        fail("handwritten status oracle drift")
    provenance = status.get("subject_provenance")
    if not isinstance(provenance, dict):
        fail("handwritten status lacks subject provenance")
    for field in (
        "compiler_blake3",
        "harness_executable_blake3",
        "harness_source_blake3",
        "worktree_diff_blake3",
        "index_diff_blake3",
        "parser_source_snapshot_blake3",
    ):
        if not is_blake3(provenance.get(field)):
            fail(f"handwritten status has invalid {field}")
    if provenance["harness_source_blake3"] != blake3_bytes(HARNESS.read_bytes()):
        fail("handwritten status was produced by a different harness source")
    source_rows = provenance.get("parser_sources")
    if not isinstance(source_rows, list) or not source_rows:
        fail("handwritten status has no parser source inventory")
    source_snapshot = b""
    for row in source_rows:
        if (
            not isinstance(row, dict)
            or not isinstance(row.get("path"), str)
            or not is_blake3(row.get("blake3"))
        ):
            fail("handwritten status has an invalid parser source row")
        source_snapshot += (
            row["path"].encode() + b"\0" + row["blake3"].encode() + b"\0"
        )
    if blake3_bytes(source_snapshot) != provenance["parser_source_snapshot_blake3"]:
        fail("handwritten parser source snapshot is internally inconsistent")
    rows = status.get("cases")
    if not isinstance(rows, list):
        fail("handwritten status cases must be an array")
    status_ids = [row.get("case_id") for row in rows]
    manifest_ids = [case["id"] for case in manifest["cases"]]
    if status_ids != manifest_ids:
        fail("handwritten status case list drift")
    exact = 0
    mismatches: list[str] = []
    cases_by_id = {case["id"]: case for case in manifest["cases"]}
    for row in rows:
        case = cases_by_id[row["case_id"]]
        result_path, _ = artifact_paths(case)
        oracle_bytes = result_path.read_bytes()
        if row.get("oracle_full_blake3") != blake3_bytes(oracle_bytes):
            fail(f"{case['id']}: status oracle full digest drift")
        result_doc = load_json(result_path)
        if case["artifacts"]["result_kind"] == "surface":
            expected_projection = blake3_bytes(oracle_bytes)
        else:
            expected_projection = projection_digest(
                result_doc, case["diagnostic"]["kind"]
            )
        if row.get("oracle_projection_blake3") != expected_projection:
            fail(f"{case['id']}: status oracle projection digest drift")
        for field in (
            "handwritten_full_blake3",
            "handwritten_projection_blake3",
        ):
            value = row.get(field)
            if value is not None and not is_blake3(value):
                fail(f"{case['id']}: invalid {field}")
        if row.get("status") == "exact":
            exact += 1
        else:
            mismatches.append(case["id"])
    expected_summary = {
        "exact": exact,
        "mismatch_or_failure": len(mismatches),
        "mismatches": mismatches,
    }
    if status.get("summary") != expected_summary:
        fail("handwritten status summary drift")


def validate_entries(manifest: dict[str, Any]) -> None:
    expected = {
        "rust-typesig.receipt.json": ("rust.TypeSigParser", "public"),
        "prism-type.receipt.json": ("prism.parse_type", "public"),
        "prism-let-pattern.receipt.json": (
            "prism.parse_let_pattern",
            "dead-public-edge",
        ),
    }
    found = sorted(path.name for path in ENTRIES.glob("*.receipt.json"))
    if found != sorted(expected):
        fail(f"direct-entry receipt set drift: {found}")
    cases = {case["id"]: case for case in manifest["cases"]}
    for name, (entry_id, visibility) in expected.items():
        receipt = load_json(ENTRIES / name)
        if receipt.get("schema") != "prism-parser-compaction-entry-receipt-v1":
            fail(f"{name}: schema drift")
        if receipt.get("oracle_commit") != ORACLE_COMMIT:
            fail(f"{name}: oracle drift")
        if receipt.get("entry_id") != entry_id:
            fail(f"{name}: entry identity drift")
        if receipt.get("visibility") != visibility:
            fail(f"{name}: visibility drift")
        if receipt.get("outcome") != "accepted" or receipt.get("status") != "exact":
            fail(f"{name}: direct entry is not exact accepted")
        case_id = receipt.get("matching_wrapper_case")
        if case_id not in cases:
            fail(f"{name}: unknown wrapper case {case_id}")
        case = cases[case_id]
        source = (CORPUS / case["source"]).read_text()
        lo, hi = case["fragment_span"]
        if receipt.get("fragment") != source.encode()[lo:hi].decode():
            fail(f"{name}: fragment bytes drift")
        token_slice = receipt.get("token_slice")
        if not isinstance(token_slice, list):
            fail(f"{name}: token slice missing")
        if receipt.get("unconsumed_position") != len(token_slice):
            fail(f"{name}: complete-consumption position drift")
        if receipt.get("stop") != hi:
            fail(f"{name}: stop offset drift")
        expected_projection = receipt.get("wrapper_value_projection")
        if receipt.get("value_projection") != expected_projection:
            fail(f"{name}: direct value differs from wrapper projection")
        if not is_blake3(receipt.get("value_projection_blake3")):
            fail(f"{name}: value projection digest missing")
        encoded = json.dumps(
            receipt["value_projection"],
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        ).encode()
        if blake3_bytes(encoded) != receipt["value_projection_blake3"]:
            fail(f"{name}: value projection digest drift")


def check_corpus(oracle: str, section: str) -> None:
    manifest = load_json(MANIFEST)
    vertical = load_json(VERTICAL)
    validate_manifest(manifest, oracle)
    if vertical.get("schema") != SCHEMAS["vertical"]:
        fail("vertical inventory schema drift")
    if vertical.get("oracle_commit") != ORACLE_COMMIT:
        fail("vertical inventory oracle drift")
    for case in manifest["cases"]:
        source = validate_source(case)
        result_path, tokens_path = artifact_paths(case)
        tokens = validate_artifact(case, tokens_path, SCHEMAS["tokens"], source)
        result_kind = case["artifacts"]["result_kind"]
        if result_kind == "surface":
            result = validate_artifact(case, result_path, SCHEMAS["surface"], source)
            if not isinstance(result.get("items"), list) or not result["items"]:
                fail(f"{case['id']}: accepted artifact has no items")
        elif result_kind == "diagnostics":
            result = validate_artifact(
                case, result_path, SCHEMAS["diagnostics"], source
            )
            diagnostic_projection(result, case["diagnostic"]["kind"])
        else:
            fail(f"{case['id']}: unknown result kind {result_kind}")
        if not isinstance(tokens.get("parse"), list):
            fail(f"{case['id']}: token artifact has no parse stream")

    expected_coverage = build_coverage(manifest, vertical)
    actual_coverage = load_json(COVERAGE)
    if actual_coverage != expected_coverage:
        fail("coverage.json is stale; rerun accept")
    if actual_coverage["uncovered"]:
        fail(
            "structural inventory has uncovered IDs: "
            f"{actual_coverage['uncovered']}"
        )
    expected_mutations = mutation_document(manifest)
    actual_mutations = load_json(MUTATIONS)
    if actual_mutations != expected_mutations:
        fail("mutation-seeds.json is stale; rerun accept")
    validate_mutation_sample(manifest)
    validate_status(load_json(STATUS), manifest)
    validate_entries(manifest)

    if section == "entries":
        if manifest["pending"]["entries"]:
            fail("entries: direct-entry receipts remain pending")
    if section in {"depth", "mutations"}:
        pending = manifest["pending"]
        key = {"depth": "depth_axes", "mutations": "mutation_lanes"}[section]
        if not pending.get(key):
            fail(f"{section}: pending ledger was silently cleared")
    if section == "vertical":
        vertical_set = set(vertical["alternatives"])
        claims = {
            coverage_id
            for case in manifest["cases"]
            for coverage_id in case["coverage_ids"]
            if coverage_id.startswith("vertical.")
        }
        unknown = claims - vertical_set
        if unknown:
            fail(f"vertical claims outside inventory: {sorted(unknown)}")
    print(
        "parser-compaction corpus: "
        f"{len(manifest['cases'])} curated cases verified; "
        f"{len(actual_coverage['uncovered'])} inventory IDs, "
        f"{len(manifest['pending']['entries'])} direct entries, "
        f"{len(manifest['pending']['depth_axes'])} depth axes, and "
        f"{len(manifest['pending']['mutation_lanes'])} mutation lanes pending; "
        "Phase 1B remains blocked"
    )


def dump_phase(binary: Path, phase: str, source: Path) -> bytes:
    result = run([str(binary), "dump", phase, str(source)], check=False)
    if result.returncode != 0:
        stderr = result.stderr.decode("utf-8", errors="replace")
        fail(f"{source.name}: `{phase}` dump failed:\n{stderr}")
    return result.stdout.rstrip(b"\n") + b"\n"


def compile_handwritten_harness(compiler: Path, output: Path) -> Path:
    output.parent.mkdir(parents=True, exist_ok=True)
    # This is a semantic replay executable, not a performance subject. Avoid
    # spending minutes in ThinLTO whenever parser sources change.
    run(
        [
            str(compiler),
            str(HARNESS),
            "-o",
            str(output),
            "--backend-opt",
            "0",
            "--no-compiler-cache",
        ]
    )
    return output


def compile_rust_entry_adapter(worktree: Path, output: Path) -> Path:
    project = worktree.parent / "entry-adapter"
    source_dir = project / "src"
    source_dir.mkdir(parents=True)
    (project / "Cargo.toml").write_text(
        "[package]\n"
        'name = "parser-compaction-entry-adapter"\n'
        'version = "0.0.0"\n'
        'edition = "2021"\n\n'
        "[dependencies]\n"
        f'prism-syntax = {{ path = "{worktree / "crates/prism-syntax"}" }}\n'
        'serde_json = "1"\n',
        encoding="utf-8",
    )
    shutil.copyfile(RUST_ENTRY_ADAPTER, source_dir / "main.rs")
    target = worktree.parent / "entry-adapter-target"
    env = os.environ.copy()
    env["CARGO_TARGET_DIR"] = str(target)
    run(
        [
            "cargo",
            "build",
            "--offline",
            "--manifest-path",
            str(project / "Cargo.toml"),
        ],
        cwd=project,
        env=env,
    )
    shutil.copyfile(target / "debug/parser-compaction-entry-adapter", output)
    output.chmod(0o755)
    return output


def token_slice(case: dict[str, Any]) -> list[dict[str, Any]]:
    _, tokens_path = artifact_paths(case)
    document = load_json(tokens_path)
    lo, hi = case["fragment_span"]
    return [
        token
        for token in document["raw"]
        if token["span"][0] >= lo and token["span"][1] <= hi
    ]


def projection_blake3(value: Any) -> str:
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode()
    return blake3_bytes(encoded)


def entry_receipt(
    *,
    corpus_version: int,
    entry_id: str,
    visibility: str,
    case: dict[str, Any],
    projection: Any,
    wrapper_projection: Any,
    initial_depth: int | None,
    spend_trace: list[str],
    subject: dict[str, Any],
) -> dict[str, Any]:
    tokens = token_slice(case)
    return {
        "schema": "prism-parser-compaction-entry-receipt-v1",
        "oracle_commit": ORACLE_COMMIT,
        "corpus_version": corpus_version,
        "entry_id": entry_id,
        "visibility": visibility,
        "scope": "named accepted direct-entry projection and complete token consumption",
        "matching_wrapper_case": case["id"],
        "fragment": case["fragment"],
        "token_slice": tokens,
        "stop": case["fragment_span"][1],
        "initial_depth": initial_depth,
        "outcome": "accepted",
        "unconsumed_position": len(tokens),
        "value_projection": projection,
        "wrapper_value_projection": wrapper_projection,
        "value_projection_blake3": projection_blake3(projection),
        "ordered_spend_trace": spend_trace,
        "status": "exact" if projection == wrapper_projection else "mismatch",
        "subject": subject,
    }


def materialize_entry_receipts(
    manifest: dict[str, Any],
    rust_adapter: Path,
    harness_binary: Path,
) -> None:
    cases = {case["id"]: case for case in manifest["cases"]}
    type_case = cases["type-forall"]
    pattern_case = cases["pattern-tuple-let"]
    type_result, type_tokens = artifact_paths(type_case)
    pattern_result, pattern_tokens = artifact_paths(pattern_case)
    type_wrapper = load_json(type_result)["items"][0]["params"][0]["ty"]
    pattern_wrapper = load_json(pattern_result)["items"][0]["body"]["arms"][0]["pat"]

    rust_run = run([str(rust_adapter), type_case["fragment"]])
    rust_projection = json.loads(rust_run.stdout)
    lo, hi = type_case["fragment_span"]
    prism_type_run = run(
        [
            str(harness_binary),
            "entry",
            "type",
            str(type_tokens),
            str(lo),
            str(hi),
        ]
    )
    prism_type_projection = json.loads(prism_type_run.stdout)
    lo, hi = pattern_case["fragment_span"]
    prism_pattern_run = run(
        [
            str(harness_binary),
            "entry",
            "let-pattern",
            str(pattern_tokens),
            str(lo),
            str(hi),
        ]
    )
    prism_pattern_projection = json.loads(prism_pattern_run.stdout)

    ENTRIES.mkdir(parents=True, exist_ok=True)
    common_rust = {
        "backend": "Rust/LALRPOP",
        "adapter_source_blake3": blake3_bytes(RUST_ENTRY_ADAPTER.read_bytes()),
        "adapter_executable_blake3": blake3_bytes(rust_adapter.read_bytes()),
    }
    common_prism = {
        "backend": "handwritten Prism",
        "harness_source_blake3": blake3_bytes(HARNESS.read_bytes()),
        "harness_executable_blake3": blake3_bytes(harness_binary.read_bytes()),
    }
    write_json(
        ENTRIES / "rust-typesig.receipt.json",
        entry_receipt(
            corpus_version=manifest["corpus_version"],
            entry_id="rust.TypeSigParser",
            visibility="public",
            case=type_case,
            projection=rust_projection,
            wrapper_projection=type_wrapper,
            initial_depth=None,
            spend_trace=[],
            subject=common_rust,
        ),
    )
    write_json(
        ENTRIES / "prism-type.receipt.json",
        entry_receipt(
            corpus_version=manifest["corpus_version"],
            entry_id="prism.parse_type",
            visibility="public",
            case=type_case,
            projection=prism_type_projection,
            wrapper_projection=type_wrapper,
            initial_depth=2048,
            spend_trace=["parse_type"],
            subject=common_prism,
        ),
    )
    write_json(
        ENTRIES / "prism-let-pattern.receipt.json",
        entry_receipt(
            corpus_version=manifest["corpus_version"],
            entry_id="prism.parse_let_pattern",
            visibility="dead-public-edge",
            case=pattern_case,
            projection=prism_pattern_projection,
            wrapper_projection=pattern_wrapper,
            initial_depth=2048,
            spend_trace=[
                "parse_let_pattern",
                "parse_pattern",
                "parse_pattern",
            ],
            subject=common_prism,
        ),
    )
    mismatches = [
        path.name
        for path in ENTRIES.glob("*.receipt.json")
        if load_json(path)["status"] != "exact"
    ]
    if mismatches:
        fail(f"direct-entry mismatches: {mismatches}")


def subject_provenance(
    compiler: Path,
    harness_binary: Path,
) -> dict[str, Any]:
    head = run(["git", "rev-parse", "HEAD"]).stdout.decode().strip()
    tree = run(["git", "rev-parse", "HEAD^{tree}"]).stdout.decode().strip()
    tracked_status = (
        run(["git", "status", "--porcelain=v1", "--untracked-files=no"])
        .stdout.decode()
        .splitlines()
    )
    worktree_diff = run(["git", "diff", "--binary"]).stdout
    index_diff = run(["git", "diff", "--cached", "--binary"]).stdout
    parser_paths = sorted(
        [
            path
            for path in (ROOT / "lib/std/Syntax").rglob("*.pr")
            if path.name in {"Parse.pr", "Cursor.pr", "Layout.pr", "Lex.pr"}
            or "Parse" in path.parts
        ]
    )
    source_rows = [
        {
            "path": path.relative_to(ROOT).as_posix(),
            "blake3": blake3_bytes(path.read_bytes()),
        }
        for path in parser_paths
    ]
    snapshot = b"".join(
        row["path"].encode()
        + b"\0"
        + row["blake3"].encode()
        + b"\0"
        for row in source_rows
    )
    return {
        "compiler_path": str(compiler),
        "compiler_blake3": blake3_bytes(compiler.read_bytes()),
        "harness_executable_path": str(harness_binary),
        "harness_executable_blake3": blake3_bytes(harness_binary.read_bytes()),
        "harness_source_path": HARNESS.relative_to(ROOT).as_posix(),
        "harness_source_blake3": blake3_bytes(HARNESS.read_bytes()),
        "git_head": head,
        "git_head_tree": tree,
        "tracked_worktree_status": tracked_status,
        "worktree_diff_blake3": blake3_bytes(worktree_diff),
        "index_diff_blake3": blake3_bytes(index_diff),
        "parser_source_snapshot_blake3": blake3_bytes(snapshot),
        "parser_sources": source_rows,
        "note": "The executable digests identify the actual comparison subject. Git fields describe the concurrent worktree when replay ran; they do not claim that the compiler binary was rebuilt after every dirty-tree edit.",
    }


def replay_handwritten(
    manifest: dict[str, Any],
    compiler: Path,
    harness_binary: Path,
) -> dict[str, Any]:
    rows = []
    for case in manifest["cases"]:
        result_path, _ = artifact_paths(case)
        oracle_bytes = result_path.read_bytes()
        kind = case["artifacts"]["result_kind"]
        replay = run(
            [str(harness_binary), kind, str(result_path)],
            check=False,
        )
        got_bytes = replay.stdout
        oracle_doc = load_json(result_path)
        oracle_projection = (
            blake3_bytes(oracle_bytes)
            if kind == "surface"
            else projection_digest(oracle_doc, case["diagnostic"]["kind"])
        )
        row: dict[str, Any] = {
            "case_id": case["id"],
            "oracle_full_blake3": blake3_bytes(oracle_bytes),
            "oracle_projection_blake3": oracle_projection,
            "handwritten_full_blake3": blake3_bytes(got_bytes),
            "exception_key": None,
        }
        if replay.returncode != 0:
            row.update(
                {
                    "status": "crash",
                    "handwritten_projection_blake3": None,
                    "reason": f"harness exited {replay.returncode}",
                }
            )
        elif got_bytes.startswith(b"HARNESS_ERROR"):
            row.update(
                {
                    "status": "mismatch",
                    "handwritten_projection_blake3": None,
                    "reason": got_bytes.decode("utf-8", errors="replace").strip(),
                }
            )
        elif kind == "surface":
            row.update(
                {
                    "status": "exact" if got_bytes == oracle_bytes else "mismatch",
                    "handwritten_projection_blake3": blake3_bytes(got_bytes),
                }
            )
        else:
            try:
                got_doc = json.loads(got_bytes)
                diag_kind = case["diagnostic"]["kind"]
                got_projection = projection_digest(got_doc, diag_kind)
                row.update(
                    {
                        "status": (
                            "exact"
                            if oracle_projection == got_projection
                            else "mismatch"
                        ),
                        "oracle_projection_blake3": oracle_projection,
                        "handwritten_projection_blake3": got_projection,
                    }
                )
            except (json.JSONDecodeError, RuntimeError) as error:
                row.update(
                    {
                        "status": "mismatch",
                        "oracle_projection_blake3": None,
                        "handwritten_projection_blake3": None,
                        "reason": f"invalid handwritten artifact: {error}",
                    }
                )
        rows.append(row)
    mismatches = [row["case_id"] for row in rows if row["status"] != "exact"]
    return {
        "schema": SCHEMAS["status"],
        "oracle_commit": ORACLE_COMMIT,
        "corpus_version": manifest["corpus_version"],
        "subject": "recorded handwritten Prism parser executable",
        "subject_provenance": subject_provenance(compiler, harness_binary),
        "gate_ready": False,
        "cases": rows,
        "summary": {
            "exact": len(rows) - len(mismatches),
            "mismatch_or_failure": len(mismatches),
            "mismatches": mismatches,
        },
        "pending_reason": "A mismatch is evidence, not an exception. Curated tranche 2 has no reviewed exception ledger and is not a parity gate.",
    }


def accept_corpus(oracle: str, compiler_arg: str | None) -> None:
    if os.environ.get(ACCEPT_ENV) != "1":
        fail(f"accept requires {ACCEPT_ENV}=1")
    manifest = load_json(MANIFEST)
    vertical = load_json(VERTICAL)
    validate_manifest(manifest, oracle)
    commit = run(["git", "rev-parse", f"{oracle}^{{commit}}"]).stdout.decode().strip()
    tree = run(["git", "rev-parse", f"{oracle}^{{tree}}"]).stdout.decode().strip()
    if commit != ORACLE_COMMIT or tree != ORACLE_TREE:
        fail("resolved oracle identity differs from the frozen commit/tree")

    rust_adapter = ROOT / "target/parser-compaction-entry-adapter"
    with tempfile.TemporaryDirectory(prefix="prism-parser-oracle-") as temp_name:
        worktree = Path(temp_name) / "worktree"
        run(["git", "worktree", "add", "--detach", str(worktree), oracle])
        try:
            if run(["git", "status", "--porcelain"], cwd=worktree).stdout:
                fail("detached oracle worktree is dirty before build")
            run(["cargo", "build", "--locked", "--bin", "prism"], cwd=worktree)
            if run(["git", "status", "--porcelain"], cwd=worktree).stdout:
                fail("detached oracle worktree became dirty during build")
            binary = worktree / "target/debug/prism"
            if not binary.is_file():
                fail("frozen oracle binary was not produced")
            compile_rust_entry_adapter(worktree, rust_adapter)
            rustc = run(["rustc", "-Vv"]).stdout.decode().strip()
            cargo = run(["cargo", "-V"]).stdout.decode().strip()
            manifest["oracle"].update(
                {
                    "tree": tree,
                    "executable_blake3": blake3_bytes(binary.read_bytes()),
                    "build_command": "cargo build --locked --bin prism",
                    "toolchain": {"rustc": rustc, "cargo": cargo},
                }
            )
            for case in manifest["cases"]:
                source_path = CORPUS / case["source"]
                if isinstance(case.get("artifacts"), dict):
                    # Existing oracle rows are immutable history. Revalidate
                    # their complete bytes against the current manifest and
                    # leave both files untouched.
                    source = validate_source(case)
                    result_path, tokens_path = artifact_paths(case)
                    validate_artifact(
                        case, tokens_path, SCHEMAS["tokens"], source
                    )
                    result_kind = case["artifacts"]["result_kind"]
                    schema = (
                        SCHEMAS["surface"]
                        if result_kind == "surface"
                        else SCHEMAS["diagnostics"]
                    )
                    validate_artifact(case, result_path, schema, source)
                    continue
                source = source_path.read_bytes()
                fragment = case["fragment"]
                text = source.decode("utf-8")
                if text.count(fragment) != 1:
                    fail(f"{case['id']}: fragment must occur exactly once")
                character_start = text.index(fragment)
                lo = len(text[:character_start].encode())
                case["fragment_span"] = [lo, lo + len(fragment.encode())]
                tokens_bytes = dump_phase(binary, "syntax-tokens", source_path)
                tokens_doc = json.loads(tokens_bytes)
                case["source_blake3"] = tokens_doc["source"]["digest"]
                token_rel = f"oracle/{case['id']}.syntax-tokens.json"
                token_path = CORPUS / token_rel
                token_path.parent.mkdir(parents=True, exist_ok=True)
                token_path.write_bytes(tokens_bytes)

                surface = run(
                    [str(binary), "dump", "surface-syntax", str(source_path)],
                    cwd=worktree,
                    check=False,
                )
                if surface.returncode == 0:
                    result_kind = "surface"
                    suffix = "surface-syntax"
                    result_bytes = surface.stdout.rstrip(b"\n") + b"\n"
                else:
                    result_kind = "diagnostics"
                    suffix = "syntax-diagnostics"
                    result_bytes = dump_phase(
                        binary, "syntax-diagnostics", source_path
                    )
                    doc = json.loads(result_bytes)
                    if len(doc.get("diagnostics", [])) != 1:
                        fail(f"{case['id']}: malformed case needs one diagnostic")
                result_rel = f"oracle/{case['id']}.{suffix}.json"
                (CORPUS / result_rel).write_bytes(result_bytes)
                case["artifacts"] = {
                    "result_kind": result_kind,
                    "result": result_rel,
                    "tokens": token_rel,
                }
        finally:
            # `git worktree remove` is scoped to the exact temporary worktree
            # created above and leaves Git's administrative records clean.
            run(["git", "worktree", "remove", "--force", str(worktree)], check=False)

    compiler = (
        Path(compiler_arg).resolve()
        if compiler_arg
        else ROOT / "target/debug/prism"
    )
    if not compiler.is_file():
        fail(
            f"handwritten subject compiler {compiler} is missing; "
            "build it or pass --handwritten-compiler"
        )
    harness_binary = ROOT / "target/parser-compaction-check"
    compile_handwritten_harness(compiler, harness_binary)
    materialize_entry_receipts(manifest, rust_adapter, harness_binary)
    manifest["pending"]["entries"] = []
    manifest["pending"]["phase1b"]["reason"] = (
        "Phase 1B generator implementation cannot claim parity until exact "
        "depth traces and mutation lanes are implemented and every recorded "
        "handwritten mismatch or intentional post-freeze delta is resolved."
    )
    write_json(MANIFEST, manifest)
    write_json(COVERAGE, build_coverage(manifest, vertical))
    write_json(MUTATIONS, mutation_document(manifest))
    write_json(STATUS, replay_handwritten(manifest, compiler, harness_binary))
    check_corpus(oracle, "all")
    print(
        "parser-compaction accept: frozen Rust artifacts written from "
        f"{ORACLE_COMMIT}; tranche remains gate_ready=false"
    )


def replay_corpus(
    oracle: str,
    compiler_arg: str | None,
    harness_arg: str | None,
    recompile_handwritten: bool,
) -> None:
    manifest = load_json(MANIFEST)
    validate_manifest(manifest, oracle)
    compiler = (
        Path(compiler_arg).resolve()
        if compiler_arg
        else ROOT / "target/debug/prism"
    )
    harness_binary = (
        Path(harness_arg).resolve()
        if harness_arg
        else ROOT / "target/parser-compaction-check"
    )
    for path, label in ((compiler, "subject compiler"),):
        if not path.is_file():
            fail(f"{label} {path} is missing")
    if recompile_handwritten:
        compile_handwritten_harness(compiler, harness_binary)
    elif not harness_binary.is_file():
        fail(f"compiled replay harness {harness_binary} is missing")
    rust_adapter = ROOT / "target/parser-compaction-entry-adapter"
    if not rust_adapter.is_file():
        fail(f"compiled Rust entry adapter {rust_adapter} is missing")
    materialize_entry_receipts(manifest, rust_adapter, harness_binary)
    # The source-only mutation schedule pins this driver's exact bytes even
    # before candidates exist, so a reviewed driver repair refreshes that
    # receipt together with the replay status.
    write_json(COVERAGE, build_coverage(manifest, load_json(VERTICAL)))
    write_json(MUTATIONS, mutation_document(manifest))
    write_json(
        STATUS,
        replay_handwritten(manifest, compiler, harness_binary),
    )
    check_corpus(oracle, "all")
    print("parser-compaction replay: handwritten status and provenance refreshed")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "command",
        choices=(
            "check",
            "accept",
            "replay",
            "tranche3-plan",
            "tranche3-depth-calibrate",
            "tranche3-depth-materialize",
            "tranche3-mutate-bounded",
        ),
    )
    parser.add_argument("--oracle", required=True)
    parser.add_argument(
        "--section",
        choices=("all", "corpus", "coverage", "mutations", "entries", "vertical", "depth"),
        default="all",
    )
    parser.add_argument("--handwritten-compiler")
    parser.add_argument("--handwritten-harness")
    parser.add_argument("--depth-harness")
    parser.add_argument("--depth-axis", choices=DEPTH_AXES)
    parser.add_argument("--mutation-oracle-compiler")
    parser.add_argument("--mutation-draw-cap", type=int, default=2)
    parser.add_argument("--mutation-lane", choices=[lane for lane, _ in MUTATION_LANES])
    parser.add_argument("--mutation-receipt")
    parser.add_argument(
        "--probe-depth-compiler",
        help="validate each depth source generator at three layers with this compiler",
    )
    parser.add_argument(
        "--refresh-derived-ledgers",
        action="store_true",
        help="with tranche3-plan, refresh coverage.json and mutation-seeds.json",
    )
    parser.add_argument(
        "--recompile-handwritten",
        action="store_true",
        help="compile the replay harness with the selected handwritten compiler first",
    )
    args = parser.parse_args()
    try:
        if args.command == "accept":
            accept_corpus(args.oracle, args.handwritten_compiler)
        elif args.command == "replay":
            replay_corpus(
                args.oracle,
                args.handwritten_compiler,
                args.handwritten_harness,
                args.recompile_handwritten,
            )
        elif args.command == "tranche3-plan":
            manifest = load_json(MANIFEST)
            validate_manifest(manifest, args.oracle)
            state, first = splitmix64_next(0)
            _, second = splitmix64_next(state)
            if (first, second) != (
                0xE220A8397B1DCDAF,
                0x6E789E6AA1B965F4,
            ):
                fail("SplitMix64-v1 known-answer test failed")
            mutation_preview = mutation_schedule_preview(manifest)
            if mutation_preview != mutation_schedule_preview(manifest):
                fail("mutation schedule preview is nondeterministic")
            probe_compiler = (
                Path(args.probe_depth_compiler).resolve()
                if args.probe_depth_compiler
                else None
            )
            if probe_compiler is not None and not probe_compiler.is_file():
                fail(f"depth probe compiler {probe_compiler} is missing")
            preview = {
                "schema": "prism-parser-compaction-tranche3-plan-preview-v1",
                "oracle_commit": ORACLE_COMMIT,
                "corpus_version": manifest["corpus_version"],
                "depth": depth_schedule_preview(manifest, probe_compiler),
                "mutations": mutation_preview,
            }
            if args.refresh_derived_ledgers:
                write_json(
                    COVERAGE,
                    build_coverage(manifest, load_json(VERTICAL)),
                )
                write_json(MUTATIONS, mutation_document(manifest))
            print(json.dumps(preview, indent=2, ensure_ascii=False))
        elif args.command == "tranche3-depth-calibrate":
            manifest = load_json(MANIFEST)
            validate_manifest(manifest, args.oracle)
            if args.depth_axis is None:
                fail("tranche3-depth-calibrate requires --depth-axis")
            compiler = (
                Path(args.handwritten_compiler).resolve()
                if args.handwritten_compiler
                else ROOT / "target/debug/prism"
            )
            harness = (
                Path(args.depth_harness).resolve()
                if args.depth_harness
                else ROOT / "target/parser-compaction-depth-check"
            )
            for path, label in (
                (compiler, "depth token compiler"),
                (harness, "compiled depth harness"),
            ):
                if not path.is_file():
                    fail(f"{label} {path} is missing")
            print(
                json.dumps(
                    calibrate_depth_axis(
                        args.depth_axis,
                        compiler,
                        harness,
                    ),
                    indent=2,
                    ensure_ascii=False,
                )
            )
        elif args.command == "tranche3-depth-materialize":
            compiler = (
                Path(args.handwritten_compiler).resolve()
                if args.handwritten_compiler
                else ROOT / "target/debug/prism"
            )
            harness = (
                Path(args.depth_harness).resolve()
                if args.depth_harness
                else ROOT / "target/parser-compaction-depth-check"
            )
            for path, label in ((compiler, "depth token compiler"), (harness, "compiled depth harness")):
                if not path.is_file():
                    fail(f"{label} {path} is missing")
            print(json.dumps(materialize_depth_receipts(compiler, harness), indent=2))
        elif args.command == "tranche3-mutate-bounded":
            manifest = load_json(MANIFEST)
            validate_manifest(manifest, args.oracle)
            oracle = (
                Path(args.mutation_oracle_compiler).resolve()
                if args.mutation_oracle_compiler
                else None
            )
            if oracle is None or not oracle.is_file():
                fail(
                    "tranche3-mutate-bounded requires "
                    "--mutation-oracle-compiler pointing at the frozen binary"
                )
            harness = (
                Path(args.handwritten_harness).resolve()
                if args.handwritten_harness
                else ROOT / "target/parser-compaction-check"
            )
            if not harness.is_file():
                fail(f"compiled replay harness {harness} is missing")
            mutation_receipt = bounded_mutation_run(
                        manifest,
                        oracle,
                        harness,
                        args.mutation_draw_cap,
                        args.mutation_lane,
                    )
            if args.mutation_receipt:
                write_json(Path(args.mutation_receipt), mutation_receipt)
            print(json.dumps(mutation_receipt, indent=2, ensure_ascii=False))
        else:
            check_corpus(args.oracle, args.section)
    except (OSError, RuntimeError, KeyError, TypeError, ValueError) as error:
        print(f"parser-compaction corpus: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
