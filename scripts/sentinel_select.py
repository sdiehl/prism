#!/usr/bin/env python3
"""Select the sentinel corpus: the small program set covering every recorded axis.

The committed manifests already classify the whole runnable corpus: the tier
manifest records each program's effect-lowering tier, the strategy snapshot
records each effectful program's lowering strategy, and the cost manifest
records interpreter-step and native-cell magnitudes. This task reads those
three, adds the effect names each program's source spells (row annotations and
effect declarations), and greedily picks the fewest programs that cover every
observed feature, padding with the costliest programs per tier up to the
target size. The result, tests/sentinel_corpus.txt, is the local fast gate's
corpus; the full matrix stays on CI.

Run with no arguments to regenerate the list, or with --check to verify the
committed list still matches what selection would produce today.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TIER_MANIFEST = ROOT / "tests" / "tier_manifest.txt"
COST_MANIFEST = ROOT / "tests" / "cost_manifest.txt"
STRATEGY_SNAPSHOT = (
    ROOT / "tests" / "snapshots" / "snapshots__effect_strategy_manifest.snap"
)
SENTINEL_LIST = ROOT / "tests" / "sentinel_corpus.txt"

TARGET_SIZE = 60

EFFECT_ROW = re.compile(r"!\s*\{([^}]*)\}")
EFFECT_DECL = re.compile(r"^\s*(?:pub\s+)?effect\s+([A-Z]\w*)", re.MULTILINE)
EFFECT_NAME = re.compile(r"^[A-Z]\w*$")

HEADER = """# Sentinel corpus: the coverage-selected subset the local fast gate runs, one
# corpus label per line. Selected so that every effect-lowering tier, every
# lowering strategy, every effect name the corpus spells, and every cost
# magnitude recorded by the committed manifests appears in at least one
# program. Read by tests/support when PRISM_SENTINEL_CORPUS is set; the full
# matrix stays on CI. Regenerate with `just sentinel` after the corpus or the
# manifests change; `just sentinel --check` verifies currency. Do not hand-edit.
"""


def manifest_rows(path: Path) -> list[list[str]]:
    rows = []
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        rows.append(line.split("\t"))
    return rows


def strategy_rows() -> dict[str, str]:
    rows = {}
    for line in STRATEGY_SNAPSHOT.read_text().splitlines():
        label, separator, strategy = line.partition(": ")
        if separator and label.endswith(".pr"):
            rows[label] = strategy
    return rows


def effect_features(label: str) -> set[str]:
    source = (ROOT / label).read_text()
    names: set[str] = set(EFFECT_DECL.findall(source))
    for row in EFFECT_ROW.findall(source):
        for token in re.split(r"[,|]", row):
            token = token.strip()
            if EFFECT_NAME.match(token):
                names.add(token)
    return {f"effect:{name}" for name in names}


def magnitude(count: str) -> str:
    return str(len(str(max(int(count), 1))))


def program_features() -> tuple[dict[str, set[str]], dict[str, int]]:
    """Feature set and interpreter-step count per corpus program."""
    tiers = {row[0]: row[1] for row in manifest_rows(TIER_MANIFEST)}
    costs = {row[0]: (row[1], row[2]) for row in manifest_rows(COST_MANIFEST)}
    strategies = strategy_rows()
    features: dict[str, set[str]] = {}
    steps: dict[str, int] = {}
    for label, tier in sorted(tiers.items()):
        found = {f"tier:{tier}"}
        if label in strategies:
            found.add(f"strategy:{strategies[label]}")
        if label in costs:
            step_count, cell_count = costs[label]
            found.add(f"steps:{magnitude(step_count)}")
            found.add(f"cells:{magnitude(cell_count)}")
            steps[label] = int(step_count)
        found |= effect_features(label)
        features[label] = found
        steps.setdefault(label, 0)
    return features, steps


def select() -> list[str]:
    features, steps = program_features()
    uncovered = set().union(*features.values())
    selected: list[str] = []
    remaining = dict(features)

    # Greedy set cover: the program covering the most uncovered features wins,
    # ties broken by the costlier program (more likely to exercise the deep
    # paths), then by label for determinism.
    while uncovered:
        label = min(
            remaining,
            key=lambda l: (-len(features[l] & uncovered), -steps[l], l),
        )
        selected.append(label)
        uncovered -= features[label]
        del remaining[label]

    # Pad toward the target with the costliest not-yet-selected programs of
    # each tier, round-robin, so magnitude depth grows evenly across tiers.
    by_tier: dict[str, list[str]] = {}
    for label in remaining:
        tier = next(f for f in features[label] if f.startswith("tier:"))
        by_tier.setdefault(tier, []).append(label)
    for tier in by_tier:
        by_tier[tier].sort(key=lambda l: (-steps[l], l))
    while len(selected) < TARGET_SIZE and any(by_tier.values()):
        for tier in sorted(by_tier):
            if by_tier[tier] and len(selected) < TARGET_SIZE:
                selected.append(by_tier[tier].pop(0))
    return sorted(selected)


def render(selected: list[str]) -> str:
    return HEADER + "".join(f"{label}\n" for label in selected)


def main(arguments: list[str]) -> int:
    rendered = render(select())
    if arguments == ["--check"]:
        committed = SENTINEL_LIST.read_text() if SENTINEL_LIST.exists() else ""
        if committed != rendered:
            print(
                "sentinel corpus is stale; regenerate with `just sentinel`",
                file=sys.stderr,
            )
            return 1
        print(f"sentinel corpus is current ({rendered.count('.pr')} programs)")
        return 0
    if arguments:
        print("usage: sentinel_select.py [--check]", file=sys.stderr)
        return 2
    SENTINEL_LIST.write_text(rendered)
    print(f"sentinel corpus selected: {rendered.count('.pr')} programs -> {SENTINEL_LIST}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
