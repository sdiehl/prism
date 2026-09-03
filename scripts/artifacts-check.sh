#!/usr/bin/env bash
# Drift check for every committed generated artifact whose currency no ordinary
# test asserts. Some have their own gate elsewhere (the stdlib reference in
# Checks, the fixture manifest in the Lean job) and some had none anywhere, so a
# stale artifact could sit green in one validator and red in the other, or red
# in neither; this is the one command that covers the set. Run via
# `just artifacts-check`, which `just ci` depends on, and from the Checks job.
#
# Every check runs before anything is reported, and each failure names the
# recipe that fixes it. The regenerating checks diff against the working tree
# rather than HEAD, so an artifact already regenerated but not yet committed
# passes; when one does drift the fresh bytes are left in place, because that is
# the fix and the diff is the review.

set -o pipefail
cd "$(dirname "$0")/.." || exit 1

PRISM=target/release/prism

fails=0
report=""

# check LABEL FIX COMMAND...: run the command, and on failure record the label
# with the recipe that repairs it.
check() {
    label="$1"
    fix="$2"
    shift 2
    printf '== %s\n' "$label"
    "$@" && return 0
    fails=$((fails + 1))
    report="${report}  - ${label}: ${fix}"$'\n'
}

# regen_diff PATH GENERATOR...: snapshot the artifact, regenerate it, and diff.
# Handles a file and a directory alike.
regen_diff() {
    path="$1"
    shift
    saved="$tmp/$(basename "$path")"
    cp -R "$path" "$saved"
    "$@" >/dev/null || return 1
    diff -ru "$saved" "$path"
}

quiet() { "$@" >/dev/null; }
gen_fixtures() { (cd models && ./gen_fixtures.sh); }
gen_figures() { PRISM_BIN="$PRISM" bash docs/scripts/gen-core.sh; }

# The release binary generates the docs; the fixture manifest pins the debug
# binary's output, as its CI job does.
cargo build --release --features native || exit 1
cargo build || exit 1

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

check "stdlib reference (docs/src/stdlib)" \
    "run 'just docs-gen', or 'just hash' if digests moved" \
    "$PRISM" docs --stdlib --check --out docs/src/stdlib

check "stdlib doctests" "run 'just bless --stdlib'" \
    quiet "$PRISM" docs --stdlib --test

check "sentinel corpus (tests/sentinel_corpus.txt)" "run 'just sentinel'" \
    ./scripts/sentinel_select.py --check

check "parser-compaction frozen corpus" "run 'just parser-corpus check'" \
    ./scripts/parser-compaction-corpus.py check \
    --oracle 46886c1fa7064e4809020c1b788b3ee3531d6a63

check "fixture manifest (models/fixtures/core-hashes.tsv)" \
    "regenerated in place, review the diff and commit" \
    regen_diff models/fixtures/core-hashes.tsv gen_fixtures

check "book compiler figures (docs/examples)" \
    "regenerated in place, review the diff and commit" \
    regen_diff docs/examples gen_figures

if [ "$fails" -gt 0 ]; then
    printf '\nartifacts-check: %d stale artifact(s)\n%s' "$fails" "$report" >&2
    exit 1
fi
echo "artifacts-check: every committed generated artifact is current"
