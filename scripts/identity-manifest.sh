#!/usr/bin/env bash
# Cross-platform determinism identity manifest.
#
# Builds the pinned corpus (tests/identity/corpus) through one prism binary and
# emits, for every corpus program, the determinism-critical artifacts as a stable
# text manifest: Core hashes, namespace roots, shape digests, the portable native
# continuation envelope, the run observation output, the step ruler, replay
# output, the serialized replay trace, and the SMT and totality query bytes.
#
# The manifest is a pure function of the source and the pinned input trace (empty
# stdin): running it twice, or from a different checkout root, yields byte-for-byte
# the same output. No absolute path, wall-clock, or platform token reaches the
# manifest -- the one platform-varying line of the native-kont envelope (the build
# target triple) is stripped so the envelope compares only where it is portable.
# Emitting the same manifest on Linux x86-64, Linux ARM64, and macOS ARM64 and
# diffing them is the cross-platform determinism gate (Lane X); a single divergent
# byte fails it.
#
# Usage:
#   scripts/identity-manifest.sh [--out FILE] [--corpus DIR]
#   PRISM_BIN=path/to/prism scripts/identity-manifest.sh > manifest.txt
#
# PRISM_BIN defaults to target/release/prism. The corpus defaults to
# tests/identity/corpus and its pinned CORPUS list.

set -euo pipefail

MANIFEST_FORMAT="prism-identity-manifest-v1"

PRISM_BIN="${PRISM_BIN:-target/release/prism}"
CORPUS_DIR="tests/identity/corpus"
OUT=""

while [ $# -gt 0 ]; do
  case "$1" in
    --out) OUT="$2"; shift 2 ;;
    --corpus) CORPUS_DIR="$2"; shift 2 ;;
    *) echo "identity-manifest: unknown argument $1" >&2; exit 2 ;;
  esac
done

if [ ! -x "$PRISM_BIN" ]; then
  echo "identity-manifest: prism binary not found or not executable: $PRISM_BIN" >&2
  echo "  build it first (cargo build --release --features native) or set PRISM_BIN" >&2
  exit 2
fi

CORPUS_LIST="$CORPUS_DIR/CORPUS"
if [ ! -f "$CORPUS_LIST" ]; then
  echo "identity-manifest: pinned corpus list not found: $CORPUS_LIST" >&2
  exit 2
fi

# Portable content digest of stdin, hex only. sha256sum on Linux, shasum on macOS;
# the digest bytes are identical, so the manifest is stable across both hosts.
digest() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum | cut -d' ' -f1
  else
    shasum -a 256 | cut -d' ' -f1
  fi
}

# The native-kont envelope carries one platform-specific line (the build target
# triple); every other line is a content hash, a config flag, or a mangled name,
# all portable. Strip only that line so the envelope compares where it is portable.
kont_envelope() {
  "$PRISM_BIN" dump native-kont-table "$1" </dev/null 2>/dev/null | grep -v '^target '
}

# Record a run to a temp trace, discarding the record command's own stdout (it
# names the trace path, which is not portable), then print the serialized trace
# bytes. The trace is a serialized observation stream, path-independent.
replay_trace() {
  local src="$1" trace
  trace="$(mktemp "${TMPDIR:-/tmp}/prism_identity.XXXXXX")"
  "$PRISM_BIN" run "$src" --record "$trace" </dev/null >/dev/null 2>/dev/null
  cat "$trace"
  rm -f "$trace"
}

# Reproduce a recorded run and print the replayed observation output. Equal to the
# direct run output by the determinism contract; compared here across platforms.
replay_output() {
  local src="$1" trace
  trace="$(mktemp "${TMPDIR:-/tmp}/prism_identity.XXXXXX")"
  "$PRISM_BIN" run "$src" --record "$trace" </dev/null >/dev/null 2>/dev/null
  "$PRISM_BIN" exec replay "$src" "$trace" </dev/null 2>/dev/null
  rm -f "$trace"
}

# The producing artifact for one (kind, file), on stdout. Every command reads empty
# stdin (the pinned input trace) and drops stderr, so only the artifact bytes count.
artifact() {
  local kind="$1" src="$2"
  case "$kind" in
    core-hash)     "$PRISM_BIN" dump core-hash "$src" </dev/null 2>/dev/null ;;
    namespace)     "$PRISM_BIN" dump namespace "$src" </dev/null 2>/dev/null ;;
    shape)         "$PRISM_BIN" dump shape "$src" </dev/null 2>/dev/null ;;
    smt)           "$PRISM_BIN" dump smt "$src" </dev/null 2>/dev/null ;;
    totality)      "$PRISM_BIN" dump totality "$src" </dev/null 2>/dev/null ;;
    kont-envelope) kont_envelope "$src" ;;
    run-output)    "$PRISM_BIN" run "$src" </dev/null 2>/dev/null ;;
    steps)         "$PRISM_BIN" exec steps --json "$src" </dev/null 2>/dev/null ;;
    replay-output) replay_output "$src" ;;
    replay-trace)  replay_trace "$src" ;;
    *) echo "identity-manifest: unknown artifact kind $kind" >&2; exit 2 ;;
  esac
}

# The artifact kinds compared for every corpus program, in a fixed order.
KINDS="core-hash namespace shape smt totality kont-envelope run-output steps replay-output replay-trace"

emit() {
  # A version string identical on every platform of the same build, so it pins
  # what was compared without perturbing the cross-platform diff.
  local version
  version="$("$PRISM_BIN" --version 2>/dev/null | awk '{print $NF}')"

  echo "$MANIFEST_FORMAT"
  echo "compiler $version"
  echo

  # Read the pinned corpus once into a sorted list so file order is stable
  # regardless of how the CORPUS list happens to be ordered.
  local files
  files="$(grep -vE '^\s*(#|$)' "$CORPUS_LIST" | LC_ALL=C sort)"

  echo "# digests: <sha256>  <kind>  <file>"
  local file kind src
  for file in $files; do
    src="$CORPUS_DIR/$file"
    if [ ! -f "$src" ]; then
      echo "identity-manifest: pinned corpus file missing: $src" >&2
      exit 2
    fi
    for kind in $KINDS; do
      printf '%s  %-13s  %s\n' "$(artifact "$kind" "$src" | digest)" "$kind" "$file"
    done
  done

  # The SMT and totality query bytes verbatim, so the manifest literally carries
  # the queries Lane X pins across platforms, not only their digests.
  echo
  echo "# smt-query-bytes"
  for file in $files; do
    src="$CORPUS_DIR/$file"
    echo ">>> smt $file"
    artifact smt "$src"
    echo "<<< smt $file"
  done

  echo
  echo "# totality-query-bytes"
  for file in $files; do
    src="$CORPUS_DIR/$file"
    echo ">>> totality $file"
    artifact totality "$src"
    echo "<<< totality $file"
  done
}

if [ -n "$OUT" ]; then
  emit > "$OUT"
  echo "identity-manifest: wrote $OUT" >&2
else
  emit
fi
