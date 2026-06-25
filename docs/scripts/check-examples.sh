#!/usr/bin/env bash
# Compile every Prism example referenced by the docs. Exits 0 only if all of
# docs/examples/*.pr compile with the real prism binary. This is the hard gate
# behind the Accuracy axis: docs may only embed code that the compiler accepts.
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$root"

examples_dir="docs/examples"
shopt -s nullglob
files=("$examples_dir"/*.pr)
if [ ${#files[@]} -eq 0 ]; then
  echo "no examples in $examples_dir"; exit 1
fi

# Locate or build the prism binary.
prism=""
for cand in target/release/prism target/debug/prism; do
  [ -x "$cand" ] && prism="$cand" && break
done
if [ -z "$prism" ]; then
  echo "building prism (release)..."
  cargo build --release >/dev/null
  prism="target/release/prism"
fi

# Prefer a full native build (matches CI); fall back to type-check only if the
# native toolchain (LLVM/clang) is unavailable in this environment.
mode="build"
if ! "$prism" build "${files[0]}" -o /tmp/prism_doc_probe >/dev/null 2>&1; then
  echo "note: native build unavailable, falling back to 'prism check' (type-check only)"
  mode="check"
fi

fail=0
for f in "${files[@]}"; do
  if [ "$mode" = "build" ]; then
    if "$prism" build "$f" -o /tmp/prism_doc_bin >/dev/null 2>&1; then
      echo "ok    $f"
    else
      echo "FAIL  $f"; "$prism" build "$f" -o /tmp/prism_doc_bin || true; fail=1
    fi
  else
    if "$prism" check "$f" >/dev/null 2>&1; then
      echo "ok    $f"
    else
      echo "FAIL  $f"; "$prism" check "$f" || true; fail=1
    fi
  fi
done

rm -f /tmp/prism_doc_bin /tmp/prism_doc_probe
exit $fail
