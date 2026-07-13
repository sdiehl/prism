#!/usr/bin/env bash
# Regenerate every committed compiler-artifact file the book includes from its
# source .pr, using the real compiler. Each row of core-artifacts.tsv is
#
#   <source.pr>	<phase>	<extract>	<output.txt>
#
# where <phase> is a `prism dump` phase (core, lowered, fbip, llvm), <extract>
# is a comma-separated list of top-level function names to slice out of the dump
# (or `-` to keep the whole prelude-stripped dump), and <output.txt> is the file
# the book includes. `dump core` already drops the prelude; `dump lowered`/`fbip`
# do not, so those rows always name the functions to keep. The `llvm` phase is
# dumped at `-O0` so a small illustrative function survives (the backend
# optimizer would otherwise inline and constant-fold it away), and only the named
# `define @prism_<fn>` blocks are kept, dropping the module header and the
# content-addressed kont tables (which embed the stdlib root hash and would churn
# on every stdlib edit). Output is normalized to no trailing blank lines and a
# single final newline so the committed files stay byte-stable and idempotent.
# Run via `just docs-core`.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../.." && pwd)"
examples="$root/docs/examples"
manifest="$examples/core-artifacts.tsv"
prism="${PRISM_BIN:-$root/target/release/prism}"

if [[ ! -x "$prism" ]]; then
  echo "gen-core: compiler binary not found at $prism (build it first, e.g. cargo build --release)" >&2
  exit 1
fi

# Print the top-level `fn NAME` blocks for the requested names, in dump order.
# A block runs from a column-0 `fn NAME` line to the next column-0 line.
extract() {
  awk -v names="$1" '
    BEGIN { n = split(names, a, ","); for (i = 1; i <= n; i++) want[a[i]] = 1 }
    /^fn / { nm = $2; sub(/\(.*/, "", nm); inblk = (nm in want) }
    /^[^ ]/ && $0 !~ /^fn / { inblk = 0 }
    inblk { print }
  '
}

# Print the `define @prism_NAME(...) { .. }` blocks for the requested names, in
# module order, each preceded by its `; Function Attrs:` comment. Names are the
# Prism function names; the emitted symbol is `@prism_<name>`.
extract_llvm() {
  awk -v names="$1" '
    BEGIN { n = split(names, a, ","); for (i = 1; i <= n; i++) want["@prism_" a[i]] = 1 }
    inblk { print; if ($0 ~ /^}/) inblk = 0; next }
    /^; Function Attrs:/ { pend = $0; next }
    /^define / {
      fn = $0; sub(/^define[^@]*/, "", fn); sub(/\(.*/, "", fn)
      if (fn in want) { if (pend != "") print pend; print; inblk = 1 }
      pend = ""; next
    }
    { pend = "" }
  '
}

# Strip trailing blank lines, guarantee exactly one final newline.
normalize() {
  awk 'BEGIN { blanks = 0 }
       { if ($0 == "") { blanks++; next } while (blanks-- > 0) print ""; blanks = 0; print }'
}

count=0
while IFS=$'\t' read -r src phase names out; do
  case "$src" in ''|'#'*) continue ;; esac
  if [[ "$phase" == "llvm" ]]; then
    raw="$("$prism" dump llvm -O0 "$examples/$src" 2>/dev/null)"
    body="$(printf '%s\n' "$raw" | extract_llvm "$names")"
  else
    raw="$("$prism" dump "$phase" "$examples/$src" 2>/dev/null)"
    if [[ "$names" == "-" ]]; then
      body="$raw"
    else
      body="$(printf '%s\n' "$raw" | extract "$names")"
    fi
  fi
  printf '%s\n' "$body" | normalize >"$examples/$out"
  count=$((count + 1))
done <"$manifest"

echo "gen-core: regenerated $count artifact file(s) from $manifest"
