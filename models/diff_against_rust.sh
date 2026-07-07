#!/usr/bin/env bash
# Differential oracle against the LIVE Rust interpreter, on the REAL lowered core.
# For each fixtures/*.pr:
#   manifest = source/core-json/Core-hash/result SHA from gen_fixtures.sh
#   rust     = `prism run` final value
#   lean     = `prism dump core-json` (the actual compiler core) | `oracle eval -`
#              run through the formally-verified CEK model
# and compares the rendered values. No hand-encoding: both sides consume the
# identical core the compiler builds, and stale generated inputs fail before the
# oracle sees them.
#
# This is a correctness gate, not a report: ANY divergence is a hard failure
# (nonzero exit). A pass requires that the fixture actually ran on both sides
# (Rust produced a value, the oracle exited 0) AND the rendered values are equal.
# An oracle that errors, a `prism run` that produces nothing, or an empty corpus
# are all failures, never a silent green: the empty-equals-empty and
# error-text-equals-value coincidences must not be mistaken for agreement.
set -uo pipefail
cd "$(dirname "$0")"
ORACLE="${ORACLE:-.lake/build/bin/oracle}"
PRISM="${PRISM:-../target/debug/prism}"
MANIFEST="${MANIFEST:-fixtures/core-hashes.tsv}"

hash_stdin() {
  python3 -c 'import hashlib, sys; print(hashlib.sha256(sys.stdin.buffer.read()).hexdigest())'
}

hash_file() {
  python3 -c 'import hashlib, pathlib, sys; print(hashlib.sha256(pathlib.Path(sys.argv[1]).read_bytes()).hexdigest())' "$1"
}

manifest_row() {
  awk -F '\t' -v name="$1" '$1 == name { print; found = 1 } END { if (!found) exit 1 }' "$MANIFEST"
}

extract_main_hash() {
  awk '$2 == "main" { print $1; found = 1 } END { if (!found) exit 1 }'
}

pass=0; fail=0; total=0
for pr in fixtures/*.pr; do
  total=$((total+1))
  name="$(basename "${pr%.pr}")"
  row="$(manifest_row "$name" 2>/dev/null)"
  source_hash="$(hash_file "$pr")"
  core_hashes="$("$PRISM" dump core-hash "$pr" 2>/dev/null)"
  core="$("$PRISM" dump core-json "$pr" 2>/dev/null)"
  defs="$(printf '%s\n' "$core_hashes" | wc -l | tr -d ' ')"
  main_hash="$(printf '%s\n' "$core_hashes" | extract_main_hash)"
  core_hash_digest="$(printf '%s\n' "$core_hashes" | hash_stdin)"
  core_json_digest="$(printf '%s' "$core" | hash_stdin)"
  rust="$("$PRISM" run "$pr" 2>/dev/null | sed -n 's/^=> //p')"
  reason=""
  lean=""
  oracle_rc=0
  if [ -z "$row" ]; then
    reason="missing manifest row; run models/gen_fixtures.sh"
  else
    IFS=$'\t' read -r manifest_name manifest_source_hash manifest_defs manifest_main_hash manifest_core_hash_digest manifest_core_json_digest manifest_result <<< "$row"
  fi
  if [ -z "$reason" ] && [ "$manifest_source_hash" != "$source_hash" ]; then
    reason="source SHA drift; run models/gen_fixtures.sh"
  elif [ -z "$reason" ] && [ "$manifest_defs" != "$defs" ]; then
    reason="Core def count drift; run models/gen_fixtures.sh"
  elif [ -z "$reason" ] && [ "$manifest_main_hash" != "$main_hash" ]; then
    reason="main Core hash drift; run models/gen_fixtures.sh"
  elif [ -z "$reason" ] && [ "$manifest_core_hash_digest" != "$core_hash_digest" ]; then
    reason="Core hash-list SHA drift; run models/gen_fixtures.sh"
  elif [ -z "$reason" ] && [ "$manifest_core_json_digest" != "$core_json_digest" ]; then
    reason="core-json SHA drift; run models/gen_fixtures.sh"
  elif [ -z "$reason" ] && [ -z "$rust" ]; then
    reason="rust produced no value (prism run failed?)"
  elif [ -z "$reason" ] && [ "$manifest_result" != "$rust" ]; then
    reason="result drift; run models/gen_fixtures.sh"
  fi
  if [ -z "$reason" ]; then
    lean="$(printf '%s' "$core" | "$ORACLE" eval - 2>&1)"; oracle_rc=$?
  fi
  if [ -z "$reason" ] && [ "$oracle_rc" -ne 0 ]; then
    reason="oracle exited $oracle_rc"
  elif [ -z "$reason" ] && [ "$rust" != "$lean" ]; then
    reason="value mismatch"
  fi
  if [ -z "$reason" ]; then
    printf '  ok    %-8s => %s\n' "$name" "$lean"; pass=$((pass+1))
  else
    printf '  DIFF  %-8s rust=[%s] lean=[%s] (%s)\n' "$name" "$rust" "$lean" "$reason"; fail=$((fail+1))
  fi
done
echo "passed=$pass failed=$fail of $total"
# Hard failure on any divergence, and on an empty corpus (nothing verified is
# not the same as everything agreeing).
[ "$total" -gt 0 ] && [ "$fail" -eq 0 ] && [ "$pass" -eq "$total" ]
