#!/usr/bin/env bash
# Differential oracle against the LIVE Rust interpreter, on the REAL lowered core.
# For each fixtures/*.pr:
#   rust  = `prism run` final value
#   lean  = `prism dump core-json` (the actual compiler core) | `oracle eval -`
#           run through the formally-verified CEK model
# and compares the rendered values. No hand-encoding: both sides consume the
# identical core the compiler builds.
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
pass=0; fail=0; total=0
for pr in fixtures/*.pr; do
  total=$((total+1))
  name="$(basename "${pr%.pr}")"
  rust="$("$PRISM" run "$pr" 2>/dev/null | sed -n 's/^=> //p')"
  core="$("$PRISM" dump core-json "$pr" 2>/dev/null)"
  lean="$(printf '%s' "$core" | "$ORACLE" eval - 2>&1)"; oracle_rc=$?
  reason=""
  if [ -z "$rust" ]; then
    reason="rust produced no value (prism run failed?)"
  elif [ "$oracle_rc" -ne 0 ]; then
    reason="oracle exited $oracle_rc"
  elif [ "$rust" != "$lean" ]; then
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
