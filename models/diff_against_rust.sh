#!/usr/bin/env bash
# Differential oracle against the LIVE Rust interpreter, on the REAL lowered core.
# For each fixtures/*.pr:
#   rust  = `prism run` final value
#   lean  = `prism dump core-json` (the actual compiler core) | `oracle eval -`
#           run through the formally-verified CEK model
# and compares the rendered values. No hand-encoding: both sides consume the
# identical core the compiler builds.
set -uo pipefail
cd "$(dirname "$0")"
ORACLE="${ORACLE:-.lake/build/bin/oracle}"
PRISM="${PRISM:-../target/debug/prism}"
pass=0; fail=0
for pr in fixtures/*.pr; do
  name="$(basename "${pr%.pr}")"
  rust="$("$PRISM" run "$pr" 2>/dev/null | sed -n 's/^=> //p')"
  lean="$("$PRISM" dump core-json "$pr" 2>/dev/null | "$ORACLE" eval - 2>&1)"
  if [ "$rust" = "$lean" ]; then
    printf '  ok    %-8s => %s\n' "$name" "$lean"; pass=$((pass+1))
  else
    printf '  DIFF  %-8s rust=[%s] lean=[%s]\n' "$name" "$rust" "$lean"; fail=$((fail+1))
  fi
done
echo "passed=$pass failed=$fail"
[ "$fail" -eq 0 ]
