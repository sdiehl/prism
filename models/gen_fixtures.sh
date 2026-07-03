#!/usr/bin/env bash
# Regenerate the committed core-json certificate fixtures.
#
# `Certificates.lean` hand-encodes the erased essence of each program below and
# proves by kernel `rfl` that the verified CEK model evaluates it to the value
# `prism run` printed. Each such program has a committed sibling
# `fixtures/<name>.json`: the FULL `prism dump core-json` of the fixture (the
# real compiler core, prelude included), so the reference in `Certificates.lean`
# points at a live artifact instead of a nonexistent file.
#
# This is the `just hash` / `just docs-gen` idiom: the .json is a committed
# artifact, and CI's drift check regenerates it and diffs (see the Lean job in
# .github/workflows/ci.yml). Run this whenever the compiler's core output or the
# fixtures change, and commit the result.
set -euo pipefail
cd "$(dirname "$0")"
PRISM="${PRISM:-../target/debug/prism}"

# The fixtures with a kernel certificate in Certificates.lean. The whole 23-file
# corpus is checked live against the model by diff_against_rust.sh; only these
# carry a committed dump, because only these are referenced by name.
CERT_FIXTURES=(inc mul vec tup ite)

for name in "${CERT_FIXTURES[@]}"; do
  "$PRISM" dump core-json "fixtures/$name.pr" > "fixtures/$name.json"
done
echo "regenerated: ${CERT_FIXTURES[*]}"
