#!/usr/bin/env bash
# Fail unless the CI workflow completed successfully for the given commit, so a
# tag release never builds off a red main. Needs gh + GH_TOKEN in the env.
set -euo pipefail
sha="${1:?usage: require-green-ci.sh <sha>}"
repo="${GITHUB_REPOSITORY:?}"
concl="$(gh api "repos/${repo}/actions/workflows/ci.yml/runs?head_sha=${sha}&per_page=1" \
           -q '.workflow_runs[0] | "\(.status)/\(.conclusion)"' 2>/dev/null || true)"
echo "CI for ${sha}: ${concl:-<none>}"
case "$concl" in
  completed/success) echo "main is green" ;;
  "" | "null/null") echo "no CI run found for ${sha}; push to main and let CI pass first"; exit 1 ;;
  *) echo "CI for ${sha} is '${concl}', not a green completed run"; exit 1 ;;
esac
