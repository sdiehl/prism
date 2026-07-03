#!/usr/bin/env bash
# Push deb/rpm packages in the given dir to Gemfury.
# Env: FURY_PUSH_TOKEN (push token), FURY_ACCOUNT (fury username).
set -euo pipefail
dir="${1:-dist}"
: "${FURY_PUSH_TOKEN:?}"
: "${FURY_ACCOUNT:?}"
shopt -s nullglob
for f in "$dir"/*.deb "$dir"/*.rpm; do
  echo "pushing $(basename "$f")"
  curl -fsS -F package=@"$f" "https://${FURY_PUSH_TOKEN}@push.fury.io/${FURY_ACCOUNT}/"
  echo
done
