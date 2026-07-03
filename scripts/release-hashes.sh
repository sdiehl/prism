#!/usr/bin/env bash
# SHA256SUMS over every asset in the target dir, then one release Merkle root
# (sha256 of the sorted manifest). Verify with `sha256sum -c SHA256SUMS`.
set -euo pipefail
dir="${1:-dist}"
cd "$dir"
: > SHA256SUMS
for f in $(find . -maxdepth 1 -type f \
             ! -name 'SHA256SUMS' ! -name 'release-merkle-root.txt' \
             ! -name '*.sha256' -printf '%f\n' | sort); do
  sha256sum "$f" >> SHA256SUMS
done
cat SHA256SUMS
root="$(sha256sum SHA256SUMS | awk '{print $1}')"
printf '%s\n' "$root" > release-merkle-root.txt
echo "release Merkle root: $root"
