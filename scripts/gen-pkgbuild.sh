#!/usr/bin/env bash
# Stamp the Arch PKGBUILD for a release: set pkgver and replace the checksums with
# the real sha256 of each Linux tarball's `.sha256` sidecar in DIST. Writes to OUT
# (default dist/PKGBUILD, the shipped release asset covered by SHA256SUMS); pass
# OUT=packaging/arch/PKGBUILD to refresh the committed template in place.
# Usage: gen-pkgbuild.sh VERSION [DIST] [OUT].
set -euo pipefail
version="${1:?usage: gen-pkgbuild.sh VERSION [DIST] [OUT]}"
dist="${2:-dist}"
out="${3:-$dist/PKGBUILD}"
template="packaging/arch/PKGBUILD"

sum_of() {
  local sidecar="$dist/prism-$version-$1-unknown-linux-gnu.tar.gz.sha256"
  [ -f "$sidecar" ] || { echo "missing $sidecar (need the release tarballs in $dist)" >&2; exit 1; }
  # First field of the tarball's .sha256 sidecar produced by the build jobs.
  awk '{print $1; exit}' "$sidecar"
}
x86=$(sum_of x86_64)
arm=$(sum_of aarch64)

# Stage through a temp file so OUT may be the template itself (in-place refresh):
# a plain `> "$out"` would truncate the input before sed reads it.
tmp="$(mktemp)"
sed -e "s/^pkgver=.*/pkgver=$version/" \
    -e "s/^sha256sums_x86_64=.*/sha256sums_x86_64=('$x86')/" \
    -e "s/^sha256sums_aarch64=.*/sha256sums_aarch64=('$arm')/" \
    "$template" > "$tmp"
mkdir -p "$(dirname "$out")"
mv "$tmp" "$out"
echo "wrote $out (pkgver=$version, x86_64=$x86, aarch64=$arm)"
