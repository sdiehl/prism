#!/usr/bin/env bash
# Stamp packaging/arch/PKGBUILD for a release: set pkgver and replace the SKIP
# checksums with the real sha256 of each Linux tarball already in the dist dir,
# then write the result to dist/PKGBUILD so it ships as a release asset (and is
# covered by SHA256SUMS, which runs after this). Usage: gen-pkgbuild.sh VERSION [DIST].
set -euo pipefail
version="${1:?usage: gen-pkgbuild.sh VERSION [DIST]}"
dist="${2:-dist}"
template="packaging/arch/PKGBUILD"

sum_of() {
  # First field of the tarball's .sha256 sidecar produced by the build jobs.
  awk '{print $1; exit}' "$dist/prism-$version-$1-unknown-linux-gnu.tar.gz.sha256"
}
x86=$(sum_of x86_64)
arm=$(sum_of aarch64)

sed -e "s/^pkgver=.*/pkgver=$version/" \
    -e "s/^sha256sums_x86_64=.*/sha256sums_x86_64=('$x86')/" \
    -e "s/^sha256sums_aarch64=.*/sha256sums_aarch64=('$arm')/" \
    "$template" > "$dist/PKGBUILD"
echo "wrote $dist/PKGBUILD (pkgver=$version, x86_64=$x86, aarch64=$arm)"
