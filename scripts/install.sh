#!/bin/sh
# Prism installer, served at https://sdiehl.github.io/prism/install.sh
#
#   curl --proto '=https' --tlsv1.2 -fsSL https://sdiehl.github.io/prism/install.sh | sh
#
# Downloads the release tarball for this platform from GitHub releases,
# verifies its SHA-256 against the release's SHA256SUMS manifest before
# anything is unpacked, optionally verifies the GitHub build-provenance
# attestation when an authenticated `gh` CLI is available, and installs the
# binary to ~/.local/bin. No sudo, no arbitrary code from the tarball is run.
#
# Supported platforms: macOS on Apple Silicon, Linux (glibc) on x86_64 and
# aarch64. Alpine/musl users should install the apk from the releases page.
#
# If Nix is installed, the installer uses it instead: `nix profile install
# github:sdiehl/prism`, where the flake pin and the Nix store's own hash
# verification replace the manual checksum path.
#
# Overrides:
#   PRISM_VERSION=v0.11.0   install a specific release (default: latest)
#   PRISM_INSTALL_DIR=DIR   install directory (default: ~/.local/bin)
#   PRISM_NO_NIX=1          skip the Nix path even if nix is installed
#
# Everything runs from main() invoked on the last line, so a truncated
# download executes nothing.
set -eu

REPO="sdiehl/prism"
API="https://api.github.com/repos/$REPO"
DOWNLOAD="https://github.com/$REPO/releases/download"

say() { printf 'prism-install: %s\n' "$1"; }
err() { printf 'prism-install: error: %s\n' "$1" >&2; exit 1; }

need_cmd() {
  command -v "$1" >/dev/null 2>&1 || err "required command not found: $1"
}

# All downloads: HTTPS only, modern TLS, fail on HTTP errors, retry transient.
fetch() {
  curl --proto '=https' --tlsv1.2 -fsSL --retry 3 -o "$2" "$1" \
    || err "download failed: $1"
}

detect_target() {
  os="$(uname -s)"
  arch="$(uname -m)"
  case "$os" in
    Darwin)
      case "$arch" in
        arm64) TARGET="aarch64-apple-darwin" ;;
        *) err "macOS on $arch is unsupported (Apple Silicon only); use Nix or build from source" ;;
      esac
      ;;
    Linux)
      if [ -f /etc/alpine-release ] || (ldd --version 2>&1 | grep -qi musl); then
        err "musl libc detected; install the apk from https://github.com/$REPO/releases instead"
      fi
      case "$arch" in
        x86_64) TARGET="x86_64-unknown-linux-gnu" ;;
        aarch64 | arm64) TARGET="aarch64-unknown-linux-gnu" ;;
        *) err "Linux on $arch is unsupported (x86_64 and aarch64 only)" ;;
      esac
      ;;
    *) err "unsupported OS: $os (macOS Apple Silicon and Linux only)" ;;
  esac
}

resolve_version() {
  if [ -n "${PRISM_VERSION:-}" ]; then
    TAG="v${PRISM_VERSION#v}"
  else
    fetch "$API/releases/latest" "$TMP/latest.json"
    TAG="$(sed -n 's/.*"tag_name" *: *"\([^"]*\)".*/\1/p' "$TMP/latest.json" | head -n 1)"
    [ -n "$TAG" ] || err "could not resolve the latest release tag from the GitHub API"
  fi
  VERSION="${TAG#v}"
}

sha256_of() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

verify_checksum() {
  fetch "$DOWNLOAD/$TAG/SHA256SUMS" "$TMP/SHA256SUMS"
  expected="$(awk -v f="$PKG.tar.gz" '$2 == f { print $1 }' "$TMP/SHA256SUMS")"
  [ -n "$expected" ] || err "no SHA256SUMS entry for $PKG.tar.gz in release $TAG"
  actual="$(sha256_of "$TMP/$PKG.tar.gz")"
  if [ "$actual" != "$expected" ]; then
    err "checksum mismatch for $PKG.tar.gz
  expected: $expected
  actual:   $actual
The download is corrupt or has been tampered with. Nothing was installed."
  fi
  say "checksum verified: $expected"
}

verify_provenance() {
  if command -v gh >/dev/null 2>&1 && gh auth status >/dev/null 2>&1; then
    if gh attestation verify "$TMP/$PKG.tar.gz" --repo "$REPO" >/dev/null 2>&1; then
      say "build provenance attestation verified"
    else
      err "build provenance attestation FAILED for $PKG.tar.gz; refusing to install"
    fi
  else
    say "provenance check skipped (no authenticated gh CLI); checksum already verified"
  fi
}

smoke() {
  if out="$("$1" --version 2>&1)"; then
    say "installed: $out"
  else
    say "binary installed but failed to launch: $out"
    case "$(uname -s)" in
      Darwin) say "prism needs LLVM 22 at runtime: brew install llvm@22" ;;
      Linux) say "prism needs LLVM 22 + clang at runtime: on Debian/Ubuntu run
  curl -fsSL https://apt.llvm.org/llvm.sh | sudo bash -s 22
on other distros install your llvm-22/clang packages, or use the rpm/pacman
packages from https://github.com/$REPO/releases which declare the dependency" ;;
    esac
    exit 1
  fi
}

try_nix() {
  [ -z "${PRISM_NO_NIX:-}" ] || return 0
  command -v nix >/dev/null 2>&1 || return 0
  ref="github:$REPO"
  [ -z "${PRISM_VERSION:-}" ] || ref="$ref/v${PRISM_VERSION#v}"
  say "nix detected; installing via the flake (hashes verified by the Nix store)"
  # `nix profile add` replaced `install` (which newer Nix warns is a
  # deprecated alias); try the new verb first, keep the old one for older Nix.
  if nix --extra-experimental-features 'nix-command flakes' \
       profile add "$ref" 2>/dev/null \
     || nix --extra-experimental-features 'nix-command flakes' \
       profile install "$ref"; then
    smoke "$(command -v prism || echo "$HOME/.nix-profile/bin/prism")"
    exit 0
  fi
  say "nix install failed; falling back to the release tarball"
}

main() {
  need_cmd curl
  need_cmd tar
  need_cmd uname
  need_cmd mktemp

  try_nix

  TMP="$(mktemp -d)"
  trap 'rm -rf "$TMP"' EXIT INT TERM

  detect_target
  resolve_version
  PKG="prism-$VERSION-$TARGET"
  say "installing prism $TAG for $TARGET"

  fetch "$DOWNLOAD/$TAG/$PKG.tar.gz" "$TMP/$PKG.tar.gz"
  verify_checksum
  verify_provenance

  tar -xzf "$TMP/$PKG.tar.gz" -C "$TMP"
  [ -f "$TMP/$PKG/prism" ] || err "tarball did not contain $PKG/prism"

  dir="${PRISM_INSTALL_DIR:-$HOME/.local/bin}"
  mkdir -p "$dir"
  cp "$TMP/$PKG/prism" "$dir/prism.tmp.$$"
  chmod 755 "$dir/prism.tmp.$$"
  mv -f "$dir/prism.tmp.$$" "$dir/prism"
  say "installed to $dir/prism"

  case ":$PATH:" in
    *":$dir:"*) ;;
    *) say "note: $dir is not on your PATH; add it, e.g.
  export PATH=\"$dir:\$PATH\"" ;;
  esac

  smoke "$dir/prism"
}

main
