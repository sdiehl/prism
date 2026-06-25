#!/usr/bin/env bash
# Assemble the unified Pages site: the mdbook docs at /, the playground at
# /play/, both driven by ONE wasm build of the crate (web/pkg/prism.js). The
# docs' inline "Run" buttons and the standalone playground load the same
# interpreter, so what runs in either matches the native parity oracle.
#
# Usage: docs/scripts/build-site.sh [output-dir]   (default: ./public)
set -euo pipefail
root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$root"
out="${1:-$root/public}"

# 1. One wasm bundle, shared by the docs and the playground.
wasm-pack build --target web --out-dir web/pkg --no-default-features --features wasm
mkdir -p docs/src/pkg
cp -f web/pkg/prism.js web/pkg/prism_bg.wasm docs/src/pkg/

# 2. The book (inline Run loads /pkg/prism.js).
mdbook build docs

# 3. The playground (bakes examples/*.pr, bundles its own wasm copy).
(cd web && pnpm install --frozen-lockfile && pnpm build)

# 4. Stitch into one tree.
rm -rf "$out"
mkdir -p "$out/play"
cp -R docs/book/. "$out/"
cp -R web/dist/. "$out/play/"
cp -f web/dist/prism.png "$out/prism.png" 2>/dev/null || true

echo "unified site assembled at $out (docs at /, playground at /play/)"
