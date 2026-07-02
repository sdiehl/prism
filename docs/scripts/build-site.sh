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

# 2. The compiler binary drives the docs preprocessor (which live-checks every
#    ```prism block) and regenerates the Standard Library reference; build it and
#    refresh the generated pages so the book is in sync with the stdlib.
cargo build --release --features native
./target/release/prism docs --stdlib --out docs/src/stdlib

# 3. The book (inline Run loads /pkg/prism.js). PRISM_MDBOOK_STRICT fails the
#    build if a block that should type-check does not.
PRISM_MDBOOK_STRICT=1 mdbook build docs

# 3. The web app: two self-contained pages, the playground (index.html) and the
#    REPL (repl.html), both bundling their own wasm copy.
(cd web && pnpm install --frozen-lockfile && pnpm build)

# 4. Stitch into one tree: book at /, playground at /play/, REPL at /repl/. Both
#    web pages share the same dist bundle; /repl/ serves repl.html as its index.
rm -rf "$out"
mkdir -p "$out/play" "$out/repl"
cp -R docs/book/. "$out/"
cp -R web/dist/. "$out/play/"
cp -R web/dist/. "$out/repl/"
cp -f web/dist/repl.html "$out/repl/index.html"
cp -f web/dist/prism.png "$out/prism.png" 2>/dev/null || true

echo "unified site assembled at $out (docs at /, playground at /play/, REPL at /repl/)"
