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

# 1. One wasm bundle, shared by the docs and the playground. cdylib is not in
#    Cargo.toml (rlib-only keeps the dead dylib off native builds); `cargo rustc
#    --crate-type cdylib` asks for it only here, and wasm-bindgen (version-matched
#    to the crate) produces the JS glue. This is `just wasm` without the just.
cargo rustc --lib --crate-type cdylib --target wasm32-unknown-unknown \
  --release --no-default-features --features wasm
wasm-bindgen target/wasm32-unknown-unknown/release/prism.wasm \
  --target web --out-dir web/pkg --out-name prism
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

# 3. The web app: the self-contained pages (playground, gallery, and the
#    gallery's residents), each bundling its own wasm copy.
(cd web && pnpm install --frozen-lockfile && pnpm build)

# 4. Stitch into one tree: book at /, playground at /play/, the
#    gallery at /gallery/, and its residents at /scrub/ and /pendulum/. The web
#    pages share the same dist bundle; each subdirectory serves its own html as
#    the directory index.
rm -rf "$out"
mkdir -p "$out/play" "$out/gallery" "$out/scrub" "$out/pendulum" "$out/branch" "$out/chaos" "$out/schedule" "$out/teleport" "$out/merkle" "$out/incr" "$out/world"
cp -R docs/book/. "$out/"
cp -R web/dist/. "$out/play/"
cp -R web/dist/. "$out/gallery/"
cp -R web/dist/. "$out/scrub/"
cp -R web/dist/. "$out/pendulum/"
cp -R web/dist/. "$out/branch/"
cp -R web/dist/. "$out/chaos/"
cp -R web/dist/. "$out/schedule/"
cp -R web/dist/. "$out/teleport/"
cp -R web/dist/. "$out/merkle/"
cp -R web/dist/. "$out/incr/"
cp -R web/dist/. "$out/world/"
cp -f web/dist/gallery.html "$out/gallery/index.html"
cp -f web/dist/scrubber.html "$out/scrub/index.html"
cp -f web/dist/pendulum.html "$out/pendulum/index.html"
cp -f web/dist/branch.html "$out/branch/index.html"
cp -f web/dist/chaos.html "$out/chaos/index.html"
cp -f web/dist/schedule.html "$out/schedule/index.html"
cp -f web/dist/teleport.html "$out/teleport/index.html"
cp -f web/dist/merkle.html "$out/merkle/index.html"
cp -f web/dist/incr.html "$out/incr/index.html"
cp -f web/dist/prism-world.html "$out/world/index.html"
cp -f web/dist/prism.png "$out/prism.png" 2>/dev/null || true

# 5. The unverified semantics sketch is generated from its tracked Typst source
#    straight into the Pages artifact. The PDF is never committed.
typst compile --root "$root" \
  models/semantics/semantics.typ "$out/semantics.pdf"

# 6. The shell installer, served at /install.sh for `curl ... | sh`.
cp -f scripts/install.sh "$out/install.sh"

echo "unified site assembled at $out (docs at /, playground at /play/, gallery at /gallery/, scrubber at /scrub/, pendulum at /pendulum/, branch at /branch/, chaos at /chaos/, schedule at /schedule/, teleport at /teleport/, merkle at /merkle/, incr at /incr/, world at /world/)"
