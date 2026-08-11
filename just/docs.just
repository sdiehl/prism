# Build and sync the wasm playground bundle.
[group('web')]
wasm:
    cargo rustc --lib --crate-type cdylib --target wasm32-unknown-unknown --release --no-default-features --features wasm
    wasm-bindgen target/wasm32-unknown-unknown/release/prism.wasm --target web --out-dir web/pkg --out-name prism
    cp web/pkg/prism.js web/pkg/prism_bg.wasm docs/src/pkg/

# Regenerate embedded playground examples.
[group('web')]
[working-directory('web')]
examples:
    pnpm gen-examples

# Build wasm and serve the playground.
[group('web')]
[working-directory('web')]
web: wasm
    pnpm install
    pnpm dev

# Lint, type-check, and build the playground.
[group('web')]
[working-directory('web')]
web-build:
    pnpm install
    pnpm lint
    pnpm typecheck
    pnpm build

# Regenerate and test the Standard Library Reference.
[group('docs')]
docs-gen:
    cargo build --release --features native
    ./target/release/prism docs --stdlib --out docs/src/stdlib
    ./target/release/prism docs --stdlib --test

# Regenerate and doctest the package references (the book's Packages part).
[group('docs')]
docs-packages:
    cargo build --release --features native
    ./target/release/prism docs packages/tzdb --out docs/src/packages/tzdb
    ./target/release/prism docs packages/tzdb --out packages/tzdb/docs
    ./target/release/prism docs packages/tzdb --test
    ./target/release/prism docs packages/typst --out docs/src/packages/typst
    ./target/release/prism docs packages/typst --out packages/typst/docs
    ./target/release/prism docs packages/typst --test
    ./target/release/prism docs packages/spectra --out docs/src/packages/spectra
    ./target/release/prism docs packages/spectra --out packages/spectra/docs
    ./target/release/prism docs packages/spectra --test
    ./target/release/prism docs packages/tc --out docs/src/packages/tc
    ./target/release/prism docs packages/tc --out packages/tc/docs
    ./target/release/prism docs packages/tc --test

# Regenerate the compaction scoreboard; pass `--check` to verify it.
[group('generated artifacts')]
scoreboard *ARGS:
    ./scripts/scoreboard.py {{ ARGS }}

# Regenerate the parser baseline; pass `--check` to verify it.
[group('generated artifacts')]
parser-baseline *ARGS:
    ./scripts/parser_baseline.py {{ ARGS }}

# Check or explicitly accept the frozen parser corpus.
[group('generated artifacts')]
parser-corpus COMMAND="check" *ARGS:
    ./scripts/parser-compaction-corpus.py {{ COMMAND }} --oracle 46886c1fa7064e4809020c1b788b3ee3531d6a63 {{ ARGS }}

# Validate the parser production manifest.
[group('generated artifacts')]
parser-production-manifest COMMAND="check":
    ./scripts/parser-production-manifest.py {{ COMMAND }}

# Regenerate Core and lowering dumps used by the book.
[group('docs')]
docs-core:
    cargo build --release
    PRISM_BIN=target/release/prism bash docs/scripts/gen-core.sh

# Regenerate every content-addressed standard-library artifact.
[group('generated artifacts')]
hash: docs-gen
    INSTA_UPDATE=always cargo test --test snapshots shape_digests

# Check every committed generated artifact for drift.
[group('generated artifacts')]
artifacts-check:
    ./scripts/artifacts-check.sh

# Regenerate dependencies, build the book, and serve it.
[group('docs')]
docs: docs-gen docs-packages wasm
    mdbook build docs
    mdbook serve docs --open

# Regenerate the Lean differential-oracle fixture manifest.
[group('generated artifacts')]
[working-directory('models')]
fixtures: build
    ./gen_fixtures.sh

# Compare generated programs with the Lean CEK oracle.
[group('tests')]
lean-fuzz: build
    python3 scripts/dev_tasks.py lean-fuzz

# Accept a reviewed effect-lowering tier manifest.
[group('generated artifacts')]
tier-accept:
    PRISM_ACCEPT_TIER_MANIFEST=1 cargo test --test native_perf tier_manifest_holds -- --nocapture

# Rewrite stale inline doctest output expectations.
[group('generated artifacts')]
bless PATH=".":
    cargo run -- docs {{ PATH }} --test --accept

# Serve the determinism scrubber.
[group('web')]
[working-directory('web')]
scrub: wasm
    pnpm install
    pnpm gen-examples
    pnpm exec vite --open /scrubber.html

# Verify that two local identity manifests are byte-identical.
[group('tests')]
identity:
    python3 scripts/check_identity.py
