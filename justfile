default:
    @just --list

build:
    cargo build

build-release:
    cargo build --release

prism *ARGS:
    cargo run -- {{ARGS}}

run FILE:
    cargo run -- run "{{FILE}}"

check FILE:
    cargo run -- check "{{FILE}}"

# Default local test runner: nextest for all Rust test binaries, then doctests
# (nextest deliberately skips rustdoc tests).
test:
    cargo nextest run --all
    cargo test --doc

parity:
    cargo test --test native_parity parity::

perf:
    cargo test --test native_perf perf_gate::

snapshots:
    cargo test --test snapshots

fmt:
    cargo fmt --all

fmt-check:
    cargo fmt --all --check

clippy:
    cargo clippy --all-targets -- -D warnings

# --- fast inner loop: filtered output, exit codes preserved ---

# Full test suite via nextest (failures-only), then doctests (nextest skips them).
t:
    cargo nextest run --all
    cargo test --doc

# Run one test target or filter, filtered the same way. e.g. `just t1 fmt_records`
t1 FILTER:
    #!/usr/bin/env bash
    set -o pipefail
    cargo test {{FILTER}} 2>&1 | grep -E "test result:|FAILED|error\[|error:|panicked"

# Regenerate snapshots (optionally one FILTER), then show which changed.
snap FILTER="":
    #!/usr/bin/env bash
    INSTA_UPDATE=always cargo test {{FILTER}} 2>&1 | grep -E "test result:|error\[|error:" || true
    git status --short tests/snapshots || true

# Interactively accept/reject pending snapshot changes (needs cargo-insta).
review:
    cargo insta review

# Format .pr files in place with the debug binary (whole tree if no args).
fmtw *FILES:
    cargo run --quiet -- fmt {{FILES}}

# Build, surfacing only errors and warnings (exit code preserved).
b:
    #!/usr/bin/env bash
    out=$(cargo build 2>&1); code=$?
    echo "$out" | grep -E "error|warning" || echo "build clean"
    exit $code

# Type-check only, no codegen or linking: the quickest "did I break it" signal.
c:
    #!/usr/bin/env bash
    out=$(cargo check --all-targets 2>&1); code=$?
    echo "$out" | grep -E "error|warning" || echo "check clean"
    exit $code

# Feature matrix as an explicit local command, matching the CI matrix below.
feature-matrix:
    cargo check --all-targets
    cargo check --no-default-features --features wasm --target wasm32-unknown-unknown
    cargo check --features mlir
    cargo check --features mimalloc

# Generated artifacts must not be rewritten by ordinary tests. Run this after a
# check/test command, or in CI after the test suite, to catch surprise mutation.
no-drift:
    git diff --exit-code
    git diff --cached --exit-code

# Compile-time baselines over the pinned corpus (benches/compile.rs). Pass extra
# criterion flags after `--`, e.g. `just bench -- --quick` for a fast pass.
bench *ARGS:
    cargo bench --bench compile -- {{ARGS}}

# Compile one program to a native binary and run it (fast codegen smoke).
smoke1 FILE:
    #!/usr/bin/env bash
    set -euo pipefail
    # A codegen sanity check without the whole parity corpus.
    # e.g. `just smoke1 examples/accum.pr`
    bin="$(mktemp "${TMPDIR:-/tmp}/prism_smoke1.XXXXXX")"
    trap 'rm -f "$bin" "$bin".bc "$bin".ll' EXIT
    cargo run --quiet -- "{{FILE}}" -o "$bin"
    "$bin"

# The four correctness oracles, filtered to summaries/failures; one definition
# the three public gate recipes share. Callers pass the cargo profile flags and
# inherit the environment (e.g. PRISM_GATE_CACHE), so the target list and filter
# live in exactly one place. Built --release for `gate`/`gate-fast` so the
# compiler-under-test runs optimized over the whole native corpus (identical
# coverage to debug, several times faster); `target/release` is separate from the
# debug artifacts `just t` uses, so the two profiles do not thrash each other.
_gate *FLAGS:
    #!/usr/bin/env bash
    set -eo pipefail
    targets="--test native_parity --test native_tier --test native_fusion --test native_perf --test native_conformance --test native_sort --test native_cache --test snapshots --test compiler"
    if command -v cargo-nextest >/dev/null; then
        cargo nextest run --profile ci {{FLAGS}} $targets
    else
        cargo test {{FLAGS}} $targets 2>&1 | grep -E "test result:|FAILED|error\["
    fi

# Full correctness gate before declaring done (release profile).
gate:
    @just _gate --release

# The gate in the debug profile: slower, but skips the one-time release compile.
gate-debug:
    @just _gate

# The gate with the content-addressed verdict cache on. Trustworthy by default
# (keyed on the compiler binary, so any source change invalidates it); fall back
# to `just gate` after changing the cache's own fingerprint logic (in
# tests/support/mod.rs) or adding a compile-time input outside src/runtime/lib.
gate-fast:
    @PRISM_GATE_CACHE=1 just _gate --release

fmt-examples: build-release
    ./target/release/prism fmt --check

package-world: build-release
    ./target/release/prism pkg check-world packages --strict

ci: fmt-check clippy test fmt-examples package-world

# Build the wasm playground bundle and sync it into the docs (docs/src/pkg), so
# the mdbook playground always runs the current compiler (no stale-bundle drift).
#
# The cdylib crate-type lives here, not in Cargo.toml: `[lib]` is rlib-only so
# native builds do not link a dead ~23 MB dylib, and `cargo rustc --crate-type
# cdylib` asks for the wasm dynamic library only when building for wasm. That
# replaces `wasm-pack build`, which hard-requires cdylib in the manifest. The
# wasm-bindgen CLI must match the `wasm-bindgen` crate version (wasm-pack caches a
# matching one; otherwise `cargo install wasm-bindgen-cli`).
wasm:
    cargo rustc --lib --crate-type cdylib --target wasm32-unknown-unknown --release --no-default-features --features wasm
    wasm-bindgen target/wasm32-unknown-unknown/release/prism.wasm --target web --out-dir web/pkg --out-name prism
    cp web/pkg/prism.js web/pkg/prism_bg.wasm docs/src/pkg/

examples:
    cd web && pnpm gen-examples

web: wasm
    cd web && pnpm install && pnpm dev

# Serve the web app and open the REPL page in the browser.
web-repl: wasm
    cd web && pnpm install && pnpm gen-examples && pnpm exec vite --open /repl.html

web-build:
    cd web && pnpm install && pnpm lint && pnpm typecheck && pnpm build

# Regenerate the committed Standard Library Reference from the stdlib sources.
# CI checks this is current (`prism docs --stdlib --check`); run it after editing
# any `-- |` doc comment under lib/.
docs-gen:
    cargo build --release --features native
    ./target/release/prism docs --stdlib --out docs/src/stdlib
    ./target/release/prism docs --stdlib --test

# Regenerate every committed content-addressed stdlib artifact after a change
# that shifts a definition/type/effect hash: the Merkle-root fingerprint and
# per-def `#hash` badges live in the stdlib docs (computed from the built stdlib,
# hence `docs-gen`'s build dependency), the shape/type digests in snapshots.
hash: docs-gen
    INSTA_UPDATE=always cargo test --test snapshots shape_digests

# `docs` regenerates the stdlib reference and rebuilds the wasm bundle first (via
# `wasm`, which syncs it into docs/src/pkg), so the book and the served
# playground are never stale.
docs: docs-gen wasm
    mdbook build docs
    mdbook serve docs --open

# Cut a release: bump the version, stamp the changelog, tag v<version>, and push.
# The Release workflow then builds and publishes the macOS arm64 binary and bumps
# the Homebrew tap. Write the changes under `## Unreleased` in CHANGELOG.md first.
# Requires: cargo install cargo-release
release VERSION:
    cargo release {{VERSION}} --execute

# deb/rpm/apk for the host arch into dist/ (needs nfpm; use a Linux binary).
pkg VERSION: build-release
    #!/usr/bin/env bash
    set -euo pipefail
    # Footgun: on macOS this wraps a darwin binary in a Linux package. Run on Linux.
    if [ "$(uname -s)" = Darwin ]; then echo "WARN: packaging a macOS binary; the deb/rpm/apk won't run on Linux" >&2; fi
    export VERSION="{{VERSION}}"
    case "$(uname -m)" in
      x86_64|amd64)  export PKG_ARCH=amd64 ;;
      aarch64|arm64) export PKG_ARCH=arm64 ;;
      *) echo "unsupported arch $(uname -m)" >&2; exit 1 ;;
    esac
    mkdir -p dist
    for fmt in deb rpm apk archlinux; do nfpm package -f packaging/nfpm.yaml -p "$fmt" -t dist; done
    ls -1 dist

# Self-contained image bundling LLVM. Push manually when ready.
docker TAG="prism:dev":
    docker build -t "{{TAG}}" .

# One command: deb, rpm, apk, and the docker image for this host.
dist VERSION: (pkg VERSION)
    just docker "prism:{{VERSION}}"

smoke: build
    ./target/debug/prism run --examples

# Regenerate the committed Lean differential-oracle fixture manifest. This pins
# each source fixture, generated `core-json`, canonical Core hashes, and expected
# result without committing line-exploding JSON. CI diffs the regenerated TSV and
# fails on drift. Run after a change that shifts fixture source, emitted core, or
# model output, and commit the result (the `just hash` / `docs-gen` idiom).
fixtures: build
    cd models && ./gen_fixtures.sh

# accept the effect-lowering tier manifest (tests/tier_manifest.txt). Run after
# a reviewed tier improvement or a corpus change; the golden then diffs like a
# snapshot and CI fails on any un-accepted tier regression. Review the
# resulting diff before committing.
tier-accept:
    PRISM_ACCEPT_TIER_MANIFEST=1 cargo test --test native_perf tier_manifest_holds -- --nocapture

# Bless doctest expectations: rewrite every stale or empty inline `output` block
# with the example's actual output, in place, `ppx_expect` style. Point PATH at a
# project/dir/.pr file, or pass `--stdlib` for the embedded standard library
# (rebuild afterwards to pick the change up). Exits nonzero when anything is
# rewritten, so review the diff before committing; a clean run is already green.
bless PATH=".":
    cargo run -- docs {{PATH}} --test --accept

# Serve the determinism-scrubber page (opens /scrubber.html).
scrub: wasm
    cd web && pnpm install && pnpm gen-examples && pnpm exec vite --open /scrubber.html
