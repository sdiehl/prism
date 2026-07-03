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

test:
    cargo test --all

test-netlayer-fd:
    cargo test --no-default-features --test netlayer_fd -- --nocapture

parity:
    cargo test --test parity

perf:
    cargo test --test perf_gate

snapshots:
    cargo test --test snapshots

research-doctests:
    #!/usr/bin/env bash
    for f in docs/research/ocapn-actors/*.md; do \
        cargo run --quiet --bin doctest-run --no-default-features -- "$f"; \
    done

fmt:
    cargo fmt --all

fmt-check:
    cargo fmt --all --check

clippy:
    cargo clippy --all-targets -- -D warnings

# --- fast inner loop: filtered output, exit codes preserved ---

# Full test suite; print only summaries, failures, and compile errors.
t:
    #!/usr/bin/env bash
    set -o pipefail
    cargo test --all 2>&1 | grep -E "test result:|FAILED|error\[|error:|panicked|warning:"

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

# Format .pr files in place with the debug binary (whole tree if no args).
fmtw *FILES:
    cargo run --quiet -- fmt {{FILES}}

# Build, surfacing only errors and warnings (exit code preserved).
b:
    #!/usr/bin/env bash
    out=$(cargo build 2>&1); code=$?
    echo "$out" | grep -E "error|warning" || echo "build clean"
    exit $code

# Correctness gates to run before declaring done.
gate:
    #!/usr/bin/env bash
    set -o pipefail
    cargo test --test parity --test tier_parity --test perf_gate --test snapshots 2>&1 | grep -E "test result:|FAILED|error\["

fmt-examples: build-release
    ./target/release/prism fmt --check

ci: fmt-check clippy test fmt-examples

# Build the wasm playground bundle and sync it into the docs (docs/src/pkg), so
# the mdbook playground always runs the current compiler (no stale-bundle drift).
wasm:
    wasm-pack build --target web --out-dir web/pkg --no-default-features --features wasm
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

smoke: build
    # for f in examples/*.pr; do ./target/debug/prism run "$f" >/dev/null 2>&1 || echo "FAIL: $f"; done
    for f in examples/*.pr; do ./target/debug/prism run "$f" || echo "FAIL: $f"; done
