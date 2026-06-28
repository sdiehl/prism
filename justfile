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

parity:
    cargo test --test parity

perf:
    cargo test --test perf_gate

snapshots:
    cargo test --test snapshots

fmt:
    cargo fmt --all

fmt-check:
    cargo fmt --all --check

clippy:
    cargo clippy --all-targets -- -D warnings

fmt-examples: build-release
    ./target/release/prism fmt --check

ci: fmt-check clippy test fmt-examples

wasm:
    wasm-pack build --target web --out-dir web/pkg --no-default-features --features wasm

examples:
    cd web && pnpm gen-examples

web: wasm
    cd web && pnpm install && pnpm dev

web-build:
    cd web && pnpm install && pnpm lint && pnpm typecheck && pnpm build

docs:
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
