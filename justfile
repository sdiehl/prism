default:
    @just --list

build:
    cargo build

build-release:
    cargo build --release

run FILE:
    cargo run -- "{{FILE}}"

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
    bash scripts/gen-playground-examples.sh

web: wasm examples
    cd web && pnpm install && pnpm dev

web-build:
    cd web && pnpm install && pnpm lint && pnpm typecheck && pnpm build

smoke: build
    for f in examples/*.pr; do ./target/debug/prism "$f" >/dev/null 2>&1 || echo "FAIL: $f"; done
