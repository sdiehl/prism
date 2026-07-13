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

# Default test runner: nextest, then doctests (nextest skips them).
test:
    PRISM_COMPILER_CACHE=0 cargo nextest run --all
    PRISM_COMPILER_CACHE=0 cargo test --doc

parity:
    PRISM_COMPILER_CACHE=0 cargo test --test native_parity parity::

perf:
    PRISM_COMPILER_CACHE=0 cargo test --test native_perf perf_gate::

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
    PRISM_COMPILER_CACHE=0 cargo nextest run --all
    PRISM_COMPILER_CACHE=0 cargo test --doc

# Run one test target or filter, filtered the same way. e.g. `just t1 fmt_records`
t1 FILTER:
    #!/usr/bin/env bash
    set -o pipefail
    PRISM_COMPILER_CACHE=0 cargo test {{FILTER}} 2>&1 | grep -E "test result:|FAILED|error\[|error:|panicked"

# Regenerate snapshots (optionally one FILTER), then show which changed.
snap FILTER="":
    #!/usr/bin/env bash
    PRISM_COMPILER_CACHE=0 INSTA_UPDATE=always cargo test {{FILTER}} 2>&1 | grep -E "test result:|error\[|error:" || true
    git status --short tests/snapshots || true

# Interactively accept/reject pending snapshot changes (needs cargo-insta).
review:
    cargo insta review

# Check the committed, byte-exact checked-HIR fixture boundary.
hir-check:
    PRISM_COMPILER_CACHE=0 cargo test --test compiler hir_fixture_goldens_hold

# Regenerate checked-HIR goldens after reviewing a checker-boundary change.
hir-accept:
    PRISM_COMPILER_CACHE=0 PRISM_ACCEPT_HIR_FIXTURES=1 cargo test --test compiler hir_fixture_goldens_hold
    git status --short tests/fixtures/hir || true

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

# Feature matrix, mirroring the CI matrix.
feature-matrix:
    cargo check --all-targets
    cargo check --no-default-features --features wasm --target wasm32-unknown-unknown
    cargo check --features mlir
    cargo check --features mimalloc

# Fail if tests mutated any committed file (surprise-drift guard).
no-drift:
    git diff --exit-code
    git diff --cached --exit-code

# Compile-time baselines over the pinned corpus. Extra criterion flags after `--`.
bench *ARGS:
    cargo bench --bench compile -- {{ARGS}}

# Compile one program to a native binary and run it (fast codegen smoke).
smoke1 FILE:
    #!/usr/bin/env bash
    set -euo pipefail
    bin="$(mktemp "${TMPDIR:-/tmp}/prism_smoke1.XXXXXX")"
    trap 'rm -f "$bin" "$bin".bc "$bin".ll' EXIT
    cargo run --quiet -- "{{FILE}}" -o "$bin"
    "$bin"

# The correctness oracles, filtered; one definition the gate recipes share (callers pass profile flags and inherit the env, e.g. PRISM_GATE_CACHE).
_gate *FLAGS:
    #!/usr/bin/env bash
    set -eo pipefail
    # Oracles compile from scratch; native_cache tests cache identity separately.
    export PRISM_COMPILER_CACHE=0
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

# The gate with the verdict cache on (keyed on the compiler binary); fall back to `just gate` after changing the cache fingerprint logic in tests/support/mod.rs.
gate-fast:
    @PRISM_GATE_CACHE=1 just _gate --release

# Fast development gate (debug profile): check + fmt + query-cache summary + snapshot/compiler oracles; a subset, never a substitute for `just gate`.
gate-dev:
    #!/usr/bin/env bash
    set -euo pipefail
    echo "gate-dev: development subset; 'just gate' stays the authoritative gate"
    cargo check --all-targets
    cargo fmt --all --check
    PRISM_COMPILER_STATS=1 cargo run --quiet -- check examples/accum.pr
    export PRISM_COMPILER_CACHE=0
    if command -v cargo-nextest >/dev/null; then
        cargo nextest run --profile ci --test snapshots --test compiler
    else
        cargo test --test snapshots --test compiler 2>&1 | grep -E "test result:|FAILED|error\["
    fi

# gate-dev plus a deterministic 1-in-8 native parity slice and a cache-explained native build; still not a substitute for `just gate`.
gate-dev-native: gate-dev
    #!/usr/bin/env bash
    set -euo pipefail
    bin="$(mktemp "${TMPDIR:-/tmp}/prism_gatedev.XXXXXX")"
    trap 'rm -f "$bin" "$bin".bc "$bin".ll' EXIT
    PRISM_COMPILER_STATS=1 PRISM_EXPLAIN_CACHE=1 cargo run --quiet -- examples/accum.pr -o "$bin"
    export PRISM_COMPILER_CACHE=0 PRISM_SHARD_TOTAL=8 PRISM_SHARD_INDEX=0
    if command -v cargo-nextest >/dev/null; then
        cargo nextest run --profile ci --test native_parity
    else
        cargo test --test native_parity 2>&1 | grep -E "test result:|FAILED|error\["
    fi

# Route `git diff --name-only REF` (plus untracked files) to the gates a change can affect; unknown paths escalate to the full gate.
gate-routed REF="HEAD":
    ./scripts/gate-route.sh --diff {{REF}}

fmt-examples: build-release
    ./target/release/prism fmt --check

package-world: build-release
    ./target/release/prism pkg check-world packages --strict

ci: fmt-check clippy stub-check doc-check feature-matrix test fmt-examples package-world

# CI-only checks mirrored locally: stub-marker grep + rustdoc deny-warnings.
stub-check:
    #!/usr/bin/env bash
    if grep -rEn 'todo!|unimplemented!|FIXME|XXX|allow\(dead_code\)' src bin; then
        echo "stub markers found (see above)"; exit 1
    fi

doc-check:
    RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --quiet

# Build the wasm playground bundle and sync it into docs/src/pkg; cdylib is requested here (not Cargo.toml) so native builds skip it, and wasm-bindgen CLI must match the crate.
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

# Regenerate the committed Standard Library Reference from lib/ `-- |` doc comments (CI checks it's current).
docs-gen:
    cargo build --release --features native
    ./target/release/prism docs --stdlib --out docs/src/stdlib
    ./target/release/prism docs --stdlib --test

# Regenerate the committed Core/lowered/fbip dumps behind the book figures from their `.pr` sources; rerun after a front-end change (ANF binder ids shift), idempotent.
docs-core:
    cargo build --release
    PRISM_BIN=target/release/prism bash docs/scripts/gen-core.sh

# Regenerate every content-addressed stdlib artifact after a hash-shifting change: the Merkle root and `#hash` badges (via docs-gen) plus the shape/type digest snapshots.
hash: docs-gen
    INSTA_UPDATE=always cargo test --test snapshots shape_digests

# Regenerate the stdlib reference and rebuild the wasm bundle first, so the book and served playground are never stale.
docs: docs-gen wasm
    mdbook build docs
    mdbook serve docs --open

# Cut a release: bump version, stamp changelog, tag, push (the Release workflow publishes the binary and bumps the Homebrew tap). Needs cargo-release.
release VERSION:
    cargo release {{VERSION}} --execute

# deb/rpm/apk for the host arch into dist/ (needs nfpm; use a Linux binary).
pkg VERSION: build-release
    #!/usr/bin/env bash
    set -euo pipefail
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

# Regenerate the committed Lean differential-oracle fixture manifest (pins fixtures, core-json, hashes, expected result); CI diffs it, rerun after a shift.
fixtures: build
    cd models && ./gen_fixtures.sh

# Accept the effect-lowering tier manifest after a reviewed tier improvement or corpus change; it then diffs like a snapshot. Review the diff before committing.
tier-accept:
    PRISM_ACCEPT_TIER_MANIFEST=1 cargo test --test native_perf tier_manifest_holds -- --nocapture

# Bless doctest expectations: rewrite stale/empty inline `output` blocks in place; PATH is a dir/.pr or `--stdlib`, exits nonzero when anything changed.
bless PATH=".":
    cargo run -- docs {{PATH}} --test --accept

# Serve the determinism-scrubber page (opens /scrubber.html).
scrub: wasm
    cd web && pnpm install && pnpm gen-examples && pnpm exec vite --open /scrubber.html
