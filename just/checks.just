# Run nextest and doctests; debug Core lint needs a larger libtest stack.
[group('tests')]
test:
    RUST_MIN_STACK=33554432 PRISM_COMPILER_CACHE=0 cargo nextest run --all
    PRISM_COMPILER_CACHE=0 cargo test --workspace --doc

# Run the native parity tests.
[group('tests')]
parity:
    PRISM_COMPILER_CACHE=0 cargo test --test native_parity parity::

# Compare the corpus across all optimizer configurations.
[group('tests')]
opt-equiv *FLAGS:
    PRISM_COMPILER_CACHE=0 PRISM_CORE_LINT=1 PRISM_QUIET=1 cargo test {{ FLAGS }} --test opt_equiv gate::optimizer_configurations_have_identical_observation_traces -- --exact

# Run native performance gates.
[group('tests')]
perf:
    PRISM_COMPILER_CACHE=0 cargo test --test native_perf perf_gate::

# Run snapshot tests.
[group('tests')]
snapshots:
    cargo test --test snapshots

# Format Rust sources.
[group('quality')]
fmt:
    cargo fmt --all
    python3 scripts/dev_tasks.py format-justfiles

# Check Rust formatting.
[group('quality')]
fmt-check:
    cargo fmt --all --check
    python3 scripts/dev_tasks.py format-justfiles --check

# Lint the workspace with warnings denied.
[group('quality')]
clippy:
    cargo clippy --workspace --all-targets -- -D warnings

# Check native, wasm, MLIR, and mimalloc configurations.
[group('quality')]
feature-matrix:
    cargo check --all-targets
    cargo check --no-default-features --features wasm --target wasm32-unknown-unknown
    # cargo check omits cfg(test), so compile the wasm lib test harness too.
    cargo test --no-default-features --features wasm --target wasm32-unknown-unknown --lib --no-run
    cargo check --features mlir
    cargo check --features mimalloc

# Fail when tracked files changed during a test run.
[group('quality')]
no-drift:
    git diff --exit-code
    git diff --cached --exit-code

[private]
_gate *FLAGS:
    python3 scripts/gate.py oracles {{ FLAGS }}

# Run the authoritative release-profile correctness gate.
[group('gates')]
gate:
    @just _gate --release
    @just opt-equiv --release

# Run the correctness gate in the debug profile.
[group('gates')]
gate-debug:
    @just _gate

# Run the cached release gate; use gate after cache-fingerprint changes.
[group('gates')]
gate-fast:
    @PRISM_GATE_CACHE=1 just _gate --release

# Run the fast development subset of the correctness gate.
[group('gates')]
gate-dev:
    python3 scripts/gate.py development

# Add a deterministic native parity slice to gate-dev.
[group('gates')]
gate-dev-native: gate-dev
    python3 scripts/gate.py native-slice

# Choose gates from changed paths; unknown paths use the full gate.
[group('gates')]
gate-routed REF="HEAD":
    ./scripts/gate-route.sh --diff "{{ REF }}"

# Check formatting of every Prism example.
[group('quality')]
fmt-examples: build-release
    ./target/release/prism fmt --check

# Strictly validate the package world.
[group('quality')]
package-world: build-release
    ./target/release/prism pkg check-world packages --strict

# Mirror the complete CI check set locally.
[group('gates')]
ci: fmt-check clippy stub-check doc-check feature-matrix test fmt-examples package-world artifacts-check

# Reject placeholder markers in production sources.
[group('quality')]
stub-check:
    python3 scripts/check_stubs.py

# Build workspace documentation with warnings denied.
[group('quality')]
doc-check:
    RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --workspace --quiet
