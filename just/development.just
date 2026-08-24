# Build the debug binary.
[group('build')]
build:
    cargo build

# Build the optimized binary.
[group('build')]
build-release:
    cargo build --release

# Run the Prism CLI through Cargo.
[group('build')]
prism *ARGS:
    cargo run -- {{ ARGS }}

# Run a Prism source file.
[group('build')]
run FILE:
    cargo run -- run "{{ FILE }}"

# Check a Prism source file.
[group('build')]
check FILE:
    cargo run -- check "{{ FILE }}"

# Run the Prism-written checker from live compiler-owned package sources. The
# release binary avoids making workbench execution pay debug-interpreter cost.
[group('development')]
tc +FILES: build-release
    PRISM_TOOL_PACKAGES_ROOT=packages ./target/release/prism bootstrap check {{ FILES }} --json

# Run the full test suite with compact output; deep-recursion tests need the
# same enlarged libtest stack the ci test recipe sets.
[group('development')]
t:
    RUST_MIN_STACK=33554432 PRISM_COMPILER_CACHE=0 cargo nextest run --all
    PRISM_COMPILER_CACHE=0 cargo test --workspace --doc

# Run one test target or filter with compact output.
[group('development')]
t1 FILTER:
    python3 scripts/dev_tasks.py test "{{ FILTER }}"

# Regenerate snapshots, optionally matching FILTER.
[group('development')]
snap FILTER="":
    python3 scripts/dev_tasks.py snapshots "{{ FILTER }}"

# Review pending snapshots interactively.
[group('development')]
review:
    cargo insta review

# Check the byte-exact checked-HIR fixtures.
[group('development')]
hir-check:
    PRISM_COMPILER_CACHE=0 cargo test --test compiler hir_fixture_goldens_hold

# Accept reviewed checked-HIR fixture changes.
[group('development')]
hir-accept:
    PRISM_COMPILER_CACHE=0 PRISM_ACCEPT_HIR_FIXTURES=1 cargo test --test compiler hir_fixture_goldens_hold
    git status --short tests/fixtures/hir

# Format Prism source files in place; defaults to the whole tree.
[group('development')]
fmtw *FILES:
    cargo run --quiet -- fmt {{ FILES }}

# Build and show diagnostics only.
[group('development')]
b:
    python3 scripts/dev_tasks.py build

# Check all targets and show diagnostics only.
[group('development')]
c:
    python3 scripts/dev_tasks.py check all

# Check the compiler middle end and show diagnostics only.
[group('development')]
ccore:
    python3 scripts/dev_tasks.py check core

# Check surface syntax and show diagnostics only.
[group('development')]
csyn:
    python3 scripts/dev_tasks.py check syntax

# Run compile-time benchmarks; pass Criterion flags after `--`.
[group('benchmarks')]
bench *ARGS:
    cargo bench --bench compile -- {{ ARGS }}

# Measure Prism lexer throughput and peak memory.
[group('benchmarks')]
lexperf *ARGS: build-release
    ./scripts/lexperf.py {{ ARGS }}

# Compile and run one source file as a native-code smoke test.
[group('development')]
smoke1 FILE:
    python3 scripts/dev_tasks.py smoke "{{ FILE }}"

# Run every example with the debug binary.
[group('development')]
smoke: build
    ./target/debug/prism run --examples
