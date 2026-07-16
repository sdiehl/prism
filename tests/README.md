# The gauntlet

Prism's test suite (or what I lovingly call "The Gauntlet") is intentionally quite extreme. It enforces byte-for-byte compiler and runtime agreement across many layers.

- **[Native parity](native_parity.rs) — Matches interpreter and native behavior byte for byte across the corpus.**
- **[Native tiers](native_tier.rs) — Makes every effect-lowering tier agree exactly.**
- **[Typed Core spine](typed_spine.rs) — Demands exact Core identity across typed erasure boundaries.**
- **[Compiler](compiler.rs) — Checks compiler internals and byte-identical cold, warm, and incremental builds.**
- **[Language](language.rs) — Probes the type, effect, module, and soundness rules.**
- **[Lineage](lineage_suite.rs) — Keeps provenance verifiable and byte-identical across repeated runs.**
- **[Native cache](native_cache.rs) — Demands byte-identical cold and cached native artifacts.**
- **[Runtime](runtime.rs) — Checks byte-for-byte replay, suspension, scheduling, and recovery.**
- **[Snapshots](snapshots.rs) — Byte-for-byte golden gates for compiler phases and program output.**
- **[Standard-library hash](stdlib_hash.rs) — Pins the standard library to one reproducible semantic root.**
- [CLI and docs](cli_docs.rs) — Keeps examples, projects, docs, and CLI output honest.
- [Formatter](formatter.rs) — Preserves syntax and comments through formatting.
- [Native conformance](native_conformance.rs) — Matches native float behavior to the interpreter.
- [Native fusion](native_fusion.rs) — Checks deterministic fusion without semantic drift.
- [Native performance](native_perf.rs) — Guards allocation, stack, fusion, and complexity budgets.
- [Native sorting](native_sort.rs) — Matches native sorting to the interpreter.
- [Packages and certificates](package.rs) — Covers package trust, transport, locking, and certificates.
- [Semantic patches](semantic_patch.rs) — Keeps patches atomic, reproducible, and behavior-checked.
- [Store and package coherence](store_pkg.rs) — Tests store immutability, concurrency, hashes, and coherence.
- [Duplicate warnings](warn_dupes.rs) — Checks clone warnings and their severity modes.

One more core gate lives outside this directory: the [Lean 4 differential-oracle runner](../models/diff_against_rust.sh) has the Rust compiler dump its live Core as JSON, feeds that same dump to the verified Lean CEK machine, and requires the Rust and Lean results to agree exactly. The [formal model](../models/README.md) also proves properties of that CEK machine, including determinism, replay faithfulness, and correspondence with the big-step semantics. The companion replayable fuzz gate generates deterministic random source programs, feeds their compiled Core to both implementations, and shrinks any disagreement to a minimal oracle-tested reproducer.
