# The gauntlet

Prism's test suite (or what I lovingly call "The Gauntlet") is intentionally quite extreme. It enforces byte-for-byte compiler and runtime agreement across many layers.

- **[Native parity](native_parity.rs): Matches interpreter and native behavior byte for byte across the corpus.**
- **[Native tiers](native_tier.rs): Makes every effect-lowering tier agree exactly.**
- **[Typed Core spine](typed_spine.rs): Demands exact Core identity across typed erasure boundaries.**
- **[Compiler](compiler.rs): Checks compiler internals and byte-identical cold, warm, and incremental builds.**
- **[Language](language.rs): Probes the type, effect, module, and soundness rules.**
- **[Lineage](lineage_suite.rs): Keeps provenance verifiable and byte-identical across repeated runs.**
- **[Native cache](native_cache.rs): Demands byte-identical cold and cached native artifacts.**
- **[Runtime](runtime.rs): Checks byte-for-byte replay, suspension, scheduling, and recovery.**
- **[Snapshots](snapshots.rs): Byte-for-byte golden gates for compiler phases and program output.**
- **[Standard-library hash](stdlib_hash.rs): Pins the standard library to one reproducible semantic root.**
- [Bootstrap](bootstrap.rs): Checks the Prism-written checker against authoritative Rust facts and reports honest coverage.
- [CLI and docs](cli_docs.rs): Keeps examples, projects, docs, and CLI output honest.
- [Contracts](contracts.rs): Keeps logical contracts checked, deterministic, and erased from executable Core.
- [Determinism](determinism.rs): Makes canonical hashes independent of compilation history and scheduling.
- [Durable driver](durable_driver.rs): Crashes and resumes persisted runs without changing their observation trace.
- [Environment knobs](env_knobs.rs): Keeps every `PRISM_*` read in its documented ownership boundary.
- [Error codes](error_codes.rs) and [explain coverage](explain_coverage.rs): Keep diagnostic identities unique and every public code explained.
- [Formatter](formatter.rs): Preserves syntax and comments through formatting.
- [Typed holes](holes.rs) and [type queries](type_query.rs): Exercise reporting, filling, search, and bounded rechecked synthesis through the real CLI.
- [ISA fixture](isa_fixture.rs): Compiles a tiny out-of-tree backend against the public shared-emitter API.
- [Lean fuzz](lean_fuzz.rs): Feeds deterministic generated Core through both the Rust interpreter and Lean CEK oracle.
- [Native conformance](native_conformance.rs): Matches native float behavior to the interpreter.
- [Native fusion](native_fusion.rs): Checks deterministic fusion without semantic drift.
- [Native performance](native_perf.rs): Guards allocation, stack, fusion, and complexity budgets.
- [Native sorting](native_sort.rs): Matches native sorting to the interpreter.
- [Optimizer equivalence](opt_equiv.rs): Forces optimizer configurations over the corpus and requires identical observation traces.
- [Packages and certificates](package.rs): Covers package trust, transport, locking, and certificates.
- [`prism test`](prism_test.rs): Covers discovery, filtering, isolation, capture, manifests, and production neutrality.
- [Semantic patches](semantic_patch.rs): Keeps patches atomic, reproducible, and behavior-checked.
- [Stable locks](stable_lock.rs): Pins migration edges and routes to their content-addressed behavior.
- [Store and package coherence](store_pkg.rs): Tests store immutability, concurrency, hashes, and coherence.
- [Totality](totality.rs): Checks structural termination evidence, assumptions, ranking obligations, and Core erasure.
- [Duplicate warnings](warn_dupes.rs): Checks clone warnings and their severity modes.

One more core gate lives outside this directory: the [Lean 4 differential-oracle runner](../models/diff_against_rust.sh) has the Rust compiler dump its live Core as JSON, feeds that same dump to the verified Lean CEK machine, and requires the Rust and Lean results to agree exactly. The [formal model](../models/README.md) also proves properties of that CEK machine, including determinism, replay faithfulness, and correspondence with the big-step semantics. The companion replayable fuzz gate generates deterministic random source programs, feeds their compiled Core to both implementations, and shrinks any disagreement to a minimal oracle-tested reproducer.
