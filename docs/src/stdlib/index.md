# Standard Library

Prism's standard library is ordinary Prism source, not compiler built-ins. A small always-on prelude supplies the core types, the type-class tower, and the common data modules in unqualified scope; everything else is opt-in via explicit import. The pages below are generated from the module sources, with signatures taken from the typechecker.

## Merkle root

- **Scheme**: `prism-core-hash-v1`
- **Hash**: `9dc9d52757d07c2af58ec73458fc65b4eaa0eb848747497eb6adb10bf1059b7d`
- **Compiler version**: Prism v0.6.0

## Modules

- [The Prelude](./prelude.md) - The always-on prelude: wired-in types, the type-class tower, core combinators, and the effect/loop machinery.
- [Data.List](./data-list.md) - Singly-linked list operations.
- [Data.Maybe](./data-maybe.md) - Operations over `Option`.
- [Data.Result](./data-result.md) - Operations over `Result`.
- [Data.Map](./data-map.md) - Persistent ordered map: an AVL-balanced binary search tree over keys.
- [Data.Set](./data-set.md) - Ordered sets, reusing the balanced-tree map.
- [Data.Char](./data-char.md) - ASCII character classification.
- [Data.String](./data-string.md) - String operations, byte-oriented and ASCII-accurate.
- [Replay](./replay.md) - Record/replay handlers for the capability effects.
- [Concurrent](./concurrent.md) - Cooperative async/await concurrency as a single handler, polymorphic in the effects the fibers perform.
- [Quickcheck](./quickcheck.md) - Property testing: run a boolean property over many generated inputs and report the first counterexample, deterministically.
- [Wire](./wire.md) - The opt-in serialization layer.
- [Incr](./incr.md) - Incremental computation as a handler over a content-addressed dependency graph.
- [Test](./test.md) - Per-type value generators for property testing.
- [Blit](./blit.md) - Range copy over the sequence types a real primitive can back.
