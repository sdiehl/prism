# Standard Library

Prism's standard library is ordinary Prism source, not compiler built-ins. A small always-on prelude supplies the core types, the type-class tower, and the common data modules in unqualified scope; everything else is opt-in via explicit import. The pages below are generated from the module sources, with signatures taken from the typechecker.

## Merkle root

- **Scheme**: `prism-core-hash-v1`
- **Hash**: `b19c086306ab35f35445114d09249f5ec1907259e92ded3dfefece53dca24e83`
- **Compiler version**: Prism v0.7.0

## Modules

- [The Prelude](./prelude.md) - The always-on prelude: wired-in types, the type-class tower, core combinators, and the effect/loop machinery.
- [Data.List](./data-list.md) - Singly-linked list operations.
- [Data.Maybe](./data-maybe.md) - Operations over `Option`.
- [Data.Result](./data-result.md) - Operations over `Result`.
- [Data.Map](./data-map.md) - Persistent ordered map: an AVL-balanced binary search tree over keys.
- [Data.Set](./data-set.md) - Ordered sets, reusing the balanced-tree map.
- [Data.Ordered](./data-ordered.md) - Explicit ordering witnesses: the branded, statically coherent path to ordered maps.
- [Data.Char](./data-char.md) - ASCII character classification.
- [Data.String](./data-string.md) - String operations, byte-oriented and ASCII-accurate.
- [Data.Foldable](./data-foldable.md) - Generic operations over any `Foldable` container.
- [Data.Monad](./data-monad.md) - Generic operations derived from the `Applicative` and `Monad` classes.
- [Data.Checked](./data-checked.md) - Safe arithmetic families over the machine-integer lanes.
- [Data.Vec](./data-vec.md) - Fixed-length vectors indexed by a `Nat` dimension.
- [Replay](./replay.md) - Record/replay handlers for the capability effects.
- [Concurrent](./concurrent.md) - Cooperative async/await concurrency as a single handler, polymorphic in the effects the fibers perform.
- [Quickcheck](./quickcheck.md) - Property testing: run a boolean property over many generated inputs and report the first counterexample, deterministically.
- [Wire](./wire.md) - The opt-in serialization layer.
- [Data.Bytes](./data-bytes.md) - Byte strings: the `String`/`Bytes` boundary, and the hex and base64 codecs.
- [Incr](./incr.md) - Incremental computation as a handler over a content-addressed dependency graph.
- [Test](./test.md) - Per-type value generators for property testing.
- [Blit](./blit.md) - Range copy over the sequence types a real primitive can back.
- [Time](./time.md) - Time: instants, wall-clock timestamps, durations, and RFC 3339.
- [Json](./json.md) - JSON: a dynamic value tree, a total parser, a canonical encoder, and a typed layer.
- [Sequence](./sequence.md) - The one lazy iteration protocol: pull-based sequences with natural names.
- [Cli](./cli.md) - CLI: an applicative command-line parser as a first-class value.
