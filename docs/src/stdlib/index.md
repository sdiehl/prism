# Standard Library

Prism's standard library is ordinary Prism source, not compiler built-ins. A small always-on Base supplies the core types, the type-class tower, and the common data modules in unqualified scope; everything else is opt-in via explicit import. The pages below are generated from the module sources, with signatures taken from the typechecker.

## Merkle root

- **Scheme**: `prism-core-hash-v1`
- **Hash**: `e8dbdf5053501277950df8c8c0b0ad6934f02ce2bcb0ff93d75a54e770f9252e`
- **Compiler version**: Prism v0.13.0

## Modules

- [Base](./base.md) - Base, the always-on surface: wired-in types, the type-class tower, core combinators, and the effect/loop machinery.
- [Control.Fresh](./control-fresh.md) - The `Fresh` effect: a deterministic monotonic name supply (gensym).
- [Control.Reader](./control-reader.md) - The canonical `Reader(r)` effect: a read-only ambient environment.
- [Control.State](./control-state.md) - The canonical `State(s)` effect: a threaded piece of mutable-looking state, interpreted by parameter passing.
- [Control.Writer](./control-writer.md) - The canonical `Writer(w)` effect: accumulate output on the side.
- [Data.Bytes](./data-bytes.md) - Byte strings: the `String`/`Bytes` boundary, and the hex and base64 codecs.
- [Data.Char](./data-char.md) - ASCII character classification.
- [Data.Checked](./data-checked.md) - Safe arithmetic families over the machine-integer lanes.
- [Data.FlatArray](./data-flatarray.md) - Flat, unboxed-element arrays: one typed surface over the raw-word buffers.
- [Data.Foldable](./data-foldable.md) - Generic operations over any `Foldable` container.
- [Data.Graph](./data-graph.md) - Directed graphs over an ordered node type, with the deterministic algorithms the compiler relies on internally, mirrored into Prism.
- [Data.List](./data-list.md) - Singly-linked list operations.
- [Data.Map](./data-map.md) - Persistent ordered map: an AVL-balanced binary search tree over keys.
- [Data.Maybe](./data-maybe.md) - Operations over `Option`.
- [Data.Monad](./data-monad.md) - Generic operations derived from the `Applicative` and `Monad` classes.
- [Data.Ordered](./data-ordered.md) - Explicit ordering witnesses: the branded, statically coherent path to ordered maps.
- [Data.Pretty](./data-pretty.md) - A Leijen-style pretty printer. Build a layout-independent `Doc` from the combinators below, then `render` it to a string at a chosen page width.
- [Data.Result](./data-result.md) - Operations over `Result`.
- [Data.Set](./data-set.md) - Ordered sets, reusing the balanced-tree map.
- [Data.String](./data-string.md) - String operations, byte-oriented and ASCII-accurate.
- [Data.Tensor](./data-tensor.md) - Dense multi-dimensional tensors over a flat `FloatBuf`.
- [Data.UnionFind](./data-unionfind.md) - A persistent union-find (disjoint-set) over an ordered key type.
- [Data.Validation](./data-validation.md) - `Validation`, the error-accumulating sibling of `Result`.
- [Data.Vec](./data-vec.md) - Fixed-length vectors indexed by a `Nat` dimension.
- [Arena](./arena.md) - Arena: allocation as an algebraic effect.
- [Blit](./blit.md) - Range copy over the sequence types a real primitive can back.
- [Cli](./cli.md) - CLI: an applicative command-line parser as a first-class value.
- [Concurrent](./concurrent.md) - Cooperative async/await concurrency as a single handler, polymorphic in the effects the fibers perform.
- [Incr](./incr.md) - Incremental computation as a handler over a content-addressed dependency graph.
- [Json](./json.md) - JSON: a dynamic value tree, a total parser, a canonical encoder, and a typed layer.
- [Math](./math.md) - Named mathematical constants, matching Rust's `f64::consts` surface.
- [Quickcheck](./quickcheck.md) - Property testing: run a boolean property over many generated inputs and report the first counterexample, deterministically.
- [Replay](./replay.md) - Record/replay handlers for the capability effects.
- [Sequence](./sequence.md) - The one lazy iteration protocol: pull-based sequences with natural names.
- [Teleport](./teleport.md) - The checked mobility boundary. `teleport` runs a portable, single-use computation as a unit that is safe to move to a fresh runtime.
- [Test](./test.md) - Per-type value generators for property testing.
- [Time](./time.md) - Time: instants, wall-clock timestamps, durations, and RFC 3339.
- [Wire](./wire.md) - The opt-in serialization layer.
