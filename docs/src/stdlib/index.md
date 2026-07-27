# Standard Library

Prism's standard library is ordinary Prism source, not compiler built-ins. A small always-on Base supplies the core types, the type-class tower, and the common data modules in unqualified scope; everything else is opt-in via explicit import. The pages below are generated from the module sources, with signatures taken from the typechecker.

## Merkle root

- **Scheme**: `prism-core-hash-v1`
- **Hash**: `fa9b26b325586f03a015c0b171e8b665a45821f42a0ba0b58fc6c1304929eb20`
- **Compiler version**: Prism v0.15.0

## Modules

- [Base](./base.md) - Base, the always-on surface: wired-in types, the type-class tower, core combinators, and the effect/loop machinery.
- [Control.Fresh](./control-fresh.md) - The `Fresh` effect: a deterministic monotonic name supply (gensym).
- [Control.Layer](./control-layer.md) - The children-and-rebuild interface a generic traversal runs on, and the collecting queries that ride it.
- [Control.Reader](./control-reader.md) - The canonical `Reader(r)` effect: a read-only ambient environment.
- [Control.Rewrite](./control-rewrite.md) - Strategy combinators: a pass as a composition of small local rules instead of a hand-written recursive match.
- [Control.State](./control-state.md) - The canonical `State(s)` effect: a threaded piece of mutable-looking state, interpreted by parameter passing.
- [Control.Validate](./control-validate.md) - Validation as an algebraic effect.
- [Control.Writer](./control-writer.md) - The canonical `Writer(w)` effect: accumulate output on the side.
- [Data.Bind](./data-bind.md) - Binders, the two nameless coordinate systems, and the canonical rendering that makes alpha-equivalent terms identical.
- [Data.Bytes](./data-bytes.md) - Byte strings: the `String`/`Bytes` boundary, and the hex and base64 codecs.
- [Data.Char](./data-char.md) - ASCII character classification.
- [Data.Checked](./data-checked.md) - Safe arithmetic families over the machine-integer lanes.
- [Data.Fixpoint](./data-fixpoint.md) - Least fixed points over a join-semilattice, solved by worklist.
- [Data.FlatArray](./data-flatarray.md) - Flat, unboxed-element arrays: one typed surface over the raw-word buffers.
- [Data.Foldable](./data-foldable.md) - Generic operations over any `Foldable` container.
- [Data.Frozen](./data-frozen.md) - Frozen arrays: the immutable array representation.
- [Data.Graph](./data-graph.md) - Directed graphs over an ordered node type, with the deterministic algorithms the compiler relies on internally, mirrored into Prism.
- [Data.IntMap](./data-intmap.md) - Persistent integer-keyed map: a big-endian patricia trie over 64-bit keys.
- [Data.IntSet](./data-intset.md) - Sets of 64-bit integers, reusing the patricia trie.
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
- [Syntax.Analysis](./syntax-analysis.md) - Analysis walks over the surface syntax tree.
- [Syntax.Ast](./syntax-ast.md) - The typed surface syntax that the `prism-surface-syntax-v1` artifact decodes into. Constructor prefixes name the family (`I` items, `E` expressions, `P` patterns, `Ty` types), and spanned nodes wrap in `Sp`. The shapes mirror the compiler's exporter exactly, so a decoded document re-encodes to identical bytes.
- [Syntax.Codec](./syntax-codec.md) - Codecs for the versioned syntax artifacts. Decoding turns the compiler's exports into the typed `Syntax` vocabularies, rejecting wrong schema tags, malformed shapes, and spans that invert or reach past the embedded source with one structured error; encoding is the exact inverse, re-emitting identical bytes.
- [Syntax.Cursor](./syntax-cursor.md) - The mechanical half of recursive descent: a token cursor with peek, advance, and expect, and a Pratt driver over a binding-power table.
- [Syntax.Diagnostic](./syntax-diagnostic.md) - The typed vocabulary of the `prism-syntax-diagnostics-v1` artifact.
- [Syntax.Edit](./syntax-edit.md) - Span-addressed source edits that refuse rather than corrupt.
- [Syntax.Flow](./syntax-flow.md) - Call-graph flow over a resolved document: occurrence analysis and liveness as one fixpoint.
- [Syntax.Identity](./syntax-identity.md) - The identities a Prism source file carries, and the two of them a published artifact is enough to compute.
- [Syntax.Layout](./syntax-layout.md) - The Prism-language reimplementation of the compiler's layout pass: the offside rule that turns the raw token stream into the post-layout `parse` stream by splicing the virtual block delimiters `VOpen`/`VClose`/`VSemi` and by opening a bare-indent body after each `class`/`instance`/`effect` head. The Rust `lex` pipeline stays the authoritative oracle; this module reproduces its output so the two can be diffed, never used as a silent fallback.
- [Syntax.Lex](./syntax-lex.md) - A Prism-language reimplementation of the compiler's raw token layer: exact UTF-8 tokenization, literal payload decoding, and interpolation splitting, expressed as ordinary Prism. The Rust `lex_raw` pipeline remains the authoritative oracle; this module produces the same raw token stream (kind, byte span, and decoded value) and the same interleaved trivia (line comments and blank-line runs) so the two can be diffed. It is compared and reported, never used as a silent fallback.
- [Syntax.Query](./syntax-query.md) - A source query over a decoded `prism-syntax-tokens-v1` artifact.
- [Syntax.Rename](./syntax-rename.md) - Rename as a join against the resolver, not as a tree walk.
- [Syntax.Report](./syntax-report.md) - Caret rendering for `Syntax.Diagnostic`: the plain-text report the compiler prints for a refused source, rebuilt in Prism from the diagnostic and the source text alone.
- [Syntax.Resolved](./syntax-resolved.md) - The typed vocabulary of the `prism-resolved-syntax-v1` artifact.
- [Syntax.Source](./syntax-source.md) - Source identity for the versioned syntax artifacts: source files and half-open byte spans. Byte offsets are the canonical position vocabulary (line and column are projections for people, never a second identity), and these are the Prism-side types the token and surface-syntax exports decode into.
- [Syntax.Token](./syntax-token.md) - The token vocabulary of the `prism-syntax-tokens-v1` artifact. A fixed token's wire kind is its source spelling, so `TFixed` carries the spelling rather than enumerating every keyword and operator; value-carrying and virtual layout tokens each get a dedicated constructor matching the grammar's terminal aliases.
- [Syntax.Walk](./syntax-walk.md) - Generic traversal over the surface syntax tree.
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
