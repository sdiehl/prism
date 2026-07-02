# Standard Library

Prism's standard library is ordinary Prism source, not compiler built-ins. The always-on prelude wires in the core types and the type-class tower and opens the `Data.*` modules with glob imports, so their names are in unqualified scope everywhere; `Replay` and `Concurrent` are brought in with an explicit `import`. The pages below are generated from the module sources by `prism docs`, with signatures taken from the typechecker.

<div class="stdlib-fingerprint">
<div class="stdlib-fp-head">Merkle root<span class="stdlib-fp-tag">prism-core-hash-v1</span></div>
<code class="stdlib-fp-root" data-copy="eb86899878ce7b9cc227af4bdbe7dc192574beaea2a4b0150bdf6fa547b43e5d" title="Click to copy">eb86899878ce7b9cc227af4bdbe7dc192574beaea2a4b0150bdf6fa547b43e5d</code>
<div class="stdlib-fp-foot">A content-addressed fingerprint of the entire standard library, compiled by Prism v0.5.0. Click the hash to copy.</div>
</div>

- [The Prelude](./prelude.md) - The always-on prelude: wired-in types, the type-class tower, core combinators, and the effect/loop machinery.
- [Data.List](./data-list.md) - Singly-linked list operations.
- [Data.Maybe](./data-maybe.md) - Operations over `Option(a)` (`None` / `Some(a)`).
- [Data.Result](./data-result.md) - Operations over `Result(a, e)` (`Ok(a)` / `Err(e)`).
- [Data.Map](./data-map.md) - Persistent ordered map: an AVL-balanced binary search tree over keys.
- [Data.Set](./data-set.md) - Ordered sets as `Map(k, Unit)`, reusing the balanced-tree map.
- [Data.Char](./data-char.md) - ASCII character classification.
- [Data.String](./data-string.md) - String operations, byte-oriented and ASCII-accurate.
- [Replay](./replay.md) - Record/replay handlers for the capability effects (Console, FileSystem, Random, Env).
- [Concurrent](./concurrent.md) - Cooperative async/await concurrency as a single handler, polymorphic in the effects the fibers perform.
