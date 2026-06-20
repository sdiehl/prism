# Changelog

## 0.1.0

Initial release.

- Strict, impure functional language with ML-family surface syntax: ADTs, pattern matching, parametric polymorphism, and a prelude of `Option`/`Result`/`List`/`Map` combinators.
- Hindley-Milner type inference with bidirectional, higher-rank (rank-N) checking and subsumption.
- Type classes by dictionary passing, with named instances and `deriving (Eq, Ord, Show)`.
- Algebraic effects and handlers: inferred, extensible effect rows via row polymorphism; multishot `resume`; `final ctl` non-resumable clauses; scoped/masked handlers and forwarding.
- Evidence-passing compilation of handlers, with tail-resumptive clauses lowered to direct calls and a free-monad fallback when effects escape tracking.
- Exhaustiveness and redundancy checking, plus decision-tree pattern-match compilation.
- First-class optics: record-update paths, view patterns, bidirectional pattern synonyms, and `deriving (Lens)`.
- Stream fusion: effectful producer/transformer/consumer pipelines fuse to zero intermediate allocations.
- Verse-inspired failure model (`fail`, `guard`, `??`, `?.`, `transact`) and structured error handling, both built on effect handlers.
- Deterministic memory management via Perceus reference counting with in-place reuse (FBIP), no garbage collector.
- Call-by-push-value core in A-normal form with tail-call optimization and tail recursion modulo cons.
- Three backends kept byte-identical: a tree-walking interpreter, native code via LLVM, and a text-MLIR backend.
- Lean model of the core with a machine-checked determinism theorem.
- Compiles to WebAssembly, so the language runs in the browser.
- Tooling: interactive shell, `run`, `build`, `check`, `fmt`, and phase `dump`.
