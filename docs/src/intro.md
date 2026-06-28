<p align="center"><img src="prism.png" alt="Prism" width="256" height="256"></p>

# Prism

Prism is a small, strict, impure functional language in the ML family whose type system tracks side effects. Effects are inferred, extensible _rows_ that combine structurally as functions call one another, and they track observability: an effect handled inside a function vanishes from its type. The core is a call-by-push-value calculus in A-normal form that compiles to native code through LLVM, with memory managed by deterministic reference counting and fully-in-place update rather than a garbage collector.

This book has two parts:

- **[Language Specification](./spec.md)** defines the surface language: lexical structure, grammar, types, effects, and evaluation.
- **[Compiler](./compiler.md)** documents the implementation: the pipeline, the core calculus, effect lowering, reference counting, the backends, and the verification harness.

Use the **[Playground](https://sdiehl.github.io/prism/play/)** to edit, run, and inspect Prism code via an interpreter run in the browser.
