<p align="center">
  <img src="assets/prism.png" alt="Prism" width="180" height="180">
</p>

<h1 align="center">Prism</h1>

<p align="center">A small functional language with algebraic effects, multishot continuations, and native codegen.</p>

Prism is an impure functional programming language whose type system tracks side effects. Effect sets are inferred and extensible, combining structurally as functions call one another via row polymorphism instead of monads. They track observability rather than implementation: so an effect handled inside a function vanishes from its type, thus code that mutates locals or throws internally is analyzed, optimized, and reused as pure code. The type system also has rank-N polymorphism, typeclasses, and first-class lenses and streams integrated into the language. The core is strict and elaborates to an A-normal-form call-by-push-value calculus where evaluation order is explicit, then compiles to native code through LLVM. Memory is managed by deterministic reference counting instead of a garbage collector. The compiler itself (written in Rust until bootstrapped) also compiles to WebAssembly, so the whole language runs in the browser. The interpreter serves as a differential oracle every backend must match byte-for-byte, and a subset of the core calculus is modeled in Lean.

The [`examples/`](./examples) directory contains a tour of most advanced features.

Try it in the browser at the [Prism playground](https://sdiehl.github.io/prism/).

## Install

The compiler links against LLVM 22, so the dev libraries must be present:

```shell
brew install llvm                    # macOS
sudo apt install llvm-22-dev         # Debian/Ubuntu
```

Then build with:

```shell
LLVM_SYS_221_PREFIX=$(brew --prefix llvm) cargo install --git https://github.com/sdiehl/tiny-prism
```

This builds the `prism` binary. Native compilation also needs `clang` on `$PATH` (override with `PRISM_CC`).

```shell
prism                                # interactive shell
prism run program.pr                 # interpret
prism build program.pr -o program    # compile to a native binary
prism check program.pr               # type check only
prism fmt program.pr                 # format source
prism dump core program.pr           # inspect a phase: tokens|ast|types|core|fbip|llvm
```

## License

This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for details.
