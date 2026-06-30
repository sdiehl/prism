<p align="center">
  <img src="assets/prism.png" alt="Prism" width="180" height="180">
</p>

<h1 align="center">Prism</h1>

<p align="center">A small functional language with algebraic effects, multishot continuations, and native codegen.</p>

Prism is an impure functional programming language whose type system tracks side effects. Effect sets are inferred and extensible, combining structurally as functions call one another via row polymorphism instead of monads. They track observability rather than implementation: so an effect handled inside a function vanishes from its type, thus code that mutates locals or throws internally is analyzed, optimized, and reused as pure code. The type system also has rank-N polymorphism, typeclasses, and first-class lenses and streams integrated into the language. The core is strict and elaborates to an A-normal-form call-by-push-value calculus where evaluation order is explicit, then compiles to native code through LLVM. Memory is managed by deterministic reference counting instead of a garbage collector. The compiler itself (written in Rust until bootstrapped) also compiles to WebAssembly, so the whole language runs in the browser. The interpreter is a CEK machine modeled in Lean and proved correct against its big-step semantics, and it serves in turn as the differential oracle every native backend must match byte-for-byte.

Try it in the browser at the [Prism playground](https://sdiehl.github.io/prism/play/).

Read the [language specification](https://sdiehl.github.io/prism/spec.html) and the [compiler documentation](https://sdiehl.github.io/prism/compiler.html).

The [`examples/`](./examples) directory contains a tour of most advanced features, and see my [blog post](https://www.stephendiehl.com/posts/prism/) about the project design.

## Install

On Apple Silicon, the Homebrew tap installs the prebuilt binary and pulls in LLVM 22:

```shell
brew install sdiehl/prism/prism
```

To build from source on any platform, the LLVM 22 dev libraries must be present, since the compiler links against them:

```shell
brew install llvm                    # macOS
sudo apt install llvm-22-dev         # Debian/Ubuntu
```

Then build with:

```shell
LLVM_SYS_221_PREFIX=$(brew --prefix llvm) cargo install --git https://github.com/sdiehl/prism
```

This builds the `prism` binary. Native compilation also needs `clang` on `$PATH` (override with `PRISM_CC`).

```shell
prism                                # interactive shell
prism program.pr                     # compile to a native binary named `program`
prism program.pr -o out              # ...with a custom output path
prism program.pr -O2                  # ...at optimization level 2 (default is -O1)
prism run program.pr                 # interpret instead of compiling
prism build                          # compile the enclosing project (needs a prism.toml), into target/
prism clean                          # remove the project's target/ directory
prism check program.pr               # type check only
prism fmt program.pr                 # format source
prism dump core program.pr           # inspect a phase: tokens|ast|types|core|core-json|core-hash|fbip|llvm
```

## License

This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for details.
