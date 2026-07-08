<p align="center">
  <img src="assets/prism.png" alt="Prism" width="180" height="180">
</p>

<h1 align="center">Prism</h1>

<p align="center">A small functional language with algebraic effects, multishot continuations, and native codegen.</p>

Prism is an impure functional programming language whose type system tracks side effects. Effect sets are inferred, extensible rows that compose through ordinary calls instead of monads, and they track observability rather than implementation: an effect handled inside a function vanishes from its type, so internally effectful code can still be analyzed, optimized, and reused as pure code. The language also has rank-N polymorphism, typeclasses, first-class lenses, fusing streams, deterministic reference counting, and native codegen through LLVM.

The compiler is built around deterministic simulation testing at the language level. Prism programs elaborate to a strict A-normal-form call-by-push-value core, definitions and packages are content-addressed by hash, project builds can explain their lineage, and suspended continuations carry the code identity they may resume against. The compiler also builds to WebAssembly, so the playground, REPL, and gallery run in the browser; the interpreter is a CEK machine modeled in Lean and serves as the differential oracle every native backend must match byte-for-byte.

Try it in the browser at the [Prism playground](https://sdiehl.github.io/prism/play/).

Read the [language specification](https://sdiehl.github.io/prism/spec.html) and the [compiler documentation](https://sdiehl.github.io/prism/compiler.html).

The [`examples/`](./examples) directory contains a tour of most advanced features, and see my [blog post](https://www.stephendiehl.com/posts/prism/) about the project design.

## Install

### Nix

```shell
nix build github:sdiehl/prism        # binary at ./result/bin/prism
nix run github:sdiehl/prism          # or run it directly
nix develop                          # dev shell: prism, LLVM, cargo, just on PATH
```

### Homebrew

```shell
brew install sdiehl/prism/prism
```

### Docker

```shell
docker run ghcr.io/sdiehl/prism --help
```

### Linux

```shell
# Debian / Ubuntu
curl -fsSL https://apt.llvm.org/llvm.sh | sudo bash -s 22
curl -LO https://github.com/sdiehl/prism/releases/download/v0.9.0/prism_0.9.0_amd64.deb
sudo apt install ./prism_0.9.0_amd64.deb

# Fedora / RHEL
sudo dnf install https://github.com/sdiehl/prism/releases/download/v0.9.0/prism-0.9.0-1.x86_64.rpm

# Arch
sudo pacman -U https://github.com/sdiehl/prism/releases/download/v0.9.0/prism-0.9.0-1-x86_64.pkg.tar.zst

# Alpine
curl -LO https://github.com/sdiehl/prism/releases/download/v0.9.0/prism_0.9.0_x86_64.apk
sudo apk add --allow-untrusted ./prism_0.9.0_x86_64.apk
```

Debian and Fedora can use the hosted repo instead, for `install prism` + upgrades:

```shell
# Debian / Ubuntu
echo 'deb [trusted=yes] https://apt.fury.io/sdiehl/ /' | sudo tee /etc/apt/sources.list.d/prism.list
sudo apt update && sudo apt install prism

# Fedora / RHEL
sudo tee /etc/yum.repos.d/prism.repo <<'EOF'
[prism]
baseurl=https://yum.fury.io/sdiehl/
enabled=1
gpgcheck=0
EOF
sudo dnf install prism
```

### From Source

You need the standard Rust toolchain installed. Native codegen also needs `clang` on `PATH` (override with `PRISM_CC`).

```shell
brew install llvm                    # macOS
sudo apt install llvm-22-dev         # Debian/Ubuntu

git clone https://github.com/sdiehl/prism.git
LLVM_SYS_221_PREFIX=$(brew --prefix llvm) cargo install --git https://github.com/sdiehl/prism
```

## Usage

```shell
prism                                # interactive shell
prism program.pr                     # compile to a native binary named `program`
prism program.pr -o out              # ...with a custom output path
prism program.pr -O2                 # ...at optimization level 2
prism run program.pr                 # interpret instead of compiling
prism build                          # compile the enclosing project (needs a prism.toml), into target/
prism clean                          # remove the project's target/ directory
prism check                          # type check the enclosing project
prism check program.pr               # type check one source file
prism pkg init                       # create a new package interactively
prism fmt program.pr                 # format source
prism dump core program.pr           # inspect a phase: tokens|ast|types|core|core-json|core-hash|native-kont-table|native-kont-state-map|fbip|llvm
```

## License

This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for details.
