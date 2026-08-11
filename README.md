<p align="center">
  <img src="assets/prism.png" alt="Prism" width="180" height="180">
</p>

<h1 align="center">Prism</h1>

<p align="center">A small functional language with algebraic effects, multishot continuations, and native codegen.</p>

Prism is an impure functional programming language whose type system tracks side effects. Effect sets are inferred, extensible rows that compose through ordinary calls instead of monads, and they track observability rather than implementation: an effect handled inside a function vanishes from its type, so internally effectful code can still be analyzed, optimized, and reused as pure code. The language also has rank-N polymorphism, typeclasses, derived lenses and optic paths, fusing streams, deterministic reference counting, and native codegen through LLVM, with an optional textual MLIR backend for parity checking.

The compiler is built around deterministic simulation testing at the language level. Prism programs elaborate to a strict A-normal-form call-by-push-value core, definitions and packages are content-addressed by hash, project builds can explain their lineage, and suspended continuations carry the code identity they may resume against. The compiler also builds to WebAssembly, so the playground and gallery run in the browser; the interpreter is a CEK machine modeled in Lean and serves as the differential oracle every native backend must match byte-for-byte.

Try it in the browser at the [Prism playground](https://sdiehl.github.io/prism/play/).

Read the [language specification](https://sdiehl.github.io/prism/spec.html) and the [compiler documentation](https://sdiehl.github.io/prism/compiler.html).

The [`examples/`](./examples) directory contains a tour of most advanced features; my [blog post](https://www.stephendiehl.com/posts/prism/) explains the project design.

## Install

### Nix

```shell
nix build github:sdiehl/prism        # binary at ./result/bin/prism
nix run github:sdiehl/prism          # or run it directly
nix develop                          # dev shell: LLVM, cargo, just; target/release on PATH
```

### macOS / Linux

Native codegen needs LLVM 22 at runtime, so install it first:

```shell
brew install llvm@22                                          # macOS
curl -fsSL https://apt.llvm.org/llvm.sh | sudo bash -s 22     # Debian/Ubuntu
```

Then install prism (macOS Apple Silicon; Linux x86_64, aarch64):

```shell
curl --proto '=https' --tlsv1.2 -fsSL https://sdiehl.github.io/prism/install.sh | PRISM_VERSION=v0.18.0 sh
```

The installer verifies the release tarball's SHA-256 against the release manifest (and its build-provenance attestation when an authenticated `gh` is available) before unpacking, and installs to `~/.local/bin` without sudo. If Nix is present it uses the flake instead, with hashes verified by the Nix store.

Also available: `brew install sdiehl/prism/prism`, `docker run ghcr.io/sdiehl/prism`, and pinned x86-64 packages:

```shell
# Debian / Ubuntu (LLVM repository, then package)
curl -fsSL https://apt.llvm.org/llvm.sh | sudo bash -s 22
curl -fLO https://github.com/sdiehl/prism/releases/download/v0.18.0/prism_0.18.0_amd64.deb && sudo apt install ./prism_0.18.0_amd64.deb

# Fedora / RHEL
sudo dnf install https://github.com/sdiehl/prism/releases/download/v0.18.0/prism-0.18.0-1.x86_64.rpm

# Arch (prebuilt package or local PKGBUILD)
sudo pacman -U https://github.com/sdiehl/prism/releases/download/v0.18.0/prism-0.18.0-1-x86_64.pkg.tar.zst
curl -fLO https://github.com/sdiehl/prism/releases/download/v0.18.0/PKGBUILD && makepkg -si

# Alpine / musl: no native package (the binary is glibc-linked). Use the image:
docker run ghcr.io/sdiehl/prism --version
```

### From Source

You need the standard Rust toolchain installed. Native codegen also needs `clang` on `PATH` (override with `PRISM_CC`).

```shell
# macOS
brew install llvm@22
LLVM_SYS_221_PREFIX="$(brew --prefix llvm@22)" \
  PRISM_CC="$(brew --prefix llvm@22)/bin/clang" \
  cargo install --git https://github.com/sdiehl/prism

# Debian/Ubuntu (after enabling apt.llvm.org as above)
sudo apt install llvm-22-dev libpolly-22-dev clang-22
LLVM_SYS_221_PREFIX=/usr/lib/llvm-22 \
  PRISM_CC=/usr/lib/llvm-22/bin/clang \
  cargo install --git https://github.com/sdiehl/prism
```

## Usage

```shell
prism                                # interactive shell
prism program.pr                     # compile to a native binary named `program`
prism program.pr -o out              # ...with a custom output path
prism program.pr -O2                 # ...at optimization level 2
prism run program.pr                 # interpret instead of compiling
prism build                          # compile the enclosing project (needs a prism.toml), into target/
prism build --watch --verbose        # rebuild on edits; show unit/Merkle impact and timing
prism clean                          # remove the project's target/ directory
prism check                          # type check the enclosing project
prism check program.pr               # type check one source file
prism search '(String) -> Bool'       # search checked interfaces by type
prism synth program.pr --at-hole name # propose bounded, rechecked hole terms
prism bootstrap check program.pr      # compare the Prism T1 shadow checker
prism pkg init                       # create a new package interactively
prism fmt program.pr                 # format source
prism dump core program.pr           # inspect one phase (`prism dump --help` lists every phase)
prism dump surface-syntax program.pr # versioned JSON surface syntax for tools
```

## License

This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for details.
