{
  description = "Prism compiler dev shell and package";

  # Substitute the LLVM/toolchain/package closure from the project's binary cache
  # so a contributor's first `nix develop`/`nix build` fetches instead of building.
  # Optional: a cache miss or outage only falls back to building, never breaks.
  nixConfig = {
    extra-substituters = [ "https://prism-lang.cachix.org" ];
    extra-trusted-public-keys = [ "prism-lang.cachix.org-1:QGPdkYkeJDrHd7shaXgb5eLsq8LGy0XmQxzKsChlnI0=" ];
  };

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    crane.url = "github:ipetkov/crane";
  };

  outputs = { self, nixpkgs, rust-overlay, crane }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f system);

      # Per-system environment shared by the dev shell and the package, so the two
      # build paths cannot drift on toolchain, LLVM version, or link inputs.
      envFor = system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ rust-overlay.overlays.default ];
          };
          toolchain = builtins.fromTOML (builtins.readFile ./rust-toolchain.toml);
          rust = pkgs.rust-bin.stable.${toolchain.toolchain.channel}.minimal.override {
            extensions = (toolchain.toolchain.components or [ ]) ++ [ "rust-src" "rust-analyzer" ];
          };
          llvm = pkgs.llvmPackages_22;
          libInputs = [
            pkgs.libffi
            pkgs.libxml2
            pkgs.zlib
            pkgs.ncurses
            pkgs.zstd
          ] ++ nixpkgs.lib.optional pkgs.stdenv.isDarwin pkgs.libiconv;
        in
        {
          inherit pkgs toolchain rust llvm libInputs;
        };
    in
    {
      devShells = forAllSystems (system:
        let
          inherit (envFor system) pkgs toolchain rust llvm libInputs;
        in
        {
          default = pkgs.mkShell {
            nativeBuildInputs = [
              rust
              llvm.clang
              pkgs.just
              pkgs.pkg-config
              pkgs.pre-commit
              pkgs.dprint
              pkgs.sccache
              pkgs.cargo-insta
              pkgs.cargo-nextest
            ];

            buildInputs = libInputs;

            LLVM_SYS_221_PREFIX = "${llvm.llvm.dev}";
            PRISM_CC = "${llvm.clang}/bin/clang";
            RUST_SRC_PATH = "${rust}/lib/rustlib/src/rust/library";
            RUSTC_WRAPPER = "sccache";

            shellHook = ''
              export PATH="$PWD/target/release:$PATH"
              echo "prism dev shell: rust ${toolchain.toolchain.channel}, llvm 22"
            '';
          };
        });

      packages = forAllSystems (system:
        let
          inherit (envFor system) pkgs toolchain rust llvm libInputs;
          craneLib = (crane.mkLib pkgs).overrideToolchain rust;

          # Crane's default filter keeps only Cargo-relevant files. The compiler
          # embeds non-.rs inputs at build time: the stdlib via include_str!, the C
          # runtime compiled by build.rs, the LALRPOP grammar processed by build.rs,
          # and the examples/*.pr the wasm feature embeds (src/wasm.rs). Those paths
          # must be unioned back in or the build
          # fails (grammar) or embeds stale/absent sources (stdlib). A stdlib mismatch
          # would surface as a `dump stdlib-hash` divergence from `cargo build`.
          fs = pkgs.lib.fileset;
          src = fs.toSource {
            root = ./.;
            fileset = fs.unions [
              (craneLib.fileset.commonCargoSources ./.)
              ./lib
              ./runtime
              ./rust-toolchain.toml
              ./examples/boids.pr
              ./examples/chaos_swarm.pr
              ./examples/incr_resident.pr
              ./examples/pendulum.pr
              ./examples/teleport.pr
              ./examples/world.pr
              ./src/syntax/grammar.lalrpop
            ];
          };

          commonArgs = {
            inherit src;
            strictDeps = true;
            nativeBuildInputs = [ llvm.clang pkgs.pkg-config ];
            buildInputs = libInputs;
            LLVM_SYS_221_PREFIX = "${llvm.llvm.dev}";
            PRISM_CC = "${llvm.clang}/bin/clang";
            # Test corpus (parity/snapshots) is CI's job, not the package build's.
            doCheck = false;
          };

          cargoArtifacts = craneLib.buildDepsOnly commonArgs;
          prism = craneLib.buildPackage (commonArgs // { inherit cargoArtifacts; });

          # WebAssembly bundle: interpreter-only front-end (no LLVM, cdylib), the
          # nix equivalent of `just wasm` (--no-default-features --features wasm on
          # wasm32-unknown-unknown, then wasm-bindgen --target web). wasm-bindgen-cli
          # MUST match the wasm-bindgen crate version in Cargo.lock exactly, so pin
          # it here rather than take nixpkgs' default (which drifts and errors).
          rustWasm = pkgs.rust-bin.stable.${toolchain.toolchain.channel}.minimal.override {
            targets = [ "wasm32-unknown-unknown" ];
          };
          craneWasm = (crane.mkLib pkgs).overrideToolchain rustWasm;
          # nixpkgs ships versioned wasm-bindgen-cli attrs; pick the one matching
          # the wasm-bindgen crate in Cargo.lock (0.2.126). Bump both together.
          wasmBindgen = pkgs.wasm-bindgen-cli_0_2_126;
          wasmArgs = {
            inherit src;
            strictDeps = true;
            doCheck = false;
            cargoExtraArgs = "--no-default-features --features wasm";
            CARGO_BUILD_TARGET = "wasm32-unknown-unknown";
          };
          prism-wasm = craneWasm.buildPackage (wasmArgs // {
            cargoArtifacts = craneWasm.buildDepsOnly wasmArgs;
            nativeBuildInputs = [ wasmBindgen pkgs.binaryen ];
            # `[lib] crate-type` is rlib-only in Cargo.toml so native builds skip
            # the dead cdylib; ask for the wasm cdylib here with `cargo rustc
            # --crate-type cdylib` (plain `cargo build` would only emit the rlib
            # and postInstall would find no prism.wasm).
            cargoBuildCommand = "cargo rustc --release --lib --crate-type cdylib";
            # buildPackage emits target/wasm32-unknown-unknown/release/prism.wasm;
            # wasm-bindgen turns it into the web-target JS + _bg.wasm pair the docs
            # and web app consume, then wasm-opt -Oz shrinks it (what wasm-pack does
            # internally) for the small, deterministic bundle the README advertises.
            postInstall = ''
              wasm-bindgen --target web --out-dir $out/pkg --out-name prism \
                target/wasm32-unknown-unknown/release/prism.wasm
              wasm-opt -Oz -o $out/pkg/prism_bg.wasm $out/pkg/prism_bg.wasm
            '';
          });
        in
        {
          default = prism;
          inherit prism;
          wasm = prism-wasm;
        });

      apps = forAllSystems (system: {
        default = {
          type = "app";
          program = "${self.packages.${system}.prism}/bin/prism";
        };
      });
    };
}
