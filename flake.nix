{
  description = "Prism compiler dev shell";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, rust-overlay }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f system);
    in
    {
      devShells = forAllSystems (system:
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
            ];

            buildInputs = [
              pkgs.libffi
              pkgs.libxml2
              pkgs.zlib
              pkgs.ncurses
              pkgs.zstd
            ] ++ nixpkgs.lib.optional pkgs.stdenv.isDarwin pkgs.libiconv;

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
    };
}
