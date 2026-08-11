# Cut and publish a release with cargo-release.
[group('release')]
release VERSION:
    cargo release {{ VERSION }} --execute

# Build deb, rpm, and Arch packages for the host architecture.
[group('release')]
pkg VERSION: build-release
    python3 scripts/package.py native "{{ VERSION }}"

# Build the self-contained LLVM container image.
[group('release')]
docker TAG="prism:dev":
    docker build -t "{{ TAG }}" .

# Build native packages and the container image.
[group('release')]
dist VERSION: (pkg VERSION)
    just docker "prism:{{ VERSION }}"

# Build the prismup toolchain installer (release profile, host target).
[group('release')]
prismup:
    cargo build --release --manifest-path tools/prismup/Cargo.toml

# Refresh the committed Arch PKGBUILD from published checksums.
[group('release')]
pkgbuild VERSION:
    python3 scripts/package.py pkgbuild "{{ VERSION }}"
