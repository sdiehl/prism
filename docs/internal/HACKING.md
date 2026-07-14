# Release checklist

Run every box on the exact tree being released, in order; never release a red tree.

## Required validation

- [ ] `cargo check --all-targets`
- [ ] `cargo check --no-default-features --lib`
- [ ] wasm feature check
- [ ] MLIR feature check
- [ ] mimalloc feature check
- [ ] `cargo clippy --all-targets -- -D warnings`
- [ ] Full test suite and doctests
- [ ] Snapshot suite with no `.snap.new` files
- [ ] Full native parity corpus
- [ ] Full tier-parity corpus
- [ ] Perf/allocation/EOp gates
- [ ] Leak checks
- [ ] ASan/UBSan runtime gates
- [ ] Cold `just gate`
- [ ] `just ci`
- [ ] `just fmt-examples`
- [ ] `just package-world`

## Release preparation

- [ ] Bump `Cargo.toml` to the release version.
- [ ] Rebuild so `Cargo.lock` records the new version.
- [ ] Update literal README installation URLs and filenames to the new version.
- [ ] Run `just hash`.
- [ ] Run `just docs-gen` twice and confirm the second run changes nothing.
- [ ] Verify all generated stdlib hashes, badges, shape/type snapshots, and reference docs are committed.
- [ ] Run final cold `just gate` and `just ci` on the exact release tree.
- [ ] Create and push the annotated version tag.
- [ ] Run `just dist <version>`.
- [ ] Publish and verify deb/rpm/apk/container artifacts.
