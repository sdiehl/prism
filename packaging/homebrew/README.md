# Homebrew tap

`brew install sdiehl/prism/prism` installs the prebuilt Apple Silicon binary and pulls in `llvm@22` (which the binary links against and shells out to for native codegen). The `Release` workflow keeps the tap formula current on every tagged release. This is the one-time setup behind that.

## One-time setup

1. Create a public repo named **`homebrew-prism`** under your account (`sdiehl/homebrew-prism`). The `homebrew-` prefix is what makes it a tap.

2. Add the formula. Copy this directory's `prism.rb` to `Formula/prism.rb` in the tap repo:

   ```sh
   mkdir -p Formula
   cp /path/to/prism/packaging/homebrew/prism.rb Formula/prism.rb
   ```

   The placeholder `url`/`sha256`/`version` are fine to commit. The release workflow rewrites them. To install before the first automated bump, point `url` at an existing release tarball and set `sha256` to its `*.tar.gz.sha256` value.

3. Let the release workflow update the formula automatically. Create a Personal Access Token with `contents: write` on `homebrew-prism` (fine-grained, scoped to that one repo) and add it to the **prism** repo as the secret **`HOMEBREW_TAP_TOKEN`**. Without it, the release still publishes the GitHub Release; only the tap bump is skipped.

## Install

```sh
brew install sdiehl/prism/prism   # or: brew tap sdiehl/prism && brew install prism
prism program.pr -o out
```

## Notes

- Apple Silicon only. The formula refuses to install on Intel; build from source there (see the top-level README).
- A binary downloaded from a browser (not via brew) is quarantined by Gatekeeper. Clear it with `xattr -dr com.apple.quarantine ./prism`. Homebrew installs are not affected.
- After editing the formula, `brew audit --strict --online prism` and `brew test prism` validate it.
