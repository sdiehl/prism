# spectra

API documentation generated from the project's source by `prism docs`. Function and value signatures are the typechecker's inferred types; prose comes from `-- |` doc comments.

## Modules

- [Backend](./backend.md) - Spectra's pure lowering from presentation values to Typst documents.
- [Code](./code.md) - Code-oriented Spectra combinators: fenced source blocks and inline monospace, as plain `Pict`/`Inline` values.
- [Example](./example.md) - Doctests on slides: the examples a reflected declaration carries.
- [Layout](./layout.md) - Backend-neutral layout values for Spectra.
- [Main](./main.md) - The standalone Spectra executable: parse the command line (`SpectraCli`), dispatch to the build orchestration (`SpectraBuild`), exit with its status.
- [Spectra](./spectra.md) - Spectra: typed Prism presentations lowered to deterministic Typst.
- [SpectraBuild](./spectrabuild.md) - Standalone Spectra build orchestration, written in Prism.
- [SpectraCli](./spectracli.md) - Spectra's command grammar, built applicatively with Std `Cli`.
- [Theme](./theme.md) - Theme values for Spectra decks.
