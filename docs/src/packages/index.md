# Packages

Prism packages are ordinary projects published into the content-addressed store: a package is named by the hash of its source root, added to a project with `prism pkg add`, and resolved by exact root rather than by version range. The packages below live in the compiler repository and double as the package system's own test corpus; their reference pages are generated from their sources by `prism docs`, the same way the [Standard Library](../stdlib/index.md) reference is.

- [Tzdb](./tzdb/index.md) is deterministic timezone arithmetic over a pinned, curated zone table: the IANA data becomes versioned package source, so a conversion is a pure function of the instant, the zone, and the package root.
- [Spectra](./spectra/index.md) is a presentation generator: a deck is a typed Prism value, slides can quote their own source through `reflect`, and the build lowers the deck to Typst and renders a PDF.
- [Typst](./typst/index.md) is the generic Typst source-construction layer beneath Spectra: typed combinators over a pretty-printing core, with escaping owned in one place and no presentation concepts.
- [Tc](./tc/index.md) is the type-and-row core of a Prism typechecker written in Prism: the value/computation type and effect-row ADTs, substitution, zonking, row normalization, unification with occurs checks, and generalization, property-tested and mirroring the statics sketch.
