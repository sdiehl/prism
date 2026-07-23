# Spectra

Spectra is a typed Prism presentation DSL that lowers deterministic deck values to inspectable Typst and PDF artifacts.

The implementation is Prism throughout. `src/Main.pr` is the standalone CLI; `Spectra.pr` is the public authoring facade; `Backend.pr` lowers the backend-neutral layout tree through the separate `typst` package.

## Build the CLI

```console
prism build packages/spectra --out ./spectra
./spectra --help
```

The executable expects `prism` and `typst` on `PATH` when checking or building a deck.

## Author a deck

```prism
import Spectra (..)

fn body() : Unit ! {SlideBuilder} =
  pict(para([plain("A deck is a typed value.")]))
  reveal_next()
  pict(item("Reveals become deterministic physical pages."))

fn slides() : Unit ! {DeckBuilder} =
  cover("Spectra", "Typed presentations through Typst")
  slide("Composition", body)

fn main() =
  emit_deck(deck(metadata("Spectra", "Prism"), prism_theme, slides))
```

`Spectra (..)` provides the normal lowercase authoring surface. Advanced users who need raw data constructors can import `Layout`, `Theme`, `Code`, or `Backend` explicitly.

## Build a deck

```console
./spectra check examples/spectra-deck
./spectra build examples/spectra-deck --output spectra-intro.pdf
```

Build outputs live under the deck's `target/spectra/` directory:

- `deck.deck.json`: canonical versioned envelope;
- `deck.typ`: retained generated Typst;
- `deck.stdout`: captured framed evaluator output;
- `deck-evaluator`: native Prism deck evaluator;
- the requested PDF.

The build pipeline uses `Result` and `?` internally. Errors acquire context at subsystem boundaries and are converted to process exit codes only in the CLI layer.

Generated Typst disables Typst's ambient document date. Repeated builds with the same renderer, fonts, assets, and inputs therefore produce byte-identical `.typ` and PDF artifacts; fully portable reproducibility still requires pinning those inputs.

The default `prism_theme` is a minimalist Beamer-inspired warm-paper theme with a violet title rule and explicit high-contrast code surfaces. `paper_theme` and `prism_dark_theme` are also available.
