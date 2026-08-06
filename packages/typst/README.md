# Typst for Prism

Typed, deterministic construction of Typst source. This package owns Typst syntax composition and escaping, and it has no presentation concepts: Spectra consumes it, but nothing here knows what a slide is.

The API mirrors Typst's own semantic structure:

- **Markup versus code is a typed distinction.** A `Doc` is markup, an `Expr` is a code-mode expression, and the only bridges are `code` (which inserts the `#` marker itself) and `content` (which wraps markup in a content block). An expression cannot land in markup position by accident, because the types refuse it.
- **Values are typed.** Lengths (`Pt`, `Em`, `Cm`, `Fr`, `Percent`), colors (`Rgb`, `Luma`), alignment, and direction come from `Typst.Value`; an invalid length is unrepresentable and rendering owns every spelling, including channel clamping.
- **Trust has two doors.** `atom` (markup) and `sym` (code) emit their argument verbatim; everything else escapes by construction, with string and markup escaping each owned in exactly one place.
- **The markup layer is combinators.** `Typst.Markup` covers headings, emphasis, lists, links, figures, tables, labels, and references over the same two types.
- **Rendering is a pure function.** Equal documents render equally, and the package's tests state determinism, stability, and the escaping round trips as laws.

A standalone document, no Spectra in the room:

```prism
import Typst (..)

import Typst.Markup (heading, bullet_list, link, table)

fn report() : String =
  document([
      set_rule("page", [named("width", len(Cm(16))), named("margin", pt(24))]),
      set_rule("text", [named("size", pt(11))]),
      heading(1, "Quarterly results"),
      text_line("Totals are unaudited; # and * render literally."),
      table(2, ["Region", "Total", "North", "1,204", "South", "982"]),
      heading(2, "Sources"),
      bullet_list(["ledger export", "field reports"]),
      link("https://example.org/method", "methodology"),
    ])

fn main() = println(report())
```

renders, deterministically, to:

```typst
#set page(width: 16cm, margin: 24pt)
#set text(size: 11pt)
#heading(level: 1)[Quarterly results]
Totals are unaudited; \# and \* render literally.
#table(columns: 2, [Region], [Total], [North], [1,204], [South], [982])
#heading(level: 2)[Sources]
#list([ledger export], [field reports])
#link("https://example.org/method")[methodology]
```

which `typst compile` accepts as-is. Keeping this package independent prevents Spectra's slide model, themes, CLI, and build orchestration from leaking into reusable Typst syntax generation.
