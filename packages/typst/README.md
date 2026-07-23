# Typst for Prism

This package is the generic Typst source-construction layer used by Spectra. It has no presentation concepts.

`Typst.Doc` is opaque and composed with small typed combinators such as `call`, `named`, `content_call`, `suite`, `set_rule`, and `let_function`. Rendering delegates layout to Std `Data.Pretty`, while `string` owns Typst string escaping.

```prism
import Typst as T

fn greeting() =
  T.document([
      T.set_rule("text", [T.named("size", T.pt(20))]),
      T.code(T.call("text", [T.string("Hello from Prism")])),
    ])
```

Keeping this package independent prevents Spectra's slide model, themes, CLI, and build orchestration from leaking into reusable Typst syntax generation.
