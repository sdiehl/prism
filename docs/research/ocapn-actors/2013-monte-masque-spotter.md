# Monte Language Implementations: Masque (Haskell) and Spotter (OCaml)

- [monte-language.org](https://www.monte-language.org/)
- [Monte documentation](https://monte.readthedocs.io/)
- [monte-language on GitHub](https://github.com/monte-language)

Created by W. Allen Short and Corbin Simpson as a spiritual successor to E. Dynamic object-capability language inspired by Python, designed for secure distributed computing. Two implementations explored distribution architecture but neither completed CapTP.

## Masque (Monte in Haskell)

- [monte-language/masque on GitHub](https://github.com/monte-language/masque)

Haskell interpreter for Monte. Small implementation (31 commits) focusing on MAST binary format deserialization and basic evaluation.

### Architecture
- **AST layer**: MAST deserialization from binary format; ADTs for `Expr`, `Patt`, `NamedExpr`, `NamedPatt`
- **Evaluation**: `EitherT` for error handling with ejectors (delimited continuations). Binding system: `FullBinding`, `VarBinding`, `FinalBinding`, etc. `IORef` for mutability
- **Object model**: Algebraic types with `RefObj` (promise-like `IORef`), `FountObj`/`DrainObj` (stream I/O), `UserObj`, `BuiltinObj`

### Distributed Identity
- `RefObj` provides mutable references with `IORef`, can be resolved later
- `ResObj` handles `"resolve"` messages
- `"connectTo"` builtin creates `FountObj`/`DrainObj` pairs from TCP
- **No CapTP, no vats, no far references** -- single-vat interpreter only

### Lessons
- Ejectors as control flow via `EitherT`
- Binding-oriented scope with slot access mediation
- MAST binary format for shared AST across implementations

## Spotter (Monte in OCaml)

- [monte-language/spotter on GitHub](https://github.com/monte-language/spotter)

Experimental low-level Monte runtime (76 commits). More complete than Masque but also lacks distribution.

### Architecture
- **Type system**: Monte objects as structurally-typed OCaml objects with row polymorphism
- **Primitives**: `MNull | MBool | MChar | MDouble | MInt | MStr | MList` with guards
- **Compiler**: MAST-to-Monte via state monad over dictionary environment
- **Safe scope**: Pre-populated built-in objects: guards (`Bool`, `Int`, `Str`, `Any`, `DeepFrozen`, `Near`), makers, flow control
- **Method dispatch**: AtomDict-based by (verb, arity) pairs

### Distributed Identity
- `Ref.promise()`, `Ref.isNear()`, `Ref.isFar()`, `Ref.isEventual()`, `Ref.isResolved()` -- hooks for eventual references
- `Near` guard: immediately accessible values
- `DeepFrozen` guard: transitive immutability, safe to copy across vats
- `Vow` guard: promises and entailments
- **No actual networking layer**

### Lessons
- Structural typing in OCaml maps naturally to Monte's dynamic object model
- `DeepFrozen` is the key abstraction for safe cross-vat copying
- Monte's design directly informed OCapN distributed identity model

## Monte's Key Concepts for OCapN

| Concept | Purpose |
|---|---|
| **Vats** | Isolation units with turn queues; membranes on boundaries |
| **Promises** | `Ref.promise()`, eventual sends (`<-`), `when` expressions |
| **DeepFrozen** | Auditor for transitive immutability; safe to copy |
| **Brands** | Sealer/unsealer pairs for rights amplification |
| **No ambient authority** | All authority must be explicitly passed |

## Links
- [Masque on GitHub](https://github.com/monte-language/masque)
- [Spotter on GitHub](https://github.com/monte-language/spotter)
- [Typhon on GitHub](https://github.com/monte-language/typhon)
- [Monte documentation](https://monte.readthedocs.io/)
  - [Vats](https://monte.readthedocs.io/en/latest/vats.html)
  - [Promises](https://monte.readthedocs.io/en/latest/promises.html)
  - [Brands](https://monte.readthedocs.io/en/latest/brands.html)
  - [Auditors](https://monte.readthedocs.io/en/latest/auditors.html)
  - [Design and security](https://monte.readthedocs.io/en/latest/design.html)
- [OCAP 2017 talk](https://www.youtube.com/watch?v=FJnck8bgmXg) — YouTube
- [E's CapTP documentation](http://erights.org/elib/distrib/captp/index.html)
