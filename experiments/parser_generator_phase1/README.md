# Generated Type parser and shared control scaffold

This generator owns the complete structural Type family used by `Syntax.Parse.Type`: `Type`, synthetic `TypeHead`, `Arrow`, `ArrowEff`, `UType`, `CoeffRowParts`, `EffLabel`, `AType`, `TypeArg`, `DimTerm`, and `DimTail`, together with their factored delimiter children.

`Syntax.Parse.GeneratedControl` owns the family-neutral `Parsed` bind and the typed phase/policy separated-list loop. `GeneratedType` supplies Type-specific value/receipt projections and FOLLOW policy; the control module knows neither the Type AST nor Type receipts. This is scaffolding for a later whole-Pattern decision, not Pattern authority.

It reads the production manifest from the worktree and the grammar and source pins from the manifest's frozen Git commit. Before rendering, it:

- extracts and validates all 133 grammar productions;
- checks terminal aliases, generic arity, owners, classes, source pins, named hooks, and hook evidence;
- computes nullable and FIRST facts to a deterministic fixed point;
- validates 40 typed action rows against exact production, alternative, RHS, action, checked-action, selector, target, completion, and hook identities;
- validates concrete `Comma<EffLabel>`, `Comma<RecordField>`, `Comma<Type>`, `Comma<TypeArg>`, and `Comma<"ident">` ownership; and
- checks exact Type and effect-label receipt transitions before the shared Type-spine template can render.

`generate` owns the isolated and production copies of `GeneratedControl`, plus the isolated `GeneratedTypeLeaf` candidate and `lib/std/Syntax/Parse/GeneratedType.pr`. The two Type artifacts differ only in their control-module import (`GeneratedControl` inside the fixture and `Syntax.Parse.GeneratedControl` in production), and each has its own recorded hash. The generator never reads either production artifact as input. Consumer-marker drift in the small `Type.pr` facade is a hard error, so one generation pass is idempotent and cannot silently stop owning production.

Usage-row semantic validation lives in `Syntax.Parse.TypeSemantics`; it accepts only consumed facts and the open-tail bit. All grammar control, cursor movement, recursive depth spending, effect attachment, and completion receipts remain generated.

The 55 tests in `generated/type_leaf/tests/type_leaf.pr` are independently maintained and fingerprinted, never rendered by Python. The full-spine cases cover recursive depth, forall/arrow receipt propagation, usage/effect retags, the two-token `()` arrow commitment, forall and row failure menus, named effect optional arguments, and TypeHead suffix behavior.

Run from the repository root:

```sh
python3 experiments/parser_generator_phase1/generate.py generate
python3 experiments/parser_generator_phase1/generate.py check
python3 experiments/parser_generator_phase1/generate.py self-test
(cd experiments/parser_generator_phase1 && python3 -m unittest test_generate.py)
target/debug/prism check experiments/parser_generator_phase1/generated/type_leaf
target/debug/prism test --fail-if-no-tests \
  experiments/parser_generator_phase1/generated/type_leaf
```

## Current convergence ledger

The promoted TypeArg checkpoint was 526 handwritten Type lines plus 286 generated lines, 812 production `G` lines. The full spine is:

- 24 lines in the public `Type.pr` facade;
- 100 lines in the handwritten semantic hook module;
- the generated line count recorded dynamically in `generated/plan.json`; and
- the generator's maintained line count recorded beside it.

The plan compares those live counts with the 812-family/2629-generator checkpoint and hard-fails self-test if maintained `T` does not improve. `TypeSemantics` is counted; moving semantics out of `Type.pr` is not presented as deletion. `GeneratedControl` is charged once to production even though it is shared infrastructure, and the plan separately reports its delta from the full-Type checkpoint. The duplicate isolated candidate and static tests are nontransitive and are not double-counted in production `G`.

This completes structural Type authority, not whole-parser authority. The control extraction is retained only if the later whole-Pattern tranche repays its explicit scaffold debt. Pratt expressions and declaration-specific return binding remain separate generated families or escaped semantic seams.
