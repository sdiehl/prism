# Parser generator experiment

This was a bootstrap experiment for generating the type parser in `lib/std/Syntax/Parse/GeneratedType.pr` from the frozen Rust/LALRPOP grammar. It also checks the parser production manifest and the typed action schema.

The self-hosted parser does not replace this yet: `Syntax.Parse.Type` still imports the generated type parser. `GeneratedPattern.pr` uses the same control scaffold, but this script does not generate or freshness-check it.

The experiment did not achieve its compaction goal. `generated/plan.json` currently records more maintained code than the handwritten baseline. Keep it while `GeneratedType.pr` is generated from it, but do not extend it as the default path for the rest of the parser. Once the type parser is maintained in Prism, or a Prism-owned generator replaces this script, this directory and its CI check can go.

From the repository root:

```sh
python3 experiments/parser_generator_phase1/generate.py generate
python3 experiments/parser_generator_phase1/generate.py check
python3 experiments/parser_generator_phase1/generate.py self-test
```

`just artifacts-check` runs the full CI gate, including the Python tests and the generated parser fixture.
