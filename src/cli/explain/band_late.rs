//! Explanations for the parse, verify, and internal bands: E7000-E9999.

use super::Explanation;

pub(super) const ENTRIES: &[Explanation] = &[
    Explanation {
        code: "E7000",
        title: "unrecognized character",
        prose: "The lexer reached a character that begins no token in the language. Outside a \
                string literal, a comment, or a raw literal, every character must start a fixed \
                token, an identifier, or a numeric literal. Characters that read naturally in \
                prose, such as a backtick or a typographic quote, are not Prism tokens, so text \
                pasted from a document often lands here.",
        example: "fn main() : Int =\n  `1`",
        fix: "Delete the character, or replace it with the token you meant.",
    },
    Explanation {
        code: "E7001",
        title: "empty interpolation hole",
        prose: "A string literal contains `{}` with nothing between the braces. An interpolation \
                hole is lexed as an expression and spliced into the string, so an empty hole has \
                nothing to splice. The check happens on the literal itself, before any name \
                resolution or typing.",
        example: "fn main() : Int =\n  println(\"value: {}\")\n  0",
        fix: "Put an expression between the braces, or write the text as a raw literal \
              (`r\"\"\"value: {}\"\"\"`), where braces carry no meaning.",
    },
    Explanation {
        code: "E7002",
        title: "unterminated interpolation hole",
        prose: "A string literal opened an interpolation hole with `{` and the source ended \
                before the matching `}`. The scanner tracks nested strings and brace depth \
                together, so it reports the outermost brace that was never closed rather than \
                the last one it saw. An unfinished hole leaves the whole literal unfinished.",
        example: "fn main() : Int =\n  let s = \"a {x",
        fix: "Close the hole with `}` and then close the string, or write the text as a raw \
              literal (`r\"\"\"...\"\"\"`) if the brace was meant literally.",
    },
    Explanation {
        code: "E7003",
        title: "unterminated string literal",
        prose: "A string literal opened with `\"` and the source ended before a closing quote. A \
                newline does not close a string. Because the scanner also counts quotes that \
                appear inside interpolation holes, one unbalanced quote inside a hole can swallow \
                the rest of the file and be reported here at the opening quote.",
        example: "fn main() : Int =\n  let s = \"unterminated\n  0",
        fix: "Add the closing quote.",
    },
    Explanation {
        code: "E7004",
        title: "malformed numeric literal separator",
        prose: "A `_` digit separator in a numeric literal was not flanked by two digits. Prism \
                accepts `_` only between digits, so a leading, trailing, or doubled separator, or \
                one adjacent to `.` or an exponent marker, is rejected. Nothing else about the \
                literal is wrong; only the separator placement is.",
        example: "fn main() : Int =\n  1_000_",
        fix: "Move or delete the separator so every `_` sits between two digits, as in \
              `1_000_000`.",
    },
    Explanation {
        code: "E7100",
        title: "syntax error",
        prose: "The parser reached a token that no production admits at that point. The \
                diagnostic names the token it found and the canonical set of tokens it could have \
                accepted there, sorted so the set does not depend on grammar order. This is the \
                general parse failure, and it rejects the whole file, so no later phase runs. A \
                block that ends earlier than expected is reported here too, at the zero-width \
                closer the layout pass inserted.",
        example: "fn main() : Int =\n  )",
        fix: "Supply one of the tokens in the expected list at the caret; a missing closer, `=`, \
              or `,` is the usual cause.",
    },
    Explanation {
        code: "E7101",
        title: "unexpected end of input",
        prose: "The token stream itself ran out while the parser still wanted more. This is a \
                separate code from E7100 so an interactive caller can distinguish `incomplete, \
                read another line` from `wrong token` without matching on message text. Only the \
                expression entry reaches it: for a whole program the layout pass closes every \
                open block before the stream ends, so a file that stops early fails as E7100 at \
                the virtual closer.",
        example: "-- The expression entry, as used by the REPL and by `Syntax.Cursor`:\n[1 + 2",
        fix: "Finish the expression: supply the closing bracket or the missing operand.",
    },
    Explanation {
        code: "E7102",
        title: "parse depth budget exhausted",
        prose: "Nesting in the input ran past the parser's depth budget. The budget is spent one \
                level at a time and refused structurally at the current token, so deeply nested \
                or adversarial input yields an ordinary diagnostic instead of exhausting the \
                stack. The code belongs to the Prism-language parser written in Prism; the \
                compiler's own parser bounds depth separately.",
        example: "import Syntax.Cursor (cursor_of)\nimport Syntax.Parse.Support (..)\n\nfn main() \
                  : Int =\n  match descend(0, cursor_of(Nil, 0)) of\n    PFault(d) => \
                  println(d.code)\n    _ => println(\"budget left\")\n  0",
        fix: "Flatten the input so it nests less deeply, or start the parse with a larger depth \
              budget.",
    },
    Explanation {
        code: "E7200",
        title: "module could not be resolved",
        prose: "An `import` named a module that is not on the search path. Modules resolve from \
                the entry file's directory, then any path dependencies, then the embedded \
                standard library, and the diagnostic lists the roots that were searched. A module \
                that is found but fails to load, and one whose name collides with the importing \
                module's own, are reported here as well.",
        example: "import No.Such.Module (thing)\n\nfn main() : Int =\n  0",
        fix: "Correct the module path, or add the directory or dependency that provides it.",
    },
    Explanation {
        code: "E7201",
        title: "project manifest error",
        prose: "`prism.toml` is malformed or missing a required field. The manifest must parse as \
                TOML and carry package name, version, authors, maintainers, and a supported SPDX \
                license identifier, \
                plus a `[bin] entry`. Optional URLs are strings and metadata files are string \
                arrays. A `[dependencies]` table maps each name to a path, a git source with a \
                version, or a hash pin. A missing dependency path is also a manifest error.",
        example: "-- A `prism.toml` with no `[package]` table, then `prism check .`:\n--   \
                  Module Error[E7201]: prism.toml: missing [package] table\nfn main() : Int =\n  \
                  0",
        fix: "Repair the field the message names in `prism.toml`.",
    },
    Explanation {
        code: "E7202",
        title: "package or lockfile error",
        prose: "A package verb could not resolve the package universe. The lockfile pins nothing, \
                pins a root the store does not hold, or the store holds a bundle whose hash does \
                not match its pin. Package resolution is content addressed and fails closed: it \
                never substitutes a different root for the one that was pinned.",
        example: "-- `prism pkg why <hash>` in a project whose lockfile pins nothing:\n--   \
                  Module Error[E7202]: prism.lock pins no dependencies; run `prism add` first",
        fix: "Pin the dependency with `prism pkg add`, or restore the store entry the lockfile \
              names.",
    },
    Explanation {
        code: "E7203",
        title: "lineage sidecar error",
        prose: "A lineage verb could not read or verify a `.plineage` sidecar. Either the file is \
                not a well-formed sidecar, or it names artifacts that no longer hash to their \
                recorded digests, or the verb was given arguments it does not accept. A sidecar \
                is the provenance record for one build or run, so a malformed one is refused \
                rather than partially trusted.",
        example: "-- `prism lineage show bogus.plineage` on a file that is not a sidecar:\n--   \
                  Module Error[E7203]: expected ident at line 1 column 2",
        fix: "Point the verb at the sidecar the build actually wrote, or rebuild to regenerate \
              it.",
    },
    Explanation {
        code: "E7204",
        title: "command or argument could not be resolved",
        prose: "The CLI could not make sense of what it was asked to do. Typical causes are an \
                unknown diagnostic code, two flags that cannot be combined, a test filter that \
                matched nothing, and a field name that no record declares when the REPL \
                re-elaborates an expression. The request is rejected before any compilation \
                happens.",
        example: "-- `prism explain E9123`, a code the catalogue does not assign:\n--   Module \
                  Error[E7204]: unknown diagnostic code `E9123`",
        fix: "Check the spelling of the argument, and check the flag combination against \
              `--help` for that subcommand.",
    },
    Explanation {
        code: "E7205",
        title: "semantic patch refused",
        prose: "`prism patch apply` or `prism patch commit` judged a digest-pinned patch and \
                refused it. The CLI prints the canonical `prism-patch-refusal-v1` JSON payload \
                directly instead of a human diagnostic: its `judgment` field names the stage that \
                refused, and its `code` field carries the underlying diagnostic. Source files are \
                left untouched by a refusal.",
        example: "-- base.pr\npub fn inc(x : Int) : Int = x + 1\n\nfn main() : Int = \
                  inc(1)\n\n-- The replacement changes the type, so `prism patch apply` refuses \
                  at\n-- the `elaborate` judgment:\npub fn inc(x : Int) : String = \"no\"",
        fix: "Read the refusal's `judgment` and `code`, repair the replacement declaration, and \
              recreate the patch.",
    },
    Explanation {
        code: "E7400",
        title: "backend or codegen failure",
        prose: "Native code generation or linking failed for a reason outside the language \
                proper: the C compiler could not be run, linking produced no artifact, or a \
                compiler query named a definition that does not exist or is ambiguous. The \
                program itself already type-checked, so the fault is in the toolchain or in the \
                request, not in the source.",
        example: "-- `prism prog.pr -o prog` with no working C compiler:\n--   Codegen \
                  Error[E7400]: codegen: running clang: No such file or directory (is clang \
                  installed?)\nfn main() : Int =\n  0",
        fix: "Install a working clang or point `PRISM_CC` at one, or qualify the ambiguous name \
              the query reported.",
    },
    Explanation {
        code: "E7401",
        title: "documentation generation failure",
        prose: "`prism docs` could not produce or confirm the documentation. Under `--check` the \
                committed pages are out of date, under `--verify-manifest` the manifest does not \
                match the pages on disk, or a documented code block failed to type-check. A \
                failing check writes nothing, so the committed pages are never left half updated.",
        example: "-- `prism docs --check lib.pr` with stale committed pages:\n--   Codegen \
                  Error[E7401]: documentation: docs are out of date; run `prism docs`\n-- | Adds \
                  one.\npub fn inc(x : Int) : Int = x + 1",
        fix: "Run `prism docs` to regenerate and commit the pages, or fix the doc block the \
              warning named.",
    },
    Explanation {
        code: "E7402",
        title: "file is not canonically formatted",
        prose: "`prism fmt --check` found at least one file whose text differs from what the \
                formatter would write. Each offending file is named on its own line and nothing \
                is written to disk. The formatter is idempotent, so the canonical form is exactly \
                whatever a plain `prism fmt` produces.",
        example: "-- `prism fmt --check unfmt.pr`:\n--   unfmt.pr: not formatted\nfn main( ) : \
                  Int   =\n      1+2",
        fix: "Run `prism fmt` on the named files.",
    },
    Explanation {
        code: "E7403",
        title: "unknown or unavailable dump phase",
        prose: "`prism dump` was asked for a pipeline artifact it cannot produce: an unrecognized \
                phase name, or an artifact this program does not have. Serialization failures \
                while writing an artifact report here as well.",
        example: "-- `prism dump bogus prog.pr`:\n--   Codegen Error[E7403]: dump: unknown phase \
                  bogus\nfn main() : Int =\n  0",
        fix: "Pass one of the documented phase names (`tokens`, `ast`, `types`, `core`, \
              `lowered`, `llvm`, `mlir`, and the rest listed by `prism dump --help`).",
    },
    Explanation {
        code: "E7404",
        title: "contracts or obligations not discharged",
        prose: "`prism verify` put the program's obligations to the solver and at least one came \
                back unproved: a contract with a counterexample, a termination obligation that \
                did not close, or a proof the build's verification step rejected. The summary \
                counts the contracts and terminations that failed. This is a verdict about the \
                program, not a tool failure.",
        example: "fn dec(x : Int) : Int\n  ensures |r| r > x\n  =\n    x - 1",
        fix: "Weaken the `ensures`, strengthen the `requires`, or fix the body so the obligation \
              actually holds.",
    },
    Explanation {
        code: "E7500",
        title: "runtime fault",
        prose: "The program type-checked but faulted while running: division by zero, an explicit \
                abort, an unhandled error, or a continuation the interpreter could not encode. \
                The CLI prints these as `fatal: <message>` and does not repeat the code, because \
                a runtime fault has no source span to underline.",
        example: "fn main() : Int =\n  let d = 0\n  10 / d",
        fix: "Guard the operation that faulted, for instance by testing the divisor or handling \
              the error, so the fault cannot arise.",
    },
    Explanation {
        code: "E7501",
        title: "replay could not reproduce the run",
        prose: "`prism exec replay` or `prism exec resume` could not consume the recording it was \
                given. Either the `.replay` trace or the `kont` snapshot is malformed, or it does \
                not match the program: the recorded observation at some event is not the one the \
                program performs there. Replay is exact by construction, so a mismatch is refused \
                rather than approximated.",
        example: "-- Recorded from a program that reads one Int, then replayed against this \
                  one:\n--   fatal: replay: trace does not match program at event 1\nfn main() : \
                  Int =\n  let a = read_int()\n  let b = read_int()\n  println(\"{a} {b}\")\n  0",
        fix: "Replay against the exact program the trace was recorded from, or re-record with \
              `prism run --record`.",
    },
    Explanation {
        code: "E7502",
        title: "debugger session fault",
        prose: "The reverse-step debugger (`prism exec debug`) could not continue. Replaying the \
                trace prefix up to the requested observation failed, or the session could not \
                read a command or write its output. The trace decoded successfully; the fault \
                happens while stepping through it.",
        example: "-- `prism exec debug other.pr t.replay`, then `g 2` and `p`, where the trace\n\
                  -- was recorded from a different program:\n--   fatal: replay: trace does not \
                  match program at event 1",
        fix: "Attach the debugger to the program the trace was recorded against, and re-record if \
              that program has since changed.",
    },
    Explanation {
        code: "E7600",
        title: "input or output error",
        prose: "An operating-system file operation failed: the path does not exist, is not \
                readable, or a write could not complete. The message is the underlying OS error \
                verbatim. Nothing is compiled, since the compiler never saw the source.",
        example: "-- `prism check /nonexistent/nope.pr`:\n--   IO Error[E7600]: No such file or \
                  directory (os error 2)",
        fix: "Check the path and the permissions on it.",
    },
    Explanation {
        code: "E8000",
        title: "unsupported in a logical context",
        prose: "A `requires` clause, an `ensures` clause, or a `logic fn` body used a construct \
                outside the supported logical fragment. A contract is a total first-order \
                proposition over `Bool` and `Int`: no effects, no data beyond those two sorts, no \
                indirect or higher-order calls, no fixed-width (`I64`/`U64`) literals, and no \
                nonlinear arithmetic (`*`, `/`, `%`, `**`). The diagnostic names the smallest \
                offending subexpression. The check runs during ordinary compilation and never \
                needs a solver.",
        example: "fn f(x : Int) : Int\n  requires x * x >= 0\n  =\n    x",
        fix: "Rewrite the clause inside the fragment, or move the computation into the body and \
              constrain its result instead.",
    },
    Explanation {
        code: "E8001",
        title: "name unresolved in a contract",
        prose: "A contract or `logic fn` body mentioned a name that is not one of its parameters, \
                not the result binder introduced by `ensures |r|`, and not a visible logical \
                declaration. Logical scope is deliberately narrow, and it is not the enclosing \
                term scope: a `let` in the body is invisible to a clause, and so is any name from \
                elsewhere in the module.",
        example: "fn f(x : Int) : Int\n  requires y >= 0\n  =\n    x",
        fix: "Use a parameter or the result binder, or declare the value as a `logic fn` and call \
              that.",
    },
    Explanation {
        code: "E8002",
        title: "runtime definition used in a contract",
        prose: "A contract named an ordinary `fn`. Runtime definitions are not in logical scope, \
                because they may be partial, effectful, or nonterminating, and a proposition may \
                be none of those. The name did resolve, which is what separates this from E8001; \
                it simply is not a logical declaration.",
        example: "fn g(x : Int) : Int = x\n\nfn f(x : Int) : Int\n  requires g(x) >= 0\n  =\n    x",
        fix: "Declare the predicate as a `logic fn` and call that from the contract, keeping the \
              runtime function separate.",
    },
    Explanation {
        code: "E8003",
        title: "logical sort error",
        prose: "A logical term had the wrong sort. Every `requires` and `ensures` clause must be \
                `Bool`; each operand must have the sort its operator takes, `Int` for arithmetic \
                and comparison and `Bool` for the connectives; and a `logic fn` body must match \
                its declared result. The message names the position and the sort that was found \
                there.",
        example: "fn f(x : Int) : Int\n  ensures |r| r + 1\n  =\n    x",
        fix: "Make the clause a proposition rather than a value, for instance by comparing the \
              term: `ensures |r| r + 1 > x`.",
    },
    Explanation {
        code: "E8004",
        title: "wrong argument count for a logical declaration",
        prose: "A use of a `logic fn` inside a contract passed the wrong number of arguments. \
                Naming a declaration that takes parameters without applying it counts as zero \
                arguments and is reported here too. Logical declarations are inlined at their use \
                sites, so the arity must match exactly and there is no partial application.",
        example: "logic fn p(a : Int) : Bool = a >= 0\n\nfn f(x : Int) : Int\n  requires p(x, \
                  x)\n  =\n    x",
        fix: "Pass exactly as many arguments as the declaration has parameters.",
    },
    Explanation {
        code: "E8005",
        title: "duplicate logical declaration",
        prose: "Two `logic fn` declarations share a name. The logical environment is a flat map \
                from name to definition, built once before any contract is checked, so a second \
                declaration would silently shadow the first and change what every contract that \
                mentions the name means.",
        example: "logic fn p(a : Int) : Bool = a >= 0\nlogic fn p(a : Int) : Bool = a <= 0\n\nfn \
                  f(x : Int) : Int = x",
        fix: "Rename one declaration, or delete the redundant one.",
    },
    Explanation {
        code: "E9990",
        title: "internal: logical IR was not well-sorted",
        prose: "The internal representation a contract compiles into failed its own \
                well-formedness check. That representation has no surface syntax, and the \
                elaborator already sorted every node before this check ran, so no source program \
                can produce an ill-sorted term directly. Reaching this means the compiler built a \
                malformed obligation.",
        example: "-- Internal compiler invariant, not reachable from any well-formed program.\n\
                  -- Hitting it is a compiler bug and warrants a report.",
        fix: "Report the bug with the source that triggered it. Removing or simplifying the \
              `requires`/`ensures` clause on the named function works around it meanwhile.",
    },
    Explanation {
        code: "E9991",
        title: "internal: typed effect lowering failed",
        prose: "Effect lowering could not produce a program that its independent verifier \
                accepts, or an internal table broke mid-lowering. The phase marker is never \
                forged around an unverified tree, so the compiler stops here rather than emitting \
                code whose effect behavior it cannot vouch for.",
        example: "-- Internal compiler invariant, not reachable from any well-formed program.\n\
                  -- Hitting it is a compiler bug and warrants a report.",
        fix: "Report the bug with the source that triggered it. Narrowing the handler or effect \
              row on the function named in the message often sidesteps it meanwhile.",
    },
    Explanation {
        code: "E9992",
        title: "internal: typed simplification did not converge",
        prose: "The typed Core simplifier kept rewriting past its runaway bound instead of \
                reaching a fixed point. Simplification is meant to be terminating, so exceeding \
                the bound means two rewrites are undoing each other rather than that the program \
                is large.",
        example: "-- Internal compiler invariant, not reachable from any well-formed program.\n\
                  -- Hitting it is a compiler bug and warrants a report.",
        fix: "Report the bug with the source that triggered it. Building with `--no-simplify`, or \
              at a lower `-O` level, works around it meanwhile.",
    },
    Explanation {
        code: "E9993",
        title: "internal: typed specialization could not preserve its scheme",
        prose: "Dictionary specialization could not build a plan that preserves the typed \
                witness: a dictionary arity disagreed with the Core signature, a builder was \
                incompatible with the parameter it would fill, or the erased result drifted from \
                the unspecialized tree. Specialization must be observationally invisible, so a \
                plan it cannot justify is refused rather than applied.",
        example: "-- Internal compiler invariant, not reachable from any well-formed program.\n\
                  -- Hitting it is a compiler bug and warrants a report.",
        fix: "Report the bug with the source that triggered it. Building with `--no-specialize` \
              works around it meanwhile.",
    },
    Explanation {
        code: "E9994",
        title: "internal: erasure changed the program",
        prose: "Erasing the type information from verified typed Core did not reproduce the \
                compatibility tree it was built from. Erasure is required to be the identity on \
                the underlying program, so any difference means the typed and untyped views have \
                diverged and neither can be trusted.",
        example: "-- Internal compiler invariant, not reachable from any well-formed program.\n\
                  -- Hitting it is a compiler bug and warrants a report.",
        fix: "Report the bug with the source that triggered it, ideally with the smallest program \
              that reproduces it.",
    },
    Explanation {
        code: "E9995",
        title: "internal: typed Core environment could not be built",
        prose: "The checked declarations could not be translated into the environment that typed \
                Core construction and verification run against, usually because a signature it \
                was handed is not one that environment can express. The declarations passed the \
                type checker, so the disagreement is between two compiler phases, not in the \
                source.",
        example: "-- Internal compiler invariant, not reachable from any well-formed program.\n\
                  -- Hitting it is a compiler bug and warrants a report.",
        fix: "Report the bug with the source that triggered it, including the item named in the \
              message.",
    },
    Explanation {
        code: "E9996",
        title: "internal: typed Core witness could not be constructed",
        prose: "The elaborator could not build the typed witness for a declaration: a function \
                had no declared Core signature, its parameter count disagreed with that \
                signature, or a subterm could not be given a well-typed witness. The program \
                already type-checked, so this is a gap between the checker and the elaborator.",
        example: "-- Internal compiler invariant, not reachable from any well-formed program.\n\
                  -- Hitting it is a compiler bug and warrants a report.",
        fix: "Report the bug with the source that triggered it; the message names the function \
              and the path within it.",
    },
    Explanation {
        code: "E9997",
        title: "internal: typed Core witness was rejected",
        prose: "The independent typed-Core checker rejected a witness the elaborator had built, \
                and lists each violated judgment with the function and path it occurred at. The \
                second checker exists precisely to catch this, so a rejection is a real \
                disagreement inside the compiler, never a diagnosis of the source program.",
        example: "-- Internal compiler invariant, not reachable from any well-formed program.\n\
                  -- Hitting it is a compiler bug and warrants a report.",
        fix: "Report the bug with the source that triggered it and the full list of violations.",
    },
    Explanation {
        code: "E9998",
        title: "internal: type-checker invariant violated",
        prose: "The type checker or elaborator broke one of its own invariants, so it stopped \
                instead of continuing on state it no longer trusts. This has no span, because the \
                fault is in the compiler's bookkeeping rather than at a place in the source.",
        example: "-- Internal compiler invariant, not reachable from any well-formed program.\n\
                  -- Hitting it is a compiler bug and warrants a report.",
        fix: "Report the bug with the source that triggered it. Shrinking the program until the \
              message disappears usually isolates the declaration to include in the report.",
    },
    Explanation {
        code: "E9999",
        title: "internal compiler error",
        prose: "An invariant broke while crossing a compiler API boundary, in a phase with no \
                more specific internal code of its own. The compiler stops and asks for a report \
                rather than producing an artifact it cannot justify.",
        example: "-- Internal compiler invariant, not reachable from any well-formed program.\n\
                  -- Hitting it is a compiler bug and warrants a report.",
        fix: "Report the bug with the source and the exact command that triggered it. Turning off \
              individual passes (`--no-inline`, `--no-simplify`, `--no-specialize`) narrows down \
              which phase to name in the report.",
    },
];
