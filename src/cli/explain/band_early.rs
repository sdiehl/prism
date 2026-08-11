//! Explanations for the type and scope bands: E1000-E2999.

use super::Explanation;

pub(super) const ENTRIES: &[Explanation] = &[
    Explanation {
        code: "E1000",
        title: "polymorphic recursion without a signature",
        prose: "A recursion group is checked monomorphically: inside the group, every\n\
                recursive call must use the one type the checker guessed for the\n\
                definition. This function calls itself at two different types, which is\n\
                polymorphic recursion, and inference cannot discover it unaided.",
        example: "fn walk(x) =\n  walk(1) + walk(\"s\")",
        fix: "Give the function an explicit signature (parameter and return annotations), \
              or make every recursive call use one type.",
    },
    Explanation {
        code: "E1001",
        title: "unknown type",
        prose: "A type annotation names a type no declaration in scope defines. Either the\n\
                `type` declaration is missing, the module exporting it was never\n\
                imported, or the name is misspelled. When a declared name is close, the\n\
                diagnostic suggests it.",
        example: "fn f(x : Widget) : Int =\n  0",
        fix: "Declare the type, import the module that exports it, or correct the spelling.",
    },
    Explanation {
        code: "E1002",
        title: "too many type arguments",
        prose: "A type constructor was applied to more arguments than it declares\n\
                parameters. `Option` takes one parameter, so `Option(Int, Bool)` supplies\n\
                one too many. The arity comes from the `type` declaration, so this is a\n\
                disagreement between the annotation and that declaration.",
        example: "fn f(x : Option(Int, Bool)) : Int =\n  0",
        fix: "Drop the extra arguments, or nest them in a type that does take them, such \
              as a tuple.",
    },
    Explanation {
        code: "E1003",
        title: "kind mismatch in a type argument",
        prose: "Type parameters carry kinds: `Type` for ordinary types, `Row` for effect\n\
                rows, `Nat` for dimension literals. This argument's syntax fixes it at one\n\
                kind while the constructor's parameter demands another, and a row literal\n\
                such as `{IO}` has no representation where a plain type is expected. A\n\
                bare type variable stays legal anywhere, since inference pins its kind.",
        example: "fn f(x : Option({IO})) : Int =\n  0",
        fix: "Supply an argument of the declared kind, and write an effect row in an \
              effect annotation (`! {IO}`), where a row belongs.",
    },
    Explanation {
        code: "E1004",
        title: "polymorphic type as a type argument",
        prose: "A type parameter ranges over monomorphic types, so a `forall` cannot be\n\
                passed as one. Prism does have higher-rank types, but only in function\n\
                argument and result positions and in declared data fields, not underneath\n\
                an arbitrary type constructor.",
        example: "fn f(x : List(forall a. a -> a)) : Int =\n  0",
        fix: "Wrap the polymorphic type in a data type with a polymorphic field, and use \
              that data type as the argument.",
    },
    Explanation {
        code: "E1005",
        title: "integer literal out of range",
        prose: "The literal does not fit the fixed-width integer type its context demands.\n\
                `I64` tops out at 2^63 - 1 and `U64` at 2^64 - 1. The check reads the\n\
                written literal, before any arithmetic runs on it.",
        example: "fn f() : U64 =\n  99999999999999999999999",
        fix: "Use a value inside the type's range, or use `Int`, which is arbitrary \
              precision.",
    },
    Explanation {
        code: "E1006",
        title: "unknown record constructor",
        prose: "The brace form `C { field = value }` builds a record, and `C` must be a\n\
                constructor some `type` declaration in scope introduces. No declaration\n\
                here does.",
        example: "fn main() : Unit ! {IO} =\n  println(Point { x = 1, y = 2 })",
        fix: "Declare the record type, import the module that exports it, or correct the \
              spelling.",
    },
    Explanation {
        code: "E1007",
        title: "constructor is not a record constructor",
        prose: "The constructor exists but was declared positionally, as `Circle(Int)`,\n\
                rather than with named fields, as `Circle { radius: Int }`. Only a\n\
                constructor with named fields accepts the brace form.",
        example: "type Shape = Circle(Int) | Square(Int)\n\nfn main() : Unit ! {IO} =\n  \
                  println(Circle { radius = 1 })",
        fix: "Apply the constructor positionally (`Circle(1)`), or redeclare it with named \
              fields.",
    },
    Explanation {
        code: "E1008",
        title: "missing fields in record construction",
        prose: "Building a record sets every field. The listed fields are fewer than the\n\
                constructor declares, and Prism supplies no implicit defaults: a\n\
                half-built record would be readable at a field nothing ever wrote.",
        example: "type Point = Point { x: Int, y: Int }\n\nfn main() : Unit ! {IO} =\n  \
                  println(Point { x = 1 })",
        fix: "Set the missing fields, or build from an existing value with the update form \
              `Point { ..p, x = 1 }`.",
    },
    Explanation {
        code: "E1009",
        title: "field access on a non-record type",
        prose: "`e.name` reads a field, so `e` must have a record type. The receiver's type\n\
                here has no fields at all. A receiver whose type is still unsolved reports\n\
                the same way, since the checker cannot find a field on a type it does not\n\
                yet know.",
        example: "fn f(x : Int) : Int =\n  x.field",
        fix: "Access a field of a record-typed value, or annotate the receiver so its \
              record type is known.",
    },
    Explanation {
        code: "E1010",
        title: "conflicting record update paths",
        prose: "A record update may name several paths at once, but no path may be a prefix\n\
                of another. Setting `pos` and `pos.x` in one update leaves the result\n\
                dependent on which of the two runs first, and Prism will not pick an order\n\
                for you.",
        example: "type Vec2 = Vec2 { x: Int, y: Int }\ntype Box = Box { pos: Vec2, n: Int }\n\
                  \nfn main() : Unit ! {IO} =\n  \
                  let b = Box { pos = Vec2 { x = 1, y = 2 }, n = 0 }\n  \
                  println({ b | pos = Vec2 { x = 0, y = 0 }, pos.x = 7 })",
        fix: "Merge the overlapping updates into one path, or sequence them as two separate \
              updates so the order is written down.",
    },
    Explanation {
        code: "E1011",
        title: "internal: optic path step survived desugaring",
        prose: "Optic steps (`each`, `[i]`, `?Ctor`, `(each where p)`) are lowered to plain\n\
                field paths during desugaring, so the typechecker only ever sees `.field`\n\
                steps in an update path. A surviving step means the desugarer left one\n\
                behind, which is a compiler bug rather than anything the program did.",
        example: "-- Not reachable from source: a backstop asserting the desugarer lowered\n\
                  -- every optic step before the typechecker walks the path.",
        fix: "Report the program that produced it; no change to the source is the right \
              repair.",
    },
    Explanation {
        code: "E1012",
        title: "update path descends into a non-record",
        prose: "A record update path walks one field at a time, and each step needs a record\n\
                to descend into. This segment tried to continue through a value whose type\n\
                has no fields, so there is nothing of that name to reach.",
        example: "type Box = Box { n: Int }\n\nfn main() : Unit ! {IO} =\n  \
                  let b = Box { n = 1 }\n  println({ b | n.x = 7 })",
        fix: "End the path at the last record-typed field, or give that field a record type.",
    },
    Explanation {
        code: "E1013",
        title: "update path through a multi-constructor type",
        prose: "Descending through a field means taking a value apart and rebuilding it, so\n\
                the compiler must know which constructor it holds. A type with several\n\
                constructors gives no single answer at compile time, so a plain field path\n\
                cannot pass through one.",
        example: "type Shape = Circle { radius: Int } | Square { side: Int }\n\n\
                  fn main() : Unit ! {IO} =\n  let s = Circle { radius = 1 }\n  \
                  println({ s | radius = 5 })",
        fix: "Match on the constructor first, or focus one alternative with a `?Ctor` step \
              in the path.",
    },
    Explanation {
        code: "E1014",
        title: "type does not support indexed assignment",
        prose: "`a[i] := v` writes through an index, and only `Array`, `List`, `HashMap`,\n\
                and `Tensor` support it. This receiver is indexable for reading but not\n\
                for writing: `s[i]` on a `String` yields a code point, yet a string is an\n\
                immutable sequence with no in-place write.",
        example: "fn main() : Unit ! {IO} =\n  var s := \"abc\"\n  s[0] := 65\n  println(s)",
        fix: "Build a new value instead of writing in place, or hold the data in a container \
              that supports writes, such as `Array`.",
    },
    Explanation {
        code: "E1015",
        title: "negation of an unsigned value",
        prose: "Unary minus is defined on `Int`, `I64`, and `Float`. `U64` has no negative\n\
                values, so negating one has no meaning, and wrapping around to a very\n\
                large positive would be a silent wrong answer rather than a result.",
        example: "fn f(x : U64) : U64 =\n  -x",
        fix: "Convert to a signed type before negating, or express the intent as a \
              subtraction from a larger value.",
    },
    Explanation {
        code: "E1016",
        title: "wrong number of arguments",
        prose: "The call supplies more arguments than the function takes. Supplying fewer is\n\
                not this error: a partial application is a value, and its function type is\n\
                what a later mismatch would report. Supplying more is an error because the\n\
                fully applied result is not itself a function.",
        example: "fn add(x : Int, y : Int) : Int =\n  x + y\n\nfn main() : Int =\n  add(1, 2, 3)",
        fix: "Pass exactly as many arguments as the signature declares.",
    },
    Explanation {
        code: "E1017",
        title: "call of a non-function",
        prose: "The expression in call position has a type that is not a function type, so\n\
                there is nothing to apply. Usually this is a stray pair of parentheses\n\
                around a value, or a local binding shadowing the function of the same\n\
                name.",
        example: "fn f(x : Int) : Int =\n  x(1)",
        fix: "Remove the call, or apply the function that was meant, checking that no local \
              binding shadows it.",
    },
    Explanation {
        code: "E1018",
        title: "unboxed values are not lowered",
        prose: "The unboxed surface (`#(...)`, `#{...}`, `.#field`) parses and typechecks,\n\
                but a projection the checker could not resolve has no known layout, and\n\
                elaboration refuses rather than guess one. The typechecker normally\n\
                reports the underlying problem first, so this fires as a backstop.",
        example: "-- A backstop: an unboxed projection reached elaboration with no recorded\n\
                  -- field resolution, so no layout is known for it.",
        fix: "Annotate the receiver so the projection resolves, or use a boxed tuple or a \
              declared record type instead of the unboxed form.",
    },
    Explanation {
        code: "E1019",
        title: "bad `OrNull` element type",
        prose: "`OrNull(T)` packs \"a `T` or nothing\" into one machine word by reserving the\n\
                null word, so `T` must never occupy that word itself. Heap types, tuples,\n\
                applied datatypes, and the tagged scalars (`Int`, `I64`, `U64`, `Bool`,\n\
                `String`) qualify. `Unit`, `Float`, `Char`, a function type, a nested\n\
                `OrNull`, and an element type inference never pinned do not.",
        example: "fn f(x : OrNull(Float)) : Int =\n  0",
        fix: "Use `Option(T)` when the element type does not qualify, or add an `OrNull(T)` \
              annotation so the element is a concrete qualifying type.",
    },
    Explanation {
        code: "E1020",
        title: "type variable used at two kinds",
        prose: "One signature is one scope, and a type variable in it has exactly one kind.\n\
                Here the same name stands once for an ordinary type (a parameter's type)\n\
                and once for an effect row (a row tail). Those are different kinds, so one\n\
                variable cannot be both.",
        example: "fn f(x : e, g : (Int) -> Int ! {IO | e}) : Int =\n  0",
        fix: "Rename one use so the type variable and the row variable are distinct names.",
    },
    Explanation {
        code: "E1021",
        title: "typed hole",
        prose: "`?name` is a deliberate hole. The checker types the program around it and\n\
                then reports what would have to go there: the expected type, the effects\n\
                permitted at that position, how many bindings are in scope, and every\n\
                in-scope binding whose type fits (marked `exact` when it matches the\n\
                expected type exactly). A hole is always an error, so a program holding\n\
                one never compiles; it is a question put to the checker, not a value.",
        example: "fn f(x : Int) : Int =\n  ?rest",
        fix: "Replace the hole with an expression of the reported type; the listed \
              candidates are the in-scope bindings that would typecheck there.",
    },
    Explanation {
        code: "E1022",
        title: "type mismatch",
        prose: "The central type error: the surrounding context demanded one type (an\n\
                annotation, a parameter's type, the other branch of an `if`) and the\n\
                expression produced another. The message names both, and the `in ...`\n\
                frames say which definition was under check when it happened.",
        example: "fn f() : Int =\n  true",
        fix: "Change the expression to produce the expected type, or change the annotation \
              to the type the expression really has.",
    },
    Explanation {
        code: "E1098",
        title: "type mismatch (no enclosing definition)",
        prose: "The same failure E1022 reports, printed from a checker path that had not\n\
                attached a definition frame. A mismatch moves onto E1022 as it gains that\n\
                context, so E1098 is what one prints when it escapes with no enclosing\n\
                definition at all.",
        example: "-- The same mismatch E1022 describes, reported before any enclosing\n\
                  -- definition frame is attached. See `prism explain E1022`.",
        fix: "Read it exactly as E1022: reconcile the expression with the expected type.",
    },
    Explanation {
        code: "E1099",
        title: "type is not indexable",
        prose: "`a[i]` is defined on `Array`, `List`, `HashMap`, `String`, and `Tensor`. The\n\
                receiver's type is none of those, so there is no indexing operation to\n\
                reach for.",
        example: "fn f(x : Int) : Int =\n  x[0]",
        fix: "Index one of the container types, or replace the index with a field access or \
              a function call that fits the receiver.",
    },
    Explanation {
        code: "E1998",
        title: "type error with no dedicated code",
        prose: "The catch-all for checker and elaboration failures that have not yet earned\n\
                their own code; the message carries the specific complaint. The most\n\
                common one is a `print`, `println`, or `\"{x}\"` interpolation whose\n\
                argument type is still a rigid type variable: with no static type, no\n\
                printer can render the value, and guessing one would make output depend\n\
                on which backend ran the program.",
        example: "fn label(x : a) : String =\n  \"value: {x}\"\n\nfn main() : Unit ! {IO} =\n  \
                  println(label(1))",
        fix: "Follow the message. For the polymorphic-print case, take a `Show` constraint \
              and call `show(x)`, or annotate the argument with a concrete type.",
    },
    Explanation {
        code: "E2000",
        title: "unbound variable",
        prose: "The name has no binder in scope: no parameter, no `let`, no top-level\n\
                definition, and no import provides it. Top-level names share one flat\n\
                namespace, so a name defined in another module needs that module\n\
                imported. When something in scope is spelled close by, the diagnostic\n\
                suggests it.",
        example: "fn main() : Int =\n  nope",
        fix: "Define or import the name, or correct the spelling to one already in scope.",
    },
    Explanation {
        code: "E2099",
        title: "scope error with no dedicated code",
        prose: "Resolution failures other than a plain unbound variable land here, each with\n\
                its own message: a qualified name whose module prefix was never imported,\n\
                or a `pub` export naming a definition the module does not actually have.",
        example: "fn main() : Unit ! {IO} =\n  println(Widget.build(1))",
        fix: "Import the module the qualifier names, drop the qualifier if the name is \
              local, or remove the export of a definition that does not exist.",
    },
];
