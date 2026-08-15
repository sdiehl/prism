//! Explanations for the effect and handler band: E6000-E6999.

use super::Explanation;

pub(super) const ENTRIES: &[Explanation] = &[
    Explanation {
        code: "E6000",
        title: "declaration named twice",
        prose: "Two declarations of the same kind claim one name. Effects and \
                patterns each live in a single flat namespace, so a second \
                declaration cannot shadow the first; it would leave every use of \
                the name ambiguous. The error points at the later declaration.",
        example: "effect Tick\n  tick() : Unit\n\neffect Tick\n  tock() : Unit\n\nfn main() = println(1)",
        fix: "Rename one of the two, or merge their contents into a single \
              declaration.",
    },
    Explanation {
        code: "E6001",
        title: "cyclic type synonym or effect alias",
        prose: "A synonym or alias expands to itself, directly or through a chain \
                of other synonyms. Both forms are purely syntactic: they are \
                expanded before checking, so a cycle has no finite expansion. The \
                message prints the path that closed the loop.",
        example: "alias Read = {Write}\n\nalias Write = {Read}\n\nfn main() = println(1)",
        fix: "Break the cycle by inlining one side, or declare a real effect or \
              data type where a recursive definition is genuinely wanted.",
    },
    Explanation {
        code: "E6002",
        title: "unknown type synonym",
        prose: "Synonym expansion was asked to resolve a name that the program \
                does not declare as a type synonym. Expansion only recurses into \
                names it has already found in the synonym table, so this is a \
                defensive check on the expander itself rather than something a \
                source program reaches; an unknown type in a signature is reported \
                as an unknown type instead.",
        example: "-- Not reachable from source: a guard on the synonym expander.",
        fix: "Report the program that triggered it, since it indicates a compiler \
              bug rather than a mistake in the source.",
    },
    Explanation {
        code: "E6003",
        title: "unknown effect alias",
        prose: "Alias expansion was asked to resolve a name that the program does \
                not declare as an alias. As with type synonyms, expansion only \
                recurses into names already present in the alias table, so a \
                source program reaches the unknown-effect diagnostics instead.",
        example: "-- Not reachable from source: a guard on the alias expander.",
        fix: "Report the program that triggered it, since it indicates a compiler \
              bug rather than a mistake in the source.",
    },
    Explanation {
        code: "E6004",
        title: "wrong number of type synonym arguments",
        prose: "A parameterized type synonym was applied to a different number of \
                arguments than it declares parameters. A synonym is expanded by \
                substituting arguments for parameters one for one, so a partial or \
                over-saturated application has no expansion.",
        example: "alias Pair(a) = (a, a)\n\nfn fst(p : Pair(Int, Int)) : Int = 1\n\nfn main() = println(1)",
        fix: "Apply the synonym to exactly as many arguments as it has \
              parameters, or change the synonym's parameter list.",
    },
    Explanation {
        code: "E6005",
        title: "unknown effect in an alias",
        prose: "An effect alias lists a label that names neither a declared effect, \
                a built-in effect, nor another alias. An alias is a name for a set \
                of real labels, so every member must resolve before the alias can \
                be expanded into a row.",
        example: "effect Tick\n  tick() : Int\n\nalias App = {Tick, Missing}\n\nfn main() = println(1)",
        fix: "Declare the missing effect, correct the spelling, or drop the label \
              from the alias.",
    },
    Explanation {
        code: "E6006",
        title: "reserved effect name",
        prose: "The program declares an effect whose name the compiler reserves for \
                a seam of its own, such as the concurrency preemption seam or the \
                network boundary capability. Those names carry fixed meaning in \
                lowering, so a user declaration cannot take them over.",
        example: "effect Net\n  fetch() : String\n\nfn main() = println(1)",
        fix: "Rename the effect to something outside the reserved set; the message \
              names what the reserved effect is used for.",
    },
    Explanation {
        code: "E6007",
        title: "operation declared in two effects",
        prose: "Effect operations share one flat namespace, so a bare call like \
                `go()` names exactly one operation. Two effects declaring an \
                operation of the same name would make that call ambiguous, and the \
                clash is rejected at the second declaration. The stdlib's \
                operations count, so a user effect can collide with a library one.",
        example: "effect A\n  go() : Unit\n\neffect B\n  go() : Unit\n\nfn main() = println(1)",
        fix: "Rename one of the operations, or fold both effects into one \
              declaration if they really are the same operation.",
    },
    Explanation {
        code: "E6008",
        title: "pattern name clashes with a constructor",
        prose: "A `pattern` declaration takes a name that a data constructor \
                already uses. A match arm cannot tell which one was meant, since \
                both are written in constructor position, so the pattern \
                declaration is rejected.",
        example: "type Box = Box { v : Int }\n\npattern Box(n) for Box =\n  view \\(b) -> Some(b.v)\n\nfn main() = println(1)",
        fix: "Give the pattern a name of its own, distinct from every constructor \
              in scope.",
    },
    Explanation {
        code: "E6009",
        title: "class-dispatched pattern with a make clause",
        prose: "A pattern declared `for` a class deconstructs every instance type \
                by dispatching its view through a class method. Construction has no \
                such method to dispatch through, so a `make` clause has nothing to \
                build with and is rejected.",
        example: "class Peek(c)\n  peek : (c) -> Option(Int)\n\npattern First(n) for Peek =\n  view peek\n  make \\(n) -> n\n\nfn main() = println(1)",
        fix: "Drop the `make` clause, or declare the pattern for a concrete type \
              where both directions can be written.",
    },
    Explanation {
        code: "E6010",
        title: "class-dispatched pattern view is not a method name",
        prose: "A pattern declared `for` a class must name one of that class's \
                methods in its `view` clause; the method's signature is what types \
                the synthesized view. Anything else, such as a lambda, gives the \
                compiler no dictionary to dispatch through.",
        example: "class Peek(c)\n  peek : (c) -> Option(Int)\n\npattern First(n) for Peek =\n  view \\(x) -> peek(x)\n\nfn main() = println(1)",
        fix: "Write the bare method name as the view, as in `view peek`.",
    },
    Explanation {
        code: "E6011",
        title: "view names a method the class does not have",
        prose: "The `view` clause of a class-dispatched pattern names an \
                identifier that the named class does not declare as a method. The \
                view is resolved against the class's method list, so an unrelated \
                function is not a candidate even when one of that name exists.",
        example: "class Peek(c)\n  peek : (c) -> Option(Int)\n\npattern First(n) for Peek =\n  view sniff\n\nfn main() = println(1)",
        fix: "Use one of the class's own method names, or add the method to the \
              class.",
    },
    Explanation {
        code: "E6012",
        title: "view method is not a function",
        prose: "A class method used as a pattern view must have a function type: \
                the view is applied to the scrutinee. The named method has a \
                non-function type, such as a plain class constant, so there is \
                nothing to apply.",
        example: "class Zero(c)\n  zero : c\n\npattern First(n) for Zero =\n  view zero\n\nfn main() = println(1)",
        fix: "Point the view at a method whose type is a one-argument function, or \
              change the method's signature.",
    },
    Explanation {
        code: "E6013",
        title: "view method takes the wrong number of arguments",
        prose: "A pattern view receives exactly one value, the scrutinee, so the \
                class method behind it must take exactly one argument. The named \
                method takes some other number, and the synthesized view could not \
                be applied.",
        example: "class Cut(c)\n  cut_at : (c, Int) -> Option(Int)\n\npattern First(n) for Cut =\n  view cut_at\n\nfn main() = println(1)",
        fix: "Use a one-argument method as the view, or curry the extra arguments \
              away in a dedicated method.",
    },
    Explanation {
        code: "E6014",
        title: "pattern declared for an unknown type or class",
        prose: "The `for` clause of a `pattern` names neither a declared data type \
                nor a declared class. That name decides whether the view is a plain \
                lambda over one concrete type or a method dispatched through a \
                class dictionary, so an unknown name leaves the pattern untypeable.",
        example: "pattern First(n) for Nowhere =\n  view \\(x) -> Some(x)\n\nfn main() = println(1)",
        fix: "Declare the type or class, or correct the name in the `for` clause.",
    },
    Explanation {
        code: "E6015",
        title: "pattern clause is not a lambda",
        prose: "The `view` and `make` clauses of a pattern declared for a concrete \
                type are lambdas: the view binds the scrutinee, and the make binds \
                the pattern's arguments. A bare reference to an existing function \
                has no binder for the desugarer to lower against.",
        example: "type Point = Point { x : Int, y : Int }\n\nfn diag(p : Point) : Option(Int) =\n  if p.x == p.y then Some(p.x) else None\n\npattern Diag(n) for Point =\n  view diag\n\nfn main() = println(1)",
        fix: "Wrap the function in a lambda, as in `view \\(p) -> diag(p)`.",
    },
    Explanation {
        code: "E6016",
        title: "hand-written Stable instance",
        prose: "`Stable` carries a compiler-computed shape digest that pins a \
                type's wire layout. A hand-written instance could claim a digest \
                that does not describe the type, which would silently break \
                compatibility checking, so only the derived instance is accepted.",
        example: "import Wire (..)\n\ntype Point = Point { x : Int }\n\ninstance stablePoint : Stable(Point)\n  fn shape_digest(p) = 0\n\nfn main() = println(1)",
        fix: "Delete the instance and write `deriving (Stable)` on the type.",
    },
    Explanation {
        code: "E6017",
        title: "unknown class in a deriving clause",
        prose: "A `deriving` clause names a class the program does not declare and \
                the prelude does not provide. Deriving resolves the name before it \
                decides whether an instance can be generated, so an unknown class \
                fails first.",
        example: "type Point = Point { x : Int } deriving (Bogus)\n\nfn main() = println(1)",
        fix: "Correct the class name, or import the module that declares it.",
    },
    Explanation {
        code: "E6018",
        title: "class cannot be derived",
        prose: "The named class exists but has no derivation rule. Deriving is a \
                closed set: the compiler knows how to generate Eq, Ord, Show, Hash, \
                Serialize, Stable, Arbitrary, ToJson, FromJson, Plate, and Lens, \
                and nothing else. Any other class needs an instance written by hand.",
        example: "class Nudge(c)\n  nudge : (c) -> c\n\ntype Point = Point { x : Int } deriving (Nudge)\n\nfn main() = println(1)",
        fix: "Remove the class from the `deriving` clause and write an `instance` \
              for it.",
    },
    Explanation {
        code: "E6019",
        title: "Lens needs a single record constructor",
        prose: "A derived lens focuses a field that is present in every value of \
                the type. With more than one constructor there is no such field, so \
                the derivation is refused rather than generating a partial \
                accessor.",
        example: "type Shape = Circle { r : Int } | Square { s : Int } deriving (Lens)\n\nfn main() = println(1)",
        fix: "Derive Lens only for single-constructor records, and reach into a \
              multi-constructor type with a `?Ctor.field` path instead.",
    },
    Explanation {
        code: "E6020",
        title: "Lens needs named fields",
        prose: "The type has one constructor, but that constructor's arguments are \
                positional rather than named. A derived lens is named after the \
                field it focuses, so there is nothing to generate for a positional \
                constructor.",
        example: "type Wrap = Wrap(Int) deriving (Lens)\n\nfn main() = println(1)",
        fix: "Give the constructor named fields, as in `Wrap { value : Int }`.",
    },
    Explanation {
        code: "E6021",
        title: "Stable field is not itself Stable",
        prose: "A derived `Stable` instance serializes every field, so each field's \
                type must be Stable too. A field holding a function, or any other \
                value with no wire representation, cannot appear in a frozen \
                format.",
        example: "import Wire (..)\n\ntype Config = Config { retry : Int, on_fail : (Unit) -> Unit } deriving (Stable)\n\nfn main() = println(1)",
        fix: "Drop the offending field from the serialized type, or replace it \
              with data that is itself Stable.",
    },
    Explanation {
        code: "E6022",
        title: "empty string interpolation",
        prose: "An interpolated string literal reached desugaring with no pieces to \
                concatenate. The lexer already rejects an empty hole `{}` in a \
                string, so this is a guard on the desugarer rather than a state a \
                source program reaches.",
        example: "-- Not reachable from source: the lexer rejects an empty `{}` hole first.",
        fix: "Report the program that triggered it, since it indicates a compiler \
              bug rather than a mistake in the source.",
    },
    Explanation {
        code: "E6023",
        title: "stable block needs the wire classes in scope",
        prose: "A `stable` block generates encoders, decoders, and migrations that \
                are typed against the wire classes. Those classes are not in the \
                default prelude, so the block cannot be lowered until the module \
                that declares them is imported.",
        example: "stable Doc {\n  V1 = { title : String }\n}\n\nfn main() = println(1)",
        fix: "Add `import Wire (..)` at the top of the file.",
    },
    Explanation {
        code: "E6024",
        title: "rung extends a non-adjacent rung",
        prose: "Rungs in a `stable` block form a ladder: each one extends the rung \
                directly above it, so the shipped history is a single chain. A rung \
                that reaches back past its predecessor would fork the history into \
                two branches with no defined order.",
        example: "import Wire (..)\n\nstable Doc {\n  V1 = { title : String },\n  V2 = { ..V1, tag : Int = 0 },\n  V3 = { ..V1, note : String = \"\" }\n}\n\nfn main() = println(1)",
        fix: "Extend the immediately preceding rung, restating any field the \
              intermediate rung added if you meant to drop it.",
    },
    Explanation {
        code: "E6025",
        title: "new rung field needs a default",
        prose: "Upgrading an older value to a newer rung has to produce a value of \
                every field the newer rung declares. A field the previous rung did \
                not carry has no source value, so the rung must say what to fill it \
                with.",
        example: "import Wire (..)\n\nstable Doc {\n  V1 = { title : String },\n  V2 = { ..V1, tag : Int }\n}\n\nfn main() = println(1)",
        fix: "Give the new field a default, as in `tag : Int = 0`.",
    },
    Explanation {
        code: "E6026",
        title: "frozen rung changed shape",
        prose: "A rung marked `frozen` carries a committed shape digest, and the \
                digest the compiler recomputed from the current fields no longer \
                matches. A shipped version is immutable: values encoded by an \
                earlier build are still out there, and editing the rung would \
                silently change how they decode.",
        example: "import Wire (..)\n\nstable Doc {\n  V1 = { title : String } frozen \"0000000000000000\",\n  V2 = { ..V1, tag : Int = 0 }\n}\n\nfn main() = println(1)",
        fix: "Add a new rung instead of editing the frozen one; if the rung never \
              shipped, reseat its digest with `prism wire --accept`.",
    },
    Explanation {
        code: "E6027",
        title: "rung retypes a field without a converter",
        prose: "The newer rung gives an inherited field a different type. That is a \
                mutation rather than an addition, and no correspondence between the \
                old and new values can be inferred from the shapes alone, so the \
                block must supply the conversion itself.",
        example: "import Wire (..)\n\nstable Doc {\n  V1 = { title : String },\n  V2 = { ..V1, title : Int = 0 }\n}\n\nfn main() = println(1)",
        fix: "Add the converter the message names to the block's `migrations` \
              table, or keep the field's original type and add a new field \
              instead.",
    },
    Explanation {
        code: "E6028",
        title: "handler clause exceeds the operation's grade",
        prose: "An operation declared with a resumption grade promises how its \
                continuation is used: `once` resumes exactly once, in tail \
                position, and `never` does not resume at all. The clause here uses \
                the continuation in a way the grade forbids, such as resuming twice \
                or resuming outside tail position. The grade is what lets the \
                fastest lowering avoid capturing a continuation, so it is enforced, \
                not advisory.",
        example: "effect Poll\n  once poll() : Int\n\nfn use_it() : Int ! {Poll} = poll()\n\nfn main() =\n  let v =\n    handle use_it() with\n      poll() resume k => k(1) + k(2)\n      return r => r\n  println(v)",
        fix: "Resume within the declared grade, or relax the operation's \
              declaration to a grade that admits what the handler does.",
    },
    Explanation {
        code: "E6029",
        title: "operation with a polymorphic return type",
        prose: "The operation's result type is a bare type variable, so its \
                continuation would have to produce a value at a type only the call \
                site knows. No handler can invent such a value, which leaves \
                aborting as the only sound interpretation.",
        example: "effect Bail\n  bail(String) : a\n\nfn main() =\n  let r =\n    handle bail(\"nope\") with\n      bail(m) resume k => k(0)\n      return v => v\n  println(r)",
        fix: "Handle the operation with a `never` clause, or give it a concrete \
              return type so a resuming handler can be written.",
    },
    Explanation {
        code: "E6030",
        title: "never clause resumes",
        prose: "A clause written `never` declares that the operation does not \
                return to its call site: the handler consumes the computation and \
                produces the block's result directly. The body mentions `resume`, \
                contradicting the declaration it was written under.",
        example: "effect Abort\n  abort(Int) : Int\n\nfn main() =\n  let v =\n    handle abort(7) with\n      never abort(code) => resume(code)\n      return r => r\n  println(v)",
        fix: "Drop the `resume` call, or write the clause as a resuming clause \
              with `resume k => ...`.",
    },
    Explanation {
        code: "E6031",
        title: "unknown operation in a handler",
        prose: "A clause of a named handler names an operation that no declared \
                effect provides. Every clause has to resolve to a real operation \
                before the handler's effect can be determined.",
        example: "effect Ask\n  ask() : Int\n\nfn main() =\n  with h <- handler\n    tell(n) resume k => k(())\n    return r => r\n  println(0)",
        fix: "Correct the operation name, or declare the effect that provides it.",
    },
    Explanation {
        code: "E6032",
        title: "named handler mixes two effects",
        prose: "A named handler is bound as a first-class instance and dispatched \
                through as `h.op(...)`, so it stands for exactly one effect. Clauses \
                drawn from two different effects give the instance no single effect \
                to represent.",
        example: "effect Ask\n  ask() : Int\n\neffect Tell\n  tell(Int) : Unit\n\nfn main() =\n  with h <- handler\n    ask() resume k => k(1)\n    tell(n) resume k => k(())\n    return r => r\n  println(h.ask())",
        fix: "Split the clauses into one named handler per effect, or use a plain \
              `handle` block, which may discharge several effects at once.",
    },
    Explanation {
        code: "E6033",
        title: "handler with no operation clauses",
        prose: "A handler carrying only a `return` clause handles nothing: there is \
                no effect for it to discharge and no instance operation to call \
                through it. The empty handler is almost always an unfinished edit.",
        example: "effect Ask\n  ask() : Int\n\nfn main() =\n  with h <- handler\n    return r => r\n  println(0)",
        fix: "Add a clause for at least one operation, or delete the handler and \
              keep the expression it wrapped.",
    },
    Explanation {
        code: "E6034",
        title: "handler instance escapes its block",
        prose: "A named handler instance is live only inside the `with` block that \
                installs it. The value produced here is a closure that still \
                performs the instance's operations, so calling it later would \
                dispatch to a handler that is already gone. Escape analysis rejects \
                that at the binding rather than letting it fail at run time.",
        example: "effect Ask\n  ask() : Int\n\nfn leak() : (Unit) -> Int =\n  with f <- handler\n    ask() resume k => k(5)\n    return r => r\n  \\(u) -> f.ask()\n\nfn main() = println(leak()(()))",
        fix: "Do the work that needs the instance inside the `with` block and \
              return its result, not a closure that captures the instance.",
    },
    Explanation {
        code: "E6035",
        title: "unknown constructor in a path step",
        prose: "A `?Ctor` step in an optic path focuses values built by that \
                constructor. The name here is not a constructor of any declared \
                type, so the step has no shape to match against.",
        example: "type Shape = Circle { radius : Int } | Square { side : Int }\n\nfn main() = println({ Circle { radius = 10 } | ?Blob.radius = 0 })",
        fix: "Correct the constructor name, or import the module that declares it.",
    },
    Explanation {
        code: "E6036",
        title: "constructor path step needs a field",
        prose: "A `?Ctor` step selects one alternative of a sum type. What follows \
                it must be one of that constructor's own fields, since the path \
                continues from inside the matched value. An index or traversal step \
                directly after `?Ctor` has no field to apply itself to.",
        example: "type Shape = Circle { radius : List(Int) } | Square { side : Int }\n\nfn main() = println({ Circle { radius = [1, 2] } | ?Circle[0] = 0 })",
        fix: "Name a field after the constructor, as in `?Circle.radius[0]`.",
    },
    Explanation {
        code: "E6037",
        title: "var cell escapes its block",
        prose: "A `var` binding is a mutable cell whose lifetime is the block that \
                declares it. The value produced here is a closure that still reads \
                or writes the cell, so calling it later would touch storage that no \
                longer exists.",
        example: "fn leak() : (Unit) -> Int =\n  var x := 0\n  \\(u) -> x + 1\n\nfn main() = println(leak()(()))",
        fix: "Return the cell's value rather than a closure over it, or thread the \
              state explicitly through a parameter or a State effect.",
    },
    Explanation {
        code: "E6038",
        title: "view pattern nested inside another pattern",
        prose: "A view pattern runs a function on the scrutinee and matches the \
                result, so it compiles to its own scrutinee test. It appears at the \
                top of a match arm, never inside another pattern where there is no \
                separate value to run the view against.",
        example: "type Box = Box { v : Int }\n\npattern Pos(n) for Box =\n  view \\(b) -> if b.v > 0 then Some(b.v) else None\n\nfn f(o : Option(Box)) : Int =\n  match o of\n    Some(Pos(n)) => n\n    _ => 0\n\nfn main() = println(f(None))",
        fix: "Match the outer constructor first, then apply the view pattern in a \
              nested `match` on the extracted value.",
    },
    Explanation {
        code: "E6039",
        title: "pattern applied to the wrong number of arguments",
        prose: "A `pattern` declaration fixes how many values it binds, and a use \
                site must bind exactly that many. The arm here supplies a different \
                count, so the view's result cannot be destructured against it.",
        example: "type Box = Box { v : Int }\n\npattern Pos(n) for Box =\n  view \\(b) -> if b.v > 0 then Some(b.v) else None\n\nfn f(b : Box) : Int =\n  match b of\n    Pos(n, m) => n\n    _ => 0\n\nfn main() = println(f(Box { v = 1 }))",
        fix: "Bind as many names as the pattern declares, or change the \
              declaration to bind the number you want.",
    },
    Explanation {
        code: "E6040",
        title: "match through a view pattern is not exhaustive",
        prose: "A view pattern matches whatever its view function chooses to \
                return, and the compiler cannot see inside that function to know \
                when it succeeds. A match built only from view patterns therefore \
                has no proof of coverage and could fall off the end at run time.",
        example: "type Point = Point { x : Int, y : Int }\n\npattern Diag(n) for Point =\n  view \\(p) -> if p.x == p.y then Some(p.x) else None\n\nfn f(p : Point) : Int =\n  match p of\n    Diag(n) => n\n\nfn main() = println(f(Point { x = 1, y = 1 }))",
        fix: "Add a catchall `_` arm giving the result for the values the view \
              rejects.",
    },
    Explanation {
        code: "E6041",
        title: "with is the last statement of a block",
        prose: "`with x <- f(..)` takes the rest of the block as its continuation: \
                the statements after it become the function passed to `f`. As the \
                final statement it has an empty continuation, which is almost \
                certainly not what was meant.",
        example: "fn cps(v, k) = k(v)\n\nfn main() =\n  println(0)\n  with x <- cps(1)",
        fix: "Move the statements the `with` should wrap below it, or call the \
              function directly if nothing follows.",
    },
    Explanation {
        code: "E6042",
        title: "handler instance used as a value",
        prose: "The name bound by `with h <- handler` denotes an installed handler, \
                not an ordinary value. It exists only to address operations, so it \
                cannot be returned, stored, or passed on; allowing that would let \
                it outlive the block that installed it.",
        example: "effect Ask\n  ask() : Int\n\nfn use_h() =\n  with h <- handler\n    ask() resume k => k(5)\n    return r => r\n  h\n\nfn main() = println(0)",
        fix: "Call the instance's operations as `h.op(...)` inside the block, and \
              return the result of that work.",
    },
    Explanation {
        code: "E6043",
        title: "pattern used as a bare value",
        prose: "A `pattern` declaration names a matcher, and with a `make` clause \
                it can also be applied to build a value. It is not a first-class \
                function, so mentioning its name without applying it has no \
                meaning.",
        example: "type Box = Box { v : Int }\n\npattern Pos(n) for Box =\n  view \\(b) -> if b.v > 0 then Some(b.v) else None\n  make \\(n) -> Box { v = n }\n\nfn main() = println(Pos)",
        fix: "Apply the pattern to its arguments, as in `Pos(3)`, or wrap it in a \
              lambda if a function value is wanted.",
    },
    Explanation {
        code: "E6044",
        title: "`?` used inside a larger expression",
        prose: "The `?` operator propagates a failure by returning early from the \
                enclosing function, so it governs the whole statement it appears \
                in. Buried inside a larger expression, the early exit would skip \
                part of an expression that has already begun to evaluate, so the \
                form is restricted to statement position.",
        example: "fn half(n) =\n  if n % 2 == 0 then Ok(n / 2) else Err(\"odd\")\n\nfn bad(n) = Ok(half(n)? + 1)\n\nfn main() = println(0)",
        fix: "Bind the result first, as in `let h = half(n)?`, then use `h` in the \
              larger expression.",
    },
    Explanation {
        code: "E6045",
        title: "pattern has no make clause",
        prose: "A pattern with only a `view` clause can deconstruct a value but not \
                build one. Using it in expression position asks for the \
                construction direction, which the declaration never defined.",
        example: "type Box = Box { v : Int }\n\npattern Pos(n) for Box =\n  view \\(b) -> if b.v > 0 then Some(b.v) else None\n\nfn main() = println(Pos(3).v)",
        fix: "Add a `make` clause to the pattern, or build the value with its \
              constructor directly.",
    },
    Explanation {
        code: "E6046",
        title: "handler instance has no such operation",
        prose: "A named handler instance answers exactly the operations its clauses \
                cover. The call addresses an operation the instance does not \
                handle, so there is nothing for the dot form to dispatch to.",
        example: "effect Ask\n  ask() : Int\n\nfn main() =\n  with h <- handler\n    ask() resume k => k(1)\n    return r => r\n  println(h.tell(1))",
        fix: "Call one of the operations the instance handles, or add a clause for \
              this one.",
    },
    Explanation {
        code: "E6047",
        title: "indexed assignment to a non-variable",
        prose: "`a[i] := v` updates an element in place, so its base has to name \
                storage that can be written. A literal or a computed expression has \
                no location to update, and the assignment would be lost.",
        example: "fn main() =\n  var xs := [1, 2, 3]\n  [1, 2][0] := 9\n  println(0)",
        fix: "Bind the collection to a `var` first, then index-assign through that \
              name.",
    },
    Explanation {
        code: "E6048",
        title: "assignment to an immutable binding",
        prose: "`let` introduces an immutable binding, and `:=` writes to a mutable \
                cell. Assigning to a `let` name would silently rebind what other \
                code has already read, so mutability is declared up front instead.",
        example: "fn main() =\n  let x = 1\n  x := 2\n  println(x)",
        fix: "Declare the binding with `var x := ...`, or compute a new value under \
              a new `let` name.",
    },
    Explanation {
        code: "E6049",
        title: "catch arm names an undeclared error",
        prose: "A `catch` arm matches a declared error by name. The name here has \
                no `error` declaration, so there is no payload shape to bind and no \
                throw site it could ever match.",
        example: "fn main() = println(try 1 catch { Malformed(m) => 2 })",
        fix: "Declare the error, as in `error Malformed(String)`, or correct the \
              name in the arm.",
    },
    Explanation {
        code: "E6050",
        title: "catch arm binds the wrong number of values",
        prose: "An `error` declaration fixes the payload a throw carries, and a \
                catch arm destructures exactly that payload. Binding a different \
                number of names leaves values unaccounted for or invents ones that \
                were never thrown.",
        example: "error Malformed(String)\n\nfn main() =\n  println(try 1 catch { Malformed(a, b) => 2 })",
        fix: "Bind one name per declared payload value, or change the `error` \
              declaration to carry what the arm expects.",
    },
    Explanation {
        code: "E6051",
        title: "invalid probe name",
        prose: "A probe is enabled by naming it in an environment variable, which \
                is read as a comma-separated list. Its name is therefore restricted \
                to letters, digits, underscore, dot, colon, and hyphen, so that \
                every declared probe stays addressable from the outside.",
        example: "fn main() : Unit ! {IO} =\n  probe \"bad name!\" do println(\"x\")\n  println(0)",
        fix: "Rename the probe using only the permitted characters, as in \
              `\"parse.tokens\"`.",
    },
    Explanation {
        code: "E6052",
        title: "reserved usage fact",
        prose: "Usage facts are written `@ fact` on a type. The name here parses as \
                a reserved fact that has no checker behind it yet. Accepting it \
                would let a program claim a contract nothing enforces, so the \
                reserved names are rejected rather than ignored.",
        example: "fn apply(f : ((Int) -> Int) @ unique, x : Int) : Int = f(x)\n\nfn main() = println(apply(\\(y) -> y + 1, 1))",
        fix: "Drop the annotation, or use one of the checked facts: `noalloc`, \
              `once`, `portable`, or `noescape`.",
    },
    Explanation {
        code: "E6053",
        title: "misplaced allocation certificate",
        prose: "`@ noalloc` certifies a whole function: it promises that calling it \
                allocates nothing. It is therefore written at the root of a \
                function's return annotation, not on a parameter or an inner type, \
                where there would be no call to certify.",
        example: "fn f(x : Int @ noalloc) : Int = x\n\nfn main() = println(f(1))",
        fix: "Move the annotation after the function's return type, as in \
              `fn f(x : Int) : Int @ noalloc = x`.",
    },
    Explanation {
        code: "E6054",
        title: "call names a parameter the function does not have",
        prose: "A named argument `p := e` is matched against the callee's parameter \
                list by name. No parameter of that function is called `p`, so the \
                argument has no slot to fill; a misspelled name is the usual cause.",
        example: "fn f(a, b := 0) = a + b\n\nfn main() = println(f(a := 1, z := 2))",
        fix: "Use one of the declared parameter names, or add the parameter to the \
              function.",
    },
    Explanation {
        code: "E6055",
        title: "argument given twice",
        prose: "Each parameter is filled once per call. The call supplies the same \
                parameter twice, whether by naming it twice or by naming a \
                parameter that a positional argument already filled, and the \
                compiler will not pick a winner.",
        example: "fn f(a, b := 0) = a + b\n\nfn main() = println(f(a := 1, a := 2))",
        fix: "Remove the duplicate argument, keeping the one you meant.",
    },
    Explanation {
        code: "E6056",
        title: "positional argument after a named argument",
        prose: "Positional arguments are matched by their place in the argument \
                list, which stops being meaningful once names have started \
                reordering the call. All positional arguments therefore come first.",
        example: "fn f(a, b := 0) = a + b\n\nfn main() = println(f(a := 1, 2))",
        fix: "Move the positional arguments before the named ones, or name them \
              too.",
    },
    Explanation {
        code: "E6057",
        title: "too many arguments in a named call",
        prose: "A call that uses any named argument is a complete call, so its \
                argument count is checked against the parameter list exactly. More \
                positional arguments were supplied than the function has \
                parameters.",
        example: "fn f(a, b := 0) = a + b\n\nfn main() = println(f(1, 2, 3, b := 4))",
        fix: "Drop the extra arguments, or add the parameters they were meant for.",
    },
    Explanation {
        code: "E6058",
        title: "call is missing a required argument",
        prose: "Naming any argument signals that the call is complete rather than a \
                partial application. A parameter with no default and no supplied \
                argument therefore has nothing to fill it, and the call cannot be \
                read as currying.",
        example: "fn f(a, b := 0) = a + b\n\nfn main() = println(f(b := 5))",
        fix: "Supply the missing argument, or give the parameter a default in the \
              declaration.",
    },
    Explanation {
        code: "E6059",
        title: "once parameter used more than once",
        prose: "A parameter marked `@ once` promises the value is called or passed \
                on at most once, and only directly. Using it twice, aliasing it \
                through a `let`, or capturing it under a lambda all count as \
                further use, since each of those makes a second call possible.",
        example: "fn twice(f : ((Int) -> Int) @ once, x : Int) : Int = f(f(x))\n\nfn main() = println(twice(\\(y) -> y + 1, 1))",
        fix: "Use the parameter exactly once, or drop the `@ once` annotation if \
              the contract is not really wanted.",
    },
    Explanation {
        code: "E6060",
        title: "portable closure captures a non-portable value",
        prose: "A `@ portable` closure may be moved to a fresh runtime, so \
                everything it captures has to travel with it: top-level functions, \
                constructors, portable-typed parameters, and portable scalar data. \
                A captured local closure, mutable cell, or handler operation is \
                bound to the runtime it was created in and is rejected by name.",
        example: "fn spawn_it(f : (() -> Int) @ portable) : Int = f()\n\nfn main() =\n  let n = 3\n  println(spawn_it(\\() -> n))",
        fix: "Pass the captured value in as an argument instead of closing over \
              it, or lift the computation to a top-level function.",
    },
    Explanation {
        code: "E6061",
        title: "noescape token escapes the callback",
        prose: "A `@ noescape` parameter is a scoped token: it is valid inside the \
                callback and no longer. Returning it, embedding it in returned \
                data, aliasing it out, or capturing it in another closure would all \
                let it be used after the call that lent it has finished.",
        example: "fn with_tok(f : (Int @ noescape) -> Int) : Int = f(1)\n\nfn main() = println(with_tok(\\(t) -> t))",
        fix: "Use the token only inside the callback and return a value derived \
              from it, not the token itself.",
    },
    Explanation {
        code: "E6062",
        title: "noescape callback is not checkable",
        prose: "The no-escape promise is verified by reading the callback's body, \
                so the argument has to be a form whose body the compiler can see: a \
                closure literal, a top-level function, or a parameter relaying the \
                same contract. A computed function value hides its body and cannot \
                be checked.",
        example: "fn with_tok(f : (Int @ noescape) -> Int) : Int = f(1)\n\nfn pick(b : Bool) : (Int) -> Int =\n  if b then \\(t) -> t + 1 else \\(t) -> t + 2\n\nfn main() = println(with_tok(pick(true)))",
        fix: "Pass a lambda or a named top-level function directly at the call \
              site.",
    },
    Explanation {
        code: "E6063",
        title: "definitions identical in behavior",
        prose: "Two or more definitions elaborate to the same content hash, so they \
                compute exactly the same function under different names. This is \
                reported when duplicate detection is enabled, and becomes an error \
                under its strict setting.",
        example: "fn bump_a(x : Int) : Int = x + 1\n\nfn bump_b(x : Int) : Int = x + 1\n\nfn main() = println(bump_a(0) + bump_b(0))",
        fix: "Keep one definition and have the others call it.",
    },
    Explanation {
        code: "E6064",
        title: "definition reimplements a standard library function",
        prose: "A definition has the same behavior hash as a function the standard \
                library already provides. The library version is tested, documented, \
                and shared across programs, so the local copy is flagged; under the \
                strict setting the reimplementation is an error.",
        example: "fn my_identity(x) = x\n\nfn main() = println(my_identity(1))",
        fix: "Delete the local definition and call the library function the \
              message names.",
    },
    Explanation {
        code: "E6065",
        title: "auto migration cannot be derived",
        prose: "`auto` derives a migration from the two rungs' shapes, which works \
                for purely additive steps. The edge here involves a field whose \
                type changed, and a rename, split, merge, or retype has no \
                correspondence the compiler can read off the shapes. It names the \
                fields that need a decision rather than guessing one.",
        example: "import Wire (..)\n\nstable Doc {\n  V1 = { title : String },\n  V2 = { ..V1, title : Int = 0 },\n  migrations {\n    V1 -> V2 = auto\n  }\n}\n\nfn main() = println(1)",
        fix: "Replace `auto` on that edge with an explicit \
              `version(upgrade = <fn>, downgrade = <fn>)`.",
    },
    Explanation {
        code: "E6066",
        title: "invalid migration edge",
        prose: "An edge in a `migrations` table names a pair of rungs the block \
                does not support: a rung it never declares, or a direction running \
                from a newer rung to an older one. Edges are declared in the \
                upgrade direction, and the reverse route is generated from them.",
        example: "import Wire (..)\n\nstable Doc {\n  V1 = { title : String },\n  V2 = { ..V1, tag : Int = 0 },\n  migrations {\n    V1 -> V9 = auto\n  }\n}\n\nfn main() = println(1)",
        fix: "Name two declared rungs, oldest first; the message says which part of \
              the edge is wrong.",
    },
    Explanation {
        code: "E6067",
        title: "locked migration drifted",
        prose: "The family has a committed lock manifest, and a re-derived \
                migration no longer matches the identity recorded in it. Once a \
                migration is locked, other builds and stored data depend on exactly \
                that behavior, so the compiler will not rewrite it implicitly. The \
                message names the changed direction, the old and new hashes, and \
                the derived loss paths.",
        example: "-- With a committed `.stable-lock` beside the file, editing a rung\n-- default changes the derived migration and `prism store lock` reports it.",
        fix: "Inspect the diff, then relock an unpublished family with \
              `prism store lock --accept`, or add a new rung or route so the old \
              behavior stays addressable.",
    },
    Explanation {
        code: "E6068",
        title: "or-pattern alternatives bind different names",
        prose: "The arm body runs whichever alternative matched, so every binder it \
                mentions has to be bound by all of them. An alternative missing one \
                of the names would leave that binder undefined in exactly the case \
                it matched.",
        example: "type Shape = Circle(Int) | Square(Int) | Dot\n\nfn area(s : Shape) : Int =\n  match s of\n    Circle(n) | Dot => n\n    Square(n) => n\n\nfn main() = println(area(Dot))",
        fix: "Bind the same names in every alternative, or split the odd \
              alternative into its own arm.",
    },
    Explanation {
        code: "E6069",
        title: "or-pattern expands to too many arms",
        prose: "Alternation is compiled by expanding an arm into one arm per \
                combination, so alternations in several argument positions multiply. \
                This arm crosses the expansion bound, and compiling it would produce \
                an arm list out of proportion to the source.",
        example: "type Bits = Bits(Int, Int, Int, Int, Int, Int, Int, Int, Int)\n\nfn low(b : Bits) : Int =\n  match b of\n    Bits(0 | 1, 0 | 1, 0 | 1, 0 | 1, 0 | 1, 0 | 1, 0 | 1, 0 | 1, 0 | 1) => 1\n    _ => 0\n\nfn main() = println(low(Bits(0, 0, 0, 0, 0, 0, 0, 0, 0)))",
        fix: "Split the nested alternations into separate arms, or match the \
              positions one at a time with a guard.",
    },
    Explanation {
        code: "E6070",
        title: "Plate cannot traverse a field",
        prose: "A derived `Plate` traversal walks lists, optionals, tuples, and the \
                data types declared alongside the type being derived. The field here \
                reaches something outside that set, such as a function, a built-in \
                container, or a recursive occurrence at different type arguments, so \
                no traversal can be generated for it.",
        example: "type Node = Leaf(Int) | Thunk((Int) -> Node) deriving (Plate)\n\nfn main() = println(1)",
        fix: "Remove the untraversable field from the derived type, or write the \
              `Plate` instance by hand and choose what the traversal visits.",
    },
    Explanation {
        code: "E6071",
        title: "reflect names an unknown declaration",
        prose: "`reflect fn f` and `reflect type T` render the source of a \
                declaration in the same file. The target here is not declared \
                there, so there is nothing to quote; reflection does not reach into \
                imported modules.",
        example: "fn main() : Unit ! {IO} =\n  println(reflect fn absent)",
        fix: "Name a `fn` or `type` declared in the same file, spelled as its \
              author wrote it.",
    },
    Explanation {
        code: "E6072",
        title: "two derived lenses claim one accessor name",
        prose: "A derived lens synthesizes `<field>_of` and `with_<field>`, named \
                after the field alone. Top-level names share one flat namespace \
                that holds one definition per name, so two record types deriving \
                Lens over a field of the same name would define each accessor \
                twice, at two unrelated types. The second derivation is refused \
                here, where both types can be named. The lens values are named \
                after their type, so those do not collide and that half of the \
                derivation is unaffected.",
        example: "type Point = Point { x : Int } deriving (Lens)\ntype Vec = Vec { x : String } deriving (Lens)\n\nfn main() = println(1)",
        fix: "Rename the field on one of the two types, or drop `Lens` from one \
              `deriving` clause and write that type's accessors by hand under \
              names of your own.",
    },
    Explanation {
        code: "E6073",
        title: "definition takes a name the prelude already opened",
        prose: "The prelude opens a set of library names into unqualified scope, \
                and a top-level definition of one of those names wins it for the \
                whole file. Every unqualified use then reaches the local \
                definition, including uses written before it and uses that meant \
                the library one. The message names the library symbol that was \
                displaced, so the module it came from is visible. Under the strict \
                setting the capture is an error.",
        example: "fn count(xs) = 0\n\nfn main() = println(count([1, 2]))",
        fix: "Rename the local definition, or keep the name and call the library \
              function by its qualified name where you meant it.",
    },
];
