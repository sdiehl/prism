//! Explanations for the class, pattern, and effect bands: E3000-E5999.
//!
//! `E3xxx` covers classes, instances, and their resolution; `E4xxx` covers
//! patterns and match coverage; `E5xxx` covers effect rows and handlers.

use super::Explanation;

pub(super) const ENTRIES: &[Explanation] = &[
    Explanation {
        code: "E3000",
        title: "constrained function without full annotations",
        prose: "A function with a `given` clause is resolved against its declared signature: \
                the compiler reads the constraint off the annotation and hands the caller an \
                instance for it. Inference cannot fill that in, because the constraint has to \
                be checked before the body is inferred. This function carries constraints but \
                leaves a parameter type or its return type unwritten.",
        example: "class Shape(a)
  area : (a) -> Float

fn describe(x) given Shape(a) = area(x)

fn main() : Int = 0",
        fix: "Annotate every parameter and the return type, or drop the `given` clause.",
    },
    Explanation {
        code: "E3001",
        title: "unknown class in a constraint",
        prose: "A `given` clause, an instance head, or an instance context named a class that \
                no `class` declaration in scope defines. Class names resolve against the \
                program's own declarations plus the imported prelude, and there is no implicit \
                class.",
        example: "fn describe(x : a) : Int given Nope(a) = 0

fn main() : Int = 0",
        fix: "Declare the class, fix the spelling, or import the module that declares it.",
    },
    Explanation {
        code: "E3002",
        title: "explicit instance selection without a named function",
        prose: "`f(args, using inst)` picks by hand the instance that fills `f`'s class \
                constraints. The compiler reads that constraint list off the name `f`, so the \
                callee has to be a name it can look up. Here the callee was an expression (a \
                lambda, an application, a projection), which carries no constraint list to \
                fill.",
        example: r"class Shape(a)
  area : (a) -> Float

instance shapeInt : Shape(Int)
  fn area(_x) = 1.0

fn main() : Float = (\(x) -> 1.0)(2, using shapeInt)",
        fix: "Bind the function to a name and call that name with `using`, or drop the \
              `using` and let resolution choose the instance.",
    },
    Explanation {
        code: "E3003",
        title: "wrong number of explicit instance arguments",
        prose: "`using` supplies one instance per class constraint on the callee, in the order \
                the constraints are declared. The compiler counted the names after `using` and \
                found a different number than the `given` clause declares. Selection is all or \
                nothing: there is no form that fixes some constraints by hand and resolves the \
                rest.",
        example: "class Shape(a)
  area : (a) -> Float

instance shapeInt : Shape(Int)
  fn area(_x) = 1.0

fn twice(x : a) : Float given Shape(a) = area(x) + area(x)

fn main() : Float = twice(1, using shapeInt, shapeInt)",
        fix: "Give exactly as many instance names as the function has constraints, or drop \
              `using`.",
    },
    Explanation {
        code: "E3004",
        title: "explicit instance selection on an unconstrained function",
        prose: "`using` names the instances that fill a function's class constraints. The \
                function named here has none, so the instances have nothing to fill.",
        example: "class Shape(a)
  area : (a) -> Float

instance shapeInt : Shape(Int)
  fn area(_x) = 1.0

fn plain(x : Int) : Int = x

fn main() : Int = plain(1, using shapeInt)",
        fix: "Drop the `using` clause, or add the constraint to the function with a `given` \
              clause.",
    },
    Explanation {
        code: "E3005",
        title: "ambiguous class constraint",
        prose: "A class constraint is discharged at each call site by resolving it against the \
                types the call fixes. A constraint whose type mentions no type variable of the \
                signature, or mentions one the signature does not quantify, is never \
                determined by a call, so no call site could choose an instance for it.",
        example: "class Shape(a)
  area : (a) -> Float

fn constant(x : Int) : Int given Shape(a) = x

fn main() : Int = constant(1)",
        fix: "Mention the constrained type variable in a parameter or in the return type, or \
              drop the constraint.",
    },
    Explanation {
        code: "E3006",
        title: "instance method performs an undeclared effect",
        prose: "A class method signature fixes the effects its implementations may perform, \
                and a signature written without an effect row is pure. This instance's method \
                body performs an effect the class signature does not permit. A method whose \
                row is universally quantified obligates every implementation to be parametric \
                in effects; it is not permission to pick a concrete one.",
        example: "class Loud(a)
  loud : (a) -> Int

instance loudInt : Loud(Int)
  fn loud(x) =
    println(x)
    x

fn main() : Int = loud(3)",
        fix: "Make the method body effect-free, or declare the effect on the class method's \
              signature so every instance may perform it.",
    },
    Explanation {
        code: "E3007",
        title: "cyclic instance resolution",
        prose: "Instance resolution keeps a stack of the goals it is discharging. If an \
                identical `Class(Type)` goal reappears on that stack the search would not \
                terminate, so the compiler reports the cycle instead of looping. The \
                declaration-time restrictions make this unreachable in practice: an instance \
                head is a type constructor over distinct variables, an instance context \
                constrains only those variables, and the superclass graph is checked acyclic, \
                so every child goal is strictly smaller than its parent.",
        example: "-- Not reachable from a well-formed program: the head and context
-- restrictions make every resolution step shrink the goal.",
        fix: "Break the loop in the instance context that reintroduces the goal already \
              being resolved.",
    },
    Explanation {
        code: "E3008",
        title: "instance resolution too deep",
        prose: "Instance resolution follows an instance's context into sub-goals. A search \
                that keeps growing without ever repeating a goal exactly cannot be caught by \
                the cycle check, so a fixed depth budget backstops it. This constraint needed \
                more than 32 nested resolution steps.",
        example: "class Size(a)
  size : (a) -> Int

instance sizeList : Size([a]) given Size(a)
  fn size(_xs) = 0

alias Deep(a) = [[[[[[a]]]]]]

fn go(x : Deep(Deep(Deep(Deep(Deep(Deep(Int))))))) : Int = size(x)

fn main() : Int = 0",
        fix: "Resolve the constraint at a shallower type, or add a direct instance for the \
              type in question so the search stops at the first step.",
    },
    Explanation {
        code: "E3009",
        title: "unknown instance name",
        prose: "`using` names an instance by the name its `instance` declaration gave it. No \
                instance with this name is in scope.",
        example: "class Shape(a)
  area : (a) -> Float

instance shapeInt : Shape(Int)
  fn area(_x) = 1.0

fn twice(x : a) : Float given Shape(a) = area(x) + area(x)

fn main() : Float = twice(1, using nope)",
        fix: "Correct the name to a declared instance, or drop the `using` clause.",
    },
    Explanation {
        code: "E3010",
        title: "instance is for the wrong class",
        prose: "The instance named after `using` belongs to a different class than the \
                constraint it was handed to fill. Explicit selection replaces resolution, so \
                the named instance has to be an instance of exactly the constrained class.",
        example: r#"class Shape(a)
  area : (a) -> Float

class Named(a)
  label : (a) -> String

instance namedInt : Named(Int)
  fn label(_x) = "int"

fn twice(x : a) : Float given Shape(a) = area(x) + area(x)

fn main() : Float = twice(1, using namedInt)"#,
        fix: "Name an instance of the class the function's `given` clause declares.",
    },
    Explanation {
        code: "E3011",
        title: "ambiguous instance during resolution",
        prose: "Several instances share a head type and none is designated canonical, so \
                implicit resolution has no deterministic choice. Coherence checking rejects \
                undesignated duplicates where they are declared (E3034), so reaching this is a \
                backstop on the instance table rather than a reachable program error.",
        example: "-- Not reachable from a well-formed program: duplicate undesignated
-- instances are rejected where they are declared, as E3034.",
        fix: "Designate one instance for the head with `canonical Class(Type) = name`.",
    },
    Explanation {
        code: "E3012",
        title: "no instance for a class constraint",
        prose: "A class method, or a `given` constraint on a function being called, was used \
                at a type that has no instance of the class. Resolution looks up the head of \
                the type in the instance table and found nothing there.",
        example: r#"class Shape(a)
  area : (a) -> Float

instance shapeInt : Shape(Int)
  fn area(_x) = 1.0

fn main() : Float = area("square")"#,
        fix: "Write an instance for the type, add the class to the type's `deriving` clause, \
              or add the constraint to the enclosing function's `given` clause so its caller \
              supplies the instance.",
    },
    Explanation {
        code: "E3013",
        title: "explicitly selected instance does not match the type",
        prose: "The instance named after `using` is for a different head type than the one the \
                constraint is being resolved at. Explicit selection does not convert anything: \
                the chosen instance's head still has to unify with the type at the call site.",
        example: "class Shape(a)
  area : (a) -> Float

instance shapeFloat : Shape(Float)
  fn area(x) = x

fn twice(x : a) : Float given Shape(a) = area(x) + area(x)

fn main() : Float = twice(1, using shapeFloat)",
        fix: "Pass the instance whose head matches the argument type, or drop `using` and \
              let resolution pick.",
    },
    Explanation {
        code: "E3014",
        title: "constraint type not yet inferred",
        prose: "Resolving a class constraint needs the head constructor of its type. Here the \
                type is still an unsolved inference variable at the point the constraint has \
                to be discharged, typically an empty literal or a value nothing in the \
                surrounding code pins down, so no instance can be chosen.",
        example: "class Size(a)
  size : (a) -> Int

instance sizeList : Size([a]) given Size(a)
  fn size(_xs) = 0

fn main() : Int = size([])",
        fix: "Annotate the expression or the binding so its type is fixed before the \
              constraint is resolved.",
    },
    Explanation {
        code: "E3015",
        title: "constraint on a rigid type variable",
        prose: "A class method was used at a type variable of the enclosing signature. A rigid \
                variable stands for every type its caller may pick, so no single instance can \
                be chosen here; the instance has to arrive from the caller.",
        example: "class Size(a)
  size : (a) -> Int

fn twice(x : a) : Int = size(x) + size(x)

fn main() : Int = 0",
        fix: "Add `given Class(var)` to the enclosing function so each call site supplies \
              the instance.",
    },
    Explanation {
        code: "E3016",
        title: "superclass cycle",
        prose: "A class may name superclasses, and each becomes an obligation discharged along \
                that chain, so the superclass graph has to be acyclic. Following the edges \
                from this class came back to the class it started from.",
        example: "class Up(a) given Down(a)
  up : (a) -> Int

class Down(a) given Up(a)
  down : (a) -> Int

fn main() : Int = 0",
        fix: "Remove one of the superclass edges on the cycle.",
    },
    Explanation {
        code: "E3017",
        title: "duplicate class declaration",
        prose: "Two `class` declarations share a name. Classes live in one flat namespace, so \
                the second declaration has no way to be told apart from the first at a use \
                site.",
        example: "class Shape(a)
  area : (a) -> Float

class Shape(a)
  perimeter : (a) -> Float

fn main() : Int = 0",
        fix: "Rename one of the classes, or delete the duplicate declaration.",
    },
    Explanation {
        code: "E3018",
        title: "class method is not a function",
        prose: "A class method is dispatched on the class parameter, and the dispatch happens \
                on an argument, so every method signature has to be a function type. A method \
                declared at a plain value type gives resolution nothing to select an instance \
                from.",
        example: "class Zeroed(a)
  zero : a

fn main() : Int = 0",
        fix: "Give the method a function type that takes the class parameter, or move the \
              value out of the class into an ordinary definition.",
    },
    Explanation {
        code: "E3019",
        title: "class method does not mention the class parameter",
        prose: "Every method of a class has to mention the class parameter somewhere in its \
                signature; that occurrence is what an instance is selected by. A method that \
                never mentions it would be the same function for every instance, and no call \
                site could say which one it meant.",
        example: "class Shape(a)
  units : (Int) -> Int

fn main() : Int = 0",
        fix: "Mention the class parameter in an argument type or the return type, or make \
              the method an ordinary top-level function.",
    },
    Explanation {
        code: "E3020",
        title: "class method clashes with an existing definition",
        prose: "Class methods live in the same flat top-level namespace as functions, so a \
                method name may not repeat a name already defined. There is no shadowing that \
                would let a use site pick between the two.",
        example: "fn area(x : Int) : Int = x

class Shape(a)
  area : (a) -> Float

fn main() : Int = 0",
        fix: "Rename the class method, or rename the definition it collides with.",
    },
    Explanation {
        code: "E3021",
        title: "instance name clashes with an existing definition",
        prose: "Instances are named values, so an instance name shares the top-level namespace \
                with functions, constants, and other instances. This name is already taken.",
        example: "class Shape(a)
  area : (a) -> Float

instance shapeInt : Shape(Int)
  fn area(_x) = 1.0

instance shapeInt : Shape(Float)
  fn area(x) = x

fn main() : Int = 0",
        fix: "Rename the instance to a name no other top-level definition uses.",
    },
    Explanation {
        code: "E3022",
        title: "unknown superclass",
        prose: "A class named a superclass that no `class` declaration in scope defines. The \
                compiler reports it when it checks an instance of the class, because each \
                superclass becomes an obligation that instance has to carry.",
        example: "class Shape(a) given Sized(a)
  area : (a) -> Float

instance shapeInt : Shape(Int)
  fn area(_x) = 1.0

fn main() : Int = 0",
        fix: "Declare the superclass, fix the spelling, or remove it from the class's \
              `given` clause.",
    },
    Explanation {
        code: "E3023",
        title: "instance head is not a type constructor",
        prose: "An instance head has to be a primitive type or a data type constructor. \
                Function types, tuples of non-variables, and other structural types have no \
                nominal head for the instance table to key on, so resolution could not look \
                them up.",
        example: "class Shape(a)
  area : (a) -> Float

instance shapeFn : Shape((Int) -> Int)
  fn area(_f) = 1.0

fn main() : Int = 0",
        fix: "Wrap the type in a data declaration and write the instance for that data type.",
    },
    Explanation {
        code: "E3024",
        title: "instance head arguments are not distinct variables",
        prose: "The arguments of an instance head must be distinct type variables: \
                `Shape([a])`, not `Shape([Int])` and not `Shape(Pair(a, a))`. Lookup keys on \
                the head constructor alone, so an instance written at a specialized argument \
                could not be told apart from one for the general case, and which of the two \
                applied would depend on declaration order.",
        example: "class Shape(a)
  area : (a) -> Float

instance shapeInts : Shape([Int])
  fn area(_xs) = 1.0

fn main() : Int = 0",
        fix: "Generalize the head arguments to distinct variables and put the specialization \
              in the instance context, as in `instance i : Shape([a]) given Shape(a)`.",
    },
    Explanation {
        code: "E3025",
        title: "instance context is not over the head's variables",
        prose: "An instance context may constrain only the type variables of its head, each on \
                its own. A context over a compound type or over a variable the head does not \
                bind does not make the resolution goal smaller, so the search would have no \
                reason to terminate.",
        example: "class Shape(a)
  area : (a) -> Float

instance shapeList : Shape([a]) given Shape([a])
  fn area(_xs) = 1.0

fn main() : Int = 0",
        fix: "Constrain a bare head variable, as in `given Shape(a)` for the head \
              `Shape([a])`.",
    },
    Explanation {
        code: "E3026",
        title: "duplicate method in an instance",
        prose: "An instance implements each of its class's methods exactly once. Two \
                definitions of the same method name appear in this instance block, and nothing \
                chooses between them.",
        example: "class Shape(a)
  area : (a) -> Float

instance shapeInt : Shape(Int)
  fn area(_x) = 1.0
  fn area(_x) = 2.0

fn main() : Int = 0",
        fix: "Keep one definition and delete the other.",
    },
    Explanation {
        code: "E3027",
        title: "instance defines a method the class does not declare",
        prose: "An instance block may only define methods its class declares. This name is not \
                one of them, so there is no signature to check the definition against and no \
                call site that would reach it.",
        example: "class Shape(a)
  area : (a) -> Float

instance shapeInt : Shape(Int)
  fn area(_x) = 1.0
  fn volume(_x) = 2.0

fn main() : Int = 0",
        fix: "Correct the method name, add the method to the class declaration, or delete \
              the definition.",
    },
    Explanation {
        code: "E3028",
        title: "instance method carries annotations",
        prose: "An instance method takes its whole signature from the class declaration, \
                specialized at the instance head: parameter types, return type, effect row, \
                and constraints are all fixed there. Repeating them on the instance would let \
                the two spellings drift apart.",
        example: "class Shape(a)
  area : (a) -> Float

instance shapeInt : Shape(Int)
  fn area(x : Int) : Float = 1.0

fn main() : Int = 0",
        fix: "Delete the annotations and write the method's parameters bare.",
    },
    Explanation {
        code: "E3029",
        title: "instance method arity does not match the class",
        prose: "An instance method binds exactly as many parameters as the class method's \
                signature takes. The definition here binds a different number, so it cannot \
                have the type the class declared.",
        example: "class Shape(a)
  area : (a) -> Float

instance shapeInt : Shape(Int)
  fn area(_x, _y) = 1.0

fn main() : Int = 0",
        fix: "Bind the same number of parameters the class method's signature declares.",
    },
    Explanation {
        code: "E3030",
        title: "instance is missing class methods",
        prose: "An instance implements every method its class declares; a class method has no \
                default definition to fall back on, so an omitted method would leave a call \
                with nothing to dispatch to.",
        example: "class Shape(a)
  area : (a) -> Float
  name : (a) -> String

instance shapeInt : Shape(Int)
  fn area(_x) = 1.0

fn main() : Int = 0",
        fix: "Define the listed methods in the instance block, or remove them from the \
              class.",
    },
    Explanation {
        code: "E3031",
        title: "canonical head is not a type constructor",
        prose: "`canonical Class(Type) = name` designates the instance implicit resolution \
                picks for a head. The type it names is looked up in the same instance table, \
                so like an instance head it has to be a primitive type or a data type \
                constructor.",
        example: "class Shape(a)
  area : (a) -> Float

instance shapeInt : Shape(Int)
  fn area(_x) = 1.0

canonical Shape((Int) -> Int) = shapeInt

fn main() : Int = 0",
        fix: "Name the same nominal head the instance was declared at.",
    },
    Explanation {
        code: "E3032",
        title: "canonical designation names a non-instance",
        prose: "`canonical Class(Type) = name` has to name an instance that was declared for \
                exactly that class and head. The name given here is not one, so there is \
                nothing for the designation to point at.",
        example: "class Shape(a)
  area : (a) -> Float

instance shapeInt : Shape(Int)
  fn area(_x) = 1.0

canonical Shape(Int) = nope

fn main() : Int = 0",
        fix: "Name one of the declared instances for that class and head.",
    },
    Explanation {
        code: "E3033",
        title: "duplicate canonical designation",
        prose: "A head has at most one canonical instance: the designation is what makes \
                implicit resolution deterministic, so two designations for the same class and \
                head would reintroduce the tie they exist to break.",
        example: "class Shape(a)
  area : (a) -> Float

instance shapeInt : Shape(Int)
  fn area(_x) = 1.0

instance shapeAlt : Shape(Int)
  fn area(_x) = 2.0

canonical Shape(Int) = shapeInt

canonical Shape(Int) = shapeAlt

fn main() : Int = 0",
        fix: "Keep one `canonical` declaration for the class and head.",
    },
    Explanation {
        code: "E3034",
        title: "multiple instances for one head",
        prose: "Two or more instances are declared for the same class and head type and none \
                is designated canonical. Implicit resolution would have to break the tie \
                silently, which would let a program's meaning depend on declaration order.",
        example: "class Shape(a)
  area : (a) -> Float

instance shapeInt : Shape(Int)
  fn area(_x) = 1.0

instance shapeAlt : Shape(Int)
  fn area(_x) = 2.0

fn main() : Float = area(1)",
        fix: "Designate one with `canonical Class(Type) = name`; the others stay reachable \
              through explicit selection, as in `f(x, using other)`.",
    },
    Explanation {
        code: "E4000",
        title: "unreachable match arm",
        prose: "Earlier arms of this `match` already cover every value this arm could match, \
                so it can never run. A wildcard, a bare variable pattern, or an arm whose \
                guard is statically true absorbs everything written after it.",
        example: "fn describe(n : Int) : Int =
  match n of
    x => 1
    0 => 2

fn main() : Int = describe(5)",
        fix: "Move the more specific arm above the one that shadows it, or delete the dead \
              arm.",
    },
    Explanation {
        code: "E4001",
        title: "non-exhaustive match",
        prose: "The scrutinee has values no arm covers, and the message names one of them as a \
                witness. Matches are total in Prism: there is no implicit fallthrough that \
                would fail at run time, so a gap is reported where it is written. A refutable \
                pattern in a `let` is checked the same way, since a `let` has only one arm.",
        example: "type Color = Red | Green | Blue

fn rank(c : Color) : Int =
  match c of
    Red => 1
    Green => 2

fn main() : Int = rank(Blue)",
        fix: "Add an arm for the missing pattern, or a `_` catchall.",
    },
    Explanation {
        code: "E4002",
        title: "suffixed literal in a pattern",
        prose: "A suffixed integer literal such as `1i64` or `1u64` names a fixed-width value. \
                Patterns match on `Int`, so a suffix in pattern position has no meaning and is \
                rejected rather than silently ignored.",
        example: "fn rank(n : Int) : Int =
  match n of
    1i64 => 1
    _ => 0

fn main() : Int = rank(1)",
        fix: "Drop the suffix and match on `Int`, or bind the value and compare it with `==` \
              in a guard.",
    },
    Explanation {
        code: "E4003",
        title: "unknown record constructor in a pattern",
        prose: "A record pattern `C { .. }` names a constructor that no data declaration in \
                scope defines, so the compiler has no field list to check the pattern against.",
        example: "type Point = Point { x: Int, y: Int }

fn get_x(p : Point) : Int =
  match p of
    Pointe { x = a, y = _b } => a

fn main() : Int = get_x(Point { x = 1, y = 2 })",
        fix: "Correct the constructor name, or declare the data type that provides it.",
    },
    Explanation {
        code: "E4004",
        title: "unknown field in a record pattern",
        prose: "A record pattern named a field its constructor does not declare. Fields are \
                matched by name against the constructor's declaration, so a name that is not \
                there cannot bind anything.",
        example: "type Point = Point { x: Int, y: Int }

fn get_z(p : Point) : Int =
  match p of
    Point { x = _a, y = _b, z = c } => c

fn main() : Int = get_z(Point { x = 1, y = 2 })",
        fix: "Correct the field name, or add the field to the constructor's declaration.",
    },
    Explanation {
        code: "E4005",
        title: "unknown constructor in a pattern",
        prose: "A constructor pattern named a constructor that no data declaration in scope \
                defines. An uppercase name in pattern position is looked up as a constructor; \
                only a lowercase name binds a new variable.",
        example: "type Color = Red | Green

fn rank(c : Color) : Int =
  match c of
    Red => 1
    Purple => 2
    Green => 3

fn main() : Int = rank(Red)",
        fix: "Correct the spelling, declare the constructor, or lowercase the name if it was \
              meant to bind a variable.",
    },
    Explanation {
        code: "E4006",
        title: "constructor pattern arity mismatch",
        prose: "A constructor pattern binds exactly as many sub-patterns as its constructor \
                declares fields. The pattern here binds a different number, so some field \
                would be left with nothing to match against.",
        example: "type Pair = MkPair(Int, Int)

fn first(p : Pair) : Int =
  match p of
    MkPair(a) => a

fn main() : Int = first(MkPair(1, 2))",
        fix: "Bind one sub-pattern per field, using `_` for the fields the arm ignores.",
    },
    Explanation {
        code: "E4007",
        title: "no such field on the type",
        prose: "A field read `x.f` needs the type of `x` to declare a field `f`. A \
                bare `.name` is always a field read and never a zero-argument call: `p.norm()` \
                calls `norm`, while `p.norm` looks for a field named `norm`.",
        example: "type Point = Point { x: Int, y: Int }

fn main() : Int =
  let p = Point { x = 1, y = 2 }
  p.z",
        fix: "Correct the field name, or add the parentheses if a call was meant.",
    },
    Explanation {
        code: "E4008",
        title: "legacy conflicting field types",
        prose: "Before v0.20, constructors of one datatype could not reuse a field name at\n\
                different types. Constructor-refined patterns now type each field from its own\n\
                arm, while an unrefined `x.f` projection is rejected separately as E1023.\n\
                E4008 remains reserved so its published identity is never reused.",
        example: "type Shape = Circle { size: Int } | Square { size: String }

fn main() : Int = 0",
        fix: "Upgrade to v0.20 or later and read the field after matching on its constructor.",
    },
    Explanation {
        code: "E4009",
        title: "incomplete record pattern",
        prose: "A record pattern without a `..` spread binds every field of its constructor. \
                That is what makes adding a field to a data type a compile error at each \
                pattern that reads it, rather than a silent wildcard over the new field.",
        example: "type Point = Point { x: Int, y: Int }

fn get_x(p : Point) : Int =
  match p of
    Point { x = a } => a

fn main() : Int = get_x(Point { x = 1, y = 2 })",
        fix: "List the remaining fields, or add `..` to ignore the rest.",
    },
    Explanation {
        code: "E5000",
        title: "wrong number of effect type arguments",
        prose: "A parameterized effect is applied to exactly the number of type arguments its \
                `effect` declaration takes, everywhere it appears in a row.",
        example: "effect Emit(a)
  emit(a) : Unit

fn broadcast() : Unit ! {Emit(Int, String)} = emit(1)

fn main() : Int = 0",
        fix: "Give the effect the number of type arguments its declaration takes.",
    },
    Explanation {
        code: "E5001",
        title: "unknown effect",
        prose: "An effect row named a label that no `effect` declaration in scope defines. \
                Effect labels resolve against the program's declarations plus the imported \
                standard library; there is no implicitly declared effect.",
        example: "fn tally(n : Int) : Int ! {Ledger} = n

fn main() : Int = 0",
        fix: "Declare the effect, fix the spelling, or import the module that declares it.",
    },
    Explanation {
        code: "E5002",
        title: "top-level constant performs an effect",
        prose: "A top-level constant is a top-level `let`, evaluated with no handler \
                installed, so its initializer has to be effect-free. The effects reported are \
                the body's inferred row, not a syntactic approximation.",
        example: r#"let banner = println("hi")

fn main() : Int = 0"#,
        fix: "Move the effectful work into a function and call it where a handler is in \
              scope, leaving the constant pure.",
    },
    Explanation {
        code: "E5003",
        title: "borrow parameter on an effectful function",
        prose: "A `borrow` parameter is passed without transferring ownership: the caller \
                keeps the value alive across the call, and the callee must not extend its \
                lifetime. That calling convention requires an effect-free body, because an \
                effect can suspend the call and resume it after the caller has released the \
                value.",
        example: "fn noisy(borrow x : Int) : Int =
  println(x)
  x

fn main() : Int = noisy(3)",
        fix: "Drop `borrow` and take the parameter by ownership, or make the body \
              effect-free.",
    },
    Explanation {
        code: "E5004",
        title: "undeclared effect",
        prose: "The body performs an operation of an effect the declared row does not list, \
                and no handler inside the body discharges it. An annotated effect row is \
                exact: it is the full set of effects the function may leave for its caller.",
        example: "effect Emit
  emit(Int) : Unit

fn broadcast() : Unit ! {} = emit(1)

fn main() : Int = 0",
        fix: "Add the effect to the annotated row, or handle it inside the function.",
    },
    Explanation {
        code: "E5005",
        title: "unknown effect operation",
        prose: "A handler clause names an operation that belongs to no effect in scope. \
                Handler clauses are matched by operation name against the declared effects, so \
                an unknown name has no signature to check the clause against.",
        example: "effect Emit
  emit(Int) : Unit

fn main() : Int =
  handle 1 with {
    shout(n) resume k => k(()),
    return r => r
  }",
        fix: "Correct the operation name, or declare the effect that owns it.",
    },
    Explanation {
        code: "E5006",
        title: "incompatible effect instantiations",
        prose: "A parameterized effect is instantiated at one type per row. Two computations \
                in this body demand different instantiations of the same effect, so one row \
                cannot describe both.",
        example: r#"effect Emit(a)
  emit(a) : Unit

fn ints() : Unit ! {Emit(Int)} = emit(1)

fn strs() : Unit ! {Emit(String)} = emit("x")

fn both() : Unit ! {Emit(Int)} =
  ints()
  strs()

fn main() : Int = 0"#,
        fix: "Handle one of the instantiations inside the function, or widen the annotation \
              so both appear as separate labels.",
    },
    Explanation {
        code: "E5007",
        title: "unknown effect in a mask",
        prose: "`mask<E>(e)` hides effect `E` from the innermost enclosing handler so an outer \
                one sees it. The label named here is not a declared effect.",
        example: "fn main() : Int = mask<Nope>(1)",
        fix: "Correct the label, or declare the effect being masked.",
    },
    Explanation {
        code: "E5008",
        title: "duplicate handler clause",
        prose: "A handler binds each operation exactly once. Two clauses for one operation \
                would have to be resolved by an order the language does not fix, and letting \
                each consumer resolve it its own way would make the choice of lowering visible \
                in program output.",
        example: "effect Pick
  pick() : Int

fn main() : Int =
  handle pick() with {
    pick() resume k => k(11),
    pick() resume k => k(22),
    return r => r
  }",
        fix: "Merge the two clauses into one.",
    },
    Explanation {
        code: "E5009",
        title: "duplicate return clause",
        prose: "A handler carries at most one `return` clause, the one that wraps the value \
                the handled computation produces. A second has no defined meaning and is \
                rejected rather than silently shadowed.",
        example: "effect Pick
  pick() : Int

fn main() : Int =
  handle pick() with {
    pick() resume k => k(1),
    return r => r,
    return r => r + 1
  }",
        fix: "Keep one `return` clause.",
    },
    Explanation {
        code: "E5010",
        title: "handler clause arity mismatch",
        prose: "A handler clause binds exactly the parameters its operation declares, plus the \
                continuation named after `resume`. Both too few and too many are errors, \
                checked where the clause is written rather than left to fault at run time.",
        example: "effect St
  put(Int) : Unit

fn main() : Int =
  handle put(1) with {
    put(a, b) resume k => k(()),
    return r => 9
  }",
        fix: "Bind one parameter per declared operation parameter, plus the continuation.",
    },
    Explanation {
        code: "E5011",
        title: "incomplete handler",
        prose: "An unmarked `handle` promises to discharge the whole effect, so it implements \
                every operation the effect declares. This one omits an operation, which would \
                leave that operation unhandled when it is performed.",
        example: "effect Pair
  one() : Int
  two() : Int

fn main() : Int =
  handle one() + two() with {
    one() resume k => k(1),
    return r => r
  }",
        fix: "Add clauses for the missing operations, or write `handle e with partial { .. \
              }`, whose effect stays residual in the row for an outer handler to discharge.",
    },
    Explanation {
        code: "E5012",
        title: "borrow parameter with an open effect row",
        prose: "A `borrow` parameter requires a body that provably performs no effects. This \
                function's row is an open row variable shared with a parameter or with its \
                result, so it forwards effects through its own interface. An unconstrained row \
                tail is not a proof of purity: a forwarded effect could suspend the call and \
                capture the borrowed value.",
        example: r"fn invoke(borrow x : Int, f : (Unit) -> Unit ! {| e}) : Int =
  f(())
  x

fn main() : Int = invoke(1, \(_u) -> ())",
        fix: "Close the row by annotating the effects the function actually performs, or \
              drop `borrow`.",
    },
];
