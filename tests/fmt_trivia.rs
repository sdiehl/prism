// Snapshot tests pinning comment and blank-line (trivia) preservation through
// the formatter, across every offside surface that can carry it. Inputs are
// inline rather than `.pr` fixtures so they stay out of the recursive
// `prism fmt --check` scan while letting us feed intentionally messy sources.
//
// Each case also asserts idempotence: formatting the formatter's own output
// must reproduce it, so a snapshot can never lock in an unstable layout.

fn fmt(src: &str) -> String {
    let once = prism::format(src).expect("case must parse");
    let twice = prism::format(&once).expect("formatted output must parse");
    assert_eq!(once, twice, "formatter is not idempotent on this case");
    once
}

macro_rules! trivia_case {
    ($name:ident, $src:expr) => {
        #[test]
        fn $name() {
            insta::assert_snapshot!(stringify!($name), fmt($src));
        }
    };
}

// Leading, between-statement, and pre-result comments in a function body.
trivia_case!(
    fn_body_statements,
    "fn main() =\n\
     \x20 -- bind the first\n\
     \x20 let x = 1\n\
     \x20 -- bind the second\n\
     \x20 let y = 2\n\
     \x20 -- combine them\n\
     \x20 x + y\n"
);

// Messy intra-line spacing still normalizes while keeping every comment.
trivia_case!(
    fn_body_messy_input,
    "fn  main ( ) =\n\
     \x20 -- leading\n\
     \x20 let   x  =  1\n\
     \x20 -- trailing\n\
     \x20 x\n"
);

// A comment trailing a binding on the same line stays on that line instead of
// being relocated above the next statement.
trivia_case!(
    trailing_same_line_comments,
    "fn test() =\n\
     \x20 let x = 1 -- trailing on x\n\
     \x20 let y = x + 2 -- and on y\n\
     \x20 y\n"
);

// Comments above match arms and inside an arm's body block.
trivia_case!(
    match_arm_comments,
    "fn classify(n : Int) : String =\n\
     \x20 -- dispatch on the value\n\
     \x20 match n of\n\
     \x20   -- the zero case\n\
     \x20   0 => \"zero\"\n\
     \x20   -- everything else\n\
     \x20   _ =>\n\
     \x20     -- build the label\n\
     \x20     let s = \"nonzero\"\n\
     \x20     s\n"
);

// Comments in each branch of an if / elif / else chain.
trivia_case!(
    if_elif_else_comments,
    "fn sign(n : Int) : Int =\n\
     \x20 if n == 0 then\n\
     \x20   -- exactly zero\n\
     \x20   0\n\
     \x20 elif n > 0 then\n\
     \x20   -- strictly positive\n\
     \x20   1\n\
     \x20 else\n\
     \x20   -- strictly negative\n\
     \x20   9\n"
);

// Comments in a `for` loop body.
trivia_case!(
    for_body_comments,
    "fn loop_it(xs : List(Int)) : Unit =\n\
     \x20 for x in xs do\n\
     \x20   -- visit each element\n\
     \x20   println(show(x))\n"
);

// Handler block: a comment above the first arm, between arms, and after the
// whole `with handler` block.
trivia_case!(
    handler_comments,
    "effect State\n\
     \x20 ctl get() : Int\n\
     \x20 ctl put(Int) : Unit\n\
     \n\
     fn run() : !{State} Int =\n\
     \x20 -- install the handler\n\
     \x20 with handler\n\
     \x20   -- read the cell\n\
     \x20   get(k) => k(42)\n\
     \x20   -- write the cell\n\
     \x20   put(v, k) => k(())\n\
     \x20 -- after the handler is in scope\n\
     \x20 let a = get()\n\
     \x20 a\n"
);

// A named handler instance carries the same trivia surfaces.
trivia_case!(
    named_handler_comments,
    "effect State\n\
     \x20 ctl get() : Int\n\
     \n\
     fn run() : !{State} Int =\n\
     \x20 -- a named handler\n\
     \x20 with h <- handler\n\
     \x20   get(k) => k(7)\n\
     \x20 -- use it\n\
     \x20 h.get()\n"
);

// A `let` whose value is itself a laid-out block.
trivia_case!(
    let_value_block_comments,
    "fn pick(b : Bool) : Int =\n\
     \x20 let r =\n\
     \x20   -- choose a branch\n\
     \x20   if b then\n\
     \x20     -- the yes side\n\
     \x20     1\n\
     \x20   else\n\
     \x20     -- the no side\n\
     \x20     2\n\
     \x20 r\n"
);

// Grouped comments and a blank line that deliberately separates two groups.
trivia_case!(
    grouped_and_blank_separated,
    "fn doc() : Int =\n\
     \x20 -- first group line one\n\
     \x20 -- first group line two\n\
     \n\
     \x20 -- second group after a blank divider\n\
     \x20 let x = 1\n\
     \x20 let y = 2\n\
     \x20 x + y\n"
);

// Top-level trivia: a header comment, comments between declarations, and a
// trailing comment after the final declaration.
trivia_case!(
    toplevel_comments,
    "-- module header\n\
     fn first() : Int = 1\n\
     -- between declarations\n\
     fn second() : Int = 2\n\
     -- dangling tail comment\n"
);

// try / catch arms.
trivia_case!(
    trycatch_comments,
    "error Boom\n\
     \n\
     fn guarded() : Int =\n\
     \x20 try\n\
     \x20   -- the risky part\n\
     \x20   throw Boom\n\
     \x20 catch\n\
     \x20   -- recover from Boom\n\
     \x20   Boom => 0\n"
);

// A trailing-lambda call whose block body carries comments.
trivia_case!(
    trailing_lambda_comments,
    "fn walk(xs : List(Int)) : Unit =\n\
     \x20 xs.foreach() fn(x)\n\
     \x20   -- handle one item\n\
     \x20   println(show(x))\n"
);

// `var` mutable bindings interleaved with comments.
trivia_case!(
    var_decl_comments,
    "fn counter() : Int =\n\
     \x20 -- start at zero\n\
     \x20 var n := 0\n\
     \x20 -- bump it\n\
     \x20 n := n + 1\n\
     \x20 n\n"
);

// A comment between call arguments must survive: the flat one-line join would
// drop it, so the formatter keeps the call in its laid-out source form.
trivia_case!(
    call_arg_comments,
    "fn main() : Int =\n\
     \x20 foo(\n\
     \x20   1,  -- keep me\n\
     \x20   2,\n\
     \x20 )\n"
);

// Comments inside a list literal are preserved the same way.
trivia_case!(
    list_element_comments,
    "fn main() : List(Int) =\n\
     \x20 [\n\
     \x20   1,  -- one\n\
     \x20   2,  -- two\n\
     \x20 ]\n"
);

// Comments inside a tuple literal are preserved the same way.
trivia_case!(
    tuple_element_comments,
    "fn main() =\n\
     \x20 (\n\
     \x20   1,  -- x coord\n\
     \x20   2,  -- y coord\n\
     \x20 )\n"
);
