use indoc::indoc;

// Snapshot tests for comment and blank-line (trivia) preservation through
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
            insta::with_settings!({
                snapshot_path => "../snapshots",
                prepend_module_to_snapshot => false,
            }, {
                insta::assert_snapshot!(concat!("fmt_trivia__", stringify!($name)), fmt($src));
            });
        }
    };
}

// Leading, between-statement, and pre-result comments in a function body.
trivia_case!(
    fn_body_statements,
    indoc! {"
        fn main() =
          -- bind the first
          let x = 1
          -- bind the second
          let y = 2
          -- combine them
          x + y
    "}
);

// Messy intra-line spacing still normalizes while keeping every comment.
trivia_case!(
    fn_body_messy_input,
    indoc! {"
        fn  main ( ) =
          -- leading
          let   x  =  1
          -- trailing
          x
    "}
);

// A comment trailing a binding on the same line stays on that line instead of
// being relocated above the next statement.
trivia_case!(
    trailing_same_line_comments,
    indoc! {"
        fn test() =
          let x = 1 -- trailing on x
          let y = x + 2 -- and on y
          y
    "}
);

// Comments above match arms and inside an arm's body block.
trivia_case!(
    match_arm_comments,
    indoc! {r#"
        fn classify(n : Int) : String =
          -- dispatch on the value
          match n of
            -- the zero case
            0 => "zero"
            -- everything else
            _ =>
              -- build the label
              let s = "nonzero"
              s
    "#}
);

// Comments in each branch of an if / elif / else chain.
trivia_case!(
    if_elif_else_comments,
    indoc! {"
        fn sign(n : Int) : Int =
          if n == 0 then
            -- exactly zero
            0
          elif n > 0 then
            -- strictly positive
            1
          else
            -- strictly negative
            9
    "}
);

// Comments in a `for` loop body.
trivia_case!(
    for_body_comments,
    indoc! {"
        fn loop_it(xs : List(Int)) : Unit =
          for x in xs do
            -- visit each element
            println(show(x))
    "}
);

// Handler block: a comment above the first arm, between arms, and after the
// whole `with handler` block.
trivia_case!(
    handler_comments,
    indoc! {"
        effect State
          get() : Int
          put(Int) : Unit

        fn run() : Int ! {State} =
          -- install the handler
          with handler
            -- read the cell
            get() resume k => k(42)
            -- write the cell
            put(v) resume k => k(())
          -- after the handler is in scope
          let a = get()
          a
    "}
);

// A named handler instance carries the same trivia surfaces.
trivia_case!(
    named_handler_comments,
    indoc! {"
        effect State
          get() : Int

        fn run() : Int ! {State} =
          -- a named handler
          with h <- handler
            get() resume k => k(7)
          -- use it
          h.get()
    "}
);

// A `let` whose value is itself a laid-out block.
trivia_case!(
    let_value_block_comments,
    indoc! {"
        fn pick(b : Bool) : Int =
          let r =
            -- choose a branch
            if b then
              -- the yes side
              1
            else
              -- the no side
              2
          r
    "}
);

// Grouped comments and a blank line that deliberately separates two groups.
trivia_case!(
    grouped_and_blank_separated,
    indoc! {"
        fn doc() : Int =
          -- first group line one
          -- first group line two

          -- second group after a blank divider
          let x = 1
          let y = 2
          x + y
    "}
);

// Top-level trivia: a header comment, comments between declarations, and a
// trailing comment after the final declaration.
trivia_case!(
    toplevel_comments,
    indoc! {"
        -- module header
        fn first() : Int = 1
        -- between declarations
        fn second() : Int = 2
        -- dangling tail comment
    "}
);

// try / catch arms.
trivia_case!(
    trycatch_comments,
    indoc! {"
        error Boom

        fn guarded() : Int =
          try
            -- the risky part
            throw Boom
          catch
            -- recover from Boom
            Boom => 0
    "}
);

// A trailing-lambda call whose block body carries comments.
trivia_case!(
    trailing_lambda_comments,
    indoc! {"
        fn walk(xs : List(Int)) : Unit =
          xs.foreach() fn(x)
            -- handle one item
            println(show(x))
    "}
);

// `var` mutable bindings interleaved with comments.
trivia_case!(
    var_decl_comments,
    indoc! {"
        fn counter() : Int =
          -- start at zero
          var n := 0
          -- bump it
          n := n + 1
          n
    "}
);

// A comment between call arguments must survive: the flat one-line join would
// drop it, so the formatter keeps the call in its laid-out source form.
trivia_case!(
    call_arg_comments,
    indoc! {"
        fn main() : Int =
          foo(
            1,  -- keep me
            2,
          )
    "}
);

// Comments inside a list literal are preserved the same way.
trivia_case!(
    list_element_comments,
    indoc! {"
        fn main() : List(Int) =
          [
            1,  -- one
            2,  -- two
          ]
    "}
);

// Comments inside a tuple literal are preserved the same way.
trivia_case!(
    tuple_element_comments,
    indoc! {"
        fn main() =
          (
            1,  -- x coord
            2,  -- y coord
          )
    "}
);

// Consecutive imports form one tight block: blank lines between two imports
// collapse, a comment between them survives, and the block is separated from
// the declarations below by a single blank line.
trivia_case!(
    import_block_spacing,
    indoc! {"
        import Data.List (append)

        import Data.Map (map_empty)
        -- picks the ordered set
        import Data.Set (set_from_list)

        fn main() = append([1], [2])
    "}
);
