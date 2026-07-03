// Explicit instance selection (`f(args, using I)`) must survive formatting on
// every layout path. The flat/break printer and the inline printer decode a
// call head through one shared classifier; when they drifted, a call wide enough
// to break re-emitted `f(a, using I)` as `f(using I)(a)` -- a fixpoint, so it
// slipped past plain idempotence. These cases pin AST-level round-trip (meaning
// preserved), not just `format(format(x)) == format(x)`.

// The parse AST with span offsets stripped, so it is invariant under the
// whitespace reflow a reformat performs. Reflow shifts only spans; a structural
// change (the `using`-drift adds a Call node) survives the strip and shows up.
fn ast_no_spans(src: &str) -> String {
    prism::dump("ast", src)
        .expect("must parse")
        .lines()
        .filter(|l| !l.trim_start().starts_with("span:"))
        .collect::<Vec<_>>()
        .join("\n")
}

// Format `src`, then assert: the output reparses, formatting is idempotent, and
// the parsed meaning is unchanged (same span-stripped AST as the input).
fn preserves_meaning(src: &str) {
    let once = prism::format(src).expect("input must parse");
    let twice = prism::format(&once).expect("formatted output must reparse");
    assert_eq!(once, twice, "formatter not idempotent: {src:?} -> {once:?}");
    assert_eq!(
        ast_no_spans(src),
        ast_no_spans(&once),
        "formatting changed the parsed meaning:\n{src}\n-->\n{once}"
    );
}

// A long value name forces the `let` value onto its own line, routing the call
// through the break path where the drift lived.
const WIDE: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

#[test]
fn using_call_survives_the_break_path() {
    let src =
        format!("fn f(x : Int) : Int given Ord(Int) = x\nfn g() : Int = f({WIDE}, using ordInt)\n");
    preserves_meaning(&src);
    // The value argument stays inside the call, ahead of the `using` clause.
    let out = prism::format(&src).unwrap();
    let arg = out.find(WIDE).expect("value arg kept");
    let using = out.find("using").expect("using clause kept");
    assert!(arg < using, "value arg moved out of the call: {out:?}");
}

#[test]
fn using_call_survives_inline() {
    let src = "fn f(x : Int) : Int given Ord(Int) = x\nfn g() : Int = f(1, using ordInt)\n";
    preserves_meaning(src);
}

#[test]
fn zero_arg_using_call_both_paths() {
    // Inline, and (with a long callee name) broken: the bare `f(using I)` form.
    for src in [
        "fn f() : Int given Ord(Int) = 0\nfn g() : Int = f(using ordInt)\n",
        &format!("fn {WIDE}() : Int given Ord(Int) = 0\nfn g() : Int = {WIDE}(using ordInt)\n"),
    ] {
        preserves_meaning(src);
    }
}

#[test]
fn using_call_with_several_args_and_instances() {
    let src = format!(
        "fn f(x : Int, y : Int) : Int given Ord(Int) = x\nfn g() : Int = f({WIDE}, 2, using ordInt)\n"
    );
    preserves_meaning(&src);
}

// Neighboring call-head shapes the same classifier decodes: a UFCS dot call and
// a `?`-receiver, each wide enough to break, must round-trip too.
#[test]
fn dot_and_try_calls_survive_the_break_path() {
    for src in [
        format!("fn g(xs : List(Int)) : Int = xs.foldl(0, {WIDE})\n"),
        format!("fn g(r : Result(Int, Int)) : !{{Throw}} Int = f({WIDE}, r?)\n"),
    ] {
        // Reparse + idempotence; these never used the Inst arm but share the decoder.
        let once = prism::format(&src).expect("input must parse");
        let twice = prism::format(&once).expect("output must reparse");
        assert_eq!(once, twice, "not idempotent: {src:?}");
    }
}
