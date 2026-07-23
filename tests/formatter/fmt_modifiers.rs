// Declaration-modifier round-trip coverage. Every declaration modifier, alone
// and in every legal stack, must format to a canonical form that round-trips
// exactly and stays idempotent, so a dropped or reordered modifier cannot slip
// through.
//
// The legal chain, in canonical order, is
// `[pub] [test] [total | assume total] [replayable] [fip | fbip] fn`, with the
// `@ noalloc` allocation certificate carried on the return type. `test`, `total`,
// and `assume` are contextual: modifiers only in the leading run before `fn`,
// ordinary identifiers everywhere else.

fn fmt(src: &str) -> String {
    let once = prism::format(src).expect("case must parse");
    let twice = prism::format(&once).expect("formatted output must parse");
    assert_eq!(once, twice, "formatter is not idempotent on this case");
    once
}

#[test]
fn each_modifier_alone_round_trips() {
    for src in [
        "fn f(x : Int) : Int = x\n",
        "pub fn f(x : Int) : Int = x\n",
        "test fn f(x : Int) : Int = x\n",
        "total fn f(x : Int) : Int = x\n",
        "assume total fn f(x : Int) : Int = x\n",
        "replayable fn f(x : Int) : Int = x\n",
        "fip fn f(x : Int) : Int = x\n",
        "fbip fn f(x : Int) : Int = x\n",
        "fn f(x : Int) : Int @ noalloc = x\n",
    ] {
        assert_eq!(
            fmt(src),
            src,
            "modifier form is not canonical/idempotent: {src:?}"
        );
    }
}

#[test]
fn full_modifier_stack_round_trips() {
    let src = "pub test assume total replayable fip fn f(x : Int) : Int @ noalloc = x\n";
    assert_eq!(fmt(src), src);
}

// Every legal ordered combination of visibility, the prefix modifiers, and the
// `@ noalloc` certificate formats to itself: the canonical order is fixed, so a
// correctly-emitted stack is already its own normal form. A dropped or reordered
// modifier breaks the equality; a non-idempotent one trips the check in `fmt`.
#[test]
fn every_modifier_combination_round_trips() {
    let pubs = ["", "pub "];
    let tests = ["", "test "];
    let totals = ["", "total ", "assume total "];
    let replays = ["", "replayable "];
    let fips = ["", "fip ", "fbip "];
    let allocs = ["", " @ noalloc"];
    let mut n = 0;
    for &p in &pubs {
        for &t in &tests {
            for &tot in &totals {
                for &rep in &replays {
                    for &fp in &fips {
                        for &al in &allocs {
                            let src = format!("{p}{t}{tot}{rep}{fp}fn f(x : Int) : Int{al} = x\n");
                            assert_eq!(fmt(&src), src, "not canonical/idempotent: {src:?}");
                            n += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(
        n,
        2 * 2 * 3 * 2 * 3 * 2,
        "expected every combination covered"
    );
}

// The three contextual modifier words stay ordinary identifiers wherever the
// leading-modifier position does not apply: as a declaration name, as parameter
// names, in expression position, and as a top-level constant name.
#[test]
fn contextual_words_stay_identifiers() {
    for src in [
        "fn total(x : Int) : Int = x\n",
        "fn test(x : Int) : Int = x\n",
        "fn assume(x : Int) : Int = x\n",
        "fn f(test : Int, total : Int, assume : Int) : Int = test + total + assume\n",
        "let total = 0\n",
    ] {
        assert_eq!(
            fmt(src),
            src,
            "contextual word was not preserved verbatim: {src:?}"
        );
    }
}
