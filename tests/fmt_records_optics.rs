// Snapshot tests pinning the multi-line layout of record constructors and nested
// optic updates. A record stacks one field per line once it has more than four
// fields or nests another constructor; a nested optic update (`{ base | .. }`)
// stacks one clause per line, leading-delimiter style. Inputs are inline rather
// than `.pr` fixtures so they stay out of the recursive `fmt --check` scan while
// letting us feed deliberately dense sources.
//
// Each case also asserts idempotence: formatting the formatter's own output must
// reproduce it, so a snapshot can never lock in an unstable layout.

fn fmt(src: &str) -> String {
    let once = prism::format(src).expect("case must parse");
    let twice = prism::format(&once).expect("formatted output must parse");
    assert_eq!(once, twice, "formatter is not idempotent on this case");
    once
}

macro_rules! case {
    ($name:ident, $src:expr) => {
        #[test]
        fn $name() {
            insta::assert_snapshot!(stringify!($name), fmt($src));
        }
    };
}

// -- Records ---------------------------------------------------------------

// Five fields, comfortably under 80 cols, still stacks one per line.
case!(
    record_over_four_fields,
    "fn mk() : Config = Config { a = 1, b = 2, c = 3, d = 4, e = 5 }\n"
);

// Four fields but one is a nested constructor: the parent breaks, the small
// inner `Vec2` stays inline on its field line.
case!(
    record_nested_child_breaks_parent,
    "fn mk(n : String, h : Int) : Player =\n\
     \x20 Player { name = n, pos = Vec2 { x = 1, y = 2 }, hp = h, bag = Nil }\n"
);

// Three levels of nesting, each breaking and indenting one step deeper.
case!(
    record_deeply_nested,
    "fn mk() : A =\n\
     \x20 A { inner = B { inner = C { p = 1, q = 2 }, y = 2 }, z = 3 }\n"
);

// A record update `r { ..base, .. }` with more than four fields and a nested
// record field.
case!(
    record_update_nested,
    "fn bump(p : Player) : Player =\n\
     \x20 Player { ..p, name = q, pos = Vec2 { x = 0, y = 0 }, hp = 100, mp = 50 }\n"
);

// Small flat record stays on one line (negative case + idempotence).
case!(
    record_small_stays_inline,
    "fn mk() : Vec2 = Vec2 { x = 1, y = 2 }\n"
);

// A field whose value is itself a record update triggers the parent break.
case!(
    record_field_is_update,
    "fn f(v : Vec2) : Player = Player { name = q, pos = Vec2 { ..v, x = 9 } }\n"
);

// -- Optics ----------------------------------------------------------------

// Multi-clause traversal update -> leading-delimiter break.
case!(
    optic_multi_clause_traversal,
    "fn tick(world : World) : World =\n\
     \x20 { world | players.each.hp ~ heal, players.each.mana = full, log = [] }\n"
);

// A path carrying a `where` filter, alongside a plain field update.
case!(
    optic_where_filter,
    "fn hurt(army : Army) : Army =\n\
     \x20 { army | units.each.(hp where alive) ~ dec, turn = next }\n"
);

// A prism `?Ctor` step and an `[i]` index step inside the paths.
case!(
    optic_prism_and_index,
    "fn f(g : Game) : Game =\n\
     \x20 { g | items[0].?Weapon.dmg ~ boost, players.each.slot[1] = empty }\n"
);

// An optic clause whose value is itself a breaking record recurses.
case!(
    optic_value_is_record,
    "fn f(g : Game) : Game =\n\
     \x20 { g | board.each.cell = Cell { a = 1, b = 2, c = 3, d = 4, e = 5 }, v = 0 }\n"
);

// Single flat clause stays inline (negative case).
case!(
    optic_single_clause_inline,
    "fn f(r : R) : R = { r | x = 1 }\n"
);

// A single-path read `base.[a.b.c]` stays inline (negative case).
case!(
    optic_read_path_inline,
    "fn f(r : R) : Int = r.[players.each.hp]\n"
);
