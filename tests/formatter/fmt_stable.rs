// A `stable` block prints as declared: rungs, then any converters, then the
// `migrations` table, one entry per line inside real braces. The migration table
// nests a further level and each direction of a `version(...)` route prints back
// as written. Layout idempotence (`format(format(x)) == format(x)`) rides along,
// and the canonical form is stable so `prism fmt` never churns the block.

fn fmt(src: &str) -> String {
    let once = prism::format(src).expect("case must parse");
    let twice = prism::format(&once).expect("formatted output must parse");
    assert_eq!(once, twice, "formatter is not idempotent on this case");
    once
}

#[test]
fn migrations_table_round_trips() {
    let src = "\
stable Save {
  V1 = { hero: String, depth: Int },
  V2 = { ..V1, fog: Int = 30 },
  V3 = { ..V2, mist: Int = 5 },
  migrations {
    V1 -> V2 = auto
    V2 -> V3 = version(upgrade = \\(s) -> Save { hero = s.hero, mist = 7 }, downgrade = auto)
    V1 -> V3 = auto
  }
}
";
    assert_eq!(fmt(src), src);
}

#[test]
fn migrations_coexist_with_inline_converters() {
    let src = "\
stable Order {
  V1 = { id: Int, qty: Int },
  V2 = { ..V1, qty: String },
  upgrade V1 -> V2 = { ..v1, qty = show(v1.qty) },
  downgrade V2 -> V1 = { ..v2, qty = 0 } drop_loss(qty),
  migrations {
    V1 -> V2 = version(upgrade = up, downgrade = down)
  }
}
";
    assert_eq!(fmt(src), src);
}
