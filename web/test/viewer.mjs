// Checks over the viewer's real modules, against a real index artifact.
//
// Run with `pnpm check:viewer`, which transpiles the TypeScript first. Needs
// `public/stdlib-index.json`, which `just index-web` writes.

import { readFileSync } from "node:fs";

import { card, check, done, installGlobals, nodes, plain, Storage, section } from "./dom.mjs";

installGlobals();

const { Index, Members, Mentions, Relations, Revisions } = await import("./build/viewer-model.mjs");
const { Review, freshness, needsAttention } = await import("./build/viewer-review.mjs");
const { packet } = await import("./build/viewer-context.mjs");
const { KINDS, Viewer, isEditable, renderDoc } = await import("./build/viewer.mjs");
const { decodeSpans } = await import("./build/viewer-model.mjs");

const index = new Index(JSON.parse(readFileSync("public/stdlib-index.json", "utf8")));
const rel = new Relations(index);

section("the artifact decodes and indexes");
check("format accepted", index.envelope.format === "prism-index-v1");
check("every definition is keyed", index.byId.size === index.defs.length);
let asymmetric = 0;
for (const e of index.edges) {
  if (!rel.get(e.kind, "out", e.from).includes(e.to)) asymmetric++;
  if (!rel.get(e.kind, "in", e.to).includes(e.from)) asymmetric++;
}
check("every edge reads from both ends", asymmetric === 0, `${asymmetric} asymmetric`);

section("every reference is explained");
let unexplained = 0;
for (const d of index.defs) {
  for (const r of d.refs ?? []) if (index.classify(r.target) === "elsewhere") unexplained++;
}
check("none left as missing from the index", unexplained === 0, `${unexplained} unexplained`);
check("a primitive is known as one", index.classify("byte_at") === "builtin");
check("a definition is known as one", index.classify("Data.List.map") === "definition");

section("hover text answers what a thing is");
const mapTip = index.describe("Data.List.map");
check("a definition leads with its type", mapTip.split("\n")[1].includes("List("));
check("and states kind and module", mapTip.includes("value in Data.List"));
const primTip = index.describe("byte_at");
check("a primitive carries its signature", primTip.includes("(String, Int) -> Int"));
check("and says it is a builtin", primTip.includes("compiler builtin"));

section("bodies render navigably and without corruption");
let bodies = 0;
let corrupt = 0;
const viewer = new Viewer(index, null, nodes(), new Storage());
viewer.start();
// Every definition, not just the referencing ones: member marks are inserted into
// declarations that carry no references at all.
for (const d of index.defs) {
  bodies++;
  if (plain(viewer.body(d)) !== d.source) corrupt++;
}
check(
  "markup insertion preserves the source exactly",
  corrupt === 0,
  `${bodies} bodies, ${corrupt} corrupt`,
);

const deck = nodes();
const v = new Viewer(index, null, deck, new Storage());
v.start();
v.show("Data.Bytes.bytes_length");
const one = card(deck.cards.innerHTML, "Data.Bytes.bytes_length");
check("a written type name is a link", one.includes('data-goto="Wire.Bytes"'));
check("hover uses the fast path", one.includes("data-tip="));
check("and no native title survives", !/\stitle="/.test(one));

section("a builtin opens as a synthesized card");
check("a primitive named in a body is a link to it", one.includes('data-goto="Int"'));
v.show("Unit");
const unit = card(deck.cards.innerHTML, "Unit");
check("the card leads with name and signature", plain(unit).includes("Unit : Type"));
check("and carries the compiler's sentence", plain(unit).includes("unit type"));
check("badged as a builtin", unit.includes("kind--builtin"));
check("and by its own kind besides", unit.includes("kind--type"));
check("with no content address offered", unit.includes("hash--none"));
check("and no relation strip", !unit.includes("card-rel"));
v.show("print");
const printCard = card(deck.cards.innerHTML, "print");
check(
  "a builtin function's signature comes from the checker's table",
  plain(printCard).includes("print : forall a. (a) -> Unit ! {IO}"),
);
check(
  "and the type names inside it are links",
  printCard.includes('data-goto="Unit"') && printCard.includes('data-goto="IO"'),
);
v.show("simd_fmax4");
const fmax4 = card(deck.cards.innerHTML, "simd_fmax4");
check("a wired SIMD type is itself a linked primitive", fmax4.includes('data-goto="F32x4"'));

section("the rail opens as a list of modules");
const rail = () => deck.list.innerHTML;
check("no definition row is drawn unasked", !rail().includes("rail-def"), rail().slice(0, 120));
// One extra collapsed group: the compiler's builtins, offered above the modules.
check(
  "every module is offered, collapsed, with its size",
  [...rail().matchAll(/data-mod="([^"]*)"[^>]*aria-expanded="false"/g)].length ===
    new Set(index.defs.map((d) => d.module)).size + 1,
);
check("the builtins stand above the modules", rail().includes('data-mod="(builtins)"'));
v.toggleModule("(builtins)");
check(
  "opened, the builtins divide into types, effects and functions",
  rail().includes("rail-sub") &&
    plain(rail()).includes("types") &&
    plain(rail()).includes("effects") &&
    plain(rail()).includes("functions"),
);
check("a wired storage type is offered", rail().includes('data-goto="FloatBuf"'));
v.toggleModule("(builtins)");
deck.search.value = "";
v.toggleModule("Data.List");
check("expanding one shows its definitions", rail().includes('data-goto="Data.List.map"'));
check(
  "and leaves its neighbours alone",
  !rail().includes('data-goto="Data.Bytes.bytes_length"'),
  rail().slice(0, 200),
);
v.toggleModule("Data.List");
check("collapsing puts them away again", !rail().includes('data-goto="Data.List.map"'));
deck.search.value = "bytes_len";
v.renderList("bytes_len");
check(
  "a search reaches into collapsed modules",
  rail().includes('data-goto="Data.Bytes.bytes_length"'),
);
check("and offers no collapsed result", !rail().includes('aria-expanded="false"'));
deck.search.value = "";
v.renderList("");

section("search reaches past canonical names");
// `Cons`, `Nil` and `pure` are members, so no definition in the rail carries those
// names — the declarations that introduce them do. Each is now a result in its own
// right, and an exact match leads.
for (const [q, owner, what] of [
  ["cons", "List", "constructor"],
  ["nil", "List", "constructor"],
  ["pure", "Applicative", "method"],
]) {
  const groups = v.search(q).groups;
  const first = groups[0].hits[0];
  check(
    `"${q}" is the first result, as a ${what} of ${owner}`,
    first.member?.toLowerCase() === q && first.def.id === owner && first.score === 0,
    JSON.stringify(groups[0].hits.map((h) => `${h.member ?? h.def.name}:${h.score}`)),
  );
}
check(
  "an exact member outranks the substring matches that used to bury it",
  v
    .search("cons")
    .groups[0].hits.map((h) => h.member ?? h.def.name)
    .join() === "Cons,const,Console",
);
deck.search.value = "pure";
v.renderList("pure");
check(
  "a member row is named for the member",
  rail().includes('<span class="rail-name">pure</span>'),
);
check(
  "and badged with what it is",
  rail().includes('<span class="kind kind--member">method</span>'),
);
check(
  "opening it goes to the declaration it lives in",
  rail().includes('data-goto="Applicative" data-member="pure"'),
);
deck.search.value = "cons";
v.renderList("cons");
const text = v.search("cons").text;
check("a text match is a separate tier, not mixed in", text.length > 100, `${text.length} in text`);
check("which the rail labels", rail().includes("in the text"));
deck.search.value = "";
v.renderList("");

section("a kind is named, not initialled");
check("a card badge spells the kind out", one.includes('data-tip="fn — a function or value">fn<'));
v.toggleModule("Prelude");
check(
  "and the rail agrees, after the name so names stay in a column",
  /<span class="rail-name">Option<\/span>\s*<span class="kind kind--type"[^>]*>type</.test(rail()),
);
v.toggleModule("Prelude");
const unlabelled = [...new Set(index.defs.map((d) => d.kind))].filter((k) => !KINDS[k]);
check(
  "every kind the artifact carries has a label and a gloss",
  unlabelled.length === 0,
  unlabelled.join(", "),
);

section("syntax highlighting is baked and merges with links");
check("the class table is present", index.tokenClasses.length > 0, index.tokenClasses.join(","));
const sing = index.byId.get("Data.List.singleton");
const decoded = decodeSpans(sing.tokens, index.tokenClasses);
check(
  "spans decode to the tokens they describe",
  decoded.some((s) => sing.source.slice(s.start, s.end) === "fn" && s.cls === "kw") &&
    decoded.some((s) => sing.source.slice(s.start, s.end) === "Cons" && s.cls === "ctor"),
  JSON.stringify(decoded.slice(0, 3)),
);
let spans = 0;
let outOfRange = 0;
let overlapping = 0;
for (const d of index.defs) {
  let prevEnd = 0;
  for (const s of decodeSpans(d.tokens, index.tokenClasses)) {
    spans++;
    if (s.end > d.source.length || s.start < 0) outOfRange++;
    if (s.start < prevEnd) overlapping++;
    prevEnd = s.end;
  }
}
check(
  "every span lies inside its source",
  outOfRange === 0,
  `${spans} spans, ${outOfRange} out of range`,
);
check("and none overlap", overlapping === 0, `${overlapping} overlapping`);
const painted = viewer.body(sing);
check("a keyword is painted", painted.includes('<span class="tk-kw">fn</span>'));
check(
  "a constructor keeps its colour inside its link",
  /<button class="ref"[^>]*><span class="tk-ctor">Cons<\/span><\/button>/.test(painted),
  painted,
);

section("a declaration's members lead to their users");
const members = new Members(index);
check(
  "a class method's users are recovered from occurrence spans",
  members.users("Applicative", "pure").join() === "Data.Monad.sequence,Data.Monad.traverse_list" &&
    members.users("Applicative", "ap").join() === "Data.Monad.map2,Data.Monad.map3",
  JSON.stringify(members.of("Applicative")),
);
// The instances that *implement* `pure` are not users of it: the name there is a
// binder, not a call. They are on the card already, as instances.
check(
  "an implementation is not counted as a use",
  !members.users("Applicative", "pure").includes("applicativeOption"),
);
check(
  "which no edge could answer: a dictionary call leaves none",
  index.edges.filter((e) => e.from === "Data.Monad.map2").length === 0,
);
check("constructors work the same way", members.users("List", "Cons").length > 100);
// Writing `Bin` inside `type Map = Tip | Bin(..)` is the declaration talking
// about itself: its own member sites are member marks, not references, so a
// declaration never leads its own members' user rows.
check(
  "a declaration is not a user of its own members",
  !members.users("Map", "Bin").includes("Map") && !members.users("Map", "Tip").includes("Map"),
  JSON.stringify(members.of("Map").map(([name, users]) => [name, users.slice(0, 3)])),
);
check(
  "and its member sites stay member marks in the body",
  viewer.body(index.byId.get("Map")).includes('data-member="Bin"'),
);
v.show("Applicative");
const klass = card(deck.cards.innerHTML, "Applicative");
check("the declaration site of a member is marked", klass.includes('data-member="pure"'));
check("and the mark stays inside the declaration", plain(klass).includes("pure : (a) -> f(a)"));
check(
  "the users are listed under the member's own name",
  /data-uses="ap"[\s\S]*?data-goto="Data\.Monad\.map2"/.test(klass) &&
    /data-uses="pure"[\s\S]*?data-goto="Data\.Monad\.sequence"/.test(klass),
);
let marked = 0;
let mislabelled = 0;
for (const d of index.defs) {
  const html = viewer.body(d);
  for (const [name] of members.of(d.id)) {
    if (!html.includes(`data-member="${name}"`)) continue;
    marked++;
    // The marked span must be the member's own name, not some other word that
    // happens to contain it.
    const cut = html.split(`data-member="${name}"`)[1].split("</button>")[0];
    if (plain(`<${cut}`) !== name) mislabelled++;
  }
}
check("every mark covers exactly its member's name", mislabelled === 0, `${marked} marked`);
// The member list comes from the compiler's own declaration lists, not from what
// something happens to use, so it is complete and its spans are exact.
let placed = 0;
let adrift = 0;
for (const d of index.defs) {
  for (const m of d.members ?? []) {
    placed++;
    if (d.source.slice(m.start, m.end) !== m.name) adrift++;
  }
}
check(
  "every declared member is located exactly",
  adrift === 0,
  `${placed} members, ${adrift} adrift`,
);
check(
  "including ones nothing uses",
  (index.byId.get("Output").members ?? []).map((m) => m.name).join() === "out_print,out_println",
);
const unused = viewer.body(index.byId.get("Output"));
check(
  "which are named and explained rather than linked to nowhere",
  unused.includes("operation of Output") && unused.includes("the effect is handled by 4"),
);
check("and are not a link", !unused.includes('data-member="out_print"'));
check(
  "an unused member is still findable by name",
  v.search("out_print").groups[0].hits[0].member === "out_print",
);

// Hundreds of definitions are typed by `List` and hundreds write its `Cons`; a
// card that opens with six hundred chips is a card nobody reads. Counted from the
// artifact rather than written down, so the check survives the library growing.
v.show("List");
const big = () => card(deck.cards.innerHTML, "List");
const chips = (html) => (html.match(/class="chip"/g) ?? []).length;
const usedBy = rel.get("uses-type", "in", "List").length;
check("a long row is capped", chips(big()) < usedBy / 3, `${chips(big())} chips of ${usedBy}`);
check(
  "but the true count is still stated",
  new RegExp(`used by\\s*<span class="rel-n">${usedBy}<`).test(big()),
  String(usedBy),
);
check("and the remainder is offered", big().includes("more</button>"));
const wider = /data-wide="([^"]*uses-type in[^"]*)"/.exec(big());
v.widen(wider[1]);
check("asking for it shows every one", chips(big()) > 380, `${chips(big())} chips`);
check("and offers to collapse again", big().includes(">fewer</button>"));
v.widen(wider[1]);

section("the call rows lead with what the source names");
const mentions = new Mentions(index);
// `arbitraryFloat` writes `gen_run(gen_float, size)`. The dependency graph has
// neither of those in full: `gen_float` is a top-level `let`, and the elaborator
// inlines a constant, so the dependency lands on what it expanded to.
check(
  "a body's own text is read from the occurrences",
  mentions.get("out", "arbitraryFloat").join() === "Quickcheck.gen_run,Quickcheck.gen_float",
  mentions.get("out", "arbitraryFloat").join(),
);
check(
  "which the dependency graph does not report",
  !rel.get("calls", "out", "arbitraryFloat").includes("Quickcheck.gen_float") &&
    rel.get("calls", "out", "arbitraryFloat").includes("Quickcheck@float_at"),
);
v.show("arbitraryFloat");
const strip = card(deck.cards.innerHTML, "arbitraryFloat");
const chip = (name) => new RegExp(`class="chip([^"]*)"[^>]*>${name}<`).exec(strip);
check("the written names come first", strip.indexOf(">gen_run<") < strip.indexOf(">float_at<"));
check("both written names are there", Boolean(chip("gen_run")) && Boolean(chip("gen_float")));
check("and are not marked derived", !chip("gen_run")[1].includes("derived"));
check("what only elaboration reaches is marked", chip("float_at")[1].includes("chip--derived"));
check(
  "and says why on hover",
  /float_at[\s\S]{0,400}?reached through elaboration/.test(
    strip.split('data-goto="Quickcheck@float_at"')[1] ?? "",
  ) || strip.includes("reached through elaboration"),
);
check("the count covers all three", /calls\s*<span class="rel-n">3</.test(strip));
// A term references a type, a constructor and a class method too; those resolve to
// the declaration that owns them and have rows of their own, so they stay out.
check(
  "a type is not listed as a call",
  !mentions.get("out", "arbitraryFloat").includes("Test.Arbitrary"),
);

section("an instance performs what its methods perform");
// An instance method is checked from inside its instance and never becomes a
// `DeclInfo`, so its effect row had nowhere to come from.
check(
  "a generator instance uses Random",
  rel.get("performs", "out", "arbitraryFloat").join() === "Random",
  rel.get("performs", "out", "arbitraryFloat").join(),
);
const instances = index.defs.filter((d) => d.kind === "instance");
const performing = instances.filter((d) => rel.get("performs", "out", d.id).length > 0);
check(
  "across the library, thirty of them perform something",
  performing.length === 30,
  `${performing.length} of ${instances.length}`,
);
check(
  "a decoder can fail",
  rel.get("performs", "out", "fromJsonInt").join() === "Fail",
  rel.get("performs", "out", "fromJsonInt").join(),
);

section("an effect relates to what interprets it");
// Nothing in the standard library performs `Output` — programs do — so before
// `handles` this card related to nothing at all in either direction.
check(
  "nothing performs it, which is why the card looked empty",
  rel.get("performs", "in", "Output").length === 0,
);
check(
  "and four definitions handle it",
  rel.get("handles", "in", "Output").join() ===
    "Incr@t_run_thunk,Replay.durable,Replay.replay,run_io",
  rel.get("handles", "in", "Output").join(),
);
check("read from the other end too", rel.get("handles", "out", "run_io").includes("Output"));
v.show("Output");
check(
  "the card lists them",
  card(deck.cards.innerHTML, "Output").includes('data-goto="Replay.replay"'),
);

section("a signature is painted and linked like a body");
v.show("Concurrent.scope");
const sig = card(deck.cards.innerHTML, "Concurrent.scope");
const between = (html, cls) => html.split(`class="${cls}"`)[1]?.split("</div>")[0] ?? "";
const tySig = between(sig, "card-sig");
check("a keyword in the type is painted", tySig.includes('<span class="tk-kw">forall</span>'));
check("a type name in the type is a link", tySig.includes('data-goto="List"'));
check(
  "a qualified effect too, with its tooltip",
  /data-goto="Concurrent.Async" data-tip=/.test(tySig),
);
check(
  "and the effect row is linked as well",
  between(sig, "card-eff").includes('data-goto="Concurrent.Async"'),
);
// A signature drops the module from a name it links, so what a card shows is the
// compiler's rendering with the qualifiers taken off — computed here from the refs,
// independently of the renderer under test.
const unqualify = (text, refs) => {
  let out = "";
  let at = 0;
  for (const r of refs ?? []) {
    out += text.slice(at, r.start) + (text.slice(r.start, r.end).split(".").at(-1) ?? "");
    at = r.end;
  }
  return out + text.slice(at);
};
const shown = (d, field, refs, tokens) =>
  plain(viewer.painted(d[field], d[refs] ?? [], d[tokens], d, true));
let sigs = 0;
let mangled = 0;
for (const d of index.defs) {
  if (!d.ty) continue;
  sigs++;
  if (shown(d, "ty", "ty_refs", "ty_tokens") !== unqualify(d.ty, d.ty_refs)) mangled++;
  if (
    d.effects &&
    shown(d, "effects", "eff_refs", "eff_tokens") !== unqualify(d.effects, d.eff_refs)
  ) {
    mangled++;
  }
}
check(
  "a qualified type in a signature reads short",
  shown(index.byId.get("Data.Vec.vempty"), "ty", "ty_refs", "ty_tokens") ===
    "forall a. () -> Vec(a, 0)",
);
// Shortening is off when it would make two different types look alike, which is
// the ambiguity the qualification exists to resolve.
const twin = { ...index.byId.get("Data.Vec.vempty"), ty: "(Data.Vec.Vec) -> Other.Vec" };
check(
  "two names that would collide stay qualified",
  plain(
    viewer.painted(
      twin.ty,
      [
        { start: 1, end: 13, target: "Data.Vec.Vec" },
        { start: 18, end: 27, target: "Other.Vec" },
      ],
      "",
      twin,
      true,
    ),
  ) === twin.ty,
);
check(
  "no signature is corrupted by its markup",
  mangled === 0,
  `${sigs} signatures, ${mangled} bad`,
);
const linked = index.defs.filter((d) => d.ty_refs?.length).length;
check("most signatures gained links", linked > 800, `${linked} of ${sigs}`);

section("a name in a body says what its type is");
// The signature answers what a definition takes; a reader in the body wants to
// know what a name *is* where it is used, and the checker already knows.
const typed = index.byId.get("Data.List.map");
const hovers = decodeSpans(typed.types, index.typeTable).map((s) => [
  typed.source.slice(s.start, s.end),
  s.cls,
]);
check(
  "a parameter is typed at its binding site",
  hovers.some(([n, t]) => n === "xs" && t.startsWith("List(")),
  JSON.stringify(hovers.slice(0, 4)),
);
check("and so are names in the body", hovers.filter(([n]) => n === "f").length >= 2);
check(
  "the types are interned, not repeated",
  index.typeTable.length > 0 && index.typeTable.length < 3000,
  `${index.typeTable.length} distinct`,
);
const painted2 = viewer.body(typed);
check("a local is hoverable but not a link", painted2.includes('class="ref ref--local"'));
check("carrying its type", /data-tip="xs\nList\(/.test(painted2), painted2.slice(0, 120));
// Nothing claims a span twice: a reference's tooltip already names the definition's
// own type, which is the better answer where there is one.
const claimed = decodeSpans(typed.types, index.typeTable).filter((s) =>
  (typed.refs ?? []).some((r) => s.start < r.end && r.start < s.end),
);
check(
  "a reference keeps its own tooltip",
  claimed.every((s) => !painted2.includes(`data-tip="${typed.source.slice(s.start, s.end)}\n`)) ||
    claimed.length === 0,
);
let out = 0;
for (const d of index.defs) {
  for (const s of decodeSpans(d.types, index.typeTable)) {
    if (s.end > d.source.length || s.start < 0) out++;
  }
}
check("every type span lies inside its source", out === 0, `${out} out of range`);

section("docstrings render as documentation");
const composed = renderDoc(index.byId.get("compose").doc);
check("prose becomes a paragraph", composed.startsWith("<p>Function composition:"));
check("inline code becomes code", composed.includes("<code>compose(f, g, x)</code>"));
check("an example becomes a code block", composed.includes('<pre class="doc-code"><code>compose('));
check(
  "and its expected output is labelled as output",
  composed.includes('<div class="doc-note">output</div><pre class="doc-code doc-out"><code>11<'),
);
check(
  "a hidden doctest line is not shown",
  !renderDoc(index.byId.get("Cli.help_text").doc).includes("let cmd = Command"),
);
let leaked = 0;
let unbalanced = 0;
let rawAngle = 0;
for (const d of index.defs) {
  if (!d.doc) continue;
  const html = renderDoc(d.doc);
  if (html.includes("```")) leaked++;
  for (const tag of ["p", "pre", "code"]) {
    const open = html.split(new RegExp(`<${tag}[ >]`)).length;
    if (open !== html.split(`</${tag}>`).length) unbalanced++;
  }
  // A `<` surviving into the text is markup the docstring wrote, not markup we
  // chose to emit: escaping happens before any tag is inserted, so there is none.
  if (plain(html).includes("<pre") || plain(html).includes("<code")) rawAngle++;
}
check("no fence survives the render", leaked === 0, `${leaked} leaked`);
check("every tag is closed", unbalanced === 0, `${unbalanced} unbalanced`);
check("and no docstring can inject markup", rawAngle === 0, `${rawAngle} injected`);

section("a card shows what was asked for");
check("open, not folded", !one.includes("is-folded") && one.includes('aria-expanded="true"'));
v.show("compose");
const folder = card(deck.cards.innerHTML, "compose");
check("the signature is its own block", folder.includes('<div class="card-sig"><code>'));
check("the docs are rendered, not escaped", folder.includes('<pre class="doc-code">'));

section("the deck keeps only the chrome that does something");
// A note is rare and a definition is not, so the field is offered rather than
// standing on every card in the deck.
check("no note field until asked for", !one.includes("card-note"));
check("but a card offers one", one.includes('data-write-note="Data.Bytes.bytes_length"'));
v.writeNote("Data.Bytes.bytes_length");
const noteCard = () => card(deck.cards.innerHTML, "Data.Bytes.bytes_length");
check("asking opens it", noteCard().includes('placeholder="note"'));
v.setNote("Data.Bytes.bytes_length", "worth a look", 1);
v.show("Data.Bytes.bytes_length");
check(
  "and a card carrying a note always shows it",
  noteCard().includes(">worth a look</textarea>"),
);
v.setNote("Data.Bytes.bytes_length", "", 2);
check("emptying it closes the field", !noteCard().includes("card-note"));
// A card leads with the canonical name, qualified — the prelude is addressed in
// global scope, so its ids are bare and the module has to be put back.
check(
  "a card names itself fully",
  one.includes(">Data.Bytes.bytes_length</button>"),
  one.slice(0, 200),
);
v.show("Result");
check(
  "including a prelude definition, whose id is bare",
  card(deck.cards.innerHTML, "Result").includes(">Prelude.Result</button>"),
);
check("and no separate module label", !deck.cards.innerHTML.includes("card-mod"));
// The deck is the trail: what you followed is still open, so returning is a click
// on a card that never went anywhere.
v.show("Wire.Bytes");
check(
  "following a link leaves the definition you came from open",
  deck.cards.innerHTML.includes('data-card="Data.Bytes.bytes_length"') &&
    deck.cards.innerHTML.includes('data-card="Wire.Bytes"'),
);
check("the read mark is offered on a single revision too", one.includes("data-reviewed"));

section("the header says what the test layer holds");
// An empty `tested by` row means one of two very different things, and the
// artifact knows which. The standard library declares no tests at all.
check("the artifact says so", index.envelope.tests === "empty");
check("and the header repeats it", deck.title.innerHTML.includes(">no tests</span>"));
const layered = (tests) => {
  const n = nodes();
  new Viewer(
    new Index({
      envelope: { ...index.envelope, tests },
      modules: [],
      defs: [],
      edges: [],
      token_classes: [],
    }),
    null,
    n,
    new Storage(),
  ).start();
  return n.title.innerHTML;
};
check("a built layer needs no note", !layered("included").includes("tag--"));
// The dangerous case: tests exist, the layer could not be built, and every row
// reads empty as though nothing were tested.
const broken = layered({ unavailable: "Type Error: in `Foo.bar`: no such field" });
check("a failed layer is called out", broken.includes(">tests unavailable</span>"));
check("with the diagnostic on hover", broken.includes("no such field"));

section("the definition list can be put away");
check("it starts showing", deck.rail.hidden === false);
v.toggleRail();
check("and hides on request", deck.rail.hidden === true);
check(
  "the control says what it now does, since it is the way back",
  deck.railToggle.dataset.tip.startsWith("show"),
);
v.toggleRail();
check("and comes back", deck.rail.hidden === false);
// The search box lives inside the rail, and a hidden element cannot take focus, so
// a search shortcut with the rail stowed did nothing at all.
v.toggleRail();
let reached = 0;
deck.search.focus = () => reached++;
deck.search.select = () => {};
v.onKey({ key: "/", target: {}, preventDefault() {} });
check("a search brings the list back", deck.rail.hidden === false && reached === 1);
v.toggleRail();
v.onKey({ key: "k", metaKey: true, target: {}, preventDefault() {} });
check("cmd-K too", deck.rail.hidden === false && reached === 2);
// Remembered: a reader who put it away wants it to stay away across a reload.
const kept = new Storage();
const first = nodes();
const one1 = new Viewer(index, null, first, kept);
one1.start();
one1.toggleRail();
const second = nodes();
new Viewer(index, null, second, kept).start();
check("the preference survives a reload", second.rail.hidden === true);
check(
  "and is not stored as a review mark",
  new Review(index.envelope.title, kept).all().length === 0,
);

section("a module that did not parse is named, not silently absent");
index.modules.push({ dotted: "Scratch", path: "Scratch.pr", error: "unexpected token" });
const brokenDeck = nodes();
new Viewer(index, null, brokenDeck, new Storage()).start();
check(
  "the header counts it",
  brokenDeck.title.innerHTML.includes("1 module not parsed"),
  brokenDeck.title.innerHTML,
);
check(
  "and the tooltip names the file and the diagnostic",
  brokenDeck.title.innerHTML.includes("Scratch.pr: unexpected token"),
);
index.modules.pop();

section("a revision pair reads as one deck");
const was = { ...index.byId.get("Data.List.map"), source: "fn map(f, xs) = previously" };
const pair = new Viewer(
  index,
  new Revisions({
    envelope: {
      format: "prism-index-diff-v1",
      old: { title: "t", contract: "aaaa" },
      new: { title: "t", contract: "bbbb" },
      counts: { changed: 1, added: 1, removed: 0, moved: 0, cone: 2, cosmetic: 1, unchanged: 9 },
    },
    entries: [
      { status: "changed", id: "Data.List.map", old: was },
      { status: "added", id: "Data.List.singleton" },
      { status: "cone", id: "Data.List.flatten" },
      { status: "cosmetic", id: "Data.List.concat_map" },
    ],
  }),
  nodes(),
  new Storage(),
);
pair.start();
check("the title counts what moved", pair.nodes.title.innerHTML.includes("1 changed"));
check(
  "the change group is a header like any other",
  pair.nodes.list.innerHTML.includes('<span class="rail-head">changed in this revision<span'),
);
// The consequences are offered rather than withheld: collapsed, so they cannot
// bury the authored edits, but reachable, which they were not.
check(
  "the cone is a group of its own, collapsed",
  /data-mod="revision: in the cone" aria-expanded="false"/.test(pair.nodes.list.innerHTML),
);
check(
  "and its entries are not listed until asked for",
  !pair.nodes.list.innerHTML.includes('data-goto="Data.List.flatten"'),
);
pair.toggleModule("revision: in the cone");
check(
  "expanding it shows them",
  pair.nodes.list.innerHTML.includes('data-goto="Data.List.flatten"'),
);
check(
  "cosmetic entries get the same treatment",
  /data-mod="revision: cosmetic"/.test(pair.nodes.list.innerHTML),
);
check(
  "an authored change is listed with its status",
  /rail-name">singleton<\/span>\s*<span class="status status--added">added</.test(
    pair.nodes.list.innerHTML,
  ),
);
pair.show("Data.List.map");
const changed = card(pair.nodes.cards.innerHTML, "Data.List.map");
check("a changed card says so", changed.includes('class="status status--changed">changed<'));
check("and on a changed one", changed.includes("data-reviewed"));
// Side by side, and the left pane is painted and linked like the right one.
check("the two revisions sit side by side", changed.includes('class="card-diff"'));
check(
  "before on the left, after on the right",
  changed.indexOf(">before<") < changed.indexOf(">after<"),
);
const before = changed.split("card-src--was")[1].split("</pre>")[0];
check(
  "and carries what the other revision had",
  plain(before).includes("fn map(f, xs) = previously"),
);

// A removed definition exists only on the diff's old side, and its review row
// must open a card rather than sit dead in the rail.
const oldOnly = {
  ...index.byId.get("Data.List.map"),
  id: "Data.List.dropped",
  name: "dropped",
  source: "fn dropped(xs) = xs",
  members: [],
  refs: [],
  tokens: "",
  types: "",
};
const withRemoved = new Viewer(
  index,
  new Revisions({
    envelope: {
      format: "prism-index-diff-v1",
      old: { title: "t", contract: "aaaa" },
      new: { title: "t", contract: "bbbb" },
      counts: { changed: 0, added: 0, removed: 1, moved: 0, cone: 0, cosmetic: 0, unchanged: 9 },
    },
    entries: [{ status: "removed", id: "Data.List.dropped", old: oldOnly }],
  }),
  nodes(),
  new Storage(),
);
withRemoved.start();
withRemoved.show("Data.List.dropped");
const removedCard = card(withRemoved.nodes.cards.innerHTML, "Data.List.dropped");
check("a removed definition opens from the rail", removedCard.length > 0);
check("and renders the revision it still has", plain(removedCard).includes("fn dropped(xs) = xs"));
check("and says it is gone", removedCard.includes('class="status status--removed">removed<'));

// A diff records the revision its new side came from; overlaying it on any
// other index would present old bodies beside definitions they were never
// compared with, so a mismatched pair is refused.
let refused = "";
try {
  new Revisions(
    {
      envelope: {
        format: "prism-index-diff-v1",
        old: { title: "t", contract: "aaaa" },
        new: { title: "t", contract: "bbbb" },
        counts: { changed: 0, added: 0, removed: 0, moved: 0, cone: 0, cosmetic: 0, unchanged: 0 },
      },
      entries: [],
    },
    [],
    [],
    index.envelope.contract,
  );
} catch (e) {
  refused = e.message;
}
check("a diff for another revision is refused", refused.includes("different revision"), refused);

// Each side's records index its own revision's tables, carried in the envelope;
// they are re-encoded into the viewer's table space, extending it where the two
// disagree.
const foreign = new Revisions(
  {
    envelope: {
      format: "prism-index-diff-v1",
      old: { title: "t", contract: "a", token_classes: ["kw"], type_table: ["Int"] },
      new: { title: "t", contract: "b" },
      counts: { changed: 1, added: 0, removed: 0, moved: 0, cone: 0, cosmetic: 0, unchanged: 0 },
    },
    entries: [
      {
        status: "changed",
        id: "x",
        old: { ...oldOnly, tokens: "0 2 0", types: "3 7 0" },
        new: { ...oldOnly },
      },
    ],
  },
  [...index.tokenClasses],
  [...index.typeTable],
);
const recoded = foreign.get("x").old;
check(
  "an old-side highlight span keeps its own table's class",
  decodeSpans(recoded.tokens, [...index.tokenClasses, "kw"])[0]?.cls === "kw",
  recoded.tokens,
);
check(
  "an old-side local type resolves against its own table",
  decodeSpans(recoded.types, [...index.typeTable, "Int"])[0]?.cls === "Int",
  recoded.types,
);

// Offsets arrive as UTF-8 byte counts and a JavaScript string is indexed in code
// units. The old revision's records are painted like any other, so they need the
// same translation — and nothing else here would notice, since the artifact the
// other checks read is the current revision's.
const utf8 = (t) => new TextEncoder().encode(t).length;
const arrowed = 'fn f() = concat("\u2192", g)';
const g = arrowed.indexOf("g", arrowed.indexOf("\u2192"));
const shifted = new Revisions(
  {
    envelope: {
      format: "prism-index-diff-v1",
      old: { title: "t", contract: "a" },
      new: { title: "t", contract: "b" },
      counts: { changed: 1, added: 0, removed: 0, moved: 0, cone: 0, cosmetic: 0, unchanged: 0 },
    },
    entries: [
      {
        status: "changed",
        id: "x",
        old: {
          ...index.byId.get("Data.List.map"),
          source: arrowed,
          members: [],
          refs: [
            { start: utf8(arrowed.slice(0, g)), end: utf8(arrowed.slice(0, g)) + 1, target: "y" },
          ],
          tokens: "",
        },
      },
    ],
  },
  index.tokenClasses,
);
const moved = shifted.get("x").old;
check(
  "a byte offset past a multi-byte character lands on the right character",
  moved.source.slice(moved.refs[0].start, moved.refs[0].end) === "g",
  JSON.stringify(moved.source.slice(moved.refs[0].start, moved.refs[0].end)),
);

section("keyboard shortcuts yield to text fields");
// The one exception, and the reason it is checked: a modified shortcut has to
// work from inside the field it focuses, so it is handled before the guard.
let focused = 0;
deck.search.focus = () => focused++;
deck.search.select = () => {};
v.onKey({ key: "k", metaKey: true, target: deck.search, preventDefault() {} });
v.onKey({ key: "K", ctrlKey: true, target: { tagName: "TEXTAREA" }, preventDefault() {} });
check("cmd-K reaches the search box from anywhere", focused === 2, `${focused} focus calls`);
v.onKey({ key: "/", target: { tagName: "TEXTAREA" }, preventDefault() {} });
check("a bare slash still yields to a text field", focused === 2);

check("a textarea is editable", isEditable({ tagName: "textarea" }));
check("an input is editable", isEditable({ tagName: "INPUT" }));
check("contenteditable is editable", isEditable({ tagName: "DIV", isContentEditable: true }));
check("a pre is not, so bodies stay navigable", !isEditable({ tagName: "PRE" }));
check("null is not", !isEditable(null));

section("review marks classify what moved");
const store = new Storage();
const review = new Review("t", store);
const target = index.byId.get("Data.List.map");
review.set(target, { reviewed: true, note: "checked" }, 1);
check("current against the same revision", freshness(review.get(target.id), target) === "current");
check(
  "changed when text and address move",
  freshness(review.get(target.id), { ...target, hash: "x", source: "different" }) === "changed",
);
check(
  "cone when only the address moves",
  freshness(review.get(target.id), { ...target, hash: "x" }) === "cone",
);
check(
  "cosmetic when only the text moves",
  freshness(review.get(target.id), { ...target, source: "reformatted" }) === "cosmetic",
);
check(
  "a reformat does not demand re-review",
  !needsAttention(review.get(target.id), { ...target, source: "reformatted" }),
);
check("an edit does", needsAttention(review.get(target.id), { ...target, hash: "x", source: "d" }));
// Equal hashes prove equal executable behavior and nothing more: a claims,
// visibility, doc, or deprecation edit is invisible to the hash (and a doc edit
// to the text too), and each is authored — the same carve-out the compiler's
// diff classification makes.
check(
  "a trust-root edit is not cosmetic",
  freshness(review.get(target.id), { ...target, claims: ["assume-total"] }) === "changed",
);
check(
  "a doc-only edit is an edit",
  freshness(review.get(target.id), { ...target, doc: "rewritten" }) === "changed",
);
check(
  "a mark from before the stamp existed degrades to the hash rule",
  freshness({ ...review.get(target.id), meta: undefined }, { ...target, doc: "rewritten" }) ===
    "current",
);
check("marks persist across a reload", new Review("t", store).get(target.id)?.note === "checked");
// A patch that carries `note: undefined` is a request to clear it, which `??`
// could not distinguish from a patch that says nothing about the note at all.
review.set(target, { note: undefined }, 2);
check("and a cleared note is cleared", review.get(target.id)?.note === undefined);
check("keeping the read mark it was attached to", review.get(target.id)?.reviewed === true);

section("marks follow a definition across renames and file moves");
// A move changes the canonical name a mark is keyed by while preserving what the
// mark is about. A loaded diff knows the rename as a fact; without one, the
// stamped hash finds the definition again — but only unambiguously.
const moveStore = new Storage();
const movable = new Review("t", moveStore);
movable.set(target, { reviewed: true, note: "looked at" }, 1);
// A rename's destination exists in the new revision, as a diff's moved entry's
// `id` always does.
const renamedTo = index.defs.find((d) => d.hash && d.id !== target.id).id;
movable.rekey(new Map([[target.id, renamedTo]]), index);
check("a diff-reported rename re-keys the mark", movable.get(renamedTo)?.note === "looked at");
check("and leaves nothing under the old name", movable.get(target.id) === undefined);
check(
  "the re-key survives a reload",
  new Review("t", moveStore).get(renamedTo)?.note === "looked at",
);
const hashStore = new Storage();
const byAddress = new Review("t", hashStore);
byAddress.set({ ...target, id: "Old.Home.map" }, { reviewed: true }, 1);
check(
  "this fixture's hash is unique",
  index.defs.filter((d) => d.hash === target.hash).length === 1,
);
byAddress.rekey(new Map(), index);
check(
  "a vanished id follows its unambiguous content address",
  byAddress.get(target.id)?.reviewed === true,
);

section("a context packet is assembled from compiler facts");
const p = packet({ index, rel, review, selected: ["Data.List.concat_map", "Data.List.flatten"] });
check("names the revision", p.includes(index.envelope.contract.slice(0, 16)));
check("carries each body", p.includes("fn concat_map") && p.includes("fn flatten"));
check("carries types", p.includes("Type: `"));
check("pulls in the closure", p.includes("## Reached by the above"));
check("relates the selection", p.includes("## Between the selected definitions"));
check("an empty selection yields nothing", packet({ index, rel, review, selected: [] }) === "");

done();
