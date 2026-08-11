// A viewer for Prism code, over the `prism index` artifact.
//
// This is a reading tool, not an editor and not a second documentation site. It
// is built on two properties of the index (compiler.html#code-index): a
// definition is addressed by content hash rather than located by file, and the
// relationships between definitions are carried as a whole edge set rather than
// answered one question at a time. So navigation here is by *definition*, in
// either direction along any relation, and the URL of a view is the definition's
// canonical name.
//
// It deliberately does not load the wasm compiler. Every fact it renders is baked
// into the artifact — the same discipline the book's typed tooltips follow, where
// hovering a subterm runs no compiler. That keeps the viewer a pure function of
// one JSON file, which is what lets it open any project's index, including one
// generated somewhere else and handed over.

import "./viewer.css";
import {
  type Def,
  type DiffEntry,
  decodeSpans,
  type EdgeKind,
  type Envelope,
  Index,
  type IndexModule,
  Members,
  Mentions,
  Relations,
  Revisions,
} from "./viewer-model.js";
import { freshness, Review, type Mark as ReviewMark } from "./viewer-review.js";

// The relations shown on a card, in the order a reviewer asks for them: who
// depends on this, what it depends on, what proves it, what it can do.
const RELATIONS: { kind: EdgeKind; dir: "in" | "out"; label: string; hint: string }[] = [
  { kind: "calls", dir: "in", label: "callers", hint: "definitions whose body calls this" },
  { kind: "calls", dir: "out", label: "calls", hint: "definitions this body calls" },
  { kind: "tests", dir: "in", label: "tested by", hint: "tests whose closure reaches this" },
  { kind: "tests", dir: "out", label: "covers", hint: "definitions this test exercises" },
  { kind: "uses-type", dir: "in", label: "used by", hint: "definitions whose type mentions this" },
  { kind: "uses-type", dir: "out", label: "types", hint: "types this signature mentions" },
  { kind: "performs", dir: "out", label: "performs", hint: "effects in this row" },
  { kind: "performs", dir: "in", label: "performed by", hint: "definitions performing this" },
  { kind: "handles", dir: "out", label: "handles", hint: "effects this interprets with a handler" },
  {
    kind: "handles",
    dir: "in",
    label: "handled by",
    hint: "definitions that interpret this effect — what gives it its meaning",
  },
  { kind: "instance-of", dir: "out", label: "instance of", hint: "the class this implements" },
  { kind: "instance-of", dir: "in", label: "instances", hint: "instances of this class" },
];

// One search result: a definition, or one member of one, with how well it matched
// (0 exact, 1 prefix, 2 substring, 3 only through the module path).
type Hit = { def: Def; member?: string; score: number };

// What a member of each kind of declaration is called.
const MEMBER_OF: Record<string, string> = {
  type: "constructor",
  synonym: "constructor",
  stable: "constructor",
  class: "method",
  effect: "operation",
  error: "operation",
};

// How well `name` matches a lowercased query; -1 for no match.
const rank = (name: string, q: string): number => {
  const n = name.toLowerCase();
  return n === q ? 0 : n.startsWith(q) ? 1 : n.includes(q) ? 2 : -1;
};

// One span in a body that gets its own markup: a reference the compiler resolved,
// or the declaration site of one of this declaration's own members.
type Mark = { start: number; end: number; target: string; member?: string; ty?: string };

const HASH_CHIP = 7;
// How many definition rows the rail will draw at once. Only expanded modules
// spend it, so with everything collapsed it is never reached.
const ROWS = 400;
// How many chips a relation row shows before offering the rest on request.
//
// Low, because the rows multiply: `Option` has one for each of its constructors
// and one for the definitions typed by it, so a cap of 24 gave that card seventy
// chips under a one-line definition. The count on the label is always the true
// one, and the rest is one click away.
const CHIPS = 12;

const el = <T extends HTMLElement>(id: string): T => document.getElementById(id) as T;
const esc = (s: string): string =>
  s.replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" })[c] ?? c);

class Viewer {
  private readonly rel: Relations;
  private readonly members: Members;
  private readonly mentions: Mentions;
  // The working set: the definitions currently open, in the order they were
  // opened. A reviewer holds several definitions in mind at once and wants them
  // side by side, not one replacing the last (Code Bubbles, Bragdon et al. 2010).
  private open: string[] = [];
  private focused: string | null = null;
  // Which open cards are folded shut. Cards open expanded: a reader who opened a
  // definition asked for the definition. Kept here rather than in the DOM so a
  // fold survives the next render.
  private readonly folded = new Set<string>();
  // The modules whose definitions the rail is showing. Empty is the default: the
  // rail opens as a list of modules.
  private readonly openMods = new Set<string>();
  // The relation rows the reader asked to see in full.
  private readonly wide = new Set<string>();
  // The cards whose note field is open. A note is rare and a definition is not, so
  // the field appears when there is one or when it has been asked for, rather than
  // standing on every card in the deck waiting to be used.
  private readonly noting = new Set<string>();
  private readonly review: Review;

  constructor(
    private readonly index: Index,
    /// The other revision, when one was supplied. Absent means the pair's two
    /// sides are the same, which is what reading a single revision is.
    private readonly revs: Revisions | null,
    private readonly nodes: {
      cards: HTMLElement;
      list: HTMLElement;
      search: HTMLInputElement;
      title: HTMLElement;
      empty: HTMLElement;
      rail: HTMLElement;
      main: HTMLElement;
      railToggle: HTMLElement;
    },
    storage: Storage | null = null,
    /// The mark store's namespace. The caller joins the artifact URL with the
    /// title (see `boot`): the title alone is not unique across projects, and
    /// the contract moves on every revision.
    unit: string = index.envelope.title,
  ) {
    this.rel = new Relations(index);
    this.members = new Members(index);
    this.mentions = new Mentions(index);
    this.review = new Review(unit, storage);
    // Follow marks across the renames a loaded diff knows as facts, and across
    // file moves by unambiguous content address.
    this.review.rekey(
      new Map(
        (revs?.all() ?? [])
          .filter((e) => e.status === "moved" && e.old_id !== undefined)
          .map((e) => [e.old_id as string, e.id]),
      ),
      index,
    );
  }

  start(): void {
    this.showRail(this.review.railShown());
    const counts = this.revs?.envelope.counts;
    const title = counts
      ? `${this.index.envelope.title} — ${counts.changed} changed, ${counts.cone} in the cone`
      : this.index.envelope.title;
    this.nodes.title.innerHTML =
      esc(title) + testLayer(this.index.envelope.tests) + brokenModules(this.index.modules);
    this.renderList("");
    this.nodes.search.addEventListener("input", () => this.renderList(this.nodes.search.value));
    window.addEventListener("hashchange", () => this.fromUrl());
    document.addEventListener("keydown", (e) => this.onKey(e));
    // Render before consulting the URL: with no fragment nothing is open, and the
    // deck still has to show what this surface is for rather than nothing at all.
    this.render();
    this.fromUrl();
  }

  // The URL fragment is the focused definition's canonical name, so any view is a
  // link: the address is stable across reformatting and file moves in a way a
  // file-and-line anchor is not.
  private fromUrl(): void {
    const id = decodeURIComponent(location.hash.replace(/^#/, ""));
    if (id && id !== this.focused && (this.lookup(id) || this.index.builtins.has(id))) {
      this.show(id);
    }
  }

  // The definition to render for `id`: the current revision's, or — for an id
  // the diff reports as removed — the old revision's record. A removed
  // definition exists only on the old side, and its review row would otherwise
  // be a dead button pointing at something `show` refuses to open.
  private lookup(id: string): Def | undefined {
    const e = this.revs?.get(id);
    return this.index.byId.get(id) ?? (e?.status === "removed" ? e.old : undefined);
  }

  // Page shortcuts, suppressed wherever the reader is typing.
  //
  // Every branch here has to check that, not just the ones that obviously look
  // dangerous: a bare `Backspace` that navigates is also a `Backspace` that
  // deletes a character, and `preventDefault` on it makes a text field silently
  // refuse to edit.
  private onKey(e: KeyboardEvent): void {
    // Checked before the editable guard, and only this one is: the point of a
    // modified shortcut is that it works from anywhere, including from inside the
    // field it focuses (where it selects what is there, so the next keystroke
    // replaces it).
    if ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === "k") {
      e.preventDefault();
      this.focusSearch();
      return;
    }
    if (isEditable(e.target)) {
      // Escape leaves the field rather than reaching the page, and clears the
      // search box when that is what is being escaped.
      if (e.key === "Escape") {
        if (e.target === this.nodes.search) {
          this.nodes.search.value = "";
          this.renderList("");
        }
        (e.target as HTMLElement).blur();
      }
      return;
    }
    if (e.key === "/") {
      e.preventDefault();
      this.focusSearch();
    } else if (e.key === "\\") {
      e.preventDefault();
      this.toggleRail();
    }
  }

  // Open `id`, or focus it if it is already in the deck.
  //
  // There is no back stack. The deck *is* the trail: what you followed is still
  // open, in the order you opened it, and clicking it again is how you return —
  // which is the working-set model doing the job a history stack was bolted on to
  // do, less well.
  show(id: string): void {
    if (!this.lookup(id) && !this.index.builtins.has(id)) return;
    if (!this.open.includes(id)) this.open.push(id);
    this.focused = id;
    history.replaceState(null, "", `#${encodeURIComponent(id)}`);
    this.render();
    this.reveal(id);
  }

  private close(id: string): void {
    this.open = this.open.filter((o) => o !== id);
    if (this.focused === id) this.focused = this.open.at(-1) ?? null;
    this.render();
  }

  private reveal(id: string): void {
    const card = this.nodes.cards.querySelector<HTMLElement>(`[data-card="${cssEscape(id)}"]`);
    card?.scrollIntoView({ behavior: "smooth", block: "nearest" });
    card?.classList.add("is-flash");
    setTimeout(() => card?.classList.remove("is-flash"), 600);
  }

  // Reach the search box, bringing the rail back if it was put away.
  //
  // Not a convenience: the box lives in the rail, and a hidden element cannot take
  // focus, so with the rail stowed the shortcut did nothing whatsoever. Asking to
  // search is asking for the list of results, so it stays out afterwards.
  private focusSearch(): void {
    this.showRail(true);
    this.nodes.search.focus();
    this.nodes.search.select();
  }

  /// Show or hide the definition list.
  ///
  /// Remembered, because a reader who put it away wants it to stay away: reading
  /// one definition and its relations needs no list, and the deck is wider without
  /// it. The control stays in the header rather than on the rail, so it is still
  /// there to press when the rail is gone.
  toggleRail(): void {
    this.showRail(this.nodes.rail.hidden);
  }

  private showRail(shown: boolean): void {
    this.nodes.rail.hidden = !shown;
    this.nodes.main.classList.toggle("is-alone", !shown);
    this.nodes.railToggle.setAttribute("aria-expanded", String(shown));
    this.nodes.railToggle.setAttribute(
      "aria-label",
      shown ? "Hide the definition list" : "Show the definition list",
    );
    this.nodes.railToggle.dataset.tip = shown
      ? "hide the definition list  ( \\ )"
      : "show the definition list  ( \\ )";
    this.review.setRailShown(shown);
  }

  /// Show or hide one module's definitions in the rail.
  toggleModule(module: string): void {
    if (!this.openMods.delete(module)) this.openMods.add(module);
    this.renderList(this.nodes.search.value);
  }

  // The left rail: the modules, collapsed, over a search that reaches into all of
  // them.
  //
  // Collapsed because the flat list was more than a thousand rows and led with an
  // answer to a question nobody asked. Which module something is in is the first
  // choice a reader makes, and forty module names is a surface you can read;
  // twelve hundred definitions is one you can only search.
  //
  // Searching expands whatever matched and drops the toggles: with a query the
  // list is a result set, and a collapsed result is a result withheld. Matching on
  // the canonical name means `Data.List` narrows to a module and `map` finds every
  // definition of that name across modules, both useful and neither special-cased.
  private renderList(query: string): void {
    const q = query.trim().toLowerCase();
    const found = this.search(q);
    // With a revision pair, what the author touched leads: on a real change the
    // cone dwarfs it, and a list that mixes the two buries the review.
    let html = this.changeList(q) + this.builtinGroup(q);
    let budget = ROWS;
    for (const g of found.groups) {
      const open = Boolean(q) || this.openMods.has(g.module);
      const name = `${esc(g.module || "(root)")}<span class="rail-n">${g.hits.length}</span>`;
      html += `<li class="rail-mod">${
        q
          ? `<span class="rail-head">${name}</span>`
          : `<button class="rail-head" data-mod="${esc(g.module)}" aria-expanded="${open}">${name}</button>`
      }</li>`;
      if (!open) continue;
      const shown = g.hits.slice(0, Math.max(budget, 0));
      budget -= shown.length;
      for (const hit of shown) html += this.railRow(hit);
      if (shown.length < g.hits.length) {
        html += `<li class="rail-more">${g.hits.length - shown.length} more; keep typing</li>`;
      }
    }
    html += this.resultGroup("in the text", found.text, budget);
    if (found.groups.length + found.text.length === 0) {
      html += `<li class="rail-more">nothing matches</li>`;
    }
    // Rebuilding resets the scroll, which on a toggle throws away the very header
    // the reader just clicked.
    const at = this.nodes.list.scrollTop;
    this.nodes.list.innerHTML = html;
    this.nodes.list.scrollTop = at;
  }

  // The compiler's primitives, above the modules: not a module (nothing
  // declares them), but every program stands on them, and a reader who follows
  // `Unit` or `byte_at` out of a body should find the same names browsable where
  // the browsing starts. Collapsed by default like any module, expanded by a
  // query that matches, and ranked the same way the modules rank their hits.
  private builtinGroup(query: string): string {
    const all = [...this.index.builtins.values()];
    const hits = query
      ? all
          .map((p) => ({ p, score: rank(p.name, query) }))
          .filter((h) => h.score >= 0)
          .sort((a, b) => a.score - b.score)
          .map((h) => h.p)
      : all;
    if (hits.length === 0) return "";
    const key = "(builtins)";
    const open = Boolean(query) || this.openMods.has(key);
    const name = `Builtins<span class="rail-n">${hits.length}</span>`;
    let html = `<li class="rail-mod">${
      query
        ? `<span class="rail-head">${name}</span>`
        : `<button class="rail-head" data-mod="${esc(key)}" aria-expanded="${open}">${name}</button>`
    }</li>`;
    if (!open) return html;
    // Three subcategories, each labelled: a wired type, a wired effect, and a
    // builtin function are different answers to "what is this", and one flat
    // run of 180 names buried the nine types and three effects entirely.
    const sections: [string, string][] = [
      ["type", "types"],
      ["effect", "effects"],
      ["value", "functions"],
    ];
    for (const [kind, label] of sections) {
      const of = hits.filter((p) => (p.kind ?? "value") === kind);
      if (of.length === 0) continue;
      html += `<li class="rail-sub">${label}</li>`;
      for (const p of of) {
        html += `<li><button class="rail-def" data-goto="${esc(p.name)}"
          data-tip="${esc(this.index.describe(p.name))}">
          <span class="rail-name">${esc(p.name)}</span>
          ${kindBadge(p.kind ?? "value")}
        </button></li>`;
      }
    }
    return html;
  }

  // What a query finds.
  //
  // A declaration's *members* are results in their own right. `Cons`, `Nil` and
  // `pure` are not definitions and so were unfindable — only the `List` and the
  // `Applicative` that introduce them were in the rail at all — and listing them
  // as their owner ("List, matched Cons") answered a question nobody asked. A
  // constructor is a name a reader looks up by name, so it appears under its
  // module as itself, badged with what it is, and opening it goes to the
  // declaration it lives in.
  //
  // Ranked by how well the name matched rather than by artifact order, because an
  // exact hit is almost always the one wanted: a search for `cons` was returning
  // `const`, `Console`, `cons_validation` and six others above `Cons` itself.
  // Modules lead with their best hit for the same reason.
  //
  // Text matches stay a separate tier at the end. They are a different question —
  // "where does this string appear" rather than "what is this called" — and there
  // are two hundred of them for a name like `Cons`, which would bury everything
  // above.
  private search(q: string): { groups: { module: string; hits: Hit[] }[]; text: Def[] } {
    if (!q) {
      return { groups: this.byModule(this.index.defs.map((def) => ({ def, score: 3 }))), text: [] };
    }
    const hits: Hit[] = [];
    const text: Def[] = [];
    for (const d of this.index.defs) {
      let matched = false;
      const own = rank(d.name, q);
      if (own >= 0) {
        hits.push({ def: d, score: own });
        matched = true;
      } else if (d.id.toLowerCase().includes(q)) {
        // Matched only through its module path, which is how `Data.List` narrows
        // to a module: a weaker hit than any match on the name itself.
        hits.push({ def: d, score: 3 });
        matched = true;
      }
      for (const { name } of d.members ?? []) {
        const score = rank(name, q);
        if (score >= 0) {
          hits.push({ def: d, member: name, score });
          matched = true;
        }
      }
      if (!matched && d.source.toLowerCase().includes(q)) text.push(d);
    }
    return { groups: this.byModule(hits), text };
  }

  // Group hits by module, best hit first, keeping artifact order among equals.
  // `sort` is stable, so ties never reshuffle between keystrokes.
  private byModule(hits: Hit[]): { module: string; hits: Hit[] }[] {
    const by = new Map<string, Hit[]>();
    for (const h of hits) {
      const at = by.get(h.def.module);
      if (at) at.push(h);
      else by.set(h.def.module, [h]);
    }
    return [...by]
      .map(([module, group]) => ({
        module,
        hits: [...group].sort((a, b) => a.score - b.score),
      }))
      .sort((a, b) => a.hits[0].score - b.hits[0].score);
  }

  // One rail row, for a definition or for a member of one.
  private railRow(hit: Hit): string {
    const { def: d, member } = hit;
    if (member === undefined) {
      return `<li><button class="rail-def" data-goto="${esc(d.id)}" data-tip="${esc(this.index.describe(d.id))}">
        <span class="rail-name">${esc(d.name)}</span>
        ${kindBadge(d.kind)}
      </button></li>`;
    }
    const what = MEMBER_OF[d.kind] ?? "member";
    return `<li><button class="rail-def" data-goto="${esc(d.id)}" data-member="${esc(member)}"
      data-tip="${esc(this.aboutMember(d, member))}">
      <span class="rail-name">${esc(member)}</span>
      <span class="kind kind--member">${esc(what)}</span>
    </button></li>`;
  }

  // One tier of results: a flat list under its own header, showing the whole
  // canonical name. Module grouping is for browsing; these are answers.
  private resultGroup(label: string, hits: Def[], budget: number): string {
    if (hits.length === 0) return "";
    const shown = hits.slice(0, Math.max(budget, 0));
    const rows = shown
      .map(
        (d) =>
          `<li><button class="rail-def" data-goto="${esc(d.id)}" data-tip="${esc(this.index.describe(d.id))}">
          <span class="rail-name">${esc(d.id)}</span>
          ${kindBadge(d.kind)}
        </button></li>`,
      )
      .join("");
    const rest =
      hits.length > shown.length
        ? `<li class="rail-more">${hits.length - shown.length} more; keep typing</li>`
        : "";
    return `<li class="rail-mod"><span class="rail-head">${esc(label)}
      <span class="rail-n">${hits.length}</span></span></li>${rows}${rest}`;
  }

  // What to say about one member of a declaration.
  //
  // The count is the honest one, including zero — and zero is the common case for
  // an effect operation, because a library declares `Output` and *programs*
  // perform it. Saying so, and naming the handlers that give it meaning instead,
  // is the difference between "this index is missing something" and "this is
  // interpreted, not called".
  private aboutMember(d: Def, member: string): string {
    const what = MEMBER_OF[d.kind] ?? "member";
    const n = this.members.users(d.id, member).length;
    const lines = [member, `${what} of ${d.id}`];
    if (n > 0) {
      lines.push(`used in ${n} definition${n === 1 ? "" : "s"}`);
      return lines.join("\n");
    }
    const handlers = this.rel.get("handles", "in", d.id).length;
    lines.push(
      handlers > 0
        ? `no definition here performs it; the effect is handled by ${handlers}`
        : "nothing in this index uses it",
    );
    return lines.join("\n");
  }

  /// Bring a member's row of users into view on an already-open card.
  revealMember(id: string, name: string): void {
    const row = this.nodes.cards.querySelector<HTMLElement>(
      `[data-card="${cssEscape(id)}"] [data-uses="${cssEscape(name)}"]`,
    );
    row?.scrollIntoView({ behavior: "smooth", block: "nearest" });
    row?.classList.add("is-flash");
    setTimeout(() => row?.classList.remove("is-flash"), 600);
  }

  // The changed definitions, at the top of the rail, authored work first.
  //
  // `cone` entries are deliberately not listed: they are the *consequence* of the
  // authored ones and are reachable from them, and on any change of size there
  // are far more of them than of the edits a reviewer came to read. They stay
  // visible where they matter, as a badge on the definition itself.
  private changeList(query: string): string {
    const all = (this.revs?.all() ?? []).filter(
      (e) => !query || e.id.toLowerCase().includes(query),
    );
    const authored = all.filter((e) => e.status !== "cone" && e.status !== "cosmetic");
    // The consequences are offered, collapsed, rather than withheld. Leading with
    // them would be wrong — on a real change the cone dwarfs the edits a reviewer
    // came to read — but leaving them out of the rail entirely made the header
    // count three cone entries the rail gave no way to reach.
    return (
      this.changeGroup("changed in this revision", authored, true) +
      this.changeGroup(
        "in the cone",
        all.filter((e) => e.status === "cone"),
        false,
      ) +
      this.changeGroup(
        "cosmetic",
        all.filter((e) => e.status === "cosmetic"),
        false,
      )
    );
  }

  // One group of revision entries. The authored group always stands open; the two
  // consequence groups toggle like a module.
  private changeGroup(label: string, entries: DiffEntry[], always: boolean): string {
    if (entries.length === 0) return "";
    const key = `revision: ${label}`;
    const open = always || this.openMods.has(key);
    const count = `<span class="rail-n">${entries.length}</span>`;
    const head = always
      ? `<span class="rail-head">${esc(label)}${count}</span>`
      : `<button class="rail-head" data-mod="${esc(key)}" aria-expanded="${open}">${esc(label)}${count}</button>`;
    const rows = open
      ? entries
          .map(
            (e) => `<li><button class="rail-def" data-goto="${esc(e.id)}"
              data-tip="${esc(this.index.describe(e.id))}">
              <span class="rail-name">${esc(shortName(e.id))}</span>
              <span class="status status--${e.status}">${e.status}</span>
            </button></li>`,
          )
          .join("")
      : "";
    return `<li class="rail-mod">${head}</li>${rows}`;
  }

  /// Mark a definition read, or clear the mark, stamping the revision it was
  /// read at so a later visit can say what moved.
  toggleReviewed(id: string, now: number): void {
    const def = this.lookup(id);
    if (!def) return;
    const was = this.review.get(id)?.reviewed ?? false;
    this.review.set(def, { reviewed: !was }, now);
    this.render();
    this.renderList(this.nodes.search.value);
  }

  /// Open a card's note field and put the caret in it.
  writeNote(id: string): void {
    this.noting.add(id);
    this.render();
    this.nodes.cards
      .querySelector<HTMLTextAreaElement>(`[data-card="${cssEscape(id)}"] [data-note]`)
      ?.focus();
  }

  /// Attach or replace a note.
  setNote(id: string, note: string, now: number): void {
    const def = this.lookup(id);
    if (!def) return;
    this.review.set(def, { note: note.trim() || undefined }, now);
    // Emptied is closed: the mark is gone, so leaving the field behind would show
    // an input for something that no longer exists.
    if (!note.trim()) {
      this.noting.delete(id);
      this.render();
    }
    this.renderList(this.nodes.search.value);
  }

  private render(): void {
    this.nodes.empty.hidden = this.open.length > 0;
    this.nodes.cards.innerHTML = this.open.map((id) => this.card(id)).join("");
    for (const b of this.nodes.cards.querySelectorAll<HTMLElement>("[data-fold]")) {
      b.addEventListener("click", () => {
        const card = b.closest<HTMLElement>(".card");
        const id = card?.dataset.card ?? "";
        const shut = !this.folded.delete(id);
        if (shut) this.folded.add(id);
        card?.classList.toggle("is-folded", shut);
        b.setAttribute("aria-expanded", String(!shut));
      });
    }
    for (const b of this.nodes.cards.querySelectorAll<HTMLElement>("[data-close]")) {
      b.addEventListener("click", () => this.close(b.dataset.close ?? ""));
    }
    for (const t of this.nodes.cards.querySelectorAll<HTMLTextAreaElement>("[data-note]")) {
      t.addEventListener("change", () => this.setNote(t.dataset.note ?? "", t.value, Date.now()));
    }
  }

  private card(id: string): string {
    const d = this.lookup(id);
    if (!d) return this.builtinCard(id);
    const focused = id === this.focused ? " is-focused" : "";
    const mark = this.review.get(id);
    // A definition's own text is what a reviewer reads, so the body is the card's
    // subject and it is shown: opening a card is already the reader asking for it,
    // and a second click to see what they asked for is a click that buys nothing.
    // Folding stays for a card being kept open for reference.
    const shut = this.folded.has(id);
    // Nothing relates to `compose` in either direction — it calls only its own
    // parameters — and an empty strip is a bordered band of nothing, so it goes.
    const rel = this.relations(id);
    return `<article class="card${focused}${shut ? " is-folded" : ""}" data-card="${esc(id)}">
      <header class="card-head">
        ${kindBadge(d.kind)}
        <button class="card-name" data-fold aria-expanded="${!shut}">${esc(qualified(d))}</button>
        ${d.vis === "public" ? '<span class="tag tag--pub">pub</span>' : ""}
        ${d.vis === "opaque" ? '<span class="tag tag--pub">opaque</span>' : ""}
        ${(d.claims ?? []).map((c) => `<span class="tag tag--claim">${esc(c)}</span>`).join("")}
        ${d.deprecated ? `<span class="tag tag--dep" data-tip="${esc(`deprecated: ${d.deprecated}`)}">deprecated</span>` : ""}
        <span class="grow"></span>
        ${this.seen(id, mark)}
        <button class="seen${mark?.note ? " is-on" : ""}" data-write-note="${esc(id)}"
          data-tip="${mark?.note ? "edit this note" : "attach a note"}">note</button>
        ${hashChip(d)}
        <button class="card-x" data-close="${esc(id)}" data-tip="close">&times;</button>
      </header>
      ${this.since(id)}
      ${this.signature(d)}
      ${this.effectRow(d)}
      ${d.doc ? `<div class="card-doc">${renderDoc(d.doc)}</div>` : ""}
      ${this.before(id)}
      ${this.sources(d)}
      ${rel ? `<div class="card-rel">${rel}</div>` : ""}
      ${
        mark?.note || this.noting.has(id)
          ? `<textarea class="card-note" data-note="${esc(id)}" rows="1"
        placeholder="note">${esc(mark?.note ?? "")}</textarea>`
          : ""
      }
    </article>`;
  }

  // A compiler primitive's card, synthesized from the artifact's `builtins` row.
  //
  // A builtin has no declaration, no content address and no revision history, so
  // the card carries none of the review apparatus: no read mark, no note, no
  // hash chip. And no relation strip either: a primitive is used from everywhere
  // by definition, so "used by" would be a list of most of the index, which
  // answers nothing. What the compiler recorded (the signature and a sentence of
  // documentation) is the whole card.
  private builtinCard(id: string): string {
    const p = this.index.builtins.get(id);
    if (!p) return "";
    const focused = id === this.focused ? " is-focused" : "";
    const shut = this.folded.has(id);
    return `<article class="card card--builtin${focused}${shut ? " is-folded" : ""}" data-card="${esc(id)}">
      <header class="card-head">
        ${kindBadge(p.kind ?? "value")}
        ${builtinBadge()}
        <button class="card-name" data-fold aria-expanded="${!shut}">${esc(p.name)}</button>
        <span class="grow"></span>
        <span class="hash hash--none" data-tip="no content address: implemented in the compiler, not defined in Prism">&mdash;</span>
        <button class="card-x" data-close="${esc(id)}" data-tip="close">&times;</button>
      </header>
      ${p.signature ? `<div class="card-sig"><code>${esc(p.name)} : ${this.linkedSig(p.signature)}</code></div>` : ""}
      ${p.doc ? `<div class="card-doc"><p>${esc(p.doc)}</p></div>` : ""}
    </article>`;
  }

  // A builtin's signature arrives as a plain string: no spans and no token
  // table, because nothing lexed it. But the names inside it are the same names
  // a painted body links, so the card resolves what it can: every identifier
  // that names a definition or another primitive becomes the same navigation a
  // painted reference is, and the rest stays text.
  private linkedSig(sig: string): string {
    return esc(sig).replace(/[A-Za-z_][A-Za-z0-9_]*/g, (word) => {
      const prim = this.index.builtins.has(word);
      if (!prim && !this.index.byId.has(word)) return word;
      const cls = prim ? "ref ref--prim" : "ref";
      return `<button class="${cls}" data-goto="${word}" data-tip="${esc(
        this.index.describe(word),
      )}">${word}</button>`;
    });
  }

  // The read mark. Its freshness is a comparison against the revision the mark was
  // made at, not against a loaded pair, so it does its job on a single index too:
  // mark, edit, re-index, and the card says whether what moved was the formatting
  // or the behavior.
  private seen(id: string, mark: ReviewMark | undefined): string {
    const tip = mark?.reviewed ? "reviewed; click to clear" : "mark reviewed at this address";
    return `<button class="seen${mark?.reviewed ? " is-on" : ""}" data-reviewed="${esc(id)}"
      data-tip="${tip}">read</button>`;
  }

  // What has happened to this definition since it was marked read.
  //
  // The whole reason a mark is anchored to a content address: it can say which
  // *kind* of change happened. A reformat is dismissed outright, a dependency
  // shift is named as one, and only a real edit asks for the definition to be
  // read again. A line-anchored mark can say none of this, because it cannot tell
  // the three apart.
  private since(id: string): string {
    const mark = this.review.get(id);
    if (!mark?.reviewed) return "";
    const at = `at <code>${esc(mark.hash?.slice(0, 7) ?? "?")}</code>`;
    switch (freshness(mark, this.index.byId.get(id))) {
      case "current":
        return `<div class="card-seen">reviewed ${at}, still current</div>`;
      case "cosmetic":
        return `<div class="card-seen">reviewed ${at}; reformatted since, behavior unchanged</div>`;
      case "cone":
        return `<div class="card-seen is-warn">reviewed ${at}; unchanged here, but a dependency moved</div>`;
      case "gone":
        return `<div class="card-seen is-warn">reviewed ${at}; no longer in this revision</div>`;
      default:
        return `<div class="card-seen is-warn">reviewed ${at}; <b>edited since</b> — read again</div>`;
    }
  }

  // What the other revision had, when it had something different.
  //
  // A `cone` entry gets a sentence rather than a second copy of identical text:
  // its bytes did not move, only its address did, because something it depends on
  // changed. Saying that plainly is the whole reason the classification exists —
  // it is the difference between a reviewer reading three edits and scrolling
  // past forty-seven.
  private before(id: string): string {
    const e = this.revs?.get(id);
    if (!e) return "";
    const was = e.old_id && e.old_id !== id ? ` &middot; was <code>${esc(e.old_id)}</code>` : "";
    const head = (note: string): string =>
      `<div class="card-was"><span class="status status--${e.status}">${e.status}</span>${note}${was}</div>`;
    switch (e.status) {
      case "cone":
        return head(" text unchanged; re-addressed because a dependency moved");
      case "added":
        return head(" new in this revision");
      case "removed":
        return head(" gone in this revision");
      case "moved":
        return head(" same bytes, new name");
      default:
        return head(e.status === "cosmetic" ? " same behavior, different text" : " previously");
    }
  }

  // The definition's text, beside the other revision's when there is one.
  //
  // Side by side rather than stacked: the two versions of a definition are being
  // compared, and comparing means reading across, not scrolling. The left pane is
  // painted and linked exactly like the right one, from the old revision's own
  // occurrence rows — a name in the version you are moving away from is as worth
  // following as one in the version you are moving to, and the artifact carries
  // what it needs to do that. A target the old revision had and this one does not
  // keeps its text without becoming a link, the same rule every other reference
  // outside the index follows.
  private sources(d: Def): string {
    const old = this.revs?.get(d.id)?.old;
    const now = `<pre class="card-src"><code>${this.body(d)}</code></pre>`;
    if (!old || old.source === d.source) return now;
    return `<div class="card-diff">
      <div class="card-pane">
        <div class="card-pane-head">before</div>
        <pre class="card-src card-src--was"><code>${this.body(old)}</code></pre>
      </div>
      <div class="card-pane">
        <div class="card-pane-head">after</div>
        ${now}
      </div>
    </div>`;
  }

  // The definition's own text, with every name that resolves to a definition
  // turned into a link.
  //
  // This is what separates reading code from browsing it: the relation strip
  // below says what a definition depends on, and these say *where*, so following
  // a call is a click on the call rather than a hunt through a list. Offsets
  // index `source` directly, so it is a slice-and-join.
  //
  // A compiler builtin like `print` links to its synthesized card; only a name
  // that genuinely leaves the artifact keeps its text and its tooltip without
  // becoming a link, because a link to nothing is worse than the name alone.
  private body(d: Def): string {
    return this.painted(d.source, this.marks(d), d.tokens, d);
  }

  // The rendered type, painted and linked exactly like a body.
  //
  // A signature is not source — no file holds it, the typechecker rendered it —
  // but the artifact carries spans over it anyway, from the compiler's own lexer
  // run across the rendered string. So `List` and `Concurrent.Async` in a
  // signature are the same colour and the same link they are in a body, which is
  // the point: the signature is the part a reader reads first. It leads with the
  // name it types, so the line reads as the declaration a reader would write.
  private signature(d: Def): string {
    if (!d.ty) return "";
    return `<div class="card-sig"><code>${esc(d.name)} : ${this.painted(d.ty, d.ty_refs ?? [], d.ty_tokens, d, true)}</code></div>`;
  }

  private effectRow(d: Def): string {
    if (!d.effects) return "";
    return `<div class="card-eff">effects <code>${this.painted(d.effects, d.eff_refs ?? [], d.eff_tokens, d, true)}</code></div>`;
  }

  // Paint one text with its highlight spans and wrap its references in links.
  //
  // `brief` drops the module from a qualified name — `Data.Vec.Vec(a, 0)` reads as
  // `Vec(a, 0)` — which is for the rendered signature, not for source. The
  // typechecker qualifies every name it prints because it has no scope to print
  // against, while a reader has this card: the module is on the header, the full
  // name is on the link's tooltip, and the body below writes `Vec` too.
  //
  // Not applied when two names in the same text would collapse onto each other,
  // since that is exactly the ambiguity the qualification exists to resolve. No
  // signature in the standard library does, across 1108 qualified names, but a
  // corpus property is not a guarantee.
  private painted(
    text: string,
    marks: Mark[],
    packed: string | undefined,
    d: Def,
    brief = false,
  ): string {
    const spans = decodeSpans(packed, this.index.tokenClasses);
    const distinct = new Map<string, string>();
    if (brief) {
      for (const m of marks) {
        const bare = short(text.slice(m.start, m.end));
        const seen = distinct.get(bare);
        distinct.set(bare, seen && seen !== m.target ? "" : m.target);
      }
    }
    // Two interval sets over one text: highlight spans, which nearly partition it,
    // and references, which cover some of its identifiers. Painting walks the
    // tokens and wraps a reference *around* whatever tokens it covers, so a
    // reference keeps its colour and gains its link rather than the two competing.
    let cursor = 0;
    const paint = (lo: number, hi: number): string => {
      let html = "";
      let pos = lo;
      while (cursor < spans.length && spans[cursor].end <= lo) cursor++;
      for (let i = cursor; i < spans.length && spans[i].start < hi; i++) {
        const from = Math.max(spans[i].start, lo);
        const to = Math.min(spans[i].end, hi);
        if (to <= from) continue;
        html += esc(text.slice(pos, from));
        html += `<span class="tk-${spans[i].cls}">${esc(text.slice(from, to))}</span>`;
        pos = to;
      }
      return html + esc(text.slice(pos, hi));
    };

    let html = "";
    let at = 0;
    for (const r of marks) {
      // Ranges arrive sorted and disjoint; skip anything that would overlap
      // rather than emitting interleaved markup.
      if (r.start < at || r.end > text.length) continue;
      html += paint(at, r.start);
      let name = paint(r.start, r.end);
      const written = text.slice(r.start, r.end);
      const bare = short(written);
      if (brief && bare !== written && distinct.get(bare) === r.target) {
        const cls = spans.find((s) => s.start <= r.start && r.start < s.end)?.cls;
        name = cls ? `<span class="tk-${cls}">${esc(bare)}</span>` : esc(bare);
      }
      at = r.end;
      // Where this declaration introduces one of its own members. It resolves to
      // nothing to navigate to — it is already here — so it points at its own
      // list of users further down the card.
      if (r.ty !== undefined) {
        // Hoverable, not navigable: a local binds here and leads nowhere.
        const tip = `${text.slice(r.start, r.end)}\n${r.ty}`;
        html += `<span class="ref ref--local" data-tip="${esc(tip)}">${name}</span>`;
        continue;
      }
      if (r.member !== undefined) {
        const users = this.members.users(d.id, r.member);
        const tip = esc(this.aboutMember(d, r.member));
        // A link only when there is somewhere to go. A member nothing uses still
        // says what it is on hover, but an underline promising a destination that
        // does not exist is worse than plain text.
        html +=
          users.length > 0
            ? `<button class="ref ref--member" data-member="${esc(r.member)}" data-tip="${tip}">${name}</button>`
            : `<span class="ref ref--prim" data-tip="${tip}">${name}</span>`;
        continue;
      }
      // A primitive is named as one rather than reported missing: it has no
      // Prism definition because it is implemented in the compiler, which is a
      // different fact from a name this artifact happens not to cover. It still
      // leads somewhere, to the builtin's own synthesized card.
      const tip = `data-tip="${esc(this.index.describe(r.target))}"`;
      switch (this.index.classify(r.target)) {
        case "definition":
          html += `<button class="ref" data-goto="${esc(r.target)}" ${tip}>${name}</button>`;
          break;
        case "builtin": {
          const to = this.index.primitive(r.target)?.name ?? r.target;
          html += `<button class="ref ref--prim" data-goto="${esc(to)}" ${tip}>${name}</button>`;
          break;
        }
        default:
          html += `<span class="ref ref--out" ${tip}>${name}</span>`;
      }
    }
    return html + paint(at, text.length);
  }

  // Every span in a body that gets its own markup: the compiler's occurrence rows,
  // plus this declaration's own members where it introduces them.
  //
  // The occurrence rows cannot supply the second. A member's declaration site is a
  // *binder*, not a use, so the renamer has nothing to record there — and a
  // reference to it would resolve to the declaration we are already reading. The
  // artifact carries those positions separately, from the compiler's own list of
  // what each declaration declares.
  private marks(d: Def): Mark[] {
    const refs = d.refs ?? [];
    const marks: Mark[] = [...refs];
    for (const m of d.members ?? []) {
      if (refs.some((r) => m.start < r.end && r.start < m.end)) continue;
      marks.push({ start: m.start, end: m.end, target: d.id, member: m.name });
    }
    // A name the checker gave a type. Only where nothing else already claims the
    // span: a reference's tooltip carries the *definition's* type, which is the
    // better answer where there is one, so these fill in what is left — the
    // parameters and locals, which have no definition to point at.
    for (const s of decodeSpans(d.types, this.index.typeTable)) {
      if (marks.some((m) => s.start < m.end && m.start < s.end)) continue;
      marks.push({ start: s.start, end: s.end, target: d.id, ty: s.cls });
    }
    return marks.sort((a, b) => a.start - b.start);
  }

  // Every relation the index knows about this definition, in both directions. A
  // builtin target (an effect like `IO`, a primitive a body calls) links to its
  // synthesized card; a target the index genuinely does not cover is rendered as
  // plain text rather than a dead link, so it reads as leaving the index instead
  // of looking broken.
  private relations(id: string): string {
    // Edges first, members after. On a type the member rows are the heaviest thing
    // on the card — `Option` has 127 uses of `None` and 135 of `Some` — and leading
    // with them buries the summary of what the definition relates to under the
    // detail of who writes each of its parts.
    return this.edgeRows(id) + this.memberRows(id);
  }

  // One row per member of this declaration that anything uses: who writes `pure`,
  // who writes `Cons`.
  //
  // These are not edges, and could not be. A class method is dispatched through a
  // dictionary, so the dependency graph records no call: `Data.Monad.map2` calls
  // `ap` and `fmap` and has no outgoing edges at all. What does know is the
  // occurrence set, read from the far end — a reference to a member resolves to
  // the declaration that owns it, and the span it covers says which member was
  // meant. Without this a class card can list its instances and nothing else.
  private memberRows(id: string): string {
    return this.members
      .of(id)
      .map(([name, users]) =>
        this.row({
          key: `${id} member ${name}`,
          label: `<code>${esc(name)}</code>`,
          hint: `definitions that write \`${name}\`, a member of this declaration`,
          targets: users,
          attrs: ` rel--member" data-uses="${esc(name)}`,
        }),
      )
      .join("");
  }

  private edgeRows(id: string): string {
    return RELATIONS.map(({ kind, dir, label, hint }) => {
      const edges = this.rel.get(kind, dir, id);
      if (kind !== "calls") {
        return this.row({ key: `${id} ${kind} ${dir}`, label, hint, targets: edges });
      }
      // The call rows lead with what the source names, in the order it names them,
      // and then with what the dependency graph adds. The two are not the same set:
      // elaboration inlines a top-level `let`, so a body that writes `gen_float`
      // depends on what the constant expanded to instead. Both are worth having —
      // one is what you can point at on the page, the other is what actually runs —
      // and a chip is marked when it is only the second, since a name appearing in
      // a row and nowhere in the body it belongs to reads as a bug.
      const written = this.mentions.get(dir, id);
      const derived = edges.filter((t) => !written.includes(t));
      return this.row({
        key: `${id} ${kind} ${dir}`,
        label,
        hint: `${hint}; a dotted chip is reached through elaboration rather than named here`,
        targets: [...written, ...derived],
        derived: new Set(derived),
      });
    }).join("");
  }

  /// Show a row in full rather than capped.
  widen(key: string): void {
    if (!this.wide.delete(key)) this.wide.add(key);
    this.render();
  }

  // One relation row: a label, a count, and the targets as chips.
  //
  // Capped, because these lists are not small — `List` is used by 374 definitions
  // and its `Cons` is written by 183 — and a card that opens with six hundred
  // chips is a card nobody reads. The count is always the true one and the
  // remainder is one click away, so nothing is silently dropped; what is hidden is
  // hidden visibly.
  private row(spec: {
    key: string;
    label: string;
    hint: string;
    targets: string[];
    attrs?: string;
    /// Targets the dependency graph reports that the source does not name.
    derived?: Set<string>;
  }): string {
    const { key, label, hint, targets, attrs = "", derived } = spec;
    if (targets.length === 0) return "";
    const all = this.wide.has(key);
    const shown = all ? targets : targets.slice(0, CHIPS);
    const chips = shown
      .map((t) => {
        const only = derived?.has(t) ?? false;
        const why = only
          ? "\nreached through elaboration, not named in this source: a constant is inlined, an instance method is lifted out"
          : "";
        const tip = `data-tip="${esc(this.index.describe(t) + why)}"`;
        const mark = only ? " chip--derived" : "";
        switch (this.index.classify(t)) {
          case "definition":
            return `<button class="chip${mark}" data-goto="${esc(t)}" ${tip}>${esc(short(t))}</button>`;
          case "builtin": {
            const to = this.index.primitive(t)?.name ?? t;
            return `<button class="chip chip--prim${mark}" data-goto="${esc(to)}" ${tip}>${esc(short(t))}</button>`;
          }
          default:
            return `<span class="chip chip--out${mark}" ${tip}>${esc(short(t))}</span>`;
        }
      })
      .join("");
    const rest = targets.length - shown.length;
    const more =
      rest > 0 || all
        ? `<button class="chip chip--more" data-wide="${esc(key)}">${all ? "fewer" : `+${rest} more`}</button>`
        : "";
    return `<div class="rel${attrs}"><span class="rel-label" data-tip="${esc(hint)}">${label}
      <span class="rel-n">${targets.length}</span></span>
      <div class="rel-chips">${chips}${more}</div></div>`;
  }
}

// What a fence's attribute says about the example, where it says anything. The
// reader is being shown code that is deliberately not run, or deliberately does
// not compile, and unlabelled that is indistinguishable from code that works.
const FENCE_NOTE: Record<string, string> = {
  output: "output",
  no_run: "not run",
  compile_fail: "does not compile",
};

/// Render a docstring.
///
/// Deliberately not a markdown library, and not markdown either: it is the small
/// dialect the docstrings actually use. Across the 723 documented definitions in
/// the standard library there is not one list, heading, emphasis or link — there
/// are 602 inline code spans and 386 examples, each usually paired with the
/// `output` block asserting what it prints. Paragraphs, inline code and fences
/// cover all of it, and a construct that never appears is not worth a dependency.
///
/// Hidden doctest lines are dropped, the same rule the book applies to the same
/// text (`docs::doctest::is_hidden`): they exist to make an example compile, and
/// what the reader is being shown is the example.
export function renderDoc(doc: string): string {
  const lines = doc.split("\n");
  const out: string[] = [];
  let para: string[] = [];
  const flush = (): void => {
    if (para.length > 0) out.push(`<p>${inline(para.join(" "))}</p>`);
    para = [];
  };
  for (let i = 0; i < lines.length; i++) {
    const fence = /^```(.*)$/.exec(lines[i]);
    if (!fence) {
      if (lines[i].trim() === "") flush();
      else para.push(lines[i].trim());
      continue;
    }
    flush();
    const [lang = "", ...attrs] = fence[1].split(",");
    const body: string[] = [];
    for (i++; i < lines.length && !lines[i].startsWith("```"); i++) {
      if (lines[i] !== "#" && !lines[i].startsWith("# ")) body.push(lines[i]);
    }
    const note = [lang, ...attrs].map((a) => FENCE_NOTE[a]).find(Boolean);
    const kind = lang === "output" ? "doc-code doc-out" : "doc-code";
    out.push(
      `${note ? `<div class="doc-note">${esc(note)}</div>` : ""}<pre class="${kind}"><code>${esc(body.join("\n"))}</code></pre>`,
    );
  }
  flush();
  return out.join("");
}

// Inline code, over already-escaped text so a backtick span cannot smuggle markup.
const inline = (s: string): string => esc(s).replace(/`([^`]+)`/g, "<code>$1</code>");

/// The name a card leads with: the canonical one, qualified.
///
/// A definition's id already carries its module wherever the compiler puts it
/// there — `Data.List.map`, and `Data.Pretty@Mode` with the `@` that marks a
/// module-private name. The prelude is addressed in global scope, so its ids are
/// bare, and prefixing the module is what makes every card read the same way:
/// `Prelude.Result`, not `Result` beside a separate module label.
const qualified = (d: Def): string =>
  d.module && !/[.@]/.test(d.id) ? `${d.module}.${d.id}` : d.id;

// What the header says about the test layer, when there is something to say.
//
// A `tested by` row is empty for two entirely different reasons, and an empty row
// looks the same either way: the unit declares no tests, or it declares tests
// whose elaboration failed and the layer could not be built. The second is the
// dangerous one — every definition then reads as untested — and the artifact knows
// which it is, so the page should not make a reader ask.
const testLayer = (tests: Envelope["tests"]): string => {
  if (tests === "included") return "";
  if (tests === "empty") {
    return ` <span class="tag tag--layer" data-tip="this unit declares no tests, so nothing has a \`tested by\` row">no tests</span>`;
  }
  return ` <span class="tag tag--dep" data-tip="${esc(`the test layer could not be built, so every \`tested by\` row is empty whether or not the definition is tested:\n\n${tests.unavailable}`)}">tests unavailable</span>`;
};

// A module that did not parse has no definitions in the artifact, and nothing
// else on the page would say so: the rail is built from definitions, so the
// module simply is not there, which reads as "not part of this code" rather
// than "broken". Same rule as the test layer: an absence with two possible
// causes must say which one it is.
const brokenModules = (modules: IndexModule[]): string => {
  const broken = modules.filter((m) => m.error);
  if (broken.length === 0) return "";
  const what = broken.length === 1 ? "1 module" : `${broken.length} modules`;
  const tip = `${what} did not parse, so ${broken.length === 1 ? "its" : "their"} definitions are not in this index:\n\n${broken
    .map((m) => `${m.path}: ${m.error}`)
    .join("\n")}`;
  return ` <span class="tag tag--dep" data-tip="${esc(tip)}">${what} not parsed</span>`;
};

// The unqualified tail, so a chip reads as a name rather than a path; the full
// canonical name stays in the button's own text for the tooltip and the URL.
const short = (id: string): string => id.split(/[.@]/).at(-1) ?? id;
const shortName = short;

const hashChip = (d: Def): string =>
  d.hash
    ? `<button class="hash" data-tip="${esc(d.hash)}\nclick to copy" data-copy="${esc(d.hash)}">${d.hash.slice(0, HASH_CHIP)}</button>`
    : `<span class="hash hash--none" data-tip="no content address: this kind has none, or the indexed program never reached it">—</span>`;

// What each surface kind is called, and what that means. The label is the
// keyword that declares it wherever Prism has one, so the badge reads the way the
// source does.
export const KINDS: Record<string, { label: string; gloss: string }> = {
  value: { label: "fn", gloss: "a function or value" },
  const: { label: "let", gloss: "a top-level constant" },
  test: { label: "test", gloss: "a test function" },
  logic: { label: "logic", gloss: "a proof-level logic function" },
  type: { label: "type", gloss: "a datatype declaration" },
  synonym: { label: "alias", gloss: "a type synonym" },
  "row-alias": { label: "row alias", gloss: "an alias for a row of effects" },
  effect: { label: "effect", gloss: "an effect declaration" },
  error: { label: "error", gloss: "an error declaration: a one-operation effect" },
  class: { label: "class", gloss: "a type class" },
  instance: { label: "instance", gloss: "an instance of a class" },
  pattern: { label: "pattern", gloss: "a pattern extractor" },
  stable: { label: "stable", gloss: "a stable version family" },
};

// The badge naming a definition's kind.
//
// Spelled out rather than initialled. A one-letter glyph fits anywhere and says
// nothing: `T`, `C`, `I` and a bare `!` are four different guesses, and three of
// the thirteen kinds wanted `!` at once. The word costs a few pixels and needs no
// legend; the tooltip carries the sentence the word still leaves out.
const kindBadge = (kind: string): string => {
  const k = KINDS[kind];
  const tip = k ? `${k.label} — ${k.gloss}` : kind;
  return `<span class="kind kind--${kind}" data-tip="${esc(tip)}">${esc(k?.label ?? kind)}</span>`;
};

// The badge naming a compiler primitive, wherever one stands in for a kind
// badge. One word for all three primitive kinds: the signature says the rest,
// and "builtin" is the fact that distinguishes the row from every definition
// around it.
const builtinBadge = (): string =>
  `<span class="kind kind--builtin" data-tip="builtin — implemented in the compiler, with no Prism definition">builtin</span>`;

// `CSS.escape` is not in every target here, and card ids are canonical names that
// can carry `.` and `@`; quoting them for an attribute selector is enough.
const cssEscape = (s: string): string => s.replace(/["\\]/g, "\\$&");

/// Wire the hover tooltip: one element, positioned on demand, shown at once.
///
/// A `title` attribute waits about a second before appearing, and on a surface
/// whose entire purpose is answering "what is this" that delay is most of the
/// answer's value gone. So the tooltip is ours.
///
/// Deliberately not a positioning library. The viewer is a self-contained artifact
/// reader — no wasm, no dependencies, under 20 kB — and a dependency to place a box
/// near a word would cost more than it explains. The book's typed tooltips
/// (`docs/theme/prism-tooltips.js`) solve the same problem the same way, so this
/// follows that precedent rather than introducing a second approach.
function wireTooltip(): void {
  const tip = document.createElement("div");
  tip.className = "tip";
  tip.setAttribute("role", "tooltip");
  tip.hidden = true;
  document.body.append(tip);

  const place = (el: HTMLElement): void => {
    const at = el.getBoundingClientRect();
    tip.hidden = false;
    // Measure after showing, then clamp: a tooltip that runs off the right edge
    // or below the fold answers nothing.
    const box = tip.getBoundingClientRect();
    const pad = 8;
    const left = Math.min(at.left, window.innerWidth - box.width - pad);
    const below = at.bottom + 6;
    const above = at.top - box.height - 6;
    const top = below + box.height + pad < window.innerHeight ? below : Math.max(pad, above);
    tip.style.left = `${Math.max(pad, left)}px`;
    tip.style.top = `${top}px`;
  };

  const show = (el: HTMLElement): void => {
    const text = el.dataset.tip;
    if (!text) return;
    tip.textContent = text;
    place(el);
  };
  const hide = (): void => {
    tip.hidden = true;
  };

  // `pointerover`/`pointerout` rather than mouseenter/leave so one delegated pair
  // covers every card the deck renders, including ones added later.
  document.addEventListener("pointerover", (e) => {
    const el = (e.target as HTMLElement | null)?.closest<HTMLElement>("[data-tip]");
    if (el) show(el);
  });
  document.addEventListener("pointerout", (e) => {
    if ((e.target as HTMLElement | null)?.closest("[data-tip]")) hide();
  });
  // Keyboard reachability: a focused link explains itself too, and scrolling
  // dismisses rather than leaving a box stranded over unrelated code.
  document.addEventListener("focusin", (e) => {
    const el = (e.target as HTMLElement | null)?.closest<HTMLElement>("[data-tip]");
    if (el) show(el);
  });
  document.addEventListener("focusout", hide);
  window.addEventListener("scroll", hide, { passive: true, capture: true });
}

/// Whether an event is headed for something the reader is typing into.
///
/// Tested on the tag rather than with `instanceof`, so it holds for an element
/// from another realm (an iframe, a different document) where the constructor
/// identity differs but the element is just as editable — and so the rule can be
/// checked without a DOM.
export function isEditable(target: EventTarget | null): boolean {
  const el = target as (Partial<HTMLElement> & { tagName?: string }) | null;
  const tag = el?.tagName?.toUpperCase();
  return tag === "INPUT" || tag === "TEXTAREA" || el?.isContentEditable === true;
}

// Delegated navigation: every `data-goto` anywhere (rail, chip, breadcrumb) opens
// its target, so no renderer has to rebind handlers for links it produced.
function wireNavigation(viewer: Viewer): void {
  document.addEventListener("click", (e) => {
    const target = e.target as HTMLElement | null;
    const goto = target?.closest<HTMLElement>("[data-goto]");
    if (goto) {
      const id = goto.dataset.goto ?? "";
      viewer.show(id);
      // A rail row for a member opens the declaration it lives in, then points at
      // the member inside it — otherwise a search for `Cons` lands you on `List`
      // with no indication of why.
      if (goto.dataset.member) viewer.revealMember(id, goto.dataset.member);
      return;
    }
    // A member name in a declaration leads to its own users, which are already on
    // this card: reveal the row rather than opening anything.
    const member = target?.closest<HTMLElement>("[data-member]");
    if (member) {
      const row = member
        .closest<HTMLElement>(".card")
        ?.querySelector<HTMLElement>(`[data-uses="${cssEscape(member.dataset.member ?? "")}"]`);
      row?.scrollIntoView({ behavior: "smooth", block: "nearest" });
      row?.classList.add("is-flash");
      setTimeout(() => row?.classList.remove("is-flash"), 600);
      return;
    }
    const wide = target?.closest<HTMLElement>("[data-wide]");
    if (wide) {
      viewer.widen(wide.dataset.wide ?? "");
      return;
    }
    const mod = target?.closest<HTMLElement>("[data-mod]");
    if (mod) {
      viewer.toggleModule(mod.dataset.mod ?? "");
      return;
    }
    if (target?.closest("#rail-toggle")) {
      viewer.toggleRail();
      return;
    }
    const writeNote = target?.closest<HTMLElement>("[data-write-note]");
    if (writeNote) {
      viewer.writeNote(writeNote.dataset.writeNote ?? "");
      return;
    }
    const seen = target?.closest<HTMLElement>("[data-reviewed]");
    if (seen) {
      viewer.toggleReviewed(seen.dataset.reviewed ?? "", Date.now());
      return;
    }
    const copy = target?.closest<HTMLElement>("[data-copy]");
    if (copy) {
      void navigator.clipboard?.writeText(copy.dataset.copy ?? "");
      copy.classList.add("is-copied");
      setTimeout(() => copy.classList.remove("is-copied"), 800);
    }
  });
}

// What to open: `?src=<url>` for any index a reader points at (else the standard
// library's, which is the one this site ships), and `?diff=<url>` to overlay the
// revision it was compared against. The diff is checked against the loaded
// index's contract: a stale or mismatched overlay would present old bodies
// beside definitions they were never compared with.
async function load(): Promise<[Index, Revisions | null, string]> {
  const params = new URLSearchParams(location.search);
  const fetchJson = async (url: string): Promise<unknown> => {
    const res = await fetch(url);
    if (!res.ok) throw new Error(`${url}: ${res.status} ${res.statusText}`);
    return res.json();
  };
  const src = params.get("src") ?? "./stdlib-index.json";
  const index = new Index((await fetchJson(src)) as never);
  const diff = params.get("diff");
  const revs = diff
    ? new Revisions(
        (await fetchJson(diff)) as never,
        index.tokenClasses,
        index.typeTable,
        index.envelope.contract,
      )
    : null;
  return [index, revs, src];
}

async function boot(): Promise<void> {
  const status = el<HTMLElement>("status");
  try {
    const [index, revs, src] = await load();
    const viewer = new Viewer(
      index,
      revs,
      {
        cards: el("cards"),
        list: el("rail-list"),
        search: el<HTMLInputElement>("search"),
        title: el("index-title"),
        empty: el("empty"),
        rail: el("rail"),
        main: el("viewer-main"),
        railToggle: el("rail-toggle"),
      },
      globalThis.localStorage ?? null,
      // Marks are namespaced by where the artifact lives *and* what it calls
      // itself: neither alone tells two projects apart reliably.
      `${src} ${index.envelope.title}`,
    );
    wireNavigation(viewer);
    wireTooltip();
    viewer.start();
    status.hidden = true;
  } catch (e) {
    status.textContent = `could not load an index: ${e instanceof Error ? e.message : String(e)}. Generate one with \`prism index\`.`;
  }
}

void boot();
