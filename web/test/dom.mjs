// The smallest DOM the viewer touches, and the harness that drives it.
//
// The viewer has no test runner because it has no framework: it is one module over
// one JSON file. But its render path is the half most worth checking — an offset
// off by one silently corrupts a body, and a guard that forgets `<textarea>`
// silently breaks typing — so the checks run the *real* module against a shim
// covering exactly the DOM surface it uses.
//
// These lived in a scratch directory for a while and went stale three times, each
// time passing when written and failing later against a constructor that had
// gained an argument. That is the argument for their being here.

/// A stand-in for one element. Only what the viewer actually calls.
export class El {
  constructor(tag = "div") {
    this.tagName = tag.toUpperCase();
    this._html = "";
    this.textContent = "";
    this.hidden = false;
    this.value = "";
    this.dataset = {};
    this.style = {};
    this.classList = {
      add() {},
      remove() {},
      toggle() {
        return false;
      },
      contains() {
        return false;
      },
    };
  }
  set innerHTML(v) {
    this._html = v;
  }
  get innerHTML() {
    return this._html;
  }
  querySelector() {
    return null;
  }
  querySelectorAll() {
    return [];
  }
  addEventListener() {}
  removeEventListener() {}
  setAttribute() {}
  closest() {
    return null;
  }
  scrollIntoView() {}
  focus() {}
  select() {}
  blur() {}
  append() {}
  getBoundingClientRect() {
    return { top: 0, left: 0, bottom: 0, right: 0, width: 0, height: 0 };
  }
}

/// The nodes a `Viewer` is constructed with.
export function nodes() {
  return {
    cards: new El(),
    list: new El(),
    search: new El("input"),
    title: new El(),
    empty: new El(),
    rail: new El("nav"),
    main: new El("main"),
    railToggle: new El("button"),
  };
}

/// Install the globals the module reaches for at load and during a render.
export function installGlobals() {
  globalThis.window = { addEventListener() {}, innerWidth: 1200, innerHeight: 800 };
  globalThis.document = {
    addEventListener() {},
    createElement: (tag) => new El(tag),
    body: new El("body"),
    getElementById: () => new El(),
  };
  globalThis.location = { hash: "", search: "" };
  globalThis.history = { replaceState() {} };
  globalThis.setTimeout = () => 0;
}

/// A `localStorage` stand-in, so review state can be exercised.
export class Storage {
  constructor() {
    this.m = new Map();
  }
  getItem(k) {
    return this.m.get(k) ?? null;
  }
  setItem(k, v) {
    this.m.set(k, v);
  }
}

let failures = 0;

export function check(name, ok, detail = "") {
  if (ok) {
    console.log(`  ok   ${name}${detail ? `  ${detail}` : ""}`);
  } else {
    failures++;
    console.log(`  FAIL ${name}${detail ? `  ${detail}` : ""}`);
  }
}

export function section(name) {
  console.log(`\n${name}`);
}

/// Strip markup and unescape, to compare rendered output against its source.
/// The strip runs to a fixpoint so no partial tag can survive a single pass.
export function plain(html) {
  let text = html;
  let stripped = text.replace(/<[^>]*>?/g, "");
  while (stripped !== text) {
    text = stripped;
    stripped = text.replace(/<[^>]*>?/g, "");
  }
  return stripped
    .replace(/&lt;/g, "<")
    .replace(/&gt;/g, ">")
    .replace(/&quot;/g, '"')
    .replace(/&amp;/g, "&");
}

/// One card's markup, isolated: the deck accumulates, so a naive search over the
/// whole deck matches a neighbouring card and passes for the wrong reason.
export function card(html, id) {
  const at = html.split(`data-card="${id}"`)[1];
  return at ? at.split("</article>")[0] : "";
}

export function done() {
  console.log(failures === 0 ? "\nALL CHECKS PASSED" : `\n${failures} CHECK(S) FAILED`);
  process.exit(failures === 0 ? 0 : 1);
}
