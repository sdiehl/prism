// Shared mechanics for every gallery resident (the determinism scrubber, the
// double pendulum, the branching timelines, the chaos counter, and every future
// one). A resident is ONE framed surface with two faces, the running demo and
// its read-only source, joined by a 3D flip: the source and its behaviour are
// two faces of one deterministic object. A page opts in with the .faces / .flip
// markup in showcase.css and calls initFaces() once its DOM exists. The wasm
// source painter both faces need lives here too, so no resident re-implements it.

interface Tok {
  s: number;
  e: number;
  c: string;
}

const esc = (s: string): string =>
  s.replace(/[&<>]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;" })[c] ?? c);

// Slice a baked example at its `-- @<name>:main-below` sentinel so the source
// face shows only the honest kernel, dropping the terminal `main` the wasm driver
// also strips. The sentinel line itself is removed.
export function kernel(src: string | undefined, sentinel: string): string {
  return (src ?? "").split(sentinel)[0].trimEnd();
}

// Paint `text` into `codeEl` with the wasm `tokens` highlighter the playground
// uses: cut at every token boundary and wrap each slice in its token class
// (`tk-<kind>`, coloured in theme.css). Read-only, no diagnostics.
export function highlight(codeEl: HTMLElement, text: string, tokens: (s: string) => string): void {
  const toks: Tok[] = JSON.parse(tokens(text));
  const cuts = [...new Set([0, text.length, ...toks.flatMap((t) => [t.s, t.e])])]
    .filter((p) => p >= 0 && p <= text.length)
    .sort((a, b) => a - b);
  let html = "";
  for (let i = 0; i < cuts.length - 1; i++) {
    const a = cuts[i];
    const b = cuts[i + 1];
    if (b <= a) continue;
    const tk = toks.find((t) => t.s <= a && t.e >= b);
    const cls = tk && tk.c !== "id" ? `tk-${tk.c}` : "";
    const seg = esc(text.slice(a, b));
    html += cls ? `<span class="${cls}">${seg}</span>` : seg;
  }
  codeEl.innerHTML = html;
}

// Wire the Demo/Source segmented toggle to the flip surface. Activating a tab
// (mouse or keyboard, they are real buttons) sets aria-pressed, flips the
// surface, and marks the hidden face inert so its controls (on the demo) or its
// text (on the source) leave the tab order and the accessibility tree: the
// transport rotated out of sight can never be tabbed into over the code, and a
// screen reader never reads the face that is turned away. Idempotent.
export function initFaces(): void {
  const flip = document.querySelector<HTMLElement>("[data-flip]");
  const tabs = Array.from(document.querySelectorAll<HTMLButtonElement>(".face-tab"));
  if (!flip || tabs.length === 0) return;
  const demoFace = flip.querySelector<HTMLElement>(".flip-face--demo");
  const sourceFace = flip.querySelector<HTMLElement>(".flip-face--source");

  const show = (face: string): void => {
    const source = face === "source";
    flip.classList.toggle("show-source", source);
    for (const t of tabs) {
      const active = t.dataset.face === face;
      t.classList.toggle("is-active", active);
      t.setAttribute("aria-pressed", String(active));
    }
    demoFace?.toggleAttribute("inert", source);
    sourceFace?.toggleAttribute("inert", !source);
    demoFace?.setAttribute("aria-hidden", String(source));
    sourceFace?.setAttribute("aria-hidden", String(!source));
  };

  for (const t of tabs) {
    t.addEventListener("click", () => show(t.dataset.face ?? "demo"));
  }
  show("demo");
}
