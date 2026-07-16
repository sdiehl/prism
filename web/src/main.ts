import { createElement, Github, Play } from "lucide";
import init, { core_ir, diagnostics, dump, dump_hir, fmt, tokens } from "../pkg/prism.js";
import { examples } from "./examples.js";
import "./styles.css";

interface Diag {
  s: number;
  e: number;
  line: number;
  col: number;
  endLine: number;
  endCol: number;
  kind: string;
  msg: string;
}
interface Tok {
  s: number;
  e: number;
  c: string;
}

const el = <T extends HTMLElement>(id: string): T => document.getElementById(id) as T;
const src = el<HTMLTextAreaElement>("src");
const out = el<HTMLPreElement>("out");
const sel = el<HTMLSelectElement>("examples");
const hl = el<HTMLPreElement>("hl");
const gutter = el<HTMLDivElement>("gutter");
const sigs = el<HTMLPreElement>("sigs");
const sigLabel = el<HTMLDivElement>("siglabel");
const tip = el<HTMLDivElement>("tip");
const mainEl = document.querySelector("main") as HTMLElement;
const runBtn = el<HTMLButtonElement>("run");
const fmtBtn = el<HTMLButtonElement>("fmt");
const dumpBtn = el<HTMLButtonElement>("dump");
const showirBtn = el<HTMLButtonElement>("showir");
const irHir = el<HTMLPreElement>("ir-hir");
const irCore = el<HTMLPreElement>("ir-core");

runBtn.prepend(createElement(Play));
// Icons come from lucide (sized 18px in CSS) rather than inline SVG markup, so
// they never flash at the unsized default size before stylesheet load.
el<HTMLAnchorElement>("gh").append(createElement(Github));

// ariadne diagnostics carry ANSI color; a browser <pre> renders the raw escapes
// as noise, so drop them before display.
const ANSI = new RegExp(`${String.fromCharCode(27)}\\[[0-9;]*m`, "g");
const strip = (s: string): string => s.replace(ANSI, "");
const esc = (s: string): string =>
  s.replace(/[&<>]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;" })[c] ?? c);

function show(text: string): void {
  const t = strip(text);
  out.textContent = t;
  out.className = `out${t.startsWith("error") ? " err" : ""}`;
}

let ready = false;
let diags: Diag[] = [];

// Repaint the highlight layer: cut the source at every token and error boundary,
// then emit each slice with its token color and an error squiggle if it falls
// inside a diagnostic range. A trailing newline keeps the last line's height in
// step with the textarea.
function paint(): void {
  const text = src.value;
  const toks: Tok[] = ready ? JSON.parse(tokens(text)) : [];
  const marks = diags.filter((d) => d.e > d.s);
  const cuts = [
    ...new Set([
      0,
      text.length,
      ...toks.flatMap((t) => [t.s, t.e]),
      ...marks.flatMap((d) => [d.s, d.e]),
    ]),
  ]
    .filter((p) => p >= 0 && p <= text.length)
    .sort((a, b) => a - b);
  let html = "";
  for (let i = 0; i < cuts.length - 1; i++) {
    const a = cuts[i];
    const b = cuts[i + 1];
    if (b <= a) continue;
    const tk = toks.find((t) => t.s <= a && t.e >= b);
    // An error span wins over a warning span when both cover this slice.
    const mk =
      marks.find((d) => d.s <= a && d.e >= b && !isWarn(d)) ??
      marks.find((d) => d.s <= a && d.e >= b);
    const sq = mk ? (isWarn(mk) ? "warn-squig" : "squig") : "";
    const cls = [tk && tk.c !== "id" ? `tk-${tk.c}` : "", sq].filter(Boolean).join(" ");
    const seg = esc(text.slice(a, b));
    html += cls ? `<span class="${cls}">${seg}</span>` : seg;
  }
  hl.innerHTML = `${html}\n`;
  paintGutter(text);
  sync();
}

// The checker reports warnings under the "Warning" kind; everything else is a
// hard "*Error". Severity drives colour: red for errors, amber for warnings.
const isWarn = (d: Diag): boolean => d.kind === "Warning";

// Diagnostic messages keyed by 1-based source line, shared by the gutter (native
// title) and the hover tooltip over the code itself, plus the per-line severity
// that colours the gutter (an error on a line outranks a warning).
let errLines = new Map<number, string>();
let lineSev = new Map<number, "err" | "warn">();
function buildErrLines(): void {
  errLines = new Map();
  lineSev = new Map();
  for (const d of diags) {
    const sev = isWarn(d) ? "warn" : "err";
    for (let l = d.line; l <= d.endLine; l++) {
      const m = `${d.kind}: ${d.msg}`;
      errLines.set(l, errLines.has(l) ? `${errLines.get(l)} | ${m}` : m);
      if (lineSev.get(l) !== "err") lineSev.set(l, sev);
    }
  }
}

function paintGutter(text: string): void {
  const total = text.split("\n").length;
  let h = "";
  for (let i = 1; i <= total; i++) {
    const m = errLines.get(i);
    const sev = lineSev.get(i);
    const title = m ? ` title="${esc(m).replace(/"/g, "&quot;")}"` : "";
    h += `<div class="ln${sev ? ` ${sev}` : ""}"${title}>${i}</div>`;
  }
  gutter.innerHTML = h;
}

function sync(): void {
  hl.scrollTop = src.scrollTop;
  hl.scrollLeft = src.scrollLeft;
  gutter.style.transform = `translateY(${-src.scrollTop}px)`;
}

// The checked-HIR fixture (`dump hir`): per-declaration schemes and effect rows
// plus the per-node checker facts. The bridge prepends the prelude so a snippet
// type-checks, so the browser strips it back out for display the same way the
// Core IR view does: prelude declarations drop by name, and prelude node facts
// drop by a metavar-normalized multiset subtraction against the prelude-only
// fixture (node ids and metavar numbering shift when user code is present, but a
// node's fact is stable once its type/row metavars are canonicalized).
const HIR_FIXTURE_SCHEMA = "prism-hir-fixture-v2";
interface HirDeclJ {
  name: string;
  scheme: string;
  effects: string[];
}
interface HirNodeJ {
  res?: unknown;
  evidence?: string[];
  lane?: string;
  ty?: string;
  handler_residual?: HirHandlerResidualJ;
}
interface HirHandlerResidualJ {
  forwarded_operations: string[];
  forwarded_effects: string[];
  residual_operations: string[];
  residual_effects: string[];
  open_row: boolean;
}
interface HirFixture {
  schema: typeof HIR_FIXTURE_SCHEMA;
  decls: HirDeclJ[];
  nodes: Record<string, HirNodeJ>;
}
const META = /\?r?\d+/g;
const isMeta = (s: string | undefined): boolean => s !== undefined && /^\?r?\d+$/.test(s);
const nodeSig = (n: HirNodeJ): string =>
  JSON.stringify([
    n.res ?? null,
    n.evidence ?? null,
    n.lane ?? null,
    (n.ty ?? "").replace(META, "?"),
    n.handler_residual ?? null,
  ]);

// The prelude projection, computed once from `dump_hir("")` (empty user source):
// the set of prelude declaration names and the multiset of prelude node facts.
let preludeNames: Set<string> | null = null;
let preludeNodes: Map<string, number> | null = null;
function ensurePrelude(): void {
  if (preludeNames || !ready) return;
  preludeNames = new Set();
  preludeNodes = new Map();
  try {
    const p = JSON.parse(dump_hir("")) as HirFixture;
    if (p.schema !== HIR_FIXTURE_SCHEMA) throw new Error(`incompatible HIR schema: ${p.schema}`);
    for (const d of p.decls) preludeNames.add(d.name);
    for (const k of Object.keys(p.nodes)) {
      const s = nodeSig(p.nodes[k]);
      preludeNodes.set(s, (preludeNodes.get(s) ?? 0) + 1);
    }
  } catch {
    // dump_hir returned a diagnostic rather than JSON; leave the prelude sets
    // empty so the raw fixture still renders (unstripped) instead of failing.
  }
}
function showRes(res: unknown): string {
  const r = res as { kind?: string; ctor?: string; index?: number; arity?: number };
  if (r && r.kind === "field") return `field ${r.ctor}.${r.index}/${r.arity}`;
  if (r && r.kind === "unboxed") return `unboxed .${r.index}/${r.arity}`;
  return JSON.stringify(res);
}
function showHandlerResidual(residual: HirHandlerResidualJ): string {
  const forwarded = [
    ...residual.forwarded_operations,
    ...residual.forwarded_effects.map((effect) => `${effect}.*`),
  ];
  const remaining = [
    ...residual.residual_operations,
    ...residual.residual_effects.map((effect) => `${effect}.*`),
  ];
  const open = residual.open_row ? " | _" : "";
  return `forward={${forwarded.join(", ")}} residual={${remaining.join(", ")}${open}}`;
}
// Render the prelude-stripped HIR of the current source: the user declarations
// with their schemes and effect rows, then the checker facts recorded on the
// user's own nodes.
function renderHir(): string {
  const raw = dump_hir(src.value);
  if (raw.startsWith("error")) return strip(raw);
  let fix: HirFixture;
  try {
    fix = JSON.parse(raw) as HirFixture;
  } catch {
    return strip(raw);
  }
  if (fix.schema !== HIR_FIXTURE_SCHEMA) {
    return `error: incompatible HIR fixture schema ${String(fix.schema)} (expected ${HIR_FIXTURE_SCHEMA})`;
  }
  ensurePrelude();
  const names = preludeNames ?? new Set<string>();
  const decls = fix.decls
    .filter((d) => !names.has(d.name))
    .map((d) => {
      // The scheme already renders a function's latent effect row on its arrow;
      // only surface the declaration's own row when the scheme doesn't end in
      // one (e.g. a top-level effectful value binding), to avoid duplication.
      const hasRow = /! \{[^}]*\}\s*$/.test(d.scheme);
      const eff = d.effects.length && !hasRow ? `  ! {${d.effects.join(", ")}}` : "";
      return `${d.name} : ${d.scheme}${eff}`;
    });
  const budget = new Map(preludeNodes ?? new Map<string, number>());
  const facts: string[] = [];
  for (const k of Object.keys(fix.nodes).sort((a, b) => Number(a) - Number(b))) {
    const n = fix.nodes[k];
    const s = nodeSig(n);
    const left = budget.get(s) ?? 0;
    if (left > 0) {
      budget.set(s, left - 1); // a prelude node, absorbed
      continue;
    }
    // Only surface nodes carrying a substantive checker fact: a resolution, a
    // dictionary evidence chain, numeric lane, or handler residual. Nodes whose
    // sole fact is a bare `ty=` (the literal-node type rows) are dropped as
    // noise; the type is then shown only as context alongside one of the
    // substantive facts.
    const lane = n.lane ? `lane=${n.lane}` : "";
    const res = n.res ? `res=${showRes(n.res)}` : "";
    const ev = n.evidence?.length ? `ev=${n.evidence.join(", ")}` : "";
    const residual = n.handler_residual ? `handler=${showHandlerResidual(n.handler_residual)}` : "";
    if (!lane && !res && !ev && !residual) continue;
    const parts: string[] = [];
    if (n.ty && !isMeta(n.ty)) parts.push(`ty=${n.ty}`);
    for (const p of [lane, res, ev, residual]) if (p) parts.push(p);
    facts.push(`#${k}  ${parts.join("  ")}`);
  }
  const out = ["-- Declarations", decls.length ? decls.join("\n") : "(no top-level declarations)"];
  if (facts.length) out.push("", `-- Checker facts (${facts.length} nodes)`, facts.join("\n"));
  return out.join("\n");
}

// The right column is a single slot shared by two mutually-exclusive panels.
// "sigs" reuses `dump` (top-level type signatures) in the shared `#sigs` pane.
// "showir" swaps in the fixed HIR-over-Core split: the top pane always shows the
// checked HIR, the bottom pane the fully lowered CBPV core. Only one panel shows
// at a time; clicking the active view's button hides it. Panels only repopulate
// while open, and track edits.
type Panel = "sigs" | "showir" | null;
function paintPre(pre: HTMLPreElement, r: string): void {
  pre.textContent = r;
  pre.className = `out${r.startsWith("error") ? " err" : ""}`;
}
let panel: Panel = null;
function refreshIr(): void {
  if (panel !== "showir" || !ready) return;
  paintPre(irHir, renderHir() || "(no declarations)");
  paintPre(irCore, strip(core_ir(src.value)) || "(no functions)");
}
function refreshSigs(): void {
  if (!ready || panel !== "sigs") return;
  const r = strip(dump(src.value));
  sigs.textContent = r || "(no top-level declarations)";
  sigs.className = `out${r.startsWith("error") ? " err" : ""}`;
}
function setPanel(next: Panel): void {
  if (!ready) return;
  panel = next;
  sigLabel.textContent = next === "sigs" ? "Type signatures" : "";
  mainEl.classList.toggle("show-sigs", next === "sigs");
  mainEl.classList.toggle("show-ir", next === "showir");
  dumpBtn.classList.toggle("active", next === "sigs");
  showirBtn.classList.toggle("active", next === "showir");
  refreshSigs();
  refreshIr();
}

let timer = 0;
function recheck(): void {
  diags = ready ? JSON.parse(diagnostics(src.value)) : [];
  buildErrLines();
  paint();
  refreshSigs();
  refreshIr();
}
function onEdit(): void {
  paint();
  window.clearTimeout(timer);
  timer = window.setTimeout(recheck, 140);
}

// Run executes in a Web Worker so a runaway program can be terminated. If it
// does not answer within the budget, the worker is killed and replaced.
const HALT_MS = 5000;
let worker = makeWorker();
let runTimer = 0;
function makeWorker(): Worker {
  return new Worker(new URL("./worker.ts", import.meta.url), { type: "module" });
}
function runProgram(): void {
  if (!ready) return;
  out.textContent = "Running...";
  out.className = "out dim";
  runBtn.disabled = true;
  worker.onmessage = (e: MessageEvent<string>) => {
    window.clearTimeout(runTimer);
    runBtn.disabled = false;
    show(e.data);
  };
  runTimer = window.setTimeout(() => {
    worker.terminate();
    worker = makeWorker();
    runBtn.disabled = false;
    show(`error: execution halted after ${HALT_MS / 1000}s (possible infinite loop)`);
  }, HALT_MS);
  worker.postMessage(src.value);
}

const names = Object.keys(examples).sort();
for (const name of names) {
  const opt = document.createElement("option");
  opt.value = name;
  opt.textContent = name;
  sel.append(opt);
}
// A docs "Open in playground" link carries the snippet UTF-8 + base64 in the
// URL fragment (`#code=...`). When present, it overrides the default example.
function sharedSource(): string | null {
  const m = /[#&]code=([^&]+)/.exec(location.hash);
  if (!m) return null;
  try {
    const bin = atob(decodeURIComponent(m[1]));
    const bytes = Uint8Array.from(bin, (c) => c.charCodeAt(0));
    return new TextDecoder().decode(bytes);
  } catch {
    return null;
  }
}

// Placeholder shown when the editor holds custom code (e.g. loaded from a
// `#code=` link or hand-edited) that matches no named example.
const custom = document.createElement("option");
custom.value = "";
custom.textContent = "--";
custom.hidden = true;
sel.prepend(custom);

const start = examples.factorial ? "factorial" : (names[0] ?? "");
const shared = sharedSource();
sel.value = shared != null ? "" : start;
src.value = shared ?? examples[start] ?? "";
sel.onchange = () => {
  if (sel.value === "") return;
  src.value = examples[sel.value] ?? "";
  out.textContent = "";
  recheck();
};

init().then(() => {
  ready = true;
  out.textContent = "Ready.";
  runBtn.disabled = false;
  fmtBtn.disabled = false;
  dumpBtn.disabled = false;
  showirBtn.disabled = false;
  recheck();
});

runBtn.onclick = runProgram;
dumpBtn.onclick = () => setPanel(panel === "sigs" ? null : "sigs");
showirBtn.onclick = () => setPanel(panel === "showir" ? null : "showir");
fmtBtn.onclick = () => {
  if (!ready) return;
  const r = strip(fmt(src.value));
  if (r.startsWith("error")) {
    show(r);
  } else {
    src.value = r;
    out.textContent = "";
    recheck();
  }
};

src.addEventListener("input", onEdit);
src.addEventListener("scroll", () => {
  sync();
  tip.style.display = "none";
});

// Hover a line that carries a diagnostic to read its message; the line is
// derived from the cursor's y, the top padding, and the scroll offset.
const PAD = 18;
src.addEventListener("mousemove", (e) => {
  const lh = Number.parseFloat(getComputedStyle(src).lineHeight) || 21;
  const line = Math.floor((e.offsetY - PAD + src.scrollTop) / lh) + 1;
  const msg = errLines.get(line);
  if (!msg) {
    tip.style.display = "none";
    return;
  }
  tip.innerHTML = `<b>line ${line}</b> &nbsp;${esc(msg)}`;
  tip.style.display = "block";
  tip.style.left = `${Math.min(e.clientX + 12, window.innerWidth - tip.offsetWidth - 12)}px`;
  tip.style.top = `${e.clientY + 16}px`;
});
src.addEventListener("mouseleave", () => {
  tip.style.display = "none";
});
src.addEventListener("keydown", (e) => {
  if ((e.metaKey || e.ctrlKey) && e.key === "Enter") {
    e.preventDefault();
    runProgram();
  }
});

paint();
