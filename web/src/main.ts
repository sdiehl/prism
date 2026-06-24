import { createElement, Play } from "lucide";
import init, { core_ir, diagnostics, dump, fmt, tokens } from "../pkg/prism.js";
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
const irBtn = el<HTMLButtonElement>("ir");

runBtn.prepend(createElement(Play));

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
  const errs = diags.map((d) => [d.s, d.e]).filter(([s, e]) => e > s);
  const cuts = [...new Set([0, text.length, ...toks.flatMap((t) => [t.s, t.e]), ...errs.flat()])]
    .filter((p) => p >= 0 && p <= text.length)
    .sort((a, b) => a - b);
  let html = "";
  for (let i = 0; i < cuts.length - 1; i++) {
    const a = cuts[i];
    const b = cuts[i + 1];
    if (b <= a) continue;
    const tk = toks.find((t) => t.s <= a && t.e >= b);
    const bad = errs.some(([s, e]) => s <= a && e >= b);
    const cls = [tk && tk.c !== "id" ? `tk-${tk.c}` : "", bad ? "squig" : ""]
      .filter(Boolean)
      .join(" ");
    const seg = esc(text.slice(a, b));
    html += cls ? `<span class="${cls}">${seg}</span>` : seg;
  }
  hl.innerHTML = `${html}\n`;
  paintGutter(text);
  sync();
}

// Diagnostic messages keyed by 1-based source line, shared by the gutter (native
// title) and the hover tooltip over the code itself.
let errLines = new Map<number, string>();
function buildErrLines(): void {
  errLines = new Map();
  for (const d of diags) {
    for (let l = d.line; l <= d.endLine; l++) {
      const m = `${d.kind}: ${d.msg}`;
      errLines.set(l, errLines.has(l) ? `${errLines.get(l)} | ${m}` : m);
    }
  }
}

function paintGutter(text: string): void {
  const total = text.split("\n").length;
  let h = "";
  for (let i = 1; i <= total; i++) {
    const m = errLines.get(i);
    const title = m ? ` title="${esc(m).replace(/"/g, "&quot;")}"` : "";
    h += `<div class="ln${m ? " err" : ""}"${title}>${i}</div>`;
  }
  gutter.innerHTML = h;
}

function sync(): void {
  hl.scrollTop = src.scrollTop;
  hl.scrollLeft = src.scrollLeft;
  gutter.style.transform = `translateY(${-src.scrollTop}px)`;
}

// The third pane is a single panel shared by two mutually-exclusive views:
// "sigs" reuses the `dump` entry point (top-level type signatures only), and
// "ir" reuses `core_ir` (the fully lowered CBPV core, with rc and reuse). Only
// one is shown at a time; clicking the active view's button hides the panel. It
// only repopulates while open, and tracks edits.
type Panel = "sigs" | "ir" | null;
const VIEW = {
  sigs: { label: "Type signatures", empty: "(no top-level declarations)", run: dump },
  ir: { label: "Core IR", empty: "(no functions)", run: core_ir },
} as const;
let panel: Panel = null;
function refreshSigs(): void {
  if (!panel || !ready) return;
  const view = VIEW[panel];
  const r = strip(view.run(src.value));
  sigs.textContent = r || view.empty;
  sigs.className = `out${r.startsWith("error") ? " err" : ""}`;
}
function setPanel(next: Panel): void {
  if (!ready) return;
  panel = next;
  sigLabel.textContent = next ? VIEW[next].label : "";
  mainEl.classList.toggle("show-sigs", next !== null);
  dumpBtn.classList.toggle("active", next === "sigs");
  irBtn.classList.toggle("active", next === "ir");
  refreshSigs();
}

let timer = 0;
function recheck(): void {
  diags = ready ? JSON.parse(diagnostics(src.value)) : [];
  buildErrLines();
  paint();
  refreshSigs();
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

const start = examples.factorial ? "factorial" : (names[0] ?? "");
sel.value = start;
const shared = sharedSource();
src.value = shared ?? examples[start] ?? "";
sel.onchange = () => {
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
  irBtn.disabled = false;
  recheck();
});

runBtn.onclick = runProgram;
dumpBtn.onclick = () => setPanel(panel === "sigs" ? null : "sigs");
irBtn.onclick = () => setPanel(panel === "ir" ? null : "ir");
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
