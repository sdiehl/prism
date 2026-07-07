// A small navigable slice of the scheduler space behind the chaos counter. Each
// node is one seeded interleaving of the same Prism program, computed by the
// existing wasm export; clicking a node shows the schedule trace and the shared
// final-state hash.
import init, { chaos_run, tokens } from "../pkg/prism.js";
import { examples } from "./examples.js";
import { highlight, initFaces, kernel } from "./showcase.js";
import "./schedule.css";

const KERNEL_SPLIT = "-- @chaos:main-below";
const KERNEL_SRC = kernel(examples.chaos_swarm, KERNEL_SPLIT);
const NODE_COUNT = 12;
const TRACE_WRAP = 12;

interface ScheduleNode {
  seed: number;
  agreed: number;
  count: number;
  hash: string;
  trace: number[];
}

const el = <T extends HTMLElement>(id: string): T => document.getElementById(id) as T;
const nodesEl = el<HTMLDivElement>("nodes");
const proofEl = el<HTMLDivElement>("proof");
const traceEl = el<HTMLPreElement>("trace");
const codeEl = el<HTMLElement>("code");
const prevBtn = el<HTMLButtonElement>("prev");
const nextBtn = el<HTMLButtonElement>("next");

let nodes: ScheduleNode[] = [];
let active = 0;

codeEl.textContent = KERNEL_SRC;
initFaces();

function parseTrace(line: string): number[] {
  return line
    .split(" ")
    .filter((part) => part.length > 0)
    .map(Number);
}

function readNode(seed: number): ScheduleNode {
  const raw = chaos_run(seed, 1);
  if (raw.startsWith("error:")) throw new Error(raw);
  const lines = raw.trimEnd().split("\n");
  const [agreed, count, hash] = lines[0].split(" ");
  return {
    seed,
    agreed: Number(agreed),
    count: Number(count),
    hash,
    trace: parseTrace(lines[1] ?? ""),
  };
}

function shortTrace(trace: number[]): string {
  return trace.slice(0, 10).join(" ");
}

function wrappedTrace(trace: number[]): string {
  const rows: string[] = [];
  for (let i = 0; i < trace.length; i += TRACE_WRAP) {
    rows.push(trace.slice(i, i + TRACE_WRAP).join(" "));
  }
  return rows.join("\n");
}

function renderNodes(): void {
  nodesEl.innerHTML = "";
  nodes.forEach((node, index) => {
    const button = document.createElement("button");
    button.type = "button";
    button.className = index === active ? "schedule-node is-active" : "schedule-node";
    button.innerHTML = `
      <div class="schedule-seed">seed ${node.seed}</div>
      <div class="schedule-hash">${node.hash}</div>
      <div class="schedule-prefix">${shortTrace(node.trace)}</div>
    `;
    button.addEventListener("click", () => select(index));
    nodesEl.appendChild(button);
  });
}

function renderDetail(): void {
  const node = nodes[active];
  if (node === undefined) return;
  const reference = nodes[0]?.hash;
  const ok = node.agreed === node.count && node.hash === reference;
  proofEl.textContent = ok
    ? `seed ${node.seed}: final hash ${node.hash}, matches reference`
    : `seed ${node.seed}: diverged from reference`;
  proofEl.className = ok ? "schedule-proof ok" : "schedule-proof err";
  traceEl.textContent = wrappedTrace(node.trace);
  prevBtn.disabled = active === 0;
  nextBtn.disabled = active + 1 >= nodes.length;
}

function select(index: number): void {
  active = Math.max(0, Math.min(index, nodes.length - 1));
  renderNodes();
  renderDetail();
}

prevBtn.addEventListener("click", () => select(active - 1));
nextBtn.addEventListener("click", () => select(active + 1));

void init()
  .then(() => {
    highlight(codeEl, KERNEL_SRC, tokens);
    nodes = Array.from({ length: NODE_COUNT }, (_, seed) => readNode(seed));
    select(0);
  })
  .catch((error: unknown) => {
    proofEl.textContent = error instanceof Error ? error.message : String(error);
    proofEl.className = "schedule-proof err";
  });
