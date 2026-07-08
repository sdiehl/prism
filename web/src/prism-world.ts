// PRISM WORLD: a shared cellular universe whose state and law are both content
// addressed values. The law is Prism (examples/world.pr) run through the wasm
// interpreter; each grid carries the compiler's blake3 state hash and each law
// carries its Core content hash. History is a branchable execution prefix: a
// fork at tick N keeps the shared past and re-evolves the future, so two
// same-origin tabs that agree on the spec compute identical hashes with no
// coordination. Multi-tab sync is a same-origin BroadcastChannel, nothing more:
// no relay, no peer-to-peer, no cross-origin, no stranger execution.
//
// The Autoverse / Copies / Dust / Garden vocabulary is an homage to Greg Egan's
// Permutation City and its Autoverse; it is framing, not a dependency or a claim
// beyond the machinery on the page. Every proof label here is either something
// that actually ran locally, or is marked reserved / unchecked.
import PrismWorldWorker from "./prism-world-worker.ts?worker";
import "./prism-world.css";

// The grid and horizon. Dimensions and tick count are tuned so one law re-evolves
// in about a second in the worker; the whole trajectory is precomputed, so
// scrubbing and playback just index frames and never call wasm.
const W = 30;
const H = 20;
const TICKS = 40;
const FPS = 10;
const MAX_BRANCHES = 6;
const HASH_LEN = 12;

// The curated law set. `id` selects the Prism step function; `rule` is the
// life-like birth/survival string the law bakes in. Two rules are two laws with
// two content hashes.
interface Law {
  id: string;
  name: string;
  rule: string;
}
const LAWS: Law[] = [
  { id: "conway", name: "Conway", rule: "B3/S23" },
  { id: "highlife", name: "HighLife", rule: "B36/S23" },
];
const lawById = (id: string): Law => LAWS.find((l) => l.id === id) ?? LAWS[0];

// The one origin-wide channel every tab speaks. No message ever leaves the
// origin, and a BroadcastChannel never echoes to its own sender.
const CHANNEL = "prism-world";

// A parsed frame: the compiler's state hash and the unpacked cells. `cells` is
// the row-major 0/1 grid the canvas paints and the fork start state.
interface Frame {
  hash: string;
  cells: Uint8Array;
}

// A branch is one execution prefix: frames over ticks 0..TICKS. A fork shares its
// parent's frames up to `forkTick`, then re-evolves under `law` (optionally with
// one cell toggled) so both branches persist and each reproduces byte for byte.
interface Branch {
  id: number;
  parent: number | null;
  forkTick: number;
  law: string;
  perturbAt: number | null;
  frames: Frame[];
  divergedAt: number;
}

// The shared universe spec: everything needed to recompute the base branch. Two
// tabs on the same spec compute the same base trajectory.
interface Spec {
  seed: string;
  seedName: string;
  law: string;
}

// Fork parameters, broadcast so every tab builds the identical branch.
interface ForkParams {
  id: number;
  parent: number;
  forkTick: number;
  law: string;
  perturbAt: number | null;
}

// -------------------------------- messages ---------------------------------

interface HelloMsg {
  kind: "hello";
  peer: string;
}
interface SyncMsg {
  kind: "sync";
  spec: Spec;
  forks: ForkParams[];
  tick: number;
}
interface SpecMsg {
  kind: "spec";
  spec: Spec;
}
interface ForkMsg {
  kind: "fork";
  fork: ForkParams;
}
interface TickMsg {
  kind: "tick";
  tick: number;
}
interface PresenceMsg {
  kind: "presence";
  peer: string;
  branch: number;
  tick: number;
  hash: string;
}
type Msg = HelloMsg | SyncMsg | SpecMsg | ForkMsg | TickMsg | PresenceMsg;

// -------------------------------- worker -----------------------------------

interface RunReply {
  id: number;
  kind: "run";
  out: string;
}
interface MetaReply {
  id: number;
  kind: "meta";
  hashes: Record<string, string>;
  source: string;
}
interface ErrReply {
  id: number;
  kind: "error";
  error: string;
}
type Reply = RunReply | MetaReply | ErrReply;

const worker = new PrismWorldWorker();
let nextReq = 1;
const pending = new Map<number, { resolve: (r: Reply) => void }>();
worker.onmessage = (e: MessageEvent<Reply>): void => {
  const waiter = pending.get(e.data.id);
  if (waiter === undefined) return;
  pending.delete(e.data.id);
  waiter.resolve(e.data);
};
const ask = (msg: Record<string, unknown>): Promise<Reply> =>
  new Promise((resolve) => {
    const id = nextReq++;
    pending.set(id, { resolve });
    worker.postMessage({ ...msg, id });
  });

// Evolve a grid under a law and parse the trajectory into frames.
async function evolve(law: string, seed: string, ticks: number): Promise<Frame[]> {
  const reply = await ask({ kind: "run", law, w: W, h: H, seed, ticks });
  if (reply.kind === "error") throw new Error(reply.error);
  if (reply.kind !== "run") throw new Error("unexpected reply");
  if (reply.out.startsWith("error:")) throw new Error(reply.out);
  return reply.out
    .split("\n")
    .filter((l) => l.length > 0)
    .map(parseFrame);
}

function parseFrame(line: string): Frame {
  const sp = line.indexOf(" ");
  const hash = line.slice(0, sp);
  const bits = line.slice(sp + 1);
  const cells = new Uint8Array(bits.length);
  for (let i = 0; i < bits.length; i++) cells[i] = bits.charCodeAt(i) === 49 ? 1 : 0;
  return { hash, cells };
}

const cellsToBits = (cells: Uint8Array): string => {
  let s = "";
  for (const c of cells) s += c === 1 ? "1" : "0";
  return s;
};

// -------------------------------- seeds ------------------------------------

// A deterministic pattern generator. Every seed is a plain bitstring, so the
// seed is data too and its content hash is the tick-0 state hash.
type SeedGen = (w: number, h: number) => Uint8Array;

const place = (
  w: number,
  h: number,
  cx: number,
  cy: number,
  cells: [number, number][],
): Uint8Array => {
  const g = new Uint8Array(w * h);
  for (const [dx, dy] of cells) {
    const x = (((cx + dx) % w) + w) % w;
    const y = (((cy + dy) % h) + h) % h;
    g[y * w + x] = 1;
  }
  return g;
};

// A small deterministic PRNG so a "soup" seed is reproducible from its name.
function mulberry32(a: number): () => number {
  return () => {
    a |= 0;
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const SEEDS: { name: string; label: string; gen: SeedGen }[] = [
  {
    name: "r-pentomino",
    label: "R-pentomino",
    gen: (w, h) =>
      place(w, h, w >> 1, h >> 1, [
        [1, 0],
        [2, 0],
        [0, 1],
        [1, 1],
        [1, 2],
      ]),
  },
  {
    name: "acorn",
    label: "Acorn",
    gen: (w, h) =>
      place(w, h, w >> 1, h >> 1, [
        [1, 0],
        [3, 1],
        [0, 2],
        [1, 2],
        [4, 2],
        [5, 2],
        [6, 2],
      ]),
  },
  {
    name: "glider",
    label: "Glider",
    gen: (w, h) =>
      place(w, h, 2, 2, [
        [1, 0],
        [2, 1],
        [0, 2],
        [1, 2],
        [2, 2],
      ]),
  },
  {
    name: "soup",
    label: "Random soup",
    gen: (w, h) => {
      const rnd = mulberry32(0x50524d);
      const g = new Uint8Array(w * h);
      const x0 = w >> 2;
      const y0 = h >> 2;
      for (let y = y0; y < h - y0; y++) {
        for (let x = x0; x < w - x0; x++) g[y * w + x] = rnd() < 0.4 ? 1 : 0;
      }
      return g;
    },
  },
];
const seedByName = (name: string): (typeof SEEDS)[number] =>
  SEEDS.find((s) => s.name === name) ?? SEEDS[0];

// ------------------------------- app state ---------------------------------

const el = <T extends HTMLElement>(id: string): T => document.getElementById(id) as T;
const peerId = crypto.randomUUID();
const chan = new BroadcastChannel(CHANNEL);

let spec: Spec = { seed: "", seedName: "r-pentomino", law: "conway" };
let branches: Branch[] = [];
let active = 0;
let tick = 0;
let playing = false;
let lawHashes: Record<string, string> = {};
let worldSource = "";
// Peers on the origin and their last-reported (branch,tick,hash), for the
// same-origin agreement readout.
const peers = new Map<string, { branch: number; tick: number; hash: string; ts: number }>();

// DOM handles.
const canvas = el<HTMLCanvasElement>("grid");
const scrub = el<HTMLInputElement>("scrub");
const playBtn = el<HTMLButtonElement>("play");
const forkBtn = el<HTMLButtonElement>("fork");
const resetBtn = el<HTMLButtonElement>("reset");
const perturbChk = el<HTMLInputElement>("perturb");
const forkLawSel = el<HTMLSelectElement>("forkLaw");
const exportBtn = el<HTMLButtonElement>("export");
const branchList = el<HTMLDivElement>("branches");
const status = el<HTMLDivElement>("status");
const sourceEl = el<HTMLElement>("source");

const hashEls = {
  state: el<HTMLElement>("hState"),
  law: el<HTMLElement>("hLaw"),
  tick: el<HTMLElement>("hTick"),
  branch: el<HTMLElement>("hBranch"),
  seed: el<HTMLElement>("hSeed"),
};

const activeBranch = (): Branch => branches.find((b) => b.id === active) ?? branches[0];
const baseBranch = (): Branch => branches.find((b) => b.id === 0) ?? branches[0];
const short = (h: string): string => (h.startsWith("error") ? h : h.slice(0, HASH_LEN));

const BR_COLORS = ["#2f6f4f", "#a4362f", "#2660a4", "#8a3fa0", "#9a6a00", "#0f7d78"];
const brColor = (id: number): string => BR_COLORS[id % BR_COLORS.length];

// ------------------------------ computing ----------------------------------

// Build the base branch (id 0) from the current spec, clearing any forks. Every
// tab that receives the spec runs this and, being deterministic, agrees.
async function buildBase(): Promise<void> {
  setBusy(`evolving ${lawById(spec.law).name} from ${seedByName(spec.seedName).label}...`);
  const frames = await evolve(spec.law, spec.seed, TICKS);
  branches = [
    { id: 0, parent: null, forkTick: 0, law: spec.law, perturbAt: null, frames, divergedAt: -1 },
  ];
  active = 0;
  tick = Math.min(tick, TICKS);
  clearBusy();
  renderAll();
}

// Build a fork from broadcast parameters (or a local action). The prefix is the
// parent's frames up to forkTick; the continuation re-evolves the (optionally
// perturbed) grid under the fork's law.
async function buildFork(fp: ForkParams): Promise<void> {
  const parent = branches.find((b) => b.id === fp.parent);
  if (parent === undefined || branches.some((b) => b.id === fp.id)) return;
  setBusy(`forking branch ${fp.id} at tick ${fp.forkTick}...`);
  const start = parent.frames[fp.forkTick].cells.slice();
  if (fp.perturbAt !== null) start[fp.perturbAt] ^= 1;
  const cont = await evolve(fp.law, cellsToBits(start), TICKS - fp.forkTick);
  const frames = parent.frames.slice(0, fp.forkTick).concat(cont);
  const divergedAt = firstDivergence(parent.frames, frames);
  branches.push({
    id: fp.id,
    parent: fp.parent,
    forkTick: fp.forkTick,
    law: fp.law,
    perturbAt: fp.perturbAt,
    frames,
    divergedAt,
  });
  active = fp.id;
  clearBusy();
  renderAll();
}

function firstDivergence(a: Frame[], b: Frame[]): number {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i++) if (a[i].hash !== b[i].hash) return i;
  return -1;
}

// ------------------------------ rendering ----------------------------------

function renderAll(): void {
  drawGrid();
  drawHashes();
  drawBranches();
  scrub.max = String(TICKS);
  scrub.value = String(tick);
}

function drawGrid(): void {
  const ctx = canvas.getContext("2d");
  if (ctx === null || branches.length === 0) return;
  const rect = canvas.getBoundingClientRect();
  const dpr = window.devicePixelRatio || 1;
  const cw = Math.floor(rect.width);
  const ch = Math.floor((rect.width * H) / W);
  if (canvas.width !== Math.round(cw * dpr)) {
    canvas.width = Math.round(cw * dpr);
    canvas.height = Math.round(ch * dpr);
    canvas.style.height = `${ch}px`;
  }
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  const bg =
    getComputedStyle(document.documentElement).getPropertyValue("--bg-soft").trim() || "#f5f5f1";
  ctx.fillStyle = bg;
  ctx.fillRect(0, 0, cw, ch);
  const br = activeBranch();
  const frame = br.frames[Math.min(tick, br.frames.length - 1)];
  if (frame === undefined) return;
  const sx = cw / W;
  const sy = ch / H;
  ctx.fillStyle = brColor(br.id);
  const r = Math.max(1, Math.min(sx, sy) / 2 - 0.5);
  for (let y = 0; y < H; y++) {
    for (let x = 0; x < W; x++) {
      if (frame.cells[y * W + x] === 1) {
        ctx.beginPath();
        ctx.arc(x * sx + sx / 2, y * sy + sy / 2, r, 0, Math.PI * 2);
        ctx.fill();
      }
    }
  }
}

function drawHashes(): void {
  if (branches.length === 0) return;
  const br = activeBranch();
  const frame = br.frames[Math.min(tick, br.frames.length - 1)];
  hashEls.state.textContent = frame === undefined ? "-" : short(frame.hash);
  hashEls.law.textContent = lawHashes[br.law] ?? "-";
  hashEls.tick.textContent = `${tick} / ${TICKS}`;
  hashEls.branch.textContent = br.id === 0 ? "main" : `branch ${br.id}`;
  hashEls.seed.textContent =
    baseBranch().frames[0] === undefined ? "-" : short(baseBranch().frames[0].hash);
  const lawEl = hashEls.law;
  lawEl.dataset.law = `${lawById(br.law).name} (${lawById(br.law).rule})`;
}

function drawBranches(): void {
  branchList.innerHTML = "";
  for (const br of branches) {
    const row = document.createElement("button");
    row.type = "button";
    row.className = `br-row${br.id === active ? " is-active" : ""}`;
    row.style.setProperty("--br", brColor(br.id));
    const dot = document.createElement("span");
    dot.className = "br-dot";
    const name = document.createElement("span");
    name.className = "br-name";
    const law = lawById(br.law);
    name.innerHTML =
      br.id === 0
        ? `<b>main</b> <span class="br-meta">${law.name} ${law.rule}</span>`
        : `<b>branch ${br.id}</b> <span class="br-meta">${law.name} ${law.rule} · forked @ ${br.forkTick}${br.perturbAt !== null ? " · poked" : ""}</span>`;
    const diverge = document.createElement("span");
    diverge.className = "br-diverge";
    diverge.textContent =
      br.divergedAt >= 0 ? `diverges @ ${br.divergedAt}` : br.id === 0 ? "" : "identical tail";
    row.append(dot, name, diverge);
    row.addEventListener("click", () => {
      active = br.id;
      renderAll();
      broadcastPresence();
    });
    branchList.appendChild(row);
  }
  updateAgreement();
}

// The same-origin agreement readout: how many other tabs report the same state
// hash for the branch and tick this tab is showing. This is a local equality
// check across tabs, not a certificate.
function updateAgreement(): void {
  const now = Date.now();
  for (const [id, p] of peers) if (now - p.ts > 4000) peers.delete(id);
  if (branches.length === 0) return;
  const br = activeBranch();
  const frame = br.frames[Math.min(tick, br.frames.length - 1)];
  const mine = frame?.hash ?? "";
  let differ = 0;
  for (const p of peers.values()) {
    if (p.branch !== active || p.tick !== tick) continue;
    if (p.hash !== mine) differ++;
  }
  const peerCount = peers.size;
  const pill = el<HTMLElement>("agree");
  if (peerCount === 0) {
    pill.textContent = "1 tab (open another to compare)";
    pill.className = "agree";
  } else if (differ === 0) {
    pill.textContent = `${peerCount + 1} same-origin tabs · state hash agrees`;
    pill.className = "agree agree--ok";
  } else {
    pill.textContent = `${peerCount + 1} tabs · ${differ} on a different spec`;
    pill.className = "agree agree--warn";
  }
}

// ------------------------------ transport ----------------------------------

function setTick(n: number): void {
  tick = Math.max(0, Math.min(TICKS, n));
  scrub.value = String(tick);
  drawGrid();
  drawHashes();
  updateAgreement();
}

let last = 0;
let acc = 0;
function frameLoop(now: number): void {
  if (!playing) return;
  acc += now - last;
  last = now;
  const interval = 1000 / FPS;
  while (acc >= interval) {
    acc -= interval;
    setTick(tick >= TICKS ? 0 : tick + 1);
    broadcastTick();
  }
  requestAnimationFrame(frameLoop);
}
function setPlaying(on: boolean): void {
  playing = on;
  playBtn.textContent = on ? "Pause" : "Play";
  if (on) {
    if (tick >= TICKS) setTick(0);
    last = performance.now();
    acc = 0;
    requestAnimationFrame(frameLoop);
  }
}

// ------------------------------ broadcast ----------------------------------

const post = (m: Msg): void => chan.postMessage(m);
const broadcastTick = (): void => post({ kind: "tick", tick });
function broadcastPresence(): void {
  if (branches.length === 0) return;
  const br = activeBranch();
  const frame = br.frames[Math.min(tick, br.frames.length - 1)];
  post({ kind: "presence", peer: peerId, branch: active, tick, hash: frame?.hash ?? "" });
}

chan.onmessage = (ev: MessageEvent<Msg>): void => {
  const m = ev.data;
  switch (m.kind) {
    case "hello":
      // A late tab joined: hand it the current spec, forks, and playhead so it
      // recomputes the same universe.
      post({
        kind: "sync",
        spec,
        forks: branches.filter((b) => b.id !== 0).map(toForkParams),
        tick,
      });
      broadcastPresence();
      break;
    case "sync":
      void adoptSync(m);
      break;
    case "spec":
      void adoptSpec(m.spec);
      break;
    case "fork":
      void buildFork(m.fork);
      break;
    case "tick":
      setTick(m.tick);
      break;
    case "presence":
      peers.set(m.peer, { branch: m.branch, tick: m.tick, hash: m.hash, ts: Date.now() });
      updateAgreement();
      break;
  }
};

const toForkParams = (b: Branch): ForkParams => ({
  id: b.id,
  parent: b.parent ?? 0,
  forkTick: b.forkTick,
  law: b.law,
  perturbAt: b.perturbAt,
});

// Adopt a spec broadcast (a new base universe) if it differs from ours.
async function adoptSpec(next: Spec): Promise<void> {
  if (next.seed === spec.seed && next.law === spec.law) return;
  spec = next;
  syncControls();
  await buildBase();
  broadcastPresence();
}

// Adopt a full sync from a peer when we first join, so a late tab lands on the
// exact shared universe (spec, all forks, playhead) the others already share.
async function adoptSync(m: SyncMsg): Promise<void> {
  if (m.spec.seed !== spec.seed || m.spec.law !== spec.law || branches.length <= 1) {
    spec = m.spec;
    syncControls();
    await buildBase();
    for (const fp of m.forks) await buildFork(fp);
    setTick(m.tick);
    broadcastPresence();
  }
}

// -------------------------------- actions ----------------------------------

// Re-evolve the whole universe under a new base law: this is the watchable beat.
// Broadcasting the spec makes every same-origin tab re-evolve and land on the
// same downstream hashes, and the law hash in the bar moves.
async function setLaw(lawId: string): Promise<void> {
  if (spec.law === lawId) return;
  spec = { ...spec, law: lawId };
  syncControls();
  post({ kind: "spec", spec });
  await buildBase();
  broadcastPresence();
}

async function setSeed(name: string): Promise<void> {
  const gen = seedByName(name);
  spec = { seed: cellsToBits(gen.gen(W, H)), seedName: name, law: spec.law };
  tick = 0;
  post({ kind: "spec", spec });
  await buildBase();
  broadcastPresence();
}

// Fork the active branch at the current tick. A different law or a one-cell poke
// makes the continuation diverge while the shared prefix (ticks 0..forkTick) is
// preserved on both branches, so scrubbing back across the fork shows identical
// hashes. Broadcasting the params lets every tab build the same branch.
async function doFork(): Promise<void> {
  if (branches.length >= MAX_BRANCHES) return;
  const parent = activeBranch();
  const forkTick = tick;
  const perturbAt = perturbChk.checked ? pokeCell(parent, forkTick) : null;
  const fp: ForkParams = {
    id: nextBranchId(),
    parent: parent.id,
    forkTick,
    law: forkLawSel.value,
    perturbAt,
  };
  post({ kind: "fork", fork: fp });
  await buildFork(fp);
  broadcastPresence();
}

// A deterministic cell to toggle for a poke: the first live cell at the fork, or
// the centre if the grid is empty there. Deterministic so every tab agrees.
function pokeCell(parent: Branch, forkTick: number): number {
  const cells = parent.frames[forkTick].cells;
  for (let i = 0; i < cells.length; i++) if (cells[i] === 1) return i;
  return (H >> 1) * W + (W >> 1);
}

const nextBranchId = (): number => {
  let id = 1;
  while (branches.some((b) => b.id === id)) id++;
  return id;
};

// --------------------------- lineage export --------------------------------

// The lineage graph vocabulary. Its one home is the Rust compiler,
// src/lineage/graph.rs (the LINEAGE_GRAPH_FORMAT, Variant, NODE_WORLD_* and
// EdgeKind consts); this emitter mirrors those exact spellings, and the Rust
// decoder (`prism lineage show/why/verify`) rejects any drift. A timeline is
// exported as the same request-less "world" graph the decoder reads: law nodes,
// state nodes named by their content hash, and fork nodes, joined by input /
// identified-by / produced edges.
const LINEAGE_GRAPH_FORMAT = "prism-lineage-graph-v1";
const WORLD_VARIANT = "world";
const NODE_WORLD_LAW = "world-law";
const NODE_WORLD_STATE = "world-state";
const NODE_WORLD_FORK = "world-fork";
const EDGE_INPUT = "input";
const EDGE_PRODUCED = "produced";
const EDGE_IDENTIFIED_BY = "identified-by";
// The minted-id scheme fork nodes commit their canonical bytes under, matching
// graph.rs's MINTED_ID_SCHEME so a browser-minted fork id equals the one the
// compiler would mint (and thus passes `lineage verify`).
const FORK_ID_SCHEME = "sha256";
const LINEAGE_EXTENSION = "plineage";
const DIMS = `${W}x${H}`;

interface WorldNode {
  id: string;
  kind: string;
  payload: Record<string, unknown>;
}
interface WorldEdge {
  from: string;
  to: string;
  kind: string;
}

// Mint a fork node id exactly as graph.rs::world_fork_node_id does: sha256 over
// the newline-joined kind tag, parent branch, fork tick, perturb flag, and the two
// state ids it joins, then the scheme-tagged lowercase hex.
async function forkId(
  parentBranch: number,
  forkTick: number,
  perturbed: boolean,
  parentState: string,
  divergent: string,
): Promise<string> {
  const canonical = `${NODE_WORLD_FORK}\n${parentBranch}\n${forkTick}\n${perturbed}\n${parentState}\n${divergent}`;
  const digest = await crypto.subtle.digest("SHA-256", new TextEncoder().encode(canonical));
  let hex = "";
  for (const b of new Uint8Array(digest)) hex += b.toString(16).padStart(2, "0");
  return `${FORK_ID_SCHEME}:${hex}`;
}

// Serialize the current timeline (all branches, all frames, every law used) into
// the shared lineage graph. States dedup by their content-hash id, so a branch's
// shared prefix collapses onto its parent's states; each state a branch newly
// introduces stepped under that branch's law, so its law edge is unambiguous.
async function buildLineageGraph(): Promise<{
  format: string;
  variant: string;
  nodes: WorldNode[];
  edges: WorldEdge[];
}> {
  const nodes: WorldNode[] = [];
  const edges: WorldEdge[] = [];

  // Law nodes: each distinct law used, named by the hash the bar already shows.
  const usedLaws = new Set(branches.map((b) => b.law));
  for (const lawId of usedLaws) {
    const law = lawById(lawId);
    const hash = lawHashes[lawId];
    if (hash === undefined) continue;
    nodes.push({ id: hash, kind: NODE_WORLD_LAW, payload: { rule: law.rule, law_hash: hash } });
  }

  // State nodes and their predecessor / law edges, first-owner wins so a shared
  // prefix state carries one law edge (its owning branch's law).
  const owned = new Set<string>();
  const byId = [...branches].sort((a, b) => a.id - b.id);
  for (const br of byId) {
    const lawHash = lawHashes[br.law];
    for (let t = 0; t < br.frames.length; t++) {
      const sid = br.frames[t].hash;
      if (owned.has(sid)) continue;
      owned.add(sid);
      nodes.push({
        id: sid,
        kind: NODE_WORLD_STATE,
        payload: { tick: t, branch: br.id, dims: DIMS },
      });
      if (lawHash !== undefined) edges.push({ from: sid, to: lawHash, kind: EDGE_IDENTIFIED_BY });
      if (t > 0) edges.push({ from: sid, to: br.frames[t - 1].hash, kind: EDGE_INPUT });
    }
  }

  // Fork nodes: one per branch that forked, joined to the parent state it left and
  // the first divergent state it produced.
  for (const br of byId) {
    if (br.parent === null) continue;
    const parent = branches.find((b) => b.id === br.parent);
    if (parent === undefined) continue;
    const parentState = parent.frames[br.forkTick].hash;
    const divTick = br.divergedAt >= 0 ? br.divergedAt : br.forkTick;
    const divergent = br.frames[divTick].hash;
    const perturbed = br.perturbAt !== null;
    const id = await forkId(br.parent, br.forkTick, perturbed, parentState, divergent);
    nodes.push({
      id,
      kind: NODE_WORLD_FORK,
      payload: { parent_branch: br.parent, fork_tick: br.forkTick, perturbed },
    });
    edges.push({ from: id, to: parentState, kind: EDGE_INPUT });
    edges.push({ from: id, to: divergent, kind: EDGE_PRODUCED });
  }

  // Sort and dedup so re-exporting the same timeline is byte-identical, the same
  // determinism seal graph.rs::finalize applies.
  nodes.sort((a, b) =>
    a.id < b.id ? -1 : a.id > b.id ? 1 : a.kind < b.kind ? -1 : a.kind > b.kind ? 1 : 0,
  );
  const seenNode = new Set<string>();
  const uniqueNodes = nodes.filter((n) => {
    if (seenNode.has(n.id)) return false;
    seenNode.add(n.id);
    return true;
  });
  const edgeKey = (e: WorldEdge): string => `${e.from}\n${e.to}\n${e.kind}`;
  edges.sort((a, b) => {
    const ka = edgeKey(a);
    const kb = edgeKey(b);
    return ka < kb ? -1 : ka > kb ? 1 : 0;
  });
  const seenEdge = new Set<string>();
  const uniqueEdges = edges.filter((e) => {
    const k = edgeKey(e);
    if (seenEdge.has(k)) return false;
    seenEdge.add(k);
    return true;
  });

  return {
    format: LINEAGE_GRAPH_FORMAT,
    variant: WORLD_VARIANT,
    nodes: uniqueNodes,
    edges: uniqueEdges,
  };
}

// Build the graph and download it as `world.plineage`, the shared sidecar format
// `prism lineage show/why/verify` reads.
async function exportLineage(): Promise<void> {
  if (branches.length === 0) return;
  const graph = await buildLineageGraph();
  const blob = new Blob([JSON.stringify(graph, null, 2)], { type: "application/json" });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = `world.${LINEAGE_EXTENSION}`;
  a.click();
  URL.revokeObjectURL(url);
}

// ------------------------------ controls -----------------------------------

function syncControls(): void {
  for (const btn of document.querySelectorAll<HTMLButtonElement>(".law-btn")) {
    btn.classList.toggle("is-active", btn.dataset.law === spec.law);
    btn.setAttribute("aria-pressed", String(btn.dataset.law === spec.law));
  }
  el<HTMLSelectElement>("seedSel").value = spec.seedName;
}

function wireControls(): void {
  for (const btn of document.querySelectorAll<HTMLButtonElement>(".law-btn")) {
    btn.addEventListener("click", () => void setLaw(btn.dataset.law ?? "conway"));
  }
  el<HTMLSelectElement>("seedSel").addEventListener("change", (e) => {
    void setSeed((e.target as HTMLSelectElement).value);
  });
  scrub.addEventListener("input", () => {
    if (playing) setPlaying(false);
    setTick(Number(scrub.value));
    broadcastTick();
  });
  playBtn.addEventListener("click", () => setPlaying(!playing));
  forkBtn.addEventListener("click", () => void doFork());
  exportBtn.addEventListener("click", () => void exportLineage());
  resetBtn.addEventListener("click", () => {
    branches = branches.slice(0, 1);
    active = 0;
    post({ kind: "spec", spec });
    renderAll();
    broadcastPresence();
  });
  window.addEventListener("resize", drawGrid);
  // Keep peers fresh and prune the stale.
  setInterval(() => {
    broadcastPresence();
    updateAgreement();
  }, 2000);
  window.addEventListener("beforeunload", () => chan.close());
}

// -------------------------------- status -----------------------------------

function setBusy(msg: string): void {
  status.textContent = msg;
  status.className = "status status--busy";
  forkBtn.disabled = true;
  for (const b of document.querySelectorAll<HTMLButtonElement>(".law-btn")) b.disabled = true;
}
function clearBusy(): void {
  status.textContent = "";
  status.className = "status";
  forkBtn.disabled = branches.length >= MAX_BRANCHES;
  for (const b of document.querySelectorAll<HTMLButtonElement>(".law-btn")) b.disabled = false;
}
function setError(msg: string): void {
  status.textContent = msg;
  status.className = "status status--err";
}

// --------------------------------- boot ------------------------------------

function fillForkLaw(): void {
  for (const law of LAWS) {
    const opt = document.createElement("option");
    opt.value = law.id;
    opt.textContent = `${law.name} (${law.rule})`;
    forkLawSel.appendChild(opt);
  }
  for (const seed of SEEDS) {
    const opt = document.createElement("option");
    opt.value = seed.name;
    opt.textContent = seed.label;
    el<HTMLSelectElement>("seedSel").appendChild(opt);
  }
}

async function boot(): Promise<void> {
  fillForkLaw();
  wireControls();
  try {
    const meta = await ask({ kind: "meta", laws: LAWS.map((l) => l.id) });
    if (meta.kind !== "meta") throw new Error("meta failed");
    lawHashes = meta.hashes;
    worldSource = meta.source;
    sourceEl.textContent = worldSource;
    for (const law of LAWS) {
      const chip = el<HTMLElement>(`lawhash-${law.id}`);
      if (chip !== null) chip.textContent = lawHashes[law.id] ?? "-";
    }
    spec = {
      seed: cellsToBits(seedByName("r-pentomino").gen(W, H)),
      seedName: "r-pentomino",
      law: "conway",
    };
    syncControls();
    await buildBase();
    // Announce; an existing tab answers with a full sync so we adopt its universe.
    post({ kind: "hello", peer: peerId });
    broadcastPresence();
  } catch (err) {
    setError(`error: ${err}`);
  }
}

void boot();
