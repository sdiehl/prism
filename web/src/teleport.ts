// Teleport: suspend a running Prism program into a portable `kont` envelope in one
// browser context and resume it in another. The whole compiler and interpreter run
// in wasm; suspend freezes the live continuation (call stack, bound values, pending
// work) into bytes, those exact bytes cross a BroadcastChannel to a second context
// (the receiver iframe here, or any other open tab), and the receiver re-derives
// the program's code identity and checks the envelope's hash against it before it
// resumes. The sender's prefix output followed by the receiver's suffix is
// byte-identical to one uninterrupted run. No dependencies beyond the wasm bundle.
import init, {
  teleport_bundle,
  teleport_cuts,
  teleport_prefix,
  teleport_resume,
  teleport_source,
  teleport_suspend,
  tokens,
} from "../pkg/prism.js";
import { highlight, initFaces } from "./showcase.js";
import "./showcase.css";
import "./teleport.css";

// The one origin-wide channel both roles speak. A host posts an envelope; every
// receiver context (this page's iframe, and any other open teleport tab) hears it,
// and posts an acknowledgement back so the host can light Tab B in place.
const CHANNEL = "prism-teleport";

// Docs anchors on GitHub Pages for the ideas the copy names, so the flavour text
// resolves to the spec/compiler chapters that define them.
const DOC_HASH = "https://sdiehl.github.io/prism/compiler.html#content-addressed-core";

// The two message shapes on the channel. The sender posts an `env`; the receiver,
// after resuming (or refusing), posts an `ack` describing what it did. A
// BroadcastChannel never delivers a message to the instance that sent it, so each
// role only hears the other.
interface EnvMsg {
  kind: "env";
  transfer: number;
  bytes: number[];
  bundle: string;
}
interface AckMsg {
  kind: "ack";
  transfer: number;
  receiver: string;
  ok: boolean;
  lines: number;
  bytes: number;
  bundle: string;
  reason?: "bundle-mismatch" | "resume-refused";
}
interface ReadyMsg {
  kind: "ready";
  receiver: string;
  bundle: string;
}
type Msg = EnvMsg | AckMsg | ReadyMsg;

// A guaranteed element (host and receiver DOMs each contain their own set), cast
// like the other residents' `el`. `find` is the nullable form the role dispatch
// uses to tell which DOM this module loaded into.
const el = <T extends HTMLElement>(id: string): T => document.getElementById(id) as T;
const find = (id: string): HTMLElement | null => document.getElementById(id);
const shortId = (s: string): string => s.slice(0, 8);
const newReceiverId = (): string => {
  if ("crypto" in globalThis && typeof globalThis.crypto.randomUUID === "function") {
    return globalThis.crypto.randomUUID();
  }
  return `recv-${Date.now().toString(36)}-${Math.random().toString(36).slice(2)}`;
};

// Count the non-empty printed lines in a transcript.
const lineCount = (s: string): number => s.split("\n").filter((l) => l.length > 0).length;

// ------------------------------- receiver ----------------------------------

async function receiver(
  outEl: HTMLElement,
  proofEl: HTMLElement,
  identityEl: HTMLElement | null,
): Promise<void> {
  await init();
  const receiverId = newReceiverId();
  const mine = teleport_bundle();
  identityEl?.replaceChildren(`receiver ${shortId(receiverId)} · code ${mine.slice(0, 12)}`);
  const chan = new BroadcastChannel(CHANNEL);
  const announce = (): void =>
    chan.postMessage({ kind: "ready", receiver: receiverId, bundle: mine } satisfies ReadyMsg);
  announce();
  chan.onmessage = (ev: MessageEvent<Msg>): void => {
    if (ev.data.kind !== "env") return;
    const env = ev.data;
    const bytes = Uint8Array.from(env.bytes);
    if (env.bundle !== mine) {
      outEl.textContent = "refused, wrong bundle";
      outEl.classList.add("err");
      proofEl.innerHTML = `<span class="tp-x">rejected</span> sender code <code>${env.bundle.slice(0, 12)}</code> does not match receiver code <code>${mine.slice(0, 12)}</code>`;
      proofEl.className = "tp-proof tp-proof--bad";
      chan.postMessage({
        kind: "ack",
        transfer: env.transfer,
        receiver: receiverId,
        ok: false,
        lines: 0,
        bytes: bytes.length,
        bundle: mine,
        reason: "bundle-mismatch",
      } satisfies AckMsg);
      return;
    }
    const suffix = teleport_resume(bytes);
    if (suffix.startsWith("error:")) {
      // Totality and the hash check in one path: a corrupted or foreign envelope is
      // refused before a single step runs, and says why.
      outEl.textContent = "refused, nothing ran";
      outEl.classList.add("err");
      const why = suffix.replace(/^error:\s*(runtime:\s*)?(resume:\s*)?/, "");
      proofEl.innerHTML = `<span class="tp-x">rejected</span> ${why}`;
      proofEl.className = "tp-proof tp-proof--bad";
      chan.postMessage({
        kind: "ack",
        transfer: env.transfer,
        receiver: receiverId,
        ok: false,
        lines: 0,
        bytes: bytes.length,
        bundle: mine,
        reason: "resume-refused",
      } satisfies AckMsg);
      return;
    }
    outEl.classList.remove("err");
    outEl.textContent = suffix;
    proofEl.innerHTML = `same program (<a href="${DOC_HASH}" target="_blank" rel="noopener">code hash</a> <code>${mine.slice(0, 12)}</code> matches), resumed from a ${bytes.length}-byte continuation snapshot`;
    proofEl.className = "tp-proof tp-proof--ok";
    // Pulse in place as the output arrives, then tell the host to pulse Tab B too.
    outEl.classList.remove("tp-arrive");
    void outEl.offsetWidth;
    outEl.classList.add("tp-arrive");
    chan.postMessage({
      kind: "ack",
      transfer: env.transfer,
      receiver: receiverId,
      ok: true,
      lines: lineCount(suffix),
      bytes: bytes.length,
      bundle: mine,
    } satisfies AckMsg);
  };
  outEl.textContent = "waiting for Tab A to pause";
  window.addEventListener("focus", announce);
  setInterval(announce, 1000);
}

// -------------------------------- sender -----------------------------------

async function sender(root: HTMLElement): Promise<void> {
  const outA = el<HTMLPreElement>("outA");
  const scrub = el<HTMLInputElement>("stepScrub");
  const stepLabel = el<HTMLElement>("stepLabel");
  const btn = el<HTMLButtonElement>("teleportBtn");
  const tamper = el<HTMLInputElement>("tamper");
  const tabA = el<HTMLElement>("tabA");
  const tabB = el<HTMLElement>("tabB");
  const wire = el<HTMLElement>("wire");
  const packet = el<HTMLElement>("packet");
  const story = el<HTMLElement>("story");
  const receiverStatus = el<HTMLElement>("receiverStatus");
  const codeEl = find("code");

  await init();
  if (codeEl) highlight(codeEl, teleport_source(), tokens);
  initFaces();

  // The machine-step budget for each interior line boundary: the slider indexes
  // this so it reads in lines ("pause after line 3"), not opaque steps.
  const cuts = Array.from(teleport_cuts());
  if (cuts.length === 0) {
    root.dataset.status = "could not map the program's line boundaries";
    return;
  }
  scrub.max = String(cuts.length);
  if (Number(scrub.value) > cuts.length) scrub.value = String(Math.min(3, cuts.length));

  const chan = new BroadcastChannel(CHANNEL);
  const receivers = new Map<string, string>();
  // What Tab A has printed at the chosen cut, so the narrative can quote its last
  // line and the receiver's ack can be phrased against a real count.
  let prefix = "";
  let nextTransfer = 1;
  let activeTransfer = 0;

  const renderReceivers = (): void => {
    const count = receivers.size;
    if (count === 0) {
      receiverStatus.textContent = "waiting for a same-origin receiver";
      btn.disabled = true;
      return;
    }
    const hashes = new Set(receivers.values());
    const mine = teleport_bundle();
    const compatible = hashes.size === 1 && hashes.has(mine);
    receiverStatus.textContent = compatible
      ? `${count} same-origin receiver${count === 1 ? "" : "s"} ready · code ${mine.slice(0, 12)}`
      : `${count} receiver${count === 1 ? "" : "s"} ready, but code identity differs`;
    btn.disabled = !compatible;
  };

  // Show what Tab A has printed by the chosen pause line. Recomputed on release (not
  // every drag tick) so dragging stays smooth; the wasm recompiles per call.
  const preview = (): void => {
    const line = Number(scrub.value);
    prefix = teleport_prefix(cuts[line - 1]);
    outA.textContent = prefix;
  };
  scrub.addEventListener("input", () => {
    stepLabel.textContent = scrub.value;
  });
  scrub.addEventListener("change", preview);

  // Light Tab B and rewrite the narrative once the receiver reports back.
  chan.onmessage = (ev: MessageEvent<Msg>): void => {
    if (ev.data.kind === "ready") {
      receivers.set(ev.data.receiver, ev.data.bundle);
      renderReceivers();
      return;
    }
    if (ev.data.kind !== "ack" || ev.data.transfer !== activeTransfer) return;
    const ack = ev.data;
    tabB.classList.remove("tp-pulse");
    void tabB.offsetWidth;
    tabB.classList.add("tp-pulse");
    const k = lineCount(prefix);
    const last =
      prefix
        .split("\n")
        .filter((l) => l.length > 0)
        .at(-1) ?? "";
    story.className = "tp-story";
    if (ack.ok) {
      story.innerHTML = `Tab A printed the first <b>${k}</b> line${k === 1 ? "" : "s"} (through &ldquo;${last}&rdquo;), then paused. Its live continuation, a <b>${ack.bytes}-byte</b> snapshot, flew over the same-origin BroadcastChannel to receiver <b>${shortId(ack.receiver)}</b>, which confirmed the <a href="${DOC_HASH}" target="_blank" rel="noopener">code hash</a> <code>${ack.bundle.slice(0, 12)}</code> matched and resumed at line <b>${k + 1}</b>. It never re-ran those first ${k} steps.`;
    } else if (ack.reason === "bundle-mismatch") {
      story.innerHTML = `Receiver <b>${shortId(ack.receiver)}</b> is on the same origin, but it has a different code hash <code>${ack.bundle.slice(0, 12)}</code>. Tab B refused the continuation before running any step; same-origin transport is not enough without matching content identity.`;
    } else {
      story.innerHTML = `One byte was corrupted in flight. Tab B decoded the snapshot, found it no longer matched, and <b>refused to run a single step</b>. No crash, no partial output. A continuation resumes only if it arrives exactly intact.`;
    }
  };

  btn.addEventListener("click", () => {
    const line = Number(scrub.value);
    activeTransfer = nextTransfer++;
    const bytes = teleport_suspend(cuts[line - 1]);
    if (bytes.length === 0) {
      root.dataset.status = "the program finished before that line, nothing to teleport";
      return;
    }
    const wireBytes = bytes.slice();
    // The tamper toggle flips one interior byte, so the receiver's total decode and
    // hash check reject the envelope: the demo's proof that resume is not blind.
    if (tamper.checked) wireBytes[Math.floor(wireBytes.length / 2)] ^= 0x5a;

    // Animate in place: pulse Tab A at the pause, send the packet along the wire
    // between the two visible tabs, and post the envelope. Tab B lights on its ack.
    tabA.classList.remove("tp-pulse");
    void tabA.offsetWidth;
    tabA.classList.add("tp-pulse");
    wire.classList.toggle("tp-wire--bad", tamper.checked);
    packet.classList.remove("tp-fly");
    void packet.offsetWidth;
    packet.classList.add("tp-fly");

    story.className = "tp-story tp-story--wait";
    story.textContent = tamper.checked
      ? "a corrupted continuation is crossing the channel…"
      : "the paused continuation is crossing the channel…";

    chan.postMessage({
      kind: "env",
      transfer: activeTransfer,
      bytes: Array.from(wireBytes),
      bundle: teleport_bundle(),
    } satisfies EnvMsg);
  });

  root.removeAttribute("data-status");
  preview();
  renderReceivers();
}

// ------------------------------- dispatch ----------------------------------

// The receiver page (teleport-recv.html) has #recvOut; the host page has the sender
// controls. One module, one of two roles by which DOM it loaded into.
const recvOut = find("recvOut");
const recvProof = find("recvProof");
const recvIdentity = find("recvIdentity");
const status = find("status");

if (recvOut && recvProof) {
  void receiver(recvOut, recvProof, recvIdentity);
} else if (status) {
  void sender(status).catch((err) => {
    status.dataset.status = `error: ${err}`;
  });
}
