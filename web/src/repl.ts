// A minimal, dependency-free browser REPL for Prism. Each line is evaluated by
// the same wasm interpreter the playground uses, off the UI thread via a worker.
// The interpreter wraps a bare expression as an implicit `main` (see wasm `run`),
// so `1 + 2` or `map(f, xs)` evaluate to a value directly. `let` bindings are
// remembered for the session and prepended to later lines; Reset clears them.
// As you type, the current line is type-checked in the background and a small
// gutter dot reports whether it is well-formed.
import "./repl.css";

// A curated gallery, from one-liners to the algebraic-effect and delimited
// continuation features that set Prism apart. Clicking one echoes its source
// into the transcript and runs it as a standalone program.
interface Example {
  label: string;
  code: string;
}

const lines = (...ls: string[]): string => ls.join("\n");

const EXAMPLES: Example[] = [
  { label: "map & square", code: "map(\\(x) -> x * x, [1, 2, 3, 4])" },
  { label: "filter", code: "filter(\\(x) -> x > 2, [1, 2, 3, 4, 5])" },
  { label: "fold a range", code: "foldl(\\(a, b) -> a + b, 0, range(1, 11))" },
  { label: "zip two lists", code: 'zip([1, 2, 3], ["a", "b", "c"])' },
  { label: "function composition", code: "compose(\\(x) -> x + 1, \\(x) -> x * 2, 10)" },
  {
    label: "pattern match",
    code: lines("match Some(42) of", "  Some(x) => x + 1", "  None => 0"),
  },
  {
    label: "guards: fizzbuzz",
    code: lines(
      "fn fizzbuzz(n : Int) : String =",
      "  match n of",
      '    k if k % 15 == 0 => "FizzBuzz"',
      '    k if k % 3 == 0 => "Fizz"',
      '    k if k % 5 == 0 => "Buzz"',
      "    k => show(k)",
      "",
      "fn main() = println(map(fizzbuzz, range(1, 16)))",
    ),
  },
  {
    label: "algebraic effects: state",
    code: lines(
      "effect State {",
      "  ctl get(Unit) : Int,",
      "  ctl put(Int) : Unit",
      "}",
      "",
      "fn counter() : !{State} Int =",
      "  put(get(()) + 1)",
      "  put(get(()) + 1)",
      "  get(())",
      "",
      "fn main() =",
      "  let run =",
      "    handle counter() with",
      "      get(u, k) => \\(s) -> k(s)(s)",
      "      put(s2, k) => \\(_s) -> k(())(s2)",
      "      return r => \\(_s) -> r",
      "  println(run(0))",
    ),
  },
  {
    label: "delimited continuations",
    code: lines(
      "effect Delim {",
      "  ctl shift0(Int) : Int",
      "}",
      "",
      "-- k is multishot: the captured slice (+10) runs twice, the outer +1 once.",
      "fn body() : !{Delim} Int = 10 + shift0(100)",
      "",
      "fn twice() =",
      "  handle body() with",
      "    shift0(v, k) => k(k(v))",
      "    return r => r",
      "",
      "fn main() = println(1 + twice())",
    ),
  },
  {
    label: "exceptions as effects",
    code: lines(
      "effect Exn {",
      "  ctl raise(Int) : Int",
      "}",
      "",
      "fn safe_div(n, d) : !{Exn} Int =",
      "  if d == 0 then raise(0 - 1) else n / d",
      "",
      "fn attempt(n, d) =",
      "  handle safe_div(n, d) with",
      "    raise(code, k) => code",
      "    return r => r",
      "",
      "fn main() =",
      "  println(attempt(10, 0))",
      "  println(attempt(10, 2))",
    ),
  },
];

const el = <T extends HTMLElement>(id: string): T => document.getElementById(id) as T;
const log = el<HTMLDivElement>("log");
const input = el<HTMLInputElement>("in");
const inputrow = el<HTMLDivElement>("inputrow");
const status = el<HTMLSpanElement>("status");
const diag = el<HTMLSpanElement>("diag");
const clear = el<HTMLButtonElement>("clear");
const gear = el<HTMLButtonElement>("gear");
const settings = el<HTMLDivElement>("settings");
const optT = el<HTMLButtonElement>("opt-t");
const optS = el<HTMLButtonElement>("opt-s");
const examples = el<HTMLDivElement>("examples");

// GHCi-style session flags. `+t` prints the result's type, `+s` its wall-clock
// time. Toggled from the settings panel or via `:set +t` / `:unset +s`, and
// remembered across visits.
const opts = { t: false, s: false };
try {
  const saved = JSON.parse(localStorage.getItem("prism-repl-opts") ?? "{}");
  opts.t = saved.t === true;
  opts.s = saved.s === true;
} catch {
  // ignore malformed storage
}
function renderOpts(): void {
  optT.setAttribute("aria-checked", String(opts.t));
  optS.setAttribute("aria-checked", String(opts.s));
  try {
    localStorage.setItem("prism-repl-opts", JSON.stringify(opts));
  } catch {
    // storage may be unavailable (private mode); flags still work this session
  }
}

// Show the bold block caret only while the prompt is empty and focused, so it
// is obvious where to type on load without distracting once you start.
function syncCaret(): void {
  inputrow.classList.toggle("empty", input.value === "" && document.activeElement === input);
}
input.addEventListener("focus", syncCaret);
input.addEventListener("blur", syncCaret);

// One worker, multiplexing `run` and `diag` requests by id. The wasm inside is
// single-threaded, so requests are serviced in the order they are posted; the id
// just routes each reply back to its awaiting caller.
let worker: Worker | undefined;
let seq = 0;
const pending = new Map<number, (s: string) => void>();

function ensureWorker(): Worker {
  if (!worker) {
    worker = new Worker(new URL("./worker.ts", import.meta.url), { type: "module" });
    worker.onmessage = (e: MessageEvent<{ id: number; data: string }>) => {
      const resolve = pending.get(e.data.id);
      if (resolve) {
        pending.delete(e.data.id);
        resolve(e.data.data);
      }
    };
    // If the worker dies (uncaught error / crash) no replies are coming, so
    // settle every awaiting caller with an error instead of leaking their
    // pending entries forever, and drop the worker so the next request spawns a
    // fresh one.
    const fail = (msg: string): void => {
      worker = undefined;
      for (const resolve of pending.values()) resolve(msg);
      pending.clear();
    };
    worker.onerror = (e: ErrorEvent) => fail(`error: worker crashed: ${e.message}`);
    worker.onmessageerror = () => fail("error: worker message could not be deserialized");
  }
  return worker;
}

const request = (kind: "run" | "diag" | "dump", src: string): Promise<string> =>
  new Promise((resolve) => {
    const id = ++seq;
    pending.set(id, resolve);
    ensureWorker().postMessage({ id, kind, src });
  });

const evalProgram = (src: string): Promise<string> => request("run", src);
const checkProgram = (src: string): Promise<string> => request("diag", src);
const dumpProgram = (src: string): Promise<string> => request("dump", src);

const defs: string[] = [];
const history: string[] = [];
let hpos = 0;

// A top-level definition (persisted) versus an expression (evaluated once).
const DEF =
  /^\s*(pub\s+)?(let|fn|fip|fbip|replayable|type|newtype|alias|class|instance|effect|error|canonical|pattern|import)\b/;
const LET_NAME = /^\s*let\s+([A-Za-z_][A-Za-z0-9_']*)/;
// The name a definition binds, for the keywords where a redefinition should
// replace the prior one (an upsert, matching the native REPL). `instance`,
// `canonical` and `import` bind no single name and are left to accumulate.
const DEF_NAME =
  /^\s*(?:pub\s+)?(?:fip\s+|fbip\s+|replayable\s+)*(?:let|fn|type|newtype|alias|class|effect|error|pattern)\s+([A-Za-z_][A-Za-z0-9_']*)/;

function append(cls: string, text: string): void {
  const div = document.createElement("div");
  div.className = cls;
  div.textContent = text;
  log.appendChild(div);
  log.scrollTop = log.scrollHeight;
}

const showResult = (text: string): void =>
  append(text.startsWith("error") ? "repl-err" : "repl-out", text);

async function submit(line: string): Promise<void> {
  const trimmed = line.trim();
  if (!trimmed) return;
  setHealth("idle");
  append("repl-in", `> ${line}`);
  history.push(line);
  hpos = history.length;
  if (trimmed.startsWith(":")) {
    await command(trimmed);
    return;
  }
  if (DEF.test(trimmed)) {
    // Upsert: redefining a name drops its earlier definition so the accumulated
    // program has no duplicate top-level binding (which the checker rejects).
    const dn = trimmed.match(DEF_NAME);
    if (dn) {
      for (let i = defs.length - 1; i >= 0; i--) {
        const pn = defs[i].match(DEF_NAME);
        if (pn && pn[1] === dn[1]) defs.splice(i, 1);
      }
    }
    defs.push(trimmed);
    const m = trimmed.match(LET_NAME);
    if (m) {
      showResult(await evalProgram([...defs, m[1]].join("\n")));
    } else {
      append("repl-in", "defined");
    }
  } else {
    const t0 = performance.now();
    const res = await evalProgram([...defs, line].join("\n"));
    const ms = performance.now() - t0;
    showResult(res);
    if (opts.t && !res.startsWith("error")) {
      const { ty } = await typeSig(line);
      if (ty) append("repl-note", `it : ${ty}`);
    }
    if (opts.s) append("repl-note", `${ms.toFixed(1)} ms`);
  }
}

// Clicking a gallery entry echoes its source (dimmed) and runs it on its own,
// independent of the session's `let` bindings.
async function runExample(code: string): Promise<void> {
  setHealth("idle");
  append("repl-src", code);
  showResult(await evalProgram(code));
}

// The type of an expression: name it in a throwaway function and read back that
// function's signature (`() -> T`, or `forall .. () -> T`), dropping the wrapper
// arrow to leave `T`.
async function typeSig(expr: string): Promise<{ ty?: string; err?: string }> {
  const out = await dumpProgram(`fn __t() =\n  ${expr}`);
  if (out.startsWith("error")) return { err: out };
  const sig = out.split("\n").find((l) => l.startsWith("__t "));
  if (!sig) return { err: "could not infer a type" };
  return {
    ty: sig
      .slice(sig.indexOf(":") + 1)
      .replace(/\(\)\s*->\s*/, "")
      .trim(),
  };
}

const HELP = [
  ":type <expr>    show the inferred type of an expression",
  ":set +t / +s    print the type / elapsed time after each result",
  ":unset +t / +s  turn those off",
  ":clear          fade the transcript away and reset the session",
  ":help           this list",
];

function setFlag(on: boolean, arg: string): void {
  const flag = arg.replace(/^\+/, "").trim();
  if (flag === "t" || flag === "s") {
    opts[flag] = on;
    renderOpts();
    append("repl-note", `+${flag} ${on ? "on" : "off"}`);
  } else {
    append("repl-err", `:${on ? "set" : "unset"} understands +t (type) and +s (timing)`);
  }
}

// REPL commands, prefixed with `:`. The browser subset: no :load / :edit / file
// or shell commands, which have no meaning in the sandbox.
async function command(line: string): Promise<void> {
  const m = line.match(/^:(\S+)\s*(.*)$/s);
  const cmd = m?.[1] ?? "";
  const arg = (m?.[2] ?? "").trim();
  if (cmd === "type" || cmd === "t") {
    if (!arg) {
      append("repl-err", "usage: :type <expr>");
      return;
    }
    const { ty, err } = await typeSig(arg);
    if (ty) append("repl-out", `${arg} : ${ty}`);
    else append("repl-err", err ?? "could not infer a type");
  } else if (cmd === "set" || cmd === "unset") {
    setFlag(cmd === "set", arg);
  } else if (cmd === "clear" || cmd === "reset" || cmd === "r") {
    resetSession();
  } else if (cmd === "help" || cmd === "h" || cmd === "?") {
    for (const l of HELP) append("repl-note", l);
  } else {
    append("repl-err", `unknown command :${cmd} (try :help)`);
  }
}

// --- Live type-checking of the current line -------------------------------

// Strip any ANSI colour a rendered diagnostic might carry (ESC built at
// runtime so the source carries no literal control character).
const ANSI = new RegExp(`${String.fromCharCode(27)}\\[[0-9;]*m`, "g");
let checkTimer: ReturnType<typeof setTimeout> | undefined;
let checkSeq = 0;

type Health = "idle" | "ok" | "error";
function setHealth(h: Health, msg = ""): void {
  status.className = `repl-status ${h}`;
  diag.textContent = msg;
  diag.classList.toggle("show", msg !== "");
}

// Wrap the line the way the interpreter's `run` does, so a bare expression
// type-checks as the body of an implicit `main`.
const wrapMain = (src: string): string =>
  `fn main() =\n${src
    .split("\n")
    .map((l) => `  ${l}`)
    .join("\n")}`;

async function runCheck(): Promise<void> {
  const line = input.value.trim();
  // Definitions are validated on submit; commands and an empty prompt have
  // nothing to type-check.
  if (!line || line.startsWith(":") || DEF.test(line)) {
    setHealth("idle");
    return;
  }
  const mine = ++checkSeq;
  const out = await checkProgram(wrapMain([...defs, line].join("\n")));
  if (mine !== checkSeq) return; // a newer keystroke superseded this check
  let entries: Array<{ kind: string; msg: string }> = [];
  try {
    entries = JSON.parse(out);
  } catch {
    entries = [];
  }
  const err = entries.find((d) => d.kind.endsWith("Error"));
  if (err) {
    setHealth("error", err.msg.replace(ANSI, "").split("\n")[0] ?? "");
  } else {
    setHealth("ok");
  }
}

function scheduleCheck(): void {
  clearTimeout(checkTimer);
  checkTimer = setTimeout(() => void runCheck(), 550);
}

input.addEventListener("input", () => {
  syncCaret();
  scheduleCheck();
});

// --- Bracket matching -----------------------------------------------------

const OPEN: Record<string, string> = { "(": ")", "[": "]", "{": "}" };
const CLOSE = new Set([")", "]", "}"]);

input.addEventListener("keydown", (e: KeyboardEvent) => {
  const s = input.selectionStart ?? 0;
  const t = input.selectionEnd ?? 0;
  const v = input.value;
  const close = OPEN[e.key];
  // Type an opener: insert the matching closer and sit between the pair (any
  // selection is wrapped).
  if (close !== undefined) {
    e.preventDefault();
    input.value = v.slice(0, s) + e.key + v.slice(s, t) + close + v.slice(t);
    input.setSelectionRange(s + 1, s + 1);
    syncCaret();
    scheduleCheck();
    return;
  }
  // Type a closer already sitting under the caret: step over it rather than
  // inserting a duplicate.
  if (CLOSE.has(e.key) && s === t && v[s] === e.key) {
    e.preventDefault();
    input.setSelectionRange(s + 1, s + 1);
    return;
  }
  // Backspace between an empty pair removes both sides.
  const opener = s > 0 ? v[s - 1] : undefined;
  if (e.key === "Backspace" && s === t && opener && OPEN[opener] === v[s]) {
    e.preventDefault();
    input.value = v.slice(0, s - 1) + v.slice(s + 1);
    input.setSelectionRange(s - 1, s - 1);
    syncCaret();
    scheduleCheck();
    return;
  }
  if (e.key === "Enter") {
    const val = input.value;
    input.value = "";
    syncCaret();
    void submit(val);
  } else if (e.key === "ArrowUp") {
    if (hpos > 0) {
      hpos -= 1;
      input.value = history[hpos] ?? "";
      syncCaret();
      e.preventDefault();
    }
  } else if (e.key === "ArrowDown") {
    if (hpos < history.length) {
      hpos += 1;
      input.value = history[hpos] ?? "";
      syncCaret();
      e.preventDefault();
    }
  }
});

// Reset fades the transcript away, then clears the session.
let resetting = false;
function resetSession(): void {
  if (resetting) return;
  const wipe = (): void => {
    defs.length = 0;
    history.length = 0;
    hpos = 0;
    checkSeq += 1;
    log.classList.remove("fading");
    log.replaceChildren();
    setHealth("idle");
    resetting = false;
    input.focus();
    syncCaret();
  };
  if (matchMedia("(prefers-reduced-motion: reduce)").matches || log.childElementCount === 0) {
    wipe();
    return;
  }
  resetting = true;
  log.classList.add("fading");
  setTimeout(wipe, 300);
}
clear.addEventListener("click", () => resetSession());

// The settings hideaway: gear toggles it, a click outside closes it, and each
// row is a switch mirroring a `:set` flag.
function toggleSettings(show?: boolean): void {
  const open = show ?? settings.hidden;
  settings.hidden = !open;
  gear.setAttribute("aria-expanded", String(open));
}
gear.addEventListener("click", (e) => {
  e.stopPropagation();
  toggleSettings();
});
document.addEventListener("click", (e) => {
  const target = e.target as Node;
  if (!settings.hidden && !settings.contains(target) && !gear.contains(target)) {
    toggleSettings(false);
  }
});
optT.addEventListener("click", () => {
  opts.t = !opts.t;
  renderOpts();
});
optS.addEventListener("click", () => {
  opts.s = !opts.s;
  renderOpts();
});
renderOpts();

for (const ex of EXAMPLES) {
  const b = document.createElement("button");
  b.className = "ex";
  b.type = "button";
  b.textContent = ex.label;
  b.title = ex.code;
  b.addEventListener("click", () => {
    input.focus();
    void runExample(ex.code);
  });
  examples.appendChild(b);
}

input.focus();
syncCaret();
// Warm the worker so the first real evaluation is instant.
void evalProgram("0");
