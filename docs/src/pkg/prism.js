/* @ts-self-types="./prism.d.ts" */

/**
 * Run the boids swarm for `steps` deterministic steps and return the whole
 * trajectory as text.
 *
 * The first line is `W H` (the toroidal world dimensions); each following line
 * is one frame, a space-separated list of `x,y` integer positions. Frame N is
 * `step` composed N times on the seeded swarm, a pure function of the index, so
 * the browser scrubber positions its playhead at any frame by replaying to it.
 * On any front-end or runtime error, returns the rendered diagnostic instead.
 * @param {number} steps
 * @returns {string}
 */
export function boids_run(steps) {
    let deferred1_0;
    let deferred1_1;
    try {
        const ret = wasm.boids_run(steps);
        deferred1_0 = ret[0];
        deferred1_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
    }
}

/**
 * Continue the boids swarm from an arbitrary state `state` for `steps` steps,
 * returning the full-state trajectory (`boids_run_full`'s format) from that
 * state.
 *
 * `state` is one full-state frame: a space-separated list of `x,y,vx,vy`
 * integer boids, exactly a line of [`boids_run_full`]'s output. The branching
 * demo forks a timeline by taking frame N of the base run, perturbing one boid,
 * and passing the perturbed frame here. Because `run_trace_from` is a pure
 * function of the swarm and the step count, replaying a branch with the same
 * perturbed state is byte-identical: that is the determinism claim the two
 * side-by-side timelines rest on. A malformed `state` returns an `error:` line.
 * @param {string} state
 * @param {number} steps
 * @returns {string}
 */
export function boids_run_from(state, steps) {
    let deferred2_0;
    let deferred2_1;
    try {
        const ptr0 = passStringToWasm0(state, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.boids_run_from(ptr0, len0, steps);
        deferred2_0 = ret[0];
        deferred2_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

/**
 * Run the boids swarm for `steps` steps and return the whole trajectory in
 * FULL state: like [`boids_run`], but each boid is `x,y,vx,vy` (position and
 * velocity), not just `x,y`.
 *
 * The velocity is what a branching timeline needs: to fork at frame N and
 * continue the run, the frontend perturbs that frame's full state and hands it
 * to [`boids_run_from`]. Positions alone cannot be continued (one `step` reads
 * each boid's velocity), so the branch demo drives on this trajectory.
 * @param {number} steps
 * @returns {string}
 */
export function boids_run_full(steps) {
    let deferred1_0;
    let deferred1_1;
    try {
        const ret = wasm.boids_run_full(steps);
        deferred1_0 = ret[0];
        deferred1_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
    }
}

/**
 * Run one batch of `count` hostile schedules of the concurrent swarm, starting
 * at seed index `start`, and report how many landed on the reference final
 * state.
 *
 * Returns three lines: `<agreed> <count> <refhash>` (agreed is how many of the
 * batch's schedules matched the global reference hash; it is always `count`,
 * which is the determinism claim), then the interleaving of the batch's first
 * two schedules as space-separated fiber ids. Each schedule is a distinct
 * seeded-shuffle of the same fibers over the same channel, so the two
 * interleavings differ while the hash does not. The browser calls this in
 * growing batches to tick a progressive counter without freezing the tab: the
 * count is what the frame budget affords, but every schedule genuinely agrees.
 * On any error, returns the rendered diagnostic instead.
 * @param {number} start
 * @param {number} count
 * @returns {string}
 */
export function chaos_run(start, count) {
    let deferred1_0;
    let deferred1_1;
    try {
        const ret = wasm.chaos_run(start, count);
        deferred1_0 = ret[0];
        deferred1_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
    }
}

/**
 * The fully lowered CBPV core IR of the snippet's own functions.
 *
 * Prelude elided: effects lowered, reference counting and FBIP reuse applied.
 * The lowest-level view the browser can produce. The LLVM back-end is native
 * only.
 * @param {string} src
 * @returns {string}
 */
export function core_ir(src) {
    let deferred2_0;
    let deferred2_1;
    try {
        const ptr0 = passStringToWasm0(src, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.core_ir(ptr0, len0);
        deferred2_0 = ret[0];
        deferred2_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

/**
 * Compiler diagnostics for `src` as JSON.
 *
 * Each entry is `{s,e,line,col,endLine,endCol,kind,msg}` with spans in the
 * snippet's own coordinates (the prepended prelude is subtracted). A hard
 * error aborts the front-end at the first one, so on failure this carries a
 * single `*Error` entry; on success it carries the type checker's non-fatal
 * `Warning`s (orphan/overlapping instances), of which there may be several.
 * @param {string} src
 * @returns {string}
 */
export function diagnostics(src) {
    let deferred2_0;
    let deferred2_1;
    try {
        const ptr0 = passStringToWasm0(src, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.diagnostics(ptr0, len0);
        deferred2_0 = ret[0];
        deferred2_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

/**
 * The top-level type signatures of the snippet's own declarations (prelude
 * signatures elided), or the front-end error as text.
 * @param {string} src
 * @returns {string}
 */
export function dump(src) {
    let deferred2_0;
    let deferred2_1;
    try {
        const ptr0 = passStringToWasm0(src, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.dump(ptr0, len0);
        deferred2_0 = ret[0];
        deferred2_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

/**
 * Pretty-print a snippet, or return the parse/lex error as text.
 * @param {string} src
 * @returns {string}
 */
export function fmt(src) {
    let deferred2_0;
    let deferred2_1;
    try {
        const ptr0 = passStringToWasm0(src, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.fmt(ptr0, len0);
        deferred2_0 = ret[0];
        deferred2_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

/**
 * The snippet's own definitions as a content-addressed Merkle DAG.
 *
 * Returns a JSON array of `{name, hash, deps}` with the prelude elided: `hash`
 * is the short content hash of the definition's elaborated core, and `deps`
 * names the other user definitions it references. A definition's hash folds in
 * its dependencies' hashes, so editing one definition moves its hash and the
 * hash of everything that transitively depends on it, while independent code
 * keeps its address. This is the same addressing `dump core-hash` and the
 * on-disk store use; the browser only renders it. On a front-end error, returns
 * `{"error": "..."}`.
 * @param {string} src
 * @returns {string}
 */
export function hash_defs(src) {
    let deferred2_0;
    let deferred2_1;
    try {
        const ptr0 = passStringToWasm0(src, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.hash_defs(ptr0, len0);
        deferred2_0 = ret[0];
        deferred2_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

/**
 * One re-demand of a fixed incremental demand graph, for the
 * incremental-computation gallery resident.
 *
 * The graph is three source cells `a`, `b`, `c` feeding `total = a + b + c`,
 * `peak = max(a, b, c)`, `scaled = total * 2`, `alert = peak * 10`, and
 * `board = scaled + alert`. The `payload` is `{"prev": {a,b,c} | null, "next":
 * {a,b,c}}`. With `prev` null this is the cold first demand: every derivation
 * recomputes. Otherwise it runs the real `Incr` engine with `prev`, changes the
 * sources to `next`, re-demands `board`, and classifies each cell: a derivation
 * whose body re-ran is `recomputed` if its value changed and `cutoff` if the
 * value was unchanged (so its dependents were spared), and one whose body never
 * ran is `cached`. Returns JSON `{"nodes": [{"name","value","state"}]}` or
 * `{"error": "..."}`.
 * @param {string} payload
 * @returns {string}
 */
export function incr_run(payload) {
    let deferred2_0;
    let deferred2_1;
    try {
        const ptr0 = passStringToWasm0(payload, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.incr_run(ptr0, len0);
        deferred2_0 = ret[0];
        deferred2_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

/**
 * Run the double pendulum for `steps` frames and return the whole trajectory as
 * text.
 *
 * The first line is the maximum reach (rod length + rod length), so the renderer
 * can scale the pivot's disk to the canvas; each following line is one frame,
 * `x1,y1,x2,y2`, the two bob centers with the pivot at the origin and y pointing
 * down. Frame N is the symplectic integrator composed N times on the chaotic
 * initial condition, a pure function of the index, so the scrubber positions its
 * playhead at any frame by replaying to it. Every op is IEEE Float over the
 * vendored libm, so the chaos is bit-identical on every backend and every replay.
 * On any front-end or runtime error, returns the rendered diagnostic instead.
 * @param {number} steps
 * @returns {string}
 */
export function pendulum_run(steps) {
    let deferred1_0;
    let deferred1_1;
    try {
        const ret = wasm.pendulum_run(steps);
        deferred1_0 = ret[0];
        deferred1_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
    }
}

/**
 * Run a snippet and return its captured `print` transcript verbatim.
 *
 * The exact bytes emitted, the same the differential oracle compares. On any
 * front-end or runtime error, returns the rendered diagnostic instead.
 * @param {string} src
 * @returns {string}
 */
export function run(src) {
    let deferred2_0;
    let deferred2_1;
    try {
        const ptr0 = passStringToWasm0(src, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.run(ptr0, len0);
        deferred2_0 = ret[0];
        deferred2_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

/**
 * The code-identity digest (namespace root) of the baked teleport program.
 *
 * Both tabs compute this from the same embedded source, so it is the hash the
 * receiver checks an incoming envelope against; the demo shows it as the proof
 * that teleport verifies code identity, not just moves bytes.
 * @returns {string}
 */
export function teleport_bundle() {
    let deferred1_0;
    let deferred1_1;
    try {
        const ret = wasm.teleport_bundle();
        deferred1_0 = ret[0];
        deferred1_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
    }
}

/**
 * The machine-step budget to pass [`teleport_prefix`]/[`teleport_suspend`] to
 * pause after each printed line, one entry per interior line boundary.
 *
 * Lets the demo's control read in lines ("pause after line 3") rather than opaque
 * machine steps: the slider indexes this list. The last line is omitted because
 * pausing there is a completed run with nothing to teleport.
 * @returns {Uint32Array}
 */
export function teleport_cuts() {
    const ret = wasm.teleport_cuts();
    var v1 = getArrayU32FromWasm0(ret[0], ret[1]).slice();
    wasm.__wbindgen_free(ret[0], ret[1] * 4, 4);
    return v1;
}

/**
 * The teleport program's output up to `steps` machine steps.
 *
 * This is what the sending tab has printed by the moment it suspends; followed by
 * [`teleport_resume`]'s output, it reproduces an uninterrupted run byte for byte.
 * @param {number} steps
 * @returns {string}
 */
export function teleport_prefix(steps) {
    let deferred1_0;
    let deferred1_1;
    try {
        const ret = wasm.teleport_prefix(steps);
        deferred1_0 = ret[0];
        deferred1_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
    }
}

/**
 * Resume a `kont` envelope in the receiving tab and return the continued output.
 *
 * The envelope is decoded totally (hostile bytes are rejected, not trusted) and
 * its bundle digest is checked against this program's freshly derived code
 * identity, so an envelope from a different program is refused by hash before a
 * step runs. On success the returned suffix, following the sender's prefix,
 * reproduces an uninterrupted run.
 * @param {Uint8Array} bytes
 * @returns {string}
 */
export function teleport_resume(bytes) {
    let deferred2_0;
    let deferred2_1;
    try {
        const ptr0 = passArray8ToWasm0(bytes, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.teleport_resume(ptr0, len0);
        deferred2_0 = ret[0];
        deferred2_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

/**
 * The baked teleport program's source, for the read-only panel beside the demo.
 * @returns {string}
 */
export function teleport_source() {
    let deferred1_0;
    let deferred1_1;
    try {
        const ret = wasm.teleport_source();
        deferred1_0 = ret[0];
        deferred1_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
    }
}

/**
 * Suspend the teleport program after `steps` machine steps and return the whole
 * continuation as `kont` envelope bytes: the value that flies between tabs.
 *
 * An empty result means the program finished before `steps` (nothing left to
 * teleport). The bytes are the exact wire the receiver decodes; the animation
 * shows them literally.
 * @param {number} steps
 * @returns {Uint8Array}
 */
export function teleport_suspend(steps) {
    const ret = wasm.teleport_suspend(steps);
    var v1 = getArrayU8FromWasm0(ret[0], ret[1]).slice();
    wasm.__wbindgen_free(ret[0], ret[1] * 1, 1);
    return v1;
}

/**
 * A JSON array of `{s,e,c}` (byte start, byte end, highlight class) for every
 * token in `src`, for editor syntax highlighting. Lex errors are skipped here;
 * they surface through [`diagnostics`].
 * @param {string} src
 * @returns {string}
 */
export function tokens(src) {
    let deferred2_0;
    let deferred2_1;
    try {
        const ptr0 = passStringToWasm0(src, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.tokens(ptr0, len0);
        deferred2_0 = ret[0];
        deferred2_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

/**
 * The content hash of a law's `step` function, the identity the resident shows
 * as its law hash. It is the compiler's own Merkle hash of the elaborated Core,
 * so it moves when and only when the rule's behaviour moves, and is independent
 * of the grid the law runs on. Returns `error: ...` for an unknown law or a
 * front-end failure.
 * @param {string} law
 * @returns {string}
 */
export function world_law_hash(law) {
    let deferred2_0;
    let deferred2_1;
    try {
        const ptr0 = passStringToWasm0(law, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.world_law_hash(ptr0, len0);
        deferred2_0 = ret[0];
        deferred2_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
    }
}

/**
 * Evolve a seed grid under a law for `ticks` generations and return the whole
 * trajectory. Each output line is one tick, `<state-hash> <bits>`: the blake3
 * digest of the canonical grid encoding (see `examples/world.pr`) and the raw
 * row-major 0/1 string. Line 0 is the seed itself, so its hash is the seed hash.
 *
 * `seed_bits` is a `w * h` string of `0`/`1` (the browser generates the pattern,
 * so the seed is data too); `law` selects the step function. Because `trace` is
 * a pure function of the seed, law, and tick count, forking a timeline is just
 * re-running from a perturbed grid, and two clients evolving the same seed under
 * the same law print identical hashes with no coordination. A malformed seed,
 * unknown law, or front-end error returns an `error:` line.
 * @param {string} law
 * @param {number} w
 * @param {number} h
 * @param {string} seed_bits
 * @param {number} ticks
 * @returns {string}
 */
export function world_run(law, w, h, seed_bits, ticks) {
    let deferred3_0;
    let deferred3_1;
    try {
        const ptr0 = passStringToWasm0(law, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(seed_bits, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.world_run(ptr0, len0, w, h, ptr1, len1, ticks);
        deferred3_0 = ret[0];
        deferred3_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred3_0, deferred3_1, 1);
    }
}

/**
 * The Prism source of the world laws, exactly as it runs: the same definitions
 * the hash and evolution paths compile, so the resident's source face shows the
 * real law, not a paraphrase.
 * @returns {string}
 */
export function world_source() {
    let deferred1_0;
    let deferred1_1;
    try {
        const ret = wasm.world_source();
        deferred1_0 = ret[0];
        deferred1_1 = ret[1];
        return getStringFromWasm0(ret[0], ret[1]);
    } finally {
        wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
    }
}
function __wbg_get_imports() {
    const import0 = {
        __proto__: null,
        __wbindgen_init_externref_table: function() {
            const table = wasm.__wbindgen_externrefs;
            const offset = table.grow(4);
            table.set(0, undefined);
            table.set(offset + 0, undefined);
            table.set(offset + 1, null);
            table.set(offset + 2, true);
            table.set(offset + 3, false);
        },
    };
    return {
        __proto__: null,
        "./prism_bg.js": import0,
    };
}

function getArrayU32FromWasm0(ptr, len) {
    ptr = ptr >>> 0;
    return getUint32ArrayMemory0().subarray(ptr / 4, ptr / 4 + len);
}

function getArrayU8FromWasm0(ptr, len) {
    ptr = ptr >>> 0;
    return getUint8ArrayMemory0().subarray(ptr / 1, ptr / 1 + len);
}

function getStringFromWasm0(ptr, len) {
    return decodeText(ptr >>> 0, len);
}

let cachedUint32ArrayMemory0 = null;
function getUint32ArrayMemory0() {
    if (cachedUint32ArrayMemory0 === null || cachedUint32ArrayMemory0.byteLength === 0) {
        cachedUint32ArrayMemory0 = new Uint32Array(wasm.memory.buffer);
    }
    return cachedUint32ArrayMemory0;
}

let cachedUint8ArrayMemory0 = null;
function getUint8ArrayMemory0() {
    if (cachedUint8ArrayMemory0 === null || cachedUint8ArrayMemory0.byteLength === 0) {
        cachedUint8ArrayMemory0 = new Uint8Array(wasm.memory.buffer);
    }
    return cachedUint8ArrayMemory0;
}

function passArray8ToWasm0(arg, malloc) {
    const ptr = malloc(arg.length * 1, 1) >>> 0;
    getUint8ArrayMemory0().set(arg, ptr / 1);
    WASM_VECTOR_LEN = arg.length;
    return ptr;
}

function passStringToWasm0(arg, malloc, realloc) {
    if (realloc === undefined) {
        const buf = cachedTextEncoder.encode(arg);
        const ptr = malloc(buf.length, 1) >>> 0;
        getUint8ArrayMemory0().subarray(ptr, ptr + buf.length).set(buf);
        WASM_VECTOR_LEN = buf.length;
        return ptr;
    }

    let len = arg.length;
    let ptr = malloc(len, 1) >>> 0;

    const mem = getUint8ArrayMemory0();

    let offset = 0;

    for (; offset < len; offset++) {
        const code = arg.charCodeAt(offset);
        if (code > 0x7F) break;
        mem[ptr + offset] = code;
    }
    if (offset !== len) {
        if (offset !== 0) {
            arg = arg.slice(offset);
        }
        ptr = realloc(ptr, len, len = offset + arg.length * 3, 1) >>> 0;
        const view = getUint8ArrayMemory0().subarray(ptr + offset, ptr + len);
        const ret = cachedTextEncoder.encodeInto(arg, view);

        offset += ret.written;
        ptr = realloc(ptr, len, offset, 1) >>> 0;
    }

    WASM_VECTOR_LEN = offset;
    return ptr;
}

let cachedTextDecoder = new TextDecoder('utf-8', { ignoreBOM: true, fatal: true });
cachedTextDecoder.decode();
const MAX_SAFARI_DECODE_BYTES = 2146435072;
let numBytesDecoded = 0;
function decodeText(ptr, len) {
    numBytesDecoded += len;
    if (numBytesDecoded >= MAX_SAFARI_DECODE_BYTES) {
        cachedTextDecoder = new TextDecoder('utf-8', { ignoreBOM: true, fatal: true });
        cachedTextDecoder.decode();
        numBytesDecoded = len;
    }
    return cachedTextDecoder.decode(getUint8ArrayMemory0().subarray(ptr, ptr + len));
}

const cachedTextEncoder = new TextEncoder();

if (!('encodeInto' in cachedTextEncoder)) {
    cachedTextEncoder.encodeInto = function (arg, view) {
        const buf = cachedTextEncoder.encode(arg);
        view.set(buf);
        return {
            read: arg.length,
            written: buf.length
        };
    };
}

let WASM_VECTOR_LEN = 0;

let wasmModule, wasmInstance, wasm;
function __wbg_finalize_init(instance, module) {
    wasmInstance = instance;
    wasm = instance.exports;
    wasmModule = module;
    cachedUint32ArrayMemory0 = null;
    cachedUint8ArrayMemory0 = null;
    wasm.__wbindgen_start();
    return wasm;
}

async function __wbg_load(module, imports) {
    if (typeof Response === 'function' && module instanceof Response) {
        if (typeof WebAssembly.instantiateStreaming === 'function') {
            try {
                return await WebAssembly.instantiateStreaming(module, imports);
            } catch (e) {
                const validResponse = module.ok && expectedResponseType(module.type);

                if (validResponse && module.headers.get('Content-Type') !== 'application/wasm') {
                    console.warn("`WebAssembly.instantiateStreaming` failed because your server does not serve Wasm with `application/wasm` MIME type. Falling back to `WebAssembly.instantiate` which is slower. Original error:\n", e);

                } else { throw e; }
            }
        }

        const bytes = await module.arrayBuffer();
        return await WebAssembly.instantiate(bytes, imports);
    } else {
        const instance = await WebAssembly.instantiate(module, imports);

        if (instance instanceof WebAssembly.Instance) {
            return { instance, module };
        } else {
            return instance;
        }
    }

    function expectedResponseType(type) {
        switch (type) {
            case 'basic': case 'cors': case 'default': return true;
        }
        return false;
    }
}

function initSync(module) {
    if (wasm !== undefined) return wasm;


    if (module !== undefined) {
        if (Object.getPrototypeOf(module) === Object.prototype) {
            ({module} = module)
        } else {
            console.warn('using deprecated parameters for `initSync()`; pass a single object instead')
        }
    }

    const imports = __wbg_get_imports();
    if (!(module instanceof WebAssembly.Module)) {
        module = new WebAssembly.Module(module);
    }
    const instance = new WebAssembly.Instance(module, imports);
    return __wbg_finalize_init(instance, module);
}

async function __wbg_init(module_or_path) {
    if (wasm !== undefined) return wasm;


    if (module_or_path !== undefined) {
        if (Object.getPrototypeOf(module_or_path) === Object.prototype) {
            ({module_or_path} = module_or_path)
        } else {
            console.warn('using deprecated parameters for the initialization function; pass a single object instead')
        }
    }

    if (module_or_path === undefined) {
        module_or_path = new URL('prism_bg.wasm', import.meta.url);
    }
    const imports = __wbg_get_imports();

    if (typeof module_or_path === 'string' || (typeof Request === 'function' && module_or_path instanceof Request) || (typeof URL === 'function' && module_or_path instanceof URL)) {
        module_or_path = fetch(module_or_path);
    }

    const { instance, module } = await __wbg_load(await module_or_path, imports);

    return __wbg_finalize_init(instance, module);
}

export { initSync, __wbg_init as default };
