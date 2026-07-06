/* Access to the native-symbol-to-definition-hash table embedded by codegen. */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#if defined(__APPLE__) && !defined(_DARWIN_C_SOURCE)
#define _DARWIN_C_SOURCE 1 /* NOLINT(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp) */
#endif
#include "prism_kont.h"

#include <limits.h>

#if defined(__APPLE__) || defined(__linux__)
#include <dlfcn.h>
#include <execinfo.h>
#define PRISM_KONT_HAVE_DLADDR 1
#define PRISM_KONT_HAVE_BACKTRACE 1
#else
#define PRISM_KONT_HAVE_DLADDR 0
#define PRISM_KONT_HAVE_BACKTRACE 0
#endif

#define PRISM_KONT_SCHEME_KEY "scheme"
#define PRISM_KONT_BUNDLE_KEY "bundle"
#define PRISM_KONT_FN_KEY "fn"
#define PRISM_KONT_STATE_KEY "state"
#define PRISM_KONT_ARITY_KEY "arity"
#define PRISM_KONT_SLOTS_KEY "slots"
#define PRISM_KONT_CAPTURE_MAX 4096L
#define PRISM_KONT_SHADOW_MAX 1024L
#define PRISM_KONT_SHADOW_VALUE_MAX 64L
#define PRISM_KONT_RESUME_ARITY_MAX 8L
#define PRISM_KONT_LONG_BUF 32
#define PRISM_KONT_MANIFEST_MAGIC "native-kont 0\n"
#define PRISM_KONT_UNKNOWN_PC_OFFSET "?"
#if defined(PRISM_NATIVE_KONT_FRAMES)
#define PRISM_KONT_MANIFEST_FRAME_MODE "frame-mode preserved\n"
#define PRISM_KONT_MANIFEST_STATE "state-values entry-abi-shadow\n"
#else
#define PRISM_KONT_MANIFEST_FRAME_MODE "frame-mode default\n"
#define PRISM_KONT_MANIFEST_STATE "state-values unsupported\n"
#endif

extern const char prism_native_kont_table[];
extern const char prism_native_kont_state_map[];
PRISM_USED const PrismNativeKontPtr prism_native_kont_ptrs[] PRISM_WEAK_DEFINE = {{0, 0, 0, 0}};
PRISM_USED const long prism_native_kont_ptrs_len PRISM_WEAK_DEFINE = 0;

typedef long (*PrismNativeKontFn0)(void);
typedef long (*PrismNativeKontFn1)(long);
typedef long (*PrismNativeKontFn2)(long, long);
typedef long (*PrismNativeKontFn3)(long, long, long);
typedef long (*PrismNativeKontFn4)(long, long, long, long);
typedef long (*PrismNativeKontFn5)(long, long, long, long, long);
typedef long (*PrismNativeKontFn6)(long, long, long, long, long, long);
typedef long (*PrismNativeKontFn7)(long, long, long, long, long, long, long);
typedef long (*PrismNativeKontFn8)(long, long, long, long, long, long, long, long);

#define PRISM_KONT_FN(type, fn) ((type)(uintptr_t)(fn))

#if defined(PRISM_NATIVE_KONT_FRAMES)
typedef struct {
    const char *symbol;
    long arity;
    long value_count;
    long values[PRISM_KONT_SHADOW_VALUE_MAX];
} PrismNativeKontShadowFrame;

static _Thread_local PrismNativeKontShadowFrame prism_kont_shadow[PRISM_KONT_SHADOW_MAX];
static _Thread_local long prism_kont_shadow_len = 0;

static void shadow_set_frame(PrismNativeKontShadowFrame *frame, const char *symbol, long arity) {
    frame->symbol = symbol;
    frame->arity = arity;
    frame->value_count = arity < PRISM_KONT_SHADOW_VALUE_MAX ? arity : PRISM_KONT_SHADOW_VALUE_MAX;
    for (long i = 0; i < frame->value_count; i++) frame->values[i] = 0;
}
#endif

PRISM_USED const char *prism_native_kont_table_bytes(void) {
    return prism_native_kont_table;
}

PRISM_USED long prism_native_kont_table_len(void) {
    return (long)strlen(prism_native_kont_table);
}

PRISM_USED const char *prism_native_kont_state_map_bytes(void) {
    return prism_native_kont_state_map;
}

PRISM_USED long prism_native_kont_state_map_len(void) {
    return (long)strlen(prism_native_kont_state_map);
}

PRISM_USED long prism_native_kont_frame_mode(void) {
#if defined(PRISM_NATIVE_KONT_FRAMES)
    return 1;
#else
    return 0;
#endif
}

PRISM_USED void prism_native_kont_enter(const char *symbol, long arity) {
#if defined(PRISM_NATIVE_KONT_FRAMES)
    if (!symbol || prism_kont_shadow_len >= PRISM_KONT_SHADOW_MAX) return;
    shadow_set_frame(&prism_kont_shadow[prism_kont_shadow_len], symbol, arity);
    prism_kont_shadow_len++;
#else
    (void)symbol;
    (void)arity;
#endif
}

PRISM_USED void prism_native_kont_arg(long index, long value) {
#if defined(PRISM_NATIVE_KONT_FRAMES)
    if (prism_kont_shadow_len <= 0 || index < 0 || index >= PRISM_KONT_SHADOW_VALUE_MAX) return;
    PrismNativeKontShadowFrame *frame = &prism_kont_shadow[prism_kont_shadow_len - 1];
    if (index >= frame->value_count) return;
    frame->values[index] = value;
#else
    (void)index;
    (void)value;
#endif
}

PRISM_USED void prism_native_kont_tailcall(const char *symbol, long arity) {
#if defined(PRISM_NATIVE_KONT_FRAMES)
    if (!symbol) return;
    if (prism_kont_shadow_len <= 0) {
        prism_native_kont_enter(symbol, arity);
        return;
    }
    shadow_set_frame(&prism_kont_shadow[prism_kont_shadow_len - 1], symbol, arity);
#else
    (void)symbol;
    (void)arity;
#endif
}

PRISM_USED void prism_native_kont_leave(void) {
#if defined(PRISM_NATIVE_KONT_FRAMES)
    if (prism_kont_shadow_len > 0) prism_kont_shadow_len--;
#endif
}

PRISM_USED long prism_native_kont_shadow_depth(void) {
#if defined(PRISM_NATIVE_KONT_FRAMES)
    return prism_kont_shadow_len;
#else
    return 0;
#endif
}

static const char *line_end(const char *p) {
    while (*p && *p != '\n') p++;
    return p;
}

static const char *skip_ws(const char *p, const char *end) {
    while (p < end && isspace((unsigned char)*p)) p++;
    return p;
}

static const char *field_end(const char *p, const char *end) {
    while (p < end && !isspace((unsigned char)*p)) p++;
    return p;
}

static const char *trim_ws_end(const char *lo, const char *hi) {
    while (hi > lo && isspace((unsigned char)hi[-1])) hi--;
    return hi;
}

static long span_len(const char *lo, const char *hi) {
    return (long)(hi - lo);
}

static int field_eq(const char *lo, const char *hi, const char *s) {
    size_t n = (size_t)(hi - lo);
    return strlen(s) == n && strncmp(lo, s, n) == 0;
}

static void set_span(const char **out, long *out_len, const char *lo, const char *hi) {
    if (out) *out = lo;
    if (out_len) *out_len = span_len(lo, hi);
}

static void set_cstr(const char **out, long *out_len, const char *s) {
    if (out) *out = s;
    if (out_len) *out_len = (long)strlen(s);
}

static long parse_nonneg_long(const char *lo, const char *hi, long *out) {
    if (lo >= hi) return 0;
    long n = 0;
    for (const char *p = lo; p < hi; p++) {
        if (*p < '0' || *p > '9') return 0;
        long digit = *p - '0';
        if (n > (LONG_MAX - digit) / 10) return 0;
        n = n * 10 + digit;
    }
    if (out) *out = n;
    return 1;
}

PRISM_USED long prism_native_kont_state_lookup(const char *symbol, PrismNativeKontState *out) {
    if (!symbol || !out) return 0;
    const char *p = prism_native_kont_state_map;
    while (*p) {
        const char *end = line_end(p);
        const char *k0 = skip_ws(p, end);
        const char *k1 = field_end(k0, end);
        if (field_eq(k0, k1, PRISM_KONT_STATE_KEY)) {
            const char *s0 = skip_ws(k1, end);
            const char *s1 = field_end(s0, end);
            const char *h0 = skip_ws(s1, end);
            const char *h1 = field_end(h0, end);
            const char *n0 = skip_ws(h1, end);
            const char *n1 = field_end(n0, end);
            const char *a0 = skip_ws(n1, end);
            const char *a1 = field_end(a0, end);
            const char *av0 = skip_ws(a1, end);
            const char *av1 = field_end(av0, end);
            const char *sl0 = skip_ws(av1, end);
            const char *sl1 = field_end(sl0, end);
            const char *sv0 = skip_ws(sl1, end);
            const char *sv1 = trim_ws_end(sv0, end);
            long parsed_arity = 0;
            if (field_eq(s0, s1, symbol) &&
                field_eq(a0, a1, PRISM_KONT_ARITY_KEY) &&
                field_eq(sl0, sl1, PRISM_KONT_SLOTS_KEY) &&
                parse_nonneg_long(av0, av1, &parsed_arity)) {
                out->def_hash = h0;
                out->def_hash_len = span_len(h0, h1);
                out->core_name = n0;
                out->core_name_len = span_len(n0, n1);
                out->arity = parsed_arity;
                out->slots = sv0;
                out->slots_len = span_len(sv0, sv1);
                return 1;
            }
        }
        p = *end == '\n' ? end + 1 : end;
    }
    return 0;
}

static void append_span(char *out, long out_cap, long *pos, const char *src, long len) {
    if (len <= 0) return;
    if (out && out_cap > 0 && *pos < out_cap - 1) {
        long room = out_cap - 1 - *pos;
        long take = len < room ? len : room;
        memcpy(out + *pos, src, (size_t)take);
    }
    *pos += len;
}

static void append_cstr(char *out, long out_cap, long *pos, const char *src) {
    append_span(out, out_cap, pos, src, (long)strlen(src));
}

static void append_long(char *out, long out_cap, long *pos, long n) {
    char buf[PRISM_KONT_LONG_BUF];
    int len = snprintf(buf, sizeof(buf), "%ld", n);
    if (len > 0) append_span(out, out_cap, pos, buf, (long)len);
}

static void append_ulong_hex(char *out, long out_cap, long *pos, unsigned long n) {
    char buf[PRISM_KONT_LONG_BUF];
    int len = snprintf(buf, sizeof(buf), "%lx", n);
    if (len > 0) append_span(out, out_cap, pos, buf, (long)len);
}

static long finish_manifest(char *out, long out_cap, long pos) {
    if (out && out_cap > 0) {
        long at = pos < out_cap ? pos : out_cap - 1;
        out[at] = 0;
    }
    return pos;
}

static long find_header(const char *key, const char **value, long *value_len) {
    const char *p = prism_native_kont_table;
    while (*p) {
        const char *end = line_end(p);
        const char *k0 = skip_ws(p, end);
        const char *k1 = field_end(k0, end);
        if (field_eq(k0, k1, key)) {
            const char *v0 = skip_ws(k1, end);
            const char *v1 = field_end(v0, end);
            set_span(value, value_len, v0, v1);
            return 1;
        }
        p = *end == '\n' ? end + 1 : end;
    }
    return 0;
}

static long lookup_symbol(const char *symbol,
                          const char **def_hash,
                          long *def_hash_len,
                          const char **core_name,
                          long *core_name_len,
                          const char **symbol_out,
                          long *symbol_len) {
    if (!symbol) return 0;
    const char *p = prism_native_kont_table;
    while (*p) {
        const char *end = line_end(p);
        const char *k0 = skip_ws(p, end);
        const char *k1 = field_end(k0, end);
        if (field_eq(k0, k1, PRISM_KONT_FN_KEY)) {
            const char *s0 = skip_ws(k1, end);
            const char *s1 = field_end(s0, end);
            const char *h0 = skip_ws(s1, end);
            const char *h1 = field_end(h0, end);
            const char *n0 = skip_ws(h1, end);
            const char *n1 = field_end(n0, end);
            if (field_eq(s0, s1, symbol)) {
                set_span(def_hash, def_hash_len, h0, h1);
                set_span(core_name, core_name_len, n0, n1);
                set_span(symbol_out, symbol_len, s0, s1);
                return 1;
            }
        }
        p = *end == '\n' ? end + 1 : end;
    }
    return 0;
}

static long lookup_ptr_detail(const void *fn,
                              const char **def_hash,
                              long *def_hash_len,
                              const char **core_name,
                              long *core_name_len,
                              const char **symbol,
                              long *symbol_len) {
    if (!fn || prism_native_kont_ptrs_len <= 0) return 0;
    for (long i = 0; i < prism_native_kont_ptrs_len; i++) {
        if (prism_native_kont_ptrs[i].fn == fn) {
            set_cstr(def_hash, def_hash_len, prism_native_kont_ptrs[i].def_hash);
            set_cstr(core_name, core_name_len, prism_native_kont_ptrs[i].core_name);
            set_cstr(symbol, symbol_len, prism_native_kont_ptrs[i].symbol);
            return 1;
        }
    }
    return 0;
}

static const PrismNativeKontPtr *lookup_symbol_ptr(const char *symbol) {
    if (!symbol || prism_native_kont_ptrs_len <= 0) return 0;
    for (long i = 0; i < prism_native_kont_ptrs_len; i++) {
        if (strcmp(prism_native_kont_ptrs[i].symbol, symbol) == 0) {
            return &prism_native_kont_ptrs[i];
        }
    }
    return 0;
}

PRISM_USED long prism_native_kont_resume_entry(const char *symbol,
                                               const long *values,
                                               long value_count,
                                               long *out) {
    if (!symbol || !out || value_count < 0 || value_count > PRISM_KONT_RESUME_ARITY_MAX) return 0;
    if (value_count > 0 && !values) return 0;
    const PrismNativeKontPtr *entry = lookup_symbol_ptr(symbol);
    if (!entry || !entry->fn) return 0;
    PrismNativeKontState state;
    if (!prism_native_kont_state_lookup(symbol, &state) || state.arity != value_count) return 0;
    switch (value_count) {
        case 0:
            *out = PRISM_KONT_FN(PrismNativeKontFn0, entry->fn)();
            return 1;
        case 1:
            *out = PRISM_KONT_FN(PrismNativeKontFn1, entry->fn)(values[0]);
            return 1;
        case 2:
            *out = PRISM_KONT_FN(PrismNativeKontFn2, entry->fn)(values[0], values[1]);
            return 1;
        case 3:
            *out = PRISM_KONT_FN(PrismNativeKontFn3, entry->fn)(values[0], values[1], values[2]);
            return 1;
        case 4:
            *out = PRISM_KONT_FN(PrismNativeKontFn4, entry->fn)(
                values[0], values[1], values[2], values[3]);
            return 1;
        case 5:
            *out = PRISM_KONT_FN(PrismNativeKontFn5, entry->fn)(
                values[0], values[1], values[2], values[3], values[4]);
            return 1;
        case 6:
            *out = PRISM_KONT_FN(PrismNativeKontFn6, entry->fn)(
                values[0], values[1], values[2], values[3], values[4], values[5]);
            return 1;
        case 7:
            *out = PRISM_KONT_FN(PrismNativeKontFn7, entry->fn)(
                values[0], values[1], values[2], values[3], values[4], values[5], values[6]);
            return 1;
        case 8:
            *out = PRISM_KONT_FN(PrismNativeKontFn8, entry->fn)(
                values[0], values[1], values[2], values[3], values[4], values[5], values[6], values[7]);
            return 1;
        default:
            return 0;
    }
}

PRISM_USED long prism_native_kont_lookup_ptr(const void *fn,
                                             const char **def_hash,
                                             long *def_hash_len,
                                             const char **core_name,
                                             long *core_name_len) {
    return lookup_ptr_detail(fn, def_hash, def_hash_len, core_name, core_name_len, 0, 0);
}

static void set_pc_offset(const void *pc,
                          const void *base,
                          unsigned long *pc_offset,
                          long *has_pc_offset) {
    if (pc_offset) *pc_offset = 0;
    if (has_pc_offset) *has_pc_offset = 0;
    if (!pc || !base) return;
    uintptr_t here = (uintptr_t)pc;
    uintptr_t start = (uintptr_t)base;
    if (here < start) return;
    if (pc_offset) *pc_offset = (unsigned long)(here - start);
    if (has_pc_offset) *has_pc_offset = 1;
}

static long lookup_pc_detail(const void *pc,
                             const char **def_hash,
                             long *def_hash_len,
                             const char **core_name,
                             long *core_name_len,
                             const char **symbol,
                             long *symbol_len,
                             unsigned long *pc_offset,
                             long *has_pc_offset) {
    if (!pc) return 0;
#if PRISM_KONT_HAVE_DLADDR
    Dl_info info;
    if (dladdr(pc, &info) && info.dli_sname) {
        if (lookup_symbol(
                info.dli_sname, def_hash, def_hash_len, core_name, core_name_len, symbol, symbol_len)) {
            set_pc_offset(pc, info.dli_saddr, pc_offset, has_pc_offset);
            return 1;
        }
        if (info.dli_sname[0] == '_' &&
            lookup_symbol(
                info.dli_sname + 1, def_hash, def_hash_len, core_name, core_name_len, symbol, symbol_len)) {
            set_pc_offset(pc, info.dli_saddr, pc_offset, has_pc_offset);
            return 1;
        }
    }
#endif
    if (lookup_ptr_detail(pc, def_hash, def_hash_len, core_name, core_name_len, symbol, symbol_len)) {
        if (pc_offset) *pc_offset = 0;
        if (has_pc_offset) *has_pc_offset = 1;
        return 1;
    }
    return 0;
}

static long capture_shadow_frames(PrismNativeKontFrame *out, long cap) {
#if defined(PRISM_NATIVE_KONT_FRAMES)
    if (!out || cap <= 0) return 0;
    long written = 0;
    for (long i = prism_kont_shadow_len - 1; i >= 0 && written < cap; i--) {
        PrismNativeKontShadowFrame *shadow = &prism_kont_shadow[i];
        const char *def_hash = 0;
        const char *core_name = 0;
        long def_hash_len = 0;
        long core_name_len = 0;
        const char *symbol = 0;
        long symbol_len = 0;
        if (!lookup_symbol(
                shadow->symbol, &def_hash, &def_hash_len, &core_name, &core_name_len, &symbol, &symbol_len)) {
            continue;
        }
        out[written].pc = 0;
        out[written].symbol = symbol;
        out[written].symbol_len = symbol_len;
        out[written].def_hash = def_hash;
        out[written].def_hash_len = def_hash_len;
        out[written].core_name = core_name;
        out[written].core_name_len = core_name_len;
        out[written].pc_offset = 0;
        out[written].has_pc_offset = 0;
        out[written].values = shadow->values;
        out[written].value_count = shadow->value_count;
        out[written].has_values = 1;
        written++;
    }
    return written;
#else
    (void)out;
    (void)cap;
    return 0;
#endif
}

PRISM_USED long prism_native_kont_lookup_pc(const void *pc,
                                            const char **def_hash,
                                            long *def_hash_len,
                                            const char **core_name,
                                            long *core_name_len) {
    return lookup_pc_detail(pc, def_hash, def_hash_len, core_name, core_name_len, 0, 0, 0, 0);
}

PRISM_USED long prism_native_kont_capture_frames(PrismNativeKontFrame *out, long cap) {
    if (!out || cap <= 0) return 0;
    long written = capture_shadow_frames(out, cap);
    if (written >= cap) return written;
#if PRISM_KONT_HAVE_BACKTRACE
    long remaining = cap - written;
    long limit = remaining > PRISM_KONT_CAPTURE_MAX ? PRISM_KONT_CAPTURE_MAX : remaining;
    void **pcs = (void **)malloc((size_t)limit * sizeof(void *));
    if (!pcs) return written;
    int n = backtrace(pcs, (int)limit);
    for (int i = 0; i < n && written < cap; i++) {
        const char *def_hash = 0;
        const char *core_name = 0;
        long def_hash_len = 0;
        long core_name_len = 0;
        const char *symbol = 0;
        long symbol_len = 0;
        unsigned long pc_offset = 0;
        long has_pc_offset = 0;
        if (lookup_pc_detail(pcs[i],
                             &def_hash,
                             &def_hash_len,
                             &core_name,
                             &core_name_len,
                             &symbol,
                             &symbol_len,
                             &pc_offset,
                             &has_pc_offset)) {
            out[written].pc = pcs[i];
            out[written].symbol = symbol;
            out[written].symbol_len = symbol_len;
            out[written].def_hash = def_hash;
            out[written].def_hash_len = def_hash_len;
            out[written].core_name = core_name;
            out[written].core_name_len = core_name_len;
            out[written].pc_offset = pc_offset;
            out[written].has_pc_offset = has_pc_offset;
            out[written].values = 0;
            out[written].value_count = 0;
            out[written].has_values = 0;
            written++;
        }
    }
    free((void *)pcs);
    return written;
#else
    (void)cap;
    return written;
#endif
}

PRISM_USED long prism_native_kont_capture_manifest(char *out, long out_cap, long frame_cap) {
    if (out_cap < 0) return -1;
    long cap = frame_cap > PRISM_KONT_CAPTURE_MAX ? PRISM_KONT_CAPTURE_MAX : frame_cap;
    if (cap < 0) cap = 0;
    PrismNativeKontFrame *frames = 0;
    if (cap > 0) {
        frames = malloc((size_t)cap * sizeof(PrismNativeKontFrame));
        if (!frames) return -1;
    }
    long n = cap > 0 ? prism_native_kont_capture_frames(frames, cap) : 0;
    const char *scheme = 0;
    const char *bundle = 0;
    long scheme_len = 0;
    long bundle_len = 0;
    if (!prism_native_kont_scheme(&scheme, &scheme_len)) {
        scheme = "";
        scheme_len = 0;
    }
    if (!prism_native_kont_bundle(&bundle, &bundle_len)) {
        bundle = "";
        bundle_len = 0;
    }

    long pos = 0;
    append_cstr(out, out_cap, &pos, PRISM_KONT_MANIFEST_MAGIC);
    append_cstr(out, out_cap, &pos, "scheme ");
    append_span(out, out_cap, &pos, scheme, scheme_len);
    append_cstr(out, out_cap, &pos, "\n");
    append_cstr(out, out_cap, &pos, "bundle ");
    append_span(out, out_cap, &pos, bundle, bundle_len);
    append_cstr(out, out_cap, &pos, "\n");
    append_cstr(out, out_cap, &pos, PRISM_KONT_MANIFEST_FRAME_MODE);
    append_cstr(out, out_cap, &pos, "frames ");
    append_long(out, out_cap, &pos, n);
    append_cstr(out, out_cap, &pos, "\n");
    for (long i = 0; i < n; i++) {
        append_cstr(out, out_cap, &pos, "frame ");
        append_span(out, out_cap, &pos, frames[i].def_hash, frames[i].def_hash_len);
        append_cstr(out, out_cap, &pos, " ");
        append_span(out, out_cap, &pos, frames[i].core_name, frames[i].core_name_len);
        append_cstr(out, out_cap, &pos, " ");
        append_span(out, out_cap, &pos, frames[i].symbol, frames[i].symbol_len);
        append_cstr(out, out_cap, &pos, " +");
        if (frames[i].has_pc_offset) {
            append_ulong_hex(out, out_cap, &pos, frames[i].pc_offset);
        } else {
            append_cstr(out, out_cap, &pos, PRISM_KONT_UNKNOWN_PC_OFFSET);
        }
        append_cstr(out, out_cap, &pos, "\n");
        if (frames[i].has_values) {
            append_cstr(out, out_cap, &pos, "values ");
            append_long(out, out_cap, &pos, frames[i].value_count);
            for (long j = 0; j < frames[i].value_count; j++) {
                append_cstr(out, out_cap, &pos, " ");
                append_ulong_hex(out, out_cap, &pos, (unsigned long)frames[i].values[j]);
            }
            append_cstr(out, out_cap, &pos, "\n");
        }
    }
    append_cstr(out, out_cap, &pos, PRISM_KONT_MANIFEST_STATE);
    free(frames);
    return finish_manifest(out, out_cap, pos);
}

PRISM_USED long prism_native_kont_scheme(const char **scheme, long *scheme_len) {
    return find_header(PRISM_KONT_SCHEME_KEY, scheme, scheme_len);
}

PRISM_USED long prism_native_kont_bundle(const char **bundle, long *bundle_len) {
    return find_header(PRISM_KONT_BUNDLE_KEY, bundle, bundle_len);
}

PRISM_USED long prism_native_kont_lookup(const char *symbol,
                                         const char **def_hash,
                                         long *def_hash_len,
                                         const char **core_name,
                                         long *core_name_len) {
    return lookup_symbol(symbol, def_hash, def_hash_len, core_name, core_name_len, 0, 0);
}
