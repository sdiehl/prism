#include "prism_kont.h"

long prism_main(void);
long prism_add(long x, long y);

const char prism_native_kont_table[] =
    "scheme  @KONT_TEST_SCHEME@\n"
    "bundle  @KONT_TEST_BUNDLE@\n"
    "fn      @KONT_TEST_SYMBOL@  @KONT_TEST_HASH@  @KONT_TEST_CORE_NAME@\n"
    "fn      prism_add  @KONT_TEST_HASH@  add\n";

const char prism_native_kont_state_map[] =
    "state-map 1\n"
    "scheme  @KONT_TEST_SCHEME@\n"
    "bundle  @KONT_TEST_BUNDLE@\n"
    "slot-format prism-native-abi-word-v1\n"
    "state @KONT_TEST_SYMBOL@ @KONT_TEST_HASH@ @KONT_TEST_CORE_NAME@ arity 0 slots abi-word[]\n"
    "state prism_add @KONT_TEST_HASH@ add arity 2 slots abi-word[arg0=%a0:word,arg1=%a1:word]\n";

#ifndef PRISM_KONT_NO_PTR_TABLE
const PrismNativeKontPtr prism_native_kont_ptrs[] = {
    {(const void *)&prism_main, "@KONT_TEST_SYMBOL@", "@KONT_TEST_HASH@", "@KONT_TEST_CORE_NAME@"},
    {(const void *)&prism_add, "prism_add", "@KONT_TEST_HASH@", "add"},
};

const long prism_native_kont_ptrs_len = 2;
#endif

static long fail(long code) {
    return (code << 1) | 1;
}

static int span_eq(const char *p, long n, const char *s) {
    return n == (long)strlen(s) && strncmp(p, s, (size_t)n) == 0;
}

__attribute__((noinline)) static long check_return_pc(void) {
    const char *p = 0;
    long n = -1;
    const char *name = 0;
    long name_n = -1;
    if (!prism_native_kont_lookup_pc(__builtin_return_address(0), &p, &n, &name, &name_n)) {
        return fail(12);
    }
    if (!span_eq(p, n, "@KONT_TEST_HASH@")) return fail(13);
    if (!span_eq(name, name_n, "@KONT_TEST_CORE_NAME@")) return fail(14);
    return 1;
}

__attribute__((noinline)) static long check_capture_frames(void) {
    PrismNativeKontFrame frames[16];
    long n = prism_native_kont_capture_frames(frames, 16);
    for (long i = 0; i < n; i++) {
        if (span_eq(frames[i].def_hash, frames[i].def_hash_len, "@KONT_TEST_HASH@") &&
            span_eq(frames[i].core_name, frames[i].core_name_len, "@KONT_TEST_CORE_NAME@") &&
            span_eq(frames[i].symbol, frames[i].symbol_len, "@KONT_TEST_SYMBOL@") &&
            frames[i].has_pc_offset) {
            return 1;
        }
    }
    return fail(15);
}

__attribute__((noinline)) static long check_manifest(void) {
    char buf[2048];
    long need = prism_native_kont_capture_manifest(buf, (long)sizeof(buf), 16);
    if (need <= 0 || need >= (long)sizeof(buf)) return fail(16);
    if (!strstr(buf, "native-kont 0\nscheme @KONT_TEST_SCHEME@\n")) return fail(17);
    if (!strstr(buf, "bundle @KONT_TEST_BUNDLE@\n")) return fail(18);
#if defined(PRISM_NATIVE_KONT_FRAMES)
    if (!strstr(buf, "frame-mode preserved\n")) return fail(19);
    if (!strstr(buf, "state-values entry-abi-shadow\n")) return fail(21);
#else
    if (!strstr(buf, "frame-mode default\n")) return fail(19);
    if (!strstr(buf, "state-values unsupported\n")) return fail(21);
#endif
    if (!strstr(buf, "frame @KONT_TEST_HASH@ @KONT_TEST_CORE_NAME@ @KONT_TEST_SYMBOL@ +")) {
        return fail(20);
    }
    return 1;
}

static long check_state_map(void) {
    PrismNativeKontState state = {0};
    if (!strstr(prism_native_kont_state_map_bytes(), "state-map 1\n")) return fail(23);
    if (prism_native_kont_state_map_len() <= 0) return fail(24);
    if (!prism_native_kont_state_lookup("@KONT_TEST_SYMBOL@", &state)) {
        return fail(25);
    }
    if (!span_eq(state.def_hash, state.def_hash_len, "@KONT_TEST_HASH@")) return fail(26);
    if (!span_eq(state.core_name, state.core_name_len, "@KONT_TEST_CORE_NAME@")) return fail(27);
    if (state.arity != 0 || !span_eq(state.slots, state.slots_len, "abi-word[]")) return fail(28);
    if (prism_native_kont_state_lookup("missing", &state)) {
        return fail(29);
    }
    if (prism_native_kont_state_lookup(0, &state)) {
        return fail(30);
    }
    if (prism_native_kont_state_lookup("@KONT_TEST_SYMBOL@", 0)) return fail(31);
    return 1;
}

static long check_shadow_api(void) {
    char buf[2048];
    PrismNativeKontFrame frames[8];
    long n = 0;
    prism_native_kont_enter("@KONT_TEST_SYMBOL@", 1);
    prism_native_kont_arg(0, 123);
#if defined(PRISM_NATIVE_KONT_FRAMES)
    if (prism_native_kont_shadow_depth() != 1) return fail(32);
    n = prism_native_kont_capture_frames(frames, 8);
    if (n <= 0 || !frames[0].has_values || frames[0].value_count != 1 || frames[0].values[0] != 123) {
        return fail(33);
    }
    n = prism_native_kont_capture_manifest(buf, (long)sizeof(buf), 8);
    if (n <= 0 || !strstr(buf, "values 1 7b\n")) return fail(34);
#endif
    prism_native_kont_tailcall("@KONT_TEST_SYMBOL@", 0);
#if defined(PRISM_NATIVE_KONT_FRAMES)
    if (prism_native_kont_shadow_depth() != 1) return fail(35);
#endif
    prism_native_kont_leave();
    if (prism_native_kont_shadow_depth() != 0) return fail(36);
    return 1;
}

long prism_add(long x, long y) {
    return x + y;
}

static long check_resume_entry(void) {
    long args[2] = {40, 2};
    long out = -1;
    if (!prism_native_kont_resume_entry("prism_add", args, 2, &out)) return fail(37);
    if (out != 42) return fail(38);
    if (prism_native_kont_resume_entry("prism_add", args, 1, &out)) return fail(39);
    if (prism_native_kont_resume_entry("missing", args, 2, &out)) return fail(40);
    if (prism_native_kont_resume_entry("prism_add", 0, 2, &out)) return fail(41);
    if (prism_native_kont_resume_entry("prism_add", args, 2, 0)) return fail(42);
    return 1;
}

long prism_main(void) {
    const char *p = 0;
    long n = -1;
    const char *name = 0;
    long name_n = -1;
    if (!prism_native_kont_scheme(&p, &n) || !span_eq(p, n, "@KONT_TEST_SCHEME@")) return fail(1);
    if (!prism_native_kont_bundle(&p, &n) || !span_eq(p, n, "@KONT_TEST_BUNDLE@")) return fail(2);
#if defined(PRISM_NATIVE_KONT_FRAMES)
    if (prism_native_kont_frame_mode() != 1) return fail(22);
#else
    if (prism_native_kont_frame_mode() != 0) return fail(22);
#endif
    if (check_state_map() != 1) return check_state_map();
    if (!prism_native_kont_lookup("@KONT_TEST_SYMBOL@", &p, &n, &name, &name_n)) return fail(3);
    if (!span_eq(p, n, "@KONT_TEST_HASH@")) return fail(4);
    if (!span_eq(name, name_n, "@KONT_TEST_CORE_NAME@")) return fail(5);
    if (prism_native_kont_lookup("missing", &p, &n, &name, &name_n)) return fail(6);
    if (prism_native_kont_lookup(0, &p, &n, &name, &name_n)) return fail(7);
#ifndef PRISM_KONT_NO_PTR_TABLE
    if (!prism_native_kont_lookup_ptr((const void *)&prism_main, &p, &n, &name, &name_n)) {
        return fail(8);
    }
    if (!span_eq(p, n, "@KONT_TEST_HASH@")) return fail(9);
    if (!span_eq(name, name_n, "@KONT_TEST_CORE_NAME@")) return fail(10);
    if (prism_native_kont_lookup_ptr((const void *)&span_eq, &p, &n, &name, &name_n)) {
        return fail(11);
    }
#else
    if (prism_native_kont_lookup_ptr((const void *)&prism_main, &p, &n, &name, &name_n)) {
        return fail(43);
    }
#endif
    if (check_return_pc() != 1) return check_return_pc();
    if (check_capture_frames() != 1) return check_capture_frames();
    if (check_manifest() != 1) return check_manifest();
    if (check_shadow_api() != 1) return check_shadow_api();
#ifndef PRISM_KONT_NO_PTR_TABLE
    if (check_resume_entry() != 1) return check_resume_entry();
#else
    {
        long args[2] = {40, 2};
        long out = -1;
        if (prism_native_kont_resume_entry("prism_add", args, 2, &out)) return fail(44);
    }
#endif
    return 1;
}
