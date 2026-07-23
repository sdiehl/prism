/* IO, environment, process, and the fault traps; main() lives here. */
#include "prism_io.h"
#include "prism_array.h"
#include "prism_buffer.h"
#include "prism_int.h"
#include "prism_mem.h"
#include "prism_string.h"
#include <fcntl.h>
#include <time.h>
#include <unistd.h>

_Noreturn void prism_div_zero(void) {
    fprintf(stderr, "fatal: division by zero\n");
    exit(1);
}

/* Reached only on an arity bug: a closure dispatched to an apply_n with no
 * matching lambda tag. A diagnostic abort beats raw `unreachable` UB. */
_Noreturn void prism_apply_error(void) {
    fprintf(stderr, "fatal: closure applied at wrong arity\n");
    exit(1);
}

/* Reached only if a `case` scrutinee carries a tag no arm covers: exhaustiveness
 * checking proves this dead for well-typed code, so it fires only on a compiler
 * bug (a coverage hole or a miscompile). A diagnostic abort beats raw
 * `unreachable` UB, and matches the interpreter's clean "no matching pattern"
 * error instead of forking native semantics into undefined behavior. */
_Noreturn void prism_match_error(void) {
    fprintf(stderr, "fatal: no matching pattern in case\n");
    exit(1);
}

_Noreturn void prism_fatal(long s) {
    fprintf(stderr, "fatal: %s\n", prism_str_data(s));
    exit(1);
}

/* `error(n)` raises the Exn fault: the interpreter reports it and terminates
 * with status 1, so native must too, rather than treating the payload as a
 * process exit code (that is `exit`, a separate builtin). exit() flushes stdout,
 * so any output printed before the fault is preserved on both backends. */
_Noreturn void prism_error_int(long n) {
    fprintf(stderr, "error(%ld)\n", n);
    exit(1);
}

long prism_prim_read_int(void) {
    /* Line-oriented to match the interpreter oracle: consume a whole line and
     * parse its trimmed contents, so a following read_line sees the next line
     * rather than the leftover newline a bare scanf("%ld") would strand. */
    char *buf = 0;
    size_t cap = 0;
    long len = getline(&buf, &cap, stdin);
    if (len < 0) {
        free(buf);
        fprintf(stderr, "fatal: read_int: no integer on stdin\n");
        exit(1);
    }
    errno = 0;
    char *end = 0;
    long n = strtol(buf, &end, 10);
    int ok = errno == 0 && end != buf;
    if (ok) {
        /* The interpreter parses the whole trimmed line (`line.trim().parse`),
         * so trailing content ("123abc") is an error, not a 123-prefix. Only
         * trailing ASCII whitespace, which `str::trim` also drops, may follow
         * the digits; strtol has already skipped the leading whitespace. */
        while (isspace((unsigned char)*end)) end++;
        ok = *end == '\0';
    }
    free(buf);
    if (!ok) {
        fprintf(stderr, "fatal: read_int: no integer on stdin\n");
        exit(1);
    }
    /* Return an encoded Int, not the raw machine word: a value in
     * (2^62, 2^63) fits an i64 but not the 63-bit tagged immediate, so
     * codegen retagging it would silently shift out bit 62 while the
     * interpreter keeps the full value. Encoding here keeps the two in
     * lockstep for the whole i64 range. */
    return prism_int_of_long(n);
}

long prism_prim_read_line(void) {
    char *buf = 0;
    size_t cap = 0;
    long n = getline(&buf, &cap, stdin);
    if (n < 0) {
        free(buf);
        return prism_str_lit("", 0);
    }
    while (n > 0 && (buf[n - 1] == '\n' || buf[n - 1] == '\r')) buf[--n] = 0;
    long cell = prism_str_lit(buf, n);
    free(buf);
    return cell;
}

/* Generic print for values whose type elaboration could not pin down (a var
 * read is an effect op whose row-polymorphic signature hides the payload
 * type). Cells are self-describing via their tag, so dispatch at runtime to
 * keep parity with the interpreter's dynamic show: a tagged immediate is an
 * Int, the zero word is Unit, and the two payload tags render themselves.
 *
 * A constructor, tuple, or list cell has no runtime type or field-name table to
 * show faithfully, so it cannot legitimately reach here; the elaborator routes
 * every statically-known structural type through the synthesized `show`. The
 * final `else` is an always-on guard (one tag compare, free on this IO-bound
 * path): rather than hand a foreign cell to prism_big_show, which would read its
 * header word as a limb count and its fields as magnitude, it traps. */
void prism_print_int(long w) {
    if (w & 1) {
        printf("%ld", w >> 1);
    } else if (!w) {
        printf("()"); /* Unit is the zero word; match the interpreter's `()`. */
    } else if (((long *)w)[PRISM_TAG_W] == PRISM_STR_TAG) {
        printf("%s", prism_str_data(w));
    } else if (((long *)w)[PRISM_TAG_W] == PRISM_BIG_TAG) {
        long s = prism_big_show(w);
        printf("%s", prism_str_data(s));
        prism_rc_dec(s);
    } else {
        fprintf(stderr,
                "fatal: print: non-printable value with heap tag %#lx reached "
                "the raw integer printer\n",
                (unsigned long)((long *)w)[PRISM_TAG_W]);
        abort();
    }
}

void prism_print_nl(void) {
    putchar('\n');
}

/* SplitMix64. A single global stream, seeded to the same default constant the
 * interpreter uses so unseeded `rand` is reproducible across backends. */
static unsigned long prism_rng = 0x9E3779B97F4A7C15UL;

void prism_srand(long seed) {
    prism_rng = (unsigned long)seed;
}

long prism_prim_rand(void) {
    prism_rng += 0x9E3779B97F4A7C15UL;
    unsigned long z = prism_rng;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9UL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBUL;
    z ^= z >> 31;
    return (long)(z >> 2);
}

/* Real OS entropy: eight bytes from /dev/urandom, backing the non-replayable
 * `Entropy` capability. Unlike the seeded `prism_prim_rand` stream this is not
 * reproducible from any seed; its reads are recorded so a replay serves the
 * captured value. Best-effort: an unavailable source yields zero rather than
 * aborting. The low bit is dropped so the result is a non-negative 63-bit Int,
 * exactly as `prism_prim_rand` keeps its value non-negative. */
long prism_prim_entropy(void) {
    unsigned long v = 0;
    int fd = open("/dev/urandom", O_RDONLY);
    if (fd >= 0) {
        size_t got = 0;
        while (got < sizeof v) {
            ssize_t n = read(fd, (unsigned char *)&v + got, sizeof v - got);
            if (n <= 0) { break; }
            got += (size_t)n;
        }
        (void)close(fd);
    }
    return (long)(v >> 1);
}

/* Wall-clock and monotonic reads, in nanoseconds, backing the `Clock` capability
 * ops. Both are recorded trace entries (the interpreter observes each), so a
 * time-reading program replays byte-identically. The monotonic origin is a fixed
 * but unspecified point, so only differences of monotonic reads are meaningful;
 * the wall reading is nanoseconds since the Unix epoch (UTC). The scale to
 * nanoseconds is checked: a reading past the 63-bit horizon (year 2262 for the
 * wall clock) aborts rather than committing signed-overflow UB. */
#define PRISM_NS_PER_SEC 1000000000L

long prism_prim_wall_now(void) {
    struct timespec ts = {0, 0};
    (void)clock_gettime(CLOCK_REALTIME, &ts);
    return prism_ckd_ladd(prism_ckd_lmul((long)ts.tv_sec, PRISM_NS_PER_SEC), (long)ts.tv_nsec);
}

long prism_prim_mono_now(void) {
    struct timespec ts = {0, 0};
    (void)clock_gettime(CLOCK_MONOTONIC, &ts);
    return prism_ckd_ladd(prism_ckd_lmul((long)ts.tv_sec, PRISM_NS_PER_SEC), (long)ts.tv_nsec);
}

/* OS surface. getenv/arg return a fresh counted string cell (empty when
 * unset, never NULL), writes consume their argument cells via the caller's
 * rc_dec and return unit. read_file fails loudly on any error and caps the
 * slurp so a pathological file cannot exhaust memory. */
#define PRISM_READ_CAP (1L << 30)

static _Noreturn void prism_read_fatal(const char *why, const char *path) {
    fprintf(stderr, "prism: read_file: %s: %s\n", why, path);
    exit(1);
}

static int prism_argc = 0;
static char **prism_argv = 0;

long prism_prim_args_count(void) {
    return prism_argc;
}

long prism_prim_arg(long i) {
    if (i < 0 || i >= prism_argc) return prism_str_lit("", 0);
    const char *a = prism_argv[i];
    return prism_str_lit(a, (long)strlen(a));
}

long prism_prim_getenv(long name) {
    const char *v = getenv(prism_str_data(name));
    if (!v) return prism_str_lit("", 0);
    return prism_str_lit(v, (long)strlen(v));
}

long prism_probe_enabled(long name) {
    const char *filter = getenv("PRISM_PROBES");
    if (!filter) return 0;
    const char *needle = prism_str_data(name);
    long needle_len = prism_str_len_bytes(name);
    const char *p = filter;
    while (*p) {
        while (*p == ' ' || *p == '\t' || *p == ',') p++;
        const char *start = p;
        while (*p && *p != ',') p++;
        const char *end = p;
        while (end > start && (end[-1] == ' ' || end[-1] == '\t')) end--;
        long len = (long)(end - start);
        if ((len == 1 && start[0] == '*') ||
            (len == needle_len && memcmp(start, needle, (size_t)len) == 0)) {
            return 1;
        }
    }
    return 0;
}

/* Slurp a whole file into a fresh String cell verbatim, with no interpretation
 * of its bytes. Faults loudly on any IO error and caps the size. Shared by
 * read_file (which then enforces UTF-8) and read_bytes (which reinterprets the
 * cell as a byte buffer), so neither path duplicates the open/size/cap/read. */
static long prism_slurp_string(long path) {
    const char *name = prism_str_data(path);
    FILE *f = fopen(name, "rb");
    if (!f) prism_read_fatal("cannot open", name);
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (n < 0) prism_read_fatal("cannot size", name);
    if (n > PRISM_READ_CAP) prism_read_fatal("exceeds 1GB cap", name);
    long *p = prism_str_alloc(n);
    char *o = (char *)(p + PRISM_HDR_WORDS);
    long got = (long)fread(o, 1, (size_t)n, f);
    o[got] = 0;
    p[PRISM_ARITY_W] = got;
    fclose(f);
    return (long)p;
}

long prism_prim_read_file(long path) {
    long s = prism_slurp_string(path);
    /* Prism's String is UTF-8 (a Rust `String`). The interpreter's read_file
     * decodes with `fs::read_to_string`, which rejects non-UTF-8 input; native
     * must reject it too, or the two tiers disagree on the same file. read_bytes
     * is the byte-faithful path for arbitrary content. */
    if (!prism_utf8_valid((const unsigned char *)prism_str_data(s), prism_str_len_bytes(s))) {
        prism_rc_dec(s);
        prism_read_fatal("stream did not contain valid UTF-8", prism_str_data(path));
    }
    return s;
}

/* Result(Unit, String): Ok(()) with the immediate Unit field, or Err(msg). */
static long prism_file_ok(void) {
    long unit = 0;
    return prism_ctor(0, 1, &unit);
}

static long prism_file_err(const char *msg) {
    long s = prism_str_lit(msg, (long)strlen(msg));
    return prism_ctor(1, 1, &s);
}

static long prism_file_write(long path, long contents, const char *mode) {
    FILE *f = fopen(prism_str_data(path), mode);
    if (!f) return prism_file_err("cannot open file for writing");
    size_t want = (size_t)prism_str_len_bytes(contents);
    size_t got = fwrite(prism_str_data(contents), 1, want, f);
    fclose(f);
    if (got < want) return prism_file_err("short write");
    return prism_file_ok();
}

long prism_write_file(long path, long contents) {
    return prism_file_write(path, contents, "wb");
}

/* Read a file's raw bytes into a byte buffer with no UTF-8 interpretation. The
 * slurp reuses prism_slurp_string (same open, cap, and error handling) rather
 * than read_file, so it skips the UTF-8 gate: its String cell holds the bytes
 * verbatim, and prism_buf_of_string copies them byte-for-byte, so an embedded
 * NUL or a non-UTF-8 byte survives intact. The transient string is dropped once
 * copied. */
long prism_prim_read_bytes(long path) {
    long s = prism_slurp_string(path);
    long b = prism_buf_of_string(s);
    prism_rc_dec(s);
    return b;
}

/* Write a buffer's raw bytes verbatim. Mirrors prism_write_file but copies from
 * the buffer payload rather than a string, so no byte is reinterpreted. Borrows
 * both arguments; returns Result(Unit, String). */
long prism_prim_write_bytes(long path, long buf) {
    FILE *f = fopen(prism_str_data(path), "wb");
    if (!f) return prism_file_err("cannot open file for writing");
    size_t want = (size_t)prism_buf_len(buf);
    size_t got = fwrite(prism_buf_ptr(buf), 1, want, f);
    fclose(f);
    if (got < want) return prism_file_err("short write");
    return prism_file_ok();
}

long prism_append_file(long path, long contents) {
    return prism_file_write(path, contents, "ab");
}

long prism_prim_file_exists(long path) {
    FILE *f = fopen(prism_str_data(path), "rb");
    if (f) fclose(f);
    return f != 0;
}

long prism_remove_file(long path) {
    remove(prism_str_data(path));
    return 0;
}

/* Run a shell command, returning its exit code (-1 on spawn failure or signal
   death). The result is a raw int the call site retags as an Int. */
long prism_system(long cmd) {
    int rc = system(prism_str_data(cmd));
    if (rc == -1 || !WIFEXITED(rc)) return -1;
    return WEXITSTATUS(rc);
}

/* Write a string to stderr (no trailing newline). Returns unit. */
long prism_eprint(long s) {
    fputs(prism_str_data(s), stderr);
    return 0;
}

long prism_exit(long code) {
    exit((int)code);
}

/* The user's entry point, emitted by codegen. It carries the `prismfn_` prefix
 * of every Core function, not this runtime's `prism_`: the two namespaces are
 * kept disjoint at index 5 precisely so a user function can be named after a
 * runtime intrinsic without colliding with it. This declaration is the one
 * place the runtime reaches across that boundary. */
extern long prismfn_main(void);

int main(int argc, char **argv) {
    /* Surface `args()` is the program argument list, not C's process argv:
     * argv[0] is the launcher path and is deliberately excluded.  The
     * interpreter already receives only arguments after `prism run ... --`, so
     * doing the normalization here keeps native and interpreted CLIs equal. */
    prism_argc = argc > 0 ? argc - 1 : 0;
    prism_argv = argc > 0 ? argv + 1 : argv;
    long r = prismfn_main();
    /* Only an explicit `exit(n)` sets the process code (it calls libc exit
     * directly, before returning here); a value-returning main exits 0. The
     * interpreter derives the exit code from `exit(n)` alone and ignores main's
     * return word, so mirroring that keeps the two tiers' exit codes identical.
     * A heap cell returned by main is still freed so the leak audit stays exact. */
    if (!(r & 1) && r) prism_rc_dec(r);
    return 0;
}
