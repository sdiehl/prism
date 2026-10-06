/* Child processes: the Unix boundary under the `Proc` capability.
 *
 * One call runs a graph of stages, a command being the graph of one. Each
 * stage's program is resolved on the parent's PATH and spawned with its
 * standard input the stage before it's output; the first stage is fed the
 * request's input, the last stage's output and every stage's error stream are
 * drained under their limits and the one deadline, and every stage is reaped.
 * A stage that cannot start answers SpawnFailed and the stage after it reads
 * an empty input. When the host stops the run, every stage that started
 * answers the reason, so the answer does not depend on which had already
 * exited. The interpreter's half is src/eval/proc.rs; every choice a host
 * could make differently is made explicitly in both, so the same request gets
 * the same response from either tier. A run stopped for its output or its
 * deadline answers with every stream empty, since what was written by then
 * depends on scheduling.
 *
 * The classification codes are the wire to `proc_error` in Proc.pr:
 *
 *   0 other   1 not found   2 denied   3 invalid   4 limit
 */
/* posix_spawn_file_actions_addchdir_np is a platform extension on both. */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE                                                                                \
    1 /* NOLINT(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp): the standard glibc      \
         feature-test macro */
#endif
#if defined(__APPLE__) && !defined(_DARWIN_C_SOURCE)
#define _DARWIN_C_SOURCE 1 /* NOLINT(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp) */
#endif
#include "prism_proc.h"
#include "prism_buffer.h"
#include "prism_mem.h"
#include "prism_string.h"

#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#ifdef __linux__
#include <pthread.h>
#endif
#include <poll.h>
#include <signal.h>
#include <spawn.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#define PRISM_PROC_OTHER 0
#define PRISM_PROC_NOT_FOUND 1
#define PRISM_PROC_DENIED 2
#define PRISM_PROC_INVALID 3
#define PRISM_PROC_LIMIT 4

#define PRISM_PROC_VERSION 1u
#define PRISM_PROC_MAX_CAPTURE (256ul * 1024ul * 1024ul)
#define PRISM_PROC_CHUNK 65536

/* The response tags, in `proc_status` order. */
#define PRISM_PROC_EXITED 0
#define PRISM_PROC_SIGNALED 1
#define PRISM_PROC_SPAWN_FAILED 2
#define PRISM_PROC_OUTPUT_LIMIT 3
#define PRISM_PROC_DEADLINE 4
#define PRISM_PROC_ABORTED 5

extern char **environ;

typedef struct {
    unsigned char *data;
    size_t len;
    size_t cap;
} prism_proc_bytes;

static int prism_proc_put(prism_proc_bytes *b, const void *src, size_t n) {
    if (n == 0) return 1;
    if (b->len + n > b->cap) {
        size_t cap = b->cap ? b->cap : 256;
        while (cap < b->len + n) cap *= 2;
        unsigned char *grown = (unsigned char *)realloc(b->data, cap);
        if (grown == NULL) return 0;
        b->data = grown;
        b->cap = cap;
    }
    memcpy(b->data + b->len, src, n);
    b->len += n;
    return 1;
}

static int prism_proc_put_uv(prism_proc_bytes *b, uint64_t n) {
    unsigned char tmp[10];
    size_t k = 0;
    while (n >= 0x80) {
        tmp[k++] = (unsigned char)((n & 0x7f) | 0x80);
        n >>= 7;
    }
    tmp[k++] = (unsigned char)n;
    return prism_proc_put(b, tmp, k);
}

/* A request reader. Strings are copied out NUL-terminated, since every one of
 * them goes to an exec call, and one with an interior NUL is refused. */
typedef struct {
    const unsigned char *p;
    size_t len;
    size_t at;
    int bad;
} prism_proc_reader;

static uint64_t prism_proc_uv(prism_proc_reader *r) {
    uint64_t v = 0;
    for (unsigned shift = 0; shift < 64; shift += 7) {
        if (r->at >= r->len) break;
        unsigned char byte = r->p[r->at++];
        v |= (uint64_t)(byte & 0x7f) << shift;
        if (byte < 0x80) return v;
    }
    r->bad = 1;
    return 0;
}

static const unsigned char *prism_proc_span(prism_proc_reader *r, size_t *n) {
    uint64_t want = prism_proc_uv(r);
    if (r->bad || want > r->len - r->at) {
        r->bad = 1;
        *n = 0;
        return NULL;
    }
    const unsigned char *s = r->p + r->at;
    r->at += (size_t)want;
    *n = (size_t)want;
    return s;
}

static char *prism_proc_text(prism_proc_reader *r) {
    size_t n;
    const unsigned char *s = prism_proc_span(r, &n);
    if (s == NULL || memchr(s, 0, n) != NULL) {
        r->bad = 1;
        return NULL;
    }
    char *out = (char *)malloc(n + 1);
    if (out == NULL) {
        r->bad = 1;
        return NULL;
    }
    memcpy(out, s, n);
    out[n] = '\0';
    return out;
}

/* One stage of a graph: a command whose standard output, unless it is the last
 * stage, is the next stage's input. */
typedef struct {
    char *program;
    char **argv; /* argv[0] is the program as written, then the arguments */
    size_t argc;
    char *cwd;
    int clean;
    char **env;
    size_t nenv;
    const unsigned char *stdin_bytes;
    size_t stdin_len;
    int feed;
    int capture[2];
    uint64_t limit[2];
} prism_proc_stage;

/* A request: one stage for a command, one or more for a pipeline. */
typedef struct {
    prism_proc_stage *stages;
    size_t n;
    int has_deadline;
    uint64_t deadline_ms;
} prism_proc_req;

static void prism_proc_free_strs(char **xs, size_t n) {
    if (xs == NULL) return;
    for (size_t i = 0; i < n; i++) free(xs[i]);
    free((void *)xs);
}

static void prism_proc_req_free(prism_proc_req *q) {
    for (size_t i = 0; q->stages != NULL && i < q->n; i++) {
        prism_proc_stage *s = &q->stages[i];
        free(s->program);
        prism_proc_free_strs(s->argv, s->argc + 1);
        free(s->cwd);
        prism_proc_free_strs(s->env, s->nenv);
    }
    free(q->stages);
}

/* The index of the entry for `key` (the bytes before its `=`), or -1. */
static long prism_proc_env_find(char **env, size_t n, const char *key, size_t klen) {
    for (size_t i = 0; i < n; i++) {
        if (env[i] != NULL && strncmp(env[i], key, klen) == 0 && env[i][klen] == '=') {
            return (long)i;
        }
    }
    return -1;
}

/* Apply one edit in place: replace or append for a set, compact for an unset.
 * `cap` bounds the array, sized for the base plus every edit. */
static int prism_proc_env_edit(prism_proc_stage *q, char *key, char *value) {
    size_t klen = strlen(key);
    long at = prism_proc_env_find(q->env, q->nenv, key, klen);
    if (value == NULL) {
        if (at >= 0) {
            free(q->env[at]);
            memmove((void *)(q->env + at), (const void *)(q->env + at + 1),
                    (q->nenv - (size_t)at - 1) * sizeof(char *));
            q->nenv--;
            q->env[q->nenv] = NULL;
        }
        return 1;
    }
    size_t vlen = strlen(value);
    char *entry = (char *)malloc(klen + vlen + 2);
    if (entry == NULL) return 0;
    memcpy(entry, key, klen);
    entry[klen] = '=';
    memcpy(entry + klen + 1, value, vlen + 1);
    if (at >= 0) {
        free(q->env[at]);
        q->env[at] = entry;
    } else {
        q->env[q->nenv++] = entry;
        q->env[q->nenv] = NULL;
    }
    return 1;
}

static int prism_proc_output(prism_proc_reader *r, int *capture, uint64_t *limit) {
    uint64_t tag = prism_proc_uv(r);
    if (tag == 0) {
        *capture = 0;
        return !r->bad;
    }
    *capture = 1;
    *limit = prism_proc_uv(r);
    return tag == 1 && !r->bad && *limit <= PRISM_PROC_MAX_CAPTURE;
}

static int prism_proc_decode_stage(prism_proc_reader *r, prism_proc_stage *q) {
    q->program = prism_proc_text(r);
    if (q->program == NULL || q->program[0] == '\0') return 0;
    uint64_t nargs = prism_proc_uv(r);
    if (r->bad || nargs > r->len) return 0;
    q->argc = (size_t)nargs + 1;
    q->argv = (char **)calloc(q->argc + 1, sizeof(char *));
    if (q->argv == NULL) return 0;
    q->argv[0] = strdup(q->program);
    if (q->argv[0] == NULL) return 0;
    for (size_t i = 1; i < q->argc; i++) {
        q->argv[i] = prism_proc_text(r);
        if (q->argv[i] == NULL) return 0;
    }
    uint64_t has_cwd = prism_proc_uv(r);
    if (has_cwd == 1) {
        q->cwd = prism_proc_text(r);
        if (q->cwd == NULL) return 0;
    } else if (has_cwd != 0) {
        return 0;
    }
    uint64_t base = prism_proc_uv(r);
    if (r->bad || base > 1) return 0;
    q->clean = (int)base;
    uint64_t nedits = prism_proc_uv(r);
    if (r->bad || nedits > r->len) return 0;
    size_t nbase = 0;
    if (!q->clean) {
        while (environ[nbase] != NULL) nbase++;
    }
    q->env = (char **)calloc(nbase + (size_t)nedits + 1, sizeof(char *));
    if (q->env == NULL) return 0;
    for (size_t i = 0; i < nbase; i++) {
        q->env[i] = strdup(environ[i]);
        if (q->env[i] == NULL) return 0;
        q->nenv++;
    }
    for (uint64_t i = 0; i < nedits; i++) {
        uint64_t op = prism_proc_uv(r);
        char *key = prism_proc_text(r);
        if (key == NULL || key[0] == '\0' || strchr(key, '=') != NULL || op > 1) {
            free(key);
            return 0;
        }
        char *value = NULL;
        if (op == 0) {
            value = prism_proc_text(r);
            if (value == NULL) {
                free(key);
                return 0;
            }
        }
        int ok = prism_proc_env_edit(q, key, value);
        free(key);
        free(value);
        if (!ok) return 0;
    }
    uint64_t feed = prism_proc_uv(r);
    if (feed == 1) {
        q->feed = 1;
        q->stdin_bytes = prism_proc_span(r, &q->stdin_len);
        if (r->bad) return 0;
    } else if (feed != 0) {
        return 0;
    }
    return prism_proc_output(r, &q->capture[0], &q->limit[0]) &&
           prism_proc_output(r, &q->capture[1], &q->limit[1]);
}

/* A command is one stage; a pipeline is a count and that many stages, of which
 * only the first may be fed, since every later stage reads the one before it.
 * Either ends with the deadline and is accepted only whole. */
static int prism_proc_decode(const unsigned char *p, size_t len, int pipeline, prism_proc_req *q) {
    prism_proc_reader r = {p, len, 0, 0};
    memset(q, 0, sizeof *q);
    if (prism_proc_uv(&r) != PRISM_PROC_VERSION || r.bad) return 0;
    uint64_t n = pipeline ? prism_proc_uv(&r) : 1;
    if (r.bad || n == 0 || n > len) return 0;
    q->stages = (prism_proc_stage *)calloc((size_t)n, sizeof(prism_proc_stage));
    if (q->stages == NULL) return 0;
    q->n = (size_t)n;
    for (size_t i = 0; i < q->n; i++) {
        if (!prism_proc_decode_stage(&r, &q->stages[i])) return 0;
        if (i > 0 && q->stages[i].feed) return 0;
    }
    uint64_t deadline = prism_proc_uv(&r);
    q->has_deadline = deadline != 0;
    q->deadline_ms = deadline ? deadline - 1 : 0;
    return !r.bad && r.at == r.len;
}

static int prism_proc_executable(const char *path) {
    struct stat st;
    return stat(path, &st) == 0 && S_ISREG(st.st_mode) && (st.st_mode & 0111) != 0;
}

/* The parent's PATH, absolute entries only. A name with a `/` is used as
 * written. Returns a malloc'd path, or NULL when nothing matches. */
static char *prism_proc_resolve(const char *program) {
    if (strchr(program, '/') != NULL) return strdup(program);
    const char *path = getenv("PATH");
    if (path == NULL) return NULL;
    size_t plen = strlen(program);
    const char *dir = path;
    for (;;) {
        const char *end = strchr(dir, ':');
        size_t dlen = end ? (size_t)(end - dir) : strlen(dir);
        /* A candidate longer than PATH_MAX cannot be executed, so it is skipped. */
        if (dlen > 0 && dir[0] == '/' && dlen + plen + 2 <= PATH_MAX) {
            char *cand = (char *)malloc(dlen + plen + 2);
            if (cand == NULL) return NULL;
            memcpy(cand, dir, dlen);
            cand[dlen] = '/';
            memcpy(cand + dlen + 1, program, plen + 1);
            if (prism_proc_executable(cand)) return cand;
            free(cand);
        }
        if (end == NULL) return NULL;
        dir = end + 1;
    }
}

static long prism_proc_classify(int e) {
    switch (e) {
    case ENOENT: return PRISM_PROC_NOT_FOUND;
    case EACCES:
    case EPERM: return PRISM_PROC_DENIED;
    case EAGAIN:
    case ENOMEM:
    case ENFILE:
    case EMFILE: return PRISM_PROC_LIMIT;
    default: return PRISM_PROC_OTHER;
    }
}

static uint64_t prism_proc_now_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000u + (uint64_t)ts.tv_nsec / 1000000u;
}

static int prism_proc_pipe(int fds[2]) {
    if (pipe(fds) != 0) return 0;
    for (int i = 0; i < 2; i++) (void)fcntl(fds[i], F_SETFD, FD_CLOEXEC);
    return 1;
}

static void prism_proc_close(int *fd) {
    if (*fd >= 0) {
        (void)close(*fd);
        *fd = -1;
    }
}

/* A write to a child that has closed its input must come back as EPIPE, not as
 * a signal that kills the program. Darwin suppresses it per descriptor; Linux
 * per thread, by blocking it around the write and discarding what it raised. */
static ssize_t prism_proc_write(int fd, const unsigned char *p, size_t n) {
#ifdef __linux__
    sigset_t pipe_set, old;
    sigemptyset(&pipe_set);
    sigaddset(&pipe_set, SIGPIPE);
    pthread_sigmask(SIG_BLOCK, &pipe_set, &old);
    ssize_t put = write(fd, p, n);
    int saved = errno;
    if (put < 0 && saved == EPIPE) {
        struct timespec zero = {0, 0};
        (void)sigtimedwait(&pipe_set, NULL, &zero);
    }
    pthread_sigmask(SIG_SETMASK, &old, NULL);
    errno = saved;
    return put;
#else
    return write(fd, p, n);
#endif
}

static void prism_proc_reap(pid_t pid, int *status) {
    while (waitpid(pid, status, 0) < 0 && errno == EINTR) {}
}

/* Spawn the resolved child. Returns its pid, or -1 with `*code` set. */
static pid_t prism_proc_spawn(const prism_proc_stage *q, const char *path, int in_fd, int out_fd,
                              int err_fd, long *code) {
    posix_spawn_file_actions_t fa;
    posix_spawnattr_t attr;
    pid_t pid = -1;
    if (posix_spawn_file_actions_init(&fa) != 0) {
        *code = PRISM_PROC_LIMIT;
        return -1;
    }
    if (posix_spawnattr_init(&attr) != 0) {
        posix_spawn_file_actions_destroy(&fa);
        *code = PRISM_PROC_LIMIT;
        return -1;
    }
    int fds[3] = {in_fd, out_fd, err_fd};
    int rc = 0;
    for (int i = 0; rc == 0 && i < 3; i++) {
        rc = fds[i] >= 0 ? posix_spawn_file_actions_adddup2(&fa, fds[i], i)
                         : posix_spawn_file_actions_addopen(&fa, i, "/dev/null",
                                                            i == 0 ? O_RDONLY : O_WRONLY, 0);
    }
    /* The `_np` spelling is the one every supported host has; newer SDKs mark it
     * deprecated in favour of the POSIX 2024 name older ones lack. */
#ifdef __APPLE__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wdeprecated-declarations"
#endif
    if (rc == 0 && q->cwd != NULL) rc = posix_spawn_file_actions_addchdir_np(&fa, q->cwd);
#ifdef __APPLE__
#pragma clang diagnostic pop
#endif
    /* The child starts with an empty signal mask and SIGPIPE at its default, so
     * a pipeline stage behaves the same whatever the parent ignored. */
    sigset_t empty, defaults;
    sigemptyset(&empty);
    sigemptyset(&defaults);
    sigaddset(&defaults, SIGPIPE);
    if (rc == 0) rc = posix_spawnattr_setsigmask(&attr, &empty);
    if (rc == 0) rc = posix_spawnattr_setsigdefault(&attr, &defaults);
    if (rc == 0) {
        rc = posix_spawnattr_setflags(&attr,
                                      (short)(POSIX_SPAWN_SETSIGMASK | POSIX_SPAWN_SETSIGDEF));
    }
    if (rc == 0) rc = posix_spawn(&pid, path, &fa, &attr, q->argv, q->env);
    posix_spawnattr_destroy(&attr);
    posix_spawn_file_actions_destroy(&fa);
    if (rc != 0) {
        *code = prism_proc_classify(rc);
        return -1;
    }
    return pid;
}

/* One stage's answer: a response tag and its number. */
typedef struct {
    int tag;
    uint64_t n;
} prism_proc_status;

/* Every child the graph started is killed, unless already reaped, and reaped;
 * the captures are dropped, since what any stage had written by then depends on
 * scheduling. For the same reason every stage that started answers the halt,
 * even one that had already exited, and a stage that never started keeps its
 * refusal. An output limit is answered by the stage that hit it; the stages the
 * host stopped on its account answer `Aborted(ResourceLimit)`. */
static void prism_proc_halt(size_t n, const pid_t *pid, const int *reaped, prism_proc_status *st,
                            prism_proc_bytes *cap, int tag, uint64_t tag_n, size_t trigger) {
    for (size_t i = 0; i < n; i++) {
        if (pid[i] < 0) continue;
        if (!reaped[i]) {
            int status;
            (void)kill(pid[i], SIGKILL);
            prism_proc_reap(pid[i], &status);
        }
        int own = tag != PRISM_PROC_OUTPUT_LIMIT || i == trigger;
        st[i].tag = own ? tag : PRISM_PROC_ABORTED;
        st[i].n = own ? tag_n : PRISM_PROC_LIMIT;
    }
    for (size_t j = 0; j <= n; j++) cap[j].len = 0;
}

/* Wait for one child, within the deadline when there is one. Answers the pid,
 * 0 when the deadline passed first, or -1 when the host lost the child. */
static pid_t prism_proc_wait(const prism_proc_req *q, uint64_t deadline, pid_t pid, int *status) {
    for (;;) {
        pid_t done = waitpid(pid, status, q->has_deadline ? WNOHANG : 0);
        if (done < 0 && errno == EINTR) continue;
        if (done != 0) return done;
        if (prism_proc_now_ms() >= deadline) return 0;
        struct timespec pause = {0, 1000000};
        (void)nanosleep(&pause, NULL);
    }
}

/* The run's working arrays, allocated together and freed together. */
typedef struct {
    pid_t *pid;
    int *reaped;
    int *fd;
    uint64_t *limit;
    struct pollfd *pfd;
    size_t *which;
    unsigned char *chunk;
} prism_proc_scratch;

/* Run the graph: each stage's output is the next one's input, the first is fed,
 * and the last stage's output and every error stream are drained concurrently
 * under their limits. The streams are slots: 0 is the last stage's output,
 * 1 + i is stage i's error stream, and n + 1 is the first stage's input. When a
 * stage fails to start, the stage after it reads an empty input and the stage
 * before it finds its output closed, as if the stage had exited at once. Fills
 * `st` (n entries) and `cap` (n + 1 slots). */
static void prism_proc_run(const prism_proc_req *q, const prism_proc_scratch *w,
                           prism_proc_status *st, prism_proc_bytes *cap) {
    size_t n = q->n, nslots = n + 2;
    pid_t *pid = w->pid;
    int *reaped = w->reaped, *fd = w->fd;
    uint64_t *limit = w->limit;
    struct pollfd *pfd = w->pfd;
    size_t *which = w->which;
    unsigned char *chunk = w->chunk;
    int tag = -1;
    uint64_t tag_n = 0;
    size_t trigger = n;
    for (size_t i = 0; i < n; i++) {
        pid[i] = -1;
        st[i] = (prism_proc_status){PRISM_PROC_ABORTED, PRISM_PROC_OTHER};
    }
    for (size_t j = 0; j < nslots; j++) fd[j] = -1;
    uint64_t deadline = q->has_deadline ? prism_proc_now_ms() + q->deadline_ms : 0;
    int upstream = -1;
    for (size_t i = 0; i < n; i++) {
        const prism_proc_stage *s = &q->stages[i];
        int last = i + 1 == n;
        int in_pipe[2] = {-1, -1}, out_pipe[2] = {-1, -1}, err_pipe[2] = {-1, -1};
        char *path = prism_proc_resolve(s->program);
        long code = path == NULL ? PRISM_PROC_NOT_FOUND : PRISM_PROC_LIMIT;
        int ok = path != NULL && (i > 0 || !s->feed || prism_proc_pipe(in_pipe)) &&
                 ((last && !s->capture[0]) || prism_proc_pipe(out_pipe)) &&
                 (!s->capture[1] || prism_proc_pipe(err_pipe));
        int in_fd = i > 0 ? upstream : in_pipe[0];
        pid_t p = ok ? prism_proc_spawn(s, path, in_fd, out_pipe[1], err_pipe[1], &code) : -1;
        free(path);
        prism_proc_close(&in_pipe[0]);
        prism_proc_close(&upstream);
        prism_proc_close(&out_pipe[1]);
        prism_proc_close(&err_pipe[1]);
        if (p < 0) {
            st[i] = (prism_proc_status){PRISM_PROC_SPAWN_FAILED, (uint64_t)code};
            prism_proc_close(&in_pipe[1]);
            prism_proc_close(&out_pipe[0]);
            prism_proc_close(&err_pipe[0]);
            continue;
        }
        pid[i] = p;
        if (i == 0) fd[n + 1] = in_pipe[1];
        if (last) {
            fd[0] = out_pipe[0];
            limit[0] = s->limit[0];
        } else {
            upstream = out_pipe[0];
        }
        fd[1 + i] = err_pipe[0];
        limit[1 + i] = s->limit[1];
    }
    const prism_proc_stage *first = &q->stages[0];
    if (fd[n + 1] >= 0) {
#ifdef F_SETNOSIGPIPE
        (void)fcntl(fd[n + 1], F_SETNOSIGPIPE, 1);
#endif
        (void)fcntl(fd[n + 1], F_SETFL, O_NONBLOCK);
        if (first->stdin_len == 0) prism_proc_close(&fd[n + 1]);
    }
    size_t fed = 0;
    while (tag < 0) {
        nfds_t k = 0;
        for (size_t j = 0; j < nslots; j++) {
            if (fd[j] < 0) continue;
            pfd[k].fd = fd[j];
            pfd[k].events = j == n + 1 ? POLLOUT : POLLIN;
            pfd[k].revents = 0;
            which[k++] = j;
        }
        if (k == 0) break;
        int wait_ms = -1;
        if (q->has_deadline) {
            uint64_t now = prism_proc_now_ms();
            if (now >= deadline) {
                tag = PRISM_PROC_DEADLINE;
                break;
            }
            uint64_t left = deadline - now;
            wait_ms = left > INT32_MAX ? INT32_MAX : (int)left;
        }
        int ready = poll(pfd, k, wait_ms);
        if (ready < 0) {
            if (errno == EINTR) continue;
            tag = PRISM_PROC_ABORTED;
            break;
        }
        for (nfds_t m = 0; tag < 0 && m < k; m++) {
            size_t j = which[m];
            if (pfd[m].revents == 0) continue;
            if (j == n + 1) {
                ssize_t put =
                    prism_proc_write(fd[j], first->stdin_bytes + fed, first->stdin_len - fed);
                if (put > 0) fed += (size_t)put;
                /* A child that stops reading closes its input early; that is its
                 * choice, not a failure, so a broken pipe ends the feed quietly. */
                if (fed == first->stdin_len || (put < 0 && errno != EAGAIN && errno != EINTR)) {
                    prism_proc_close(&fd[j]);
                }
                continue;
            }
            ssize_t got = read(fd[j], chunk, PRISM_PROC_CHUNK);
            if (got < 0) {
                if (errno == EINTR || errno == EAGAIN) continue;
                tag = PRISM_PROC_ABORTED;
            } else if (got == 0) {
                prism_proc_close(&fd[j]);
            } else if (!prism_proc_put(&cap[j], chunk, (size_t)got)) {
                tag = PRISM_PROC_ABORTED;
                tag_n = PRISM_PROC_LIMIT;
            } else if (cap[j].len > limit[j]) {
                tag = PRISM_PROC_OUTPUT_LIMIT;
                tag_n = j == 0 ? 0 : 1;
                trigger = j == 0 ? n - 1 : j - 1;
            }
        }
    }
    for (size_t j = 0; j < nslots; j++) prism_proc_close(&fd[j]);
    for (size_t i = 0; tag < 0 && i < n; i++) {
        if (pid[i] < 0) continue;
        int status = 0;
        pid_t got = prism_proc_wait(q, deadline, pid[i], &status);
        if (got == 0) {
            tag = PRISM_PROC_DEADLINE;
        } else if (got < 0) {
            tag = PRISM_PROC_ABORTED;
            tag_n = PRISM_PROC_OTHER;
        } else {
            reaped[i] = 1;
            if (WIFEXITED(status)) {
                st[i] = (prism_proc_status){PRISM_PROC_EXITED, (uint64_t)WEXITSTATUS(status)};
            } else if (WIFSIGNALED(status)) {
                st[i] = (prism_proc_status){PRISM_PROC_SIGNALED, (uint64_t)WTERMSIG(status)};
            }
        }
    }
    if (tag >= 0) prism_proc_halt(n, pid, reaped, st, cap, tag, tag_n, trigger);
}

static void prism_proc_graph(const prism_proc_req *q, prism_proc_status *st,
                             prism_proc_bytes *cap) {
    size_t n = q->n, nslots = n + 2;
    prism_proc_scratch w = {
        (pid_t *)malloc(n * sizeof(pid_t)),
        (int *)calloc(n, sizeof(int)),
        (int *)malloc(nslots * sizeof(int)),
        (uint64_t *)calloc(nslots, sizeof(uint64_t)),
        (struct pollfd *)malloc(nslots * sizeof(struct pollfd)),
        (size_t *)malloc(nslots * sizeof(size_t)),
        (unsigned char *)malloc(PRISM_PROC_CHUNK),
    };
    if (w.pid != NULL && w.reaped != NULL && w.fd != NULL && w.limit != NULL && w.pfd != NULL &&
        w.which != NULL && w.chunk != NULL) {
        prism_proc_run(q, &w, st, cap);
    } else {
        for (size_t i = 0; i < n; i++) {
            st[i] = (prism_proc_status){PRISM_PROC_ABORTED, PRISM_PROC_LIMIT};
        }
    }
    free(w.pid);
    free(w.reaped);
    free(w.fd);
    free(w.limit);
    free(w.pfd);
    free((void *)w.which);
    free(w.chunk);
}

/* The response: the version, the stage count for a pipeline, each stage's
 * status, the last stage's output, and each stage's error stream. A command's
 * response is the same layout for one stage without the count. */
static long prism_proc_answer(int pipeline, size_t n, const prism_proc_status *st,
                              const prism_proc_bytes *cap) {
    prism_proc_bytes b = {NULL, 0, 0};
    int ok = prism_proc_put_uv(&b, PRISM_PROC_VERSION) && (!pipeline || prism_proc_put_uv(&b, n));
    for (size_t i = 0; ok && i < n; i++) {
        ok = prism_proc_put_uv(&b, (uint64_t)st[i].tag) && prism_proc_put_uv(&b, st[i].n);
    }
    for (size_t j = 0; ok && j <= n; j++) {
        ok = prism_proc_put_uv(&b, cap[j].len) && prism_proc_put(&b, cap[j].data, cap[j].len);
    }
    long s = ok ? prism_str_lit((const char *)b.data, (long)b.len) : prism_str_lit("", 0);
    free(b.data);
    long buf = prism_buf_of_string(s);
    prism_rc_dec(s);
    return buf;
}

static long prism_proc_call(long req, int pipeline) {
    prism_proc_req q;
    int decoded = prism_proc_decode(prism_buf_ptr(req), (size_t)prism_buf_len(req), pipeline, &q);
    size_t n = decoded ? q.n : 1;
    prism_proc_status *st = (prism_proc_status *)calloc(n, sizeof(prism_proc_status));
    prism_proc_bytes *cap = (prism_proc_bytes *)calloc(n + 1, sizeof(prism_proc_bytes));
    long answer;
    if (st == NULL || cap == NULL) {
        prism_proc_status lost = {PRISM_PROC_ABORTED, PRISM_PROC_LIMIT};
        prism_proc_bytes none[2] = {{NULL, 0, 0}, {NULL, 0, 0}};
        answer = prism_proc_answer(pipeline, 1, &lost, none);
    } else {
        if (decoded) {
            prism_proc_graph(&q, st, cap);
        } else {
            st[0] = (prism_proc_status){PRISM_PROC_SPAWN_FAILED, PRISM_PROC_INVALID};
        }
        answer = prism_proc_answer(pipeline, n, st, cap);
    }
    for (size_t j = 0; cap != NULL && j <= n; j++) free(cap[j].data);
    free(cap);
    free(st);
    prism_proc_req_free(&q);
    return answer;
}

long prism_prim_proc_collect(long req) {
    return prism_proc_call(req, 0);
}

long prism_prim_proc_pipeline(long req) {
    return prism_proc_call(req, 1);
}
