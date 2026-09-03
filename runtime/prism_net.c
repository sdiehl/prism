/* Stream sockets: the Unix TCP boundary under the `Net` capability.
 *
 * A Prism program never sees a file descriptor. Each open socket takes a slot in
 * the table below and is named by a logical handle from a counter starting at 1,
 * so the nth socket a program opens is handle n whatever the OS hands out. The
 * interpreter numbers them the same way, which is what lets one recorded
 * observation name the same socket in both tiers.
 *
 * The table is unsynchronized: a program's capability calls all run on the one
 * entry thread prism_io.c creates, the same assumption the argument and
 * environment accessors make.
 *
 * Every entry point returns a Prism `Result` whose error side is a
 * classification code rather than `errno`, since errno numbers differ across
 * platforms and the same failure has to be the same Prism value everywhere. The
 * codes are the wire between this file and `Net.pr`, which maps each to the
 * `NetError` constructor it names, so the two change together:
 *
 *   0 other   1 refused   2 unreachable   3 timed out   4 reset
 *   5 address in use   6 invalid   7 closed   8 denied   9 limit
 */
#include "prism_net.h"
#include "prism_buffer.h"
#include "prism_int.h"
#include "prism_mem.h"
#include "prism_string.h"

#include <errno.h>
#include <netdb.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

/* One classification code per `NetError` constructor in Net.pr. */
#define PRISM_NET_OTHER 0
#define PRISM_NET_REFUSED 1
#define PRISM_NET_UNREACHABLE 2
#define PRISM_NET_TIMED_OUT 3
#define PRISM_NET_RESET 4
#define PRISM_NET_IN_USE 5
#define PRISM_NET_INVALID 6
#define PRISM_NET_CLOSED 7
#define PRISM_NET_DENIED 8
#define PRISM_NET_LIMIT 9

/* The open-socket table. 0 in the id column marks a free slot. The bound is a
 * policy, not an OS limit: a program that wants thousands of concurrent sockets
 * wants an event loop and a different capability, and a fixed table keeps this
 * file free of allocation and its failure modes.
 *
 * A slot records what kind of socket it holds, because the two kinds accept
 * different operations and the answer for the wrong one must be the classified
 * `Closed`, not whatever errno the syscall would have produced. The interpreter
 * distinguishes them the same way. */
#define PRISM_NET_SLOTS 256
#define PRISM_NET_LISTENER 0
#define PRISM_NET_STREAM 1

static long prism_net_ids[PRISM_NET_SLOTS];
static int prism_net_fds[PRISM_NET_SLOTS];
static int prism_net_kinds[PRISM_NET_SLOTS];
static long prism_net_next_id = 1;

/* Some platforms suppress SIGPIPE per send, others per socket; a write to a
 * closed peer must come back as an ordinary error either way, and the runtime
 * does not install a process-wide handler on the program's behalf. */
#ifdef MSG_NOSIGNAL
#define PRISM_NET_SEND_FLAGS MSG_NOSIGNAL
#else
#define PRISM_NET_SEND_FLAGS 0
#endif

static long prism_net_code(int e) {
    switch (e) {
    case ECONNREFUSED: return PRISM_NET_REFUSED;
    case ENETUNREACH:
    case EHOSTUNREACH:
    case ENETDOWN: return PRISM_NET_UNREACHABLE;
    case ETIMEDOUT: return PRISM_NET_TIMED_OUT;
    case ECONNRESET:
    case ECONNABORTED:
    case EPIPE: return PRISM_NET_RESET;
    case EADDRINUSE:
    case EADDRNOTAVAIL: return PRISM_NET_IN_USE;
    case EAFNOSUPPORT:
    case EINVAL: return PRISM_NET_INVALID;
    case EBADF:
    case ENOTCONN:
    case ENOTSOCK: return PRISM_NET_CLOSED;
    case EACCES:
    case EPERM: return PRISM_NET_DENIED;
    case EMFILE:
    case ENFILE:
    case ENOBUFS:
    case ENOMEM: return PRISM_NET_LIMIT;
    default: return PRISM_NET_OTHER;
    }
}

/* Result(a, Int): Ok carries an already-built Prism value, Err a bare code. */
static long prism_net_ok(long v) {
    return prism_ctor(0, 1, &v);
}

static long prism_net_err(long code) {
    long c = prism_int_of_long(code);
    return prism_ctor(1, 1, &c);
}

static long prism_net_errno(void) {
    return prism_net_err(prism_net_code(errno));
}

/* Take a slot for `fd` and return its handle, or -1 with the descriptor closed
 * if the table is full: a caller that cannot name a socket must not leak it. */
static long prism_net_intern(int fd, int kind) {
    for (long i = 0; i < PRISM_NET_SLOTS; i++) {
        if (prism_net_ids[i] != 0) continue;
        prism_net_ids[i] = prism_net_next_id++;
        prism_net_fds[i] = fd;
        prism_net_kinds[i] = kind;
        return prism_net_ids[i];
    }
    close(fd);
    return -1;
}

/* The descriptor for a live handle, or -1 for a handle that was never issued or
 * has already been closed. */
static int prism_net_fd(long handle) {
    for (long i = 0; i < PRISM_NET_SLOTS; i++) {
        if (prism_net_ids[i] == handle) return prism_net_fds[i];
    }
    return -1;
}

/* As above, but only for a handle of the kind the operation can act on. A live
 * handle of the other kind answers -1, and so reports `Closed`. */
static int prism_net_fd_of(long handle, int kind) {
    for (long i = 0; i < PRISM_NET_SLOTS; i++) {
        if (prism_net_ids[i] == handle) return prism_net_kinds[i] == kind ? prism_net_fds[i] : -1;
    }
    return -1;
}

static void prism_net_release(long handle) {
    for (long i = 0; i < PRISM_NET_SLOTS; i++) {
        if (prism_net_ids[i] != handle) continue;
        prism_net_ids[i] = 0;
        prism_net_fds[i] = -1;
        return;
    }
}

/* A NUL-terminated copy of a Prism string, for the libc calls that read one.
 * Returns NULL if the text does not fit the caller's buffer or contains an
 * interior NUL, both of which are invalid as a host name or service. */
static int prism_net_cstr(long s, char *out, size_t cap) {
    size_t n = (size_t)prism_str_len_bytes(s);
    if (n >= cap) return 0;
    const char *d = prism_str_data(s);
    if (memchr(d, 0, n) != NULL) return 0;
    memcpy(out, d, n);
    out[n] = '\0';
    return 1;
}

/* The largest port a 16-bit port field can name, and the largest host string
 * this boundary will copy out of a Prism value. The port bound is the same one
 * `net_port_max` states in Net.pr, so a port the parser there accepts is one this
 * resolver accepts. The host bound is generous for a numeric address or a name
 * and is a bound rather than an allocation because the caller controls the
 * string. */
#define PRISM_NET_PORT_MAX 65535
#define PRISM_NET_NODE_MAX 256

/* Resolve host and port to a stream-socket address list. The host is required
 * and must be non-empty even for a listener: the wildcard is spelled "0.0.0.0"
 * or "::" by the program. A passive lookup with no host would pick the family,
 * and the two tiers would then disagree about which address a bare listener
 * bound, so the choice belongs to the program that has to live with it. */
static int prism_net_resolve(const char *host, long port, struct addrinfo **out) {
    if (port < 0 || port > PRISM_NET_PORT_MAX) return EINVAL;
    if (host == NULL || host[0] == '\0') return EINVAL;
    char service[8];
    (void)snprintf(service, sizeof service, "%ld", port);
    struct addrinfo hints;
    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    return getaddrinfo(host, service, &hints, out) == 0 ? 0 : EINVAL;
}

static void prism_net_nosigpipe(int fd) {
#ifdef SO_NOSIGPIPE
    int on = 1;
    (void)setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &on, sizeof on);
#else
    (void)fd;
#endif
}

long prism_prim_net_listen(long host, long port, long backlog) {
    char node[PRISM_NET_NODE_MAX];
    if (!prism_net_cstr(host, node, sizeof node)) return prism_net_err(PRISM_NET_INVALID);
    struct addrinfo *list = NULL;
    if (prism_net_resolve(node, port, &list) != 0) return prism_net_err(PRISM_NET_INVALID);

    int last = EINVAL;
    for (struct addrinfo *a = list; a != NULL; a = a->ai_next) {
        int fd = socket(a->ai_family, a->ai_socktype, a->ai_protocol);
        if (fd < 0) {
            last = errno;
            continue;
        }
        int on = 1;
        (void)setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &on, sizeof on);
        prism_net_nosigpipe(fd);
        long depth = backlog < 1 ? 1 : backlog > SOMAXCONN ? SOMAXCONN : backlog;
        if (bind(fd, a->ai_addr, a->ai_addrlen) == 0 && listen(fd, (int)depth) == 0) {
            freeaddrinfo(list);
            long h = prism_net_intern(fd, PRISM_NET_LISTENER);
            return h < 0 ? prism_net_err(PRISM_NET_LIMIT) : prism_net_ok(prism_int_of_long(h));
        }
        last = errno;
        close(fd);
    }
    freeaddrinfo(list);
    return prism_net_err(prism_net_code(last));
}

long prism_prim_net_accept(long handle) {
    int fd = prism_net_fd_of(handle, PRISM_NET_LISTENER);
    if (fd < 0) return prism_net_err(PRISM_NET_CLOSED);
    int peer;
    do { peer = accept(fd, NULL, NULL); } while (peer < 0 && errno == EINTR);
    if (peer < 0) return prism_net_errno();
    prism_net_nosigpipe(peer);
    long h = prism_net_intern(peer, PRISM_NET_STREAM);
    return h < 0 ? prism_net_err(PRISM_NET_LIMIT) : prism_net_ok(prism_int_of_long(h));
}

long prism_prim_net_connect(long host, long port) {
    char node[PRISM_NET_NODE_MAX];
    if (!prism_net_cstr(host, node, sizeof node)) return prism_net_err(PRISM_NET_INVALID);
    struct addrinfo *list = NULL;
    if (prism_net_resolve(node, port, &list) != 0) return prism_net_err(PRISM_NET_INVALID);

    int last = EINVAL;
    for (struct addrinfo *a = list; a != NULL; a = a->ai_next) {
        int fd = socket(a->ai_family, a->ai_socktype, a->ai_protocol);
        if (fd < 0) {
            last = errno;
            continue;
        }
        prism_net_nosigpipe(fd);
        int rc;
        do { rc = connect(fd, a->ai_addr, a->ai_addrlen); } while (rc != 0 && errno == EINTR);
        if (rc == 0) {
            freeaddrinfo(list);
            long h = prism_net_intern(fd, PRISM_NET_STREAM);
            return h < 0 ? prism_net_err(PRISM_NET_LIMIT) : prism_net_ok(prism_int_of_long(h));
        }
        last = errno;
        close(fd);
    }
    freeaddrinfo(list);
    return prism_net_err(prism_net_code(last));
}

/* At most `max` bytes, however many have arrived. An empty buffer is the peer's
 * orderly close: `Net.pr` turns the length-zero read into `End`, so a read that
 * could not have returned bytes must not answer with one and a non-positive
 * `max` is invalid rather than a false end of stream. */
long prism_prim_net_recv(long handle, long max) {
    int fd = prism_net_fd_of(handle, PRISM_NET_STREAM);
    if (fd < 0) return prism_net_err(PRISM_NET_CLOSED);
    if (max <= 0) return prism_net_err(PRISM_NET_INVALID);
    size_t want = (size_t)max;
    char *tmp = (char *)malloc(want);
    if (tmp == NULL) return prism_net_err(PRISM_NET_LIMIT);
    ssize_t got;
    do { got = recv(fd, tmp, want, 0); } while (got < 0 && errno == EINTR);
    if (got < 0) {
        free(tmp);
        return prism_net_errno();
    }
    long s = prism_str_lit(tmp, (long)got);
    free(tmp);
    long b = prism_buf_of_string(s);
    prism_rc_dec(s);
    return prism_net_ok(b);
}

/* Write what the kernel accepts from `off` onward and report how much that was;
 * a short write is an ordinary outcome, not an error, and the caller advances. */
long prism_prim_net_send(long handle, long buf, long off) {
    int fd = prism_net_fd_of(handle, PRISM_NET_STREAM);
    if (fd < 0) return prism_net_err(PRISM_NET_CLOSED);
    long len = prism_buf_len(buf);
    if (off < 0 || off > len) return prism_net_err(PRISM_NET_INVALID);
    size_t want = (size_t)(len - off);
    if (want == 0) return prism_net_ok(prism_int_of_long(0));
    const unsigned char *p = prism_buf_ptr(buf) + off;
    ssize_t put;
    do { put = send(fd, p, want, PRISM_NET_SEND_FLAGS); } while (put < 0 && errno == EINTR);
    if (put < 0) return prism_net_errno();
    return prism_net_ok(prism_int_of_long((long)put));
}

long prism_prim_net_close(long handle) {
    int fd = prism_net_fd(handle);
    if (fd < 0) return prism_net_err(PRISM_NET_CLOSED);
    prism_net_release(handle);
    /* One close, never a retry. A close interrupted by a signal has already
     * consumed the descriptor on the systems this runtime targets, so calling
     * again would close whatever number the kernel reissued in the meantime;
     * `EINTR` is therefore success. The slot is gone whatever the outcome, since
     * a descriptor whose close failed is not one the program may retry. */
    int rc = close(fd);
    if (rc != 0 && errno != EINTR) return prism_net_errno();
    long unit = 0;
    return prism_net_ok(unit);
}

/* "host:port", numeric on both halves, so no name lookup enters the answer, and
 * an IPv6 host in brackets ("[::1]:9000") so the colons of the address cannot be
 * confused with the separator. That bracketed spelling is also what the
 * interpreter's `SocketAddr` renders, which is what keeps one program's reported
 * address the same string in both tiers.
 *
 * The buffers are sized here rather than taken from NI_MAXHOST/NI_MAXSERV, which
 * are not POSIX and are hidden behind feature-test macros on some libcs: a
 * numeric IPv6 address with a scope id fits well inside 128 bytes, a port in 16. */
#define PRISM_NET_HOST_MAX 128
#define PRISM_NET_SERV_MAX 16

static long prism_net_addr_text(const struct sockaddr *sa, socklen_t len) {
    char host[PRISM_NET_HOST_MAX];
    char service[PRISM_NET_SERV_MAX];
    if (getnameinfo(sa, len, host, sizeof host, service, sizeof service,
                    NI_NUMERICHOST | NI_NUMERICSERV) != 0) {
        return prism_net_err(PRISM_NET_INVALID);
    }
    char text[PRISM_NET_HOST_MAX + PRISM_NET_SERV_MAX + 4];
    int n = sa->sa_family == AF_INET6 ? snprintf(text, sizeof text, "[%s]:%s", host, service)
                                      : snprintf(text, sizeof text, "%s:%s", host, service);
    if (n < 0) return prism_net_err(PRISM_NET_OTHER);
    return prism_net_ok(prism_str_lit(text, (long)n));
}

long prism_prim_net_local_addr(long handle) {
    int fd = prism_net_fd(handle);
    if (fd < 0) return prism_net_err(PRISM_NET_CLOSED);
    struct sockaddr_storage ss;
    socklen_t len = (socklen_t)sizeof ss;
    if (getsockname(fd, (struct sockaddr *)&ss, &len) != 0) return prism_net_errno();
    return prism_net_addr_text((const struct sockaddr *)&ss, len);
}

long prism_prim_net_peer_addr(long handle) {
    int fd = prism_net_fd_of(handle, PRISM_NET_STREAM);
    if (fd < 0) return prism_net_err(PRISM_NET_CLOSED);
    struct sockaddr_storage ss;
    socklen_t len = (socklen_t)sizeof ss;
    if (getpeername(fd, (struct sockaddr *)&ss, &len) != 0) return prism_net_errno();
    return prism_net_addr_text((const struct sockaddr *)&ss, len);
}
