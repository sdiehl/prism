/* Stream sockets: the Unix TCP boundary under the `Net` capability. Listeners
 * and connections are named by a logical handle allocated from a per-process
 * counter, never by a file descriptor, so the interpreter and a native binary
 * number the same sockets identically and a recorded observation means the same
 * thing in both. Every entry point returns a Prism `Result` whose error side is
 * a small classification code (see prism_net.c), not `errno`. */
#ifndef PRISM_NET_H
#define PRISM_NET_H

#include "prism_internal.h"

long prism_prim_net_listen(long host, long port, long backlog);
long prism_prim_net_accept(long handle);
long prism_prim_net_connect(long host, long port);
long prism_prim_net_recv(long handle, long max);
long prism_prim_net_send(long handle, long buf, long off);
long prism_prim_net_close(long handle);
long prism_prim_net_local_addr(long handle);
long prism_prim_net_peer_addr(long handle);

#endif /* PRISM_NET_H */
