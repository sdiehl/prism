/* Child processes: the Unix boundary under the `Proc` capability. One call runs
 * a command, or a pipeline of them, to completion and answers its outcome;
 * nothing outlives the call.
 * The request and the response are the byte layouts `Proc.pr` encodes and
 * decodes, and src/eval/proc.rs answers the same request the same way. */
#ifndef PRISM_PROC_H
#define PRISM_PROC_H

#include "prism_internal.h"

long prism_prim_proc_collect(long req);
long prism_prim_proc_pipeline(long req);

#endif /* PRISM_PROC_H */
