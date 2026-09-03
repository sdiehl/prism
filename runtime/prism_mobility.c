/* The mobility envelope, on the tier that cannot carry one.
 *
 * Sealing a computation captures a machine state: the stack, the registers, and
 * the closure about to be entered. The interpreter has all of that as data and
 * can write it out; a compiled binary has it as machine registers and a native
 * stack, which are not portable bytes and not reconstructible on another host.
 * So both halves refuse here, and they refuse the same way every other boundary
 * in this runtime does: with a `Result` whose error side is a classification
 * code rather than a message, so the same failure is the same Prism value on
 * both tiers and on every host.
 *
 * The codes are the wire between this file, `src/eval/mobility.rs`, and
 * `lib/std/Teleport.pr`, which maps each to the `MoveError` constructor it
 * names, so the three must stay in step:
 *
 *   1 unportable   2 malformed   3 foreign   4 unsupported   5 uncertified
 *
 * A program that wants mobility runs on the interpreter. One compiled ahead of
 * time gets `Unsupported` and can say so, which is the point of classifying the
 * refusal instead of aborting: placement is a decision the program is allowed to
 * make, including the decision to run the work where it already is.
 */
#include "prism_mobility.h"
#include "prism_int.h"
#include "prism_mem.h"

/* One classification code per `MoveError` constructor in Teleport.pr. */
#define PRISM_MOVE_UNPORTABLE 1
#define PRISM_MOVE_MALFORMED 2
#define PRISM_MOVE_FOREIGN 3
#define PRISM_MOVE_UNSUPPORTED 4
#define PRISM_MOVE_UNCERTIFIED 5

static long prism_move_err(long code) {
    long c = prism_int_of_long(code);
    return prism_ctor(1, 1, &c);
}

/* Both entry points borrow their argument, as every builtin does, so neither
 * releases it. */

long prism_prim_kont_encode(long work) {
    (void)work;
    return prism_move_err(PRISM_MOVE_UNSUPPORTED);
}

long prism_prim_kont_resume(long envelope) {
    (void)envelope;
    return prism_move_err(PRISM_MOVE_UNSUPPORTED);
}
