/* Public interface of the standalone region (arena) allocator in
 * prism_arena.c. The substrate knows nothing about Prism cells, reference
 * counts, or handlers: it hands out aligned raw bytes with O(1) bulk
 * reclamation. The Prism-facing region policy (one region per `with_arena`
 * activation, the arena-owned refcount bit, escape promotion) lives in
 * prism_mem.c on top of exactly this interface. */
#ifndef PRISM_ARENA_H
#define PRISM_ARENA_H

#include <stddef.h>

typedef struct PrismArena PrismArena;

/* One arena with blocks of `block_size` usable bytes (0 = default). NULL only
 * on allocation failure. */
PrismArena *prism_arena_create(size_t block_size);

/* Bump `size` bytes at the natural (max_align_t) alignment. NULL only on
 * allocation failure or size/alignment overflow. */
void *prism_arena_alloc(PrismArena *a, size_t size);

/* Bump `size` bytes at `align`, a power of two (aborts otherwise: a bad
 * alignment is a codegen bug, never a recoverable condition). */
void *prism_arena_alloc_aligned(PrismArena *a, size_t size, size_t align);

/* Reclaim every object at once by rewinding the blocks, keeping the memory. */
void prism_arena_reset(PrismArena *a);

/* Return every block to the system and free the arena itself. */
void prism_arena_destroy(PrismArena *a);

/* Bytes handed out since creation or the last reset (stats and tests). */
size_t prism_arena_used(const PrismArena *a);

#endif /* PRISM_ARENA_H */
