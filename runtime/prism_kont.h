/* Native kont metadata accessors.
 *
 * Generated LLVM modules embed a NUL-terminated `prism_native_kont_table`
 * symbol in a dedicated section. The runtime exposes it through a stable C ABI
 * so native suspend/resume can parse the table without knowing object-file
 * section details. */
#ifndef PRISM_KONT_H
#define PRISM_KONT_H

#include "prism_internal.h"

typedef struct {
    const void *fn;
    const char *symbol;
    const char *def_hash;
    const char *core_name;
} PrismNativeKontPtr;

typedef struct {
    const void *pc;
    const char *symbol;
    long symbol_len;
    const char *def_hash;
    long def_hash_len;
    const char *core_name;
    long core_name_len;
    unsigned long pc_offset;
    long has_pc_offset;
    const long *values;
    long value_count;
    long has_values;
} PrismNativeKontFrame;

typedef struct {
    const char *def_hash;
    long def_hash_len;
    const char *core_name;
    long core_name_len;
    long arity;
    const char *slots;
    long slots_len;
} PrismNativeKontState;

const char *prism_native_kont_table_bytes(void);
long prism_native_kont_table_len(void);
const char *prism_native_kont_state_map_bytes(void);
long prism_native_kont_state_map_len(void);
long prism_native_kont_frame_mode(void);
void prism_native_kont_enter(const char *symbol, long arity);
void prism_native_kont_arg(long index, long value);
void prism_native_kont_tailcall(const char *symbol, long arity);
void prism_native_kont_leave(void);
long prism_native_kont_shadow_depth(void);
long prism_native_kont_state_lookup(const char *symbol, PrismNativeKontState *out);
long prism_native_kont_scheme(const char **scheme, long *scheme_len);
long prism_native_kont_bundle(const char **bundle, long *bundle_len);
long prism_native_kont_lookup(const char *symbol,
                              const char **def_hash,
                              long *def_hash_len,
                              const char **core_name,
                              long *core_name_len);
long prism_native_kont_lookup_ptr(const void *fn,
                                  const char **def_hash,
                                  long *def_hash_len,
                                  const char **core_name,
                                  long *core_name_len);
long prism_native_kont_lookup_pc(const void *pc,
                                 const char **def_hash,
                                 long *def_hash_len,
                                 const char **core_name,
                                 long *core_name_len);
long prism_native_kont_capture_frames(PrismNativeKontFrame *out, long cap);
long prism_native_kont_capture_manifest(char *out, long out_cap, long frame_cap);
long prism_native_kont_resume_entry(const char *symbol,
                                    const long *values,
                                    long value_count,
                                    long *out);

#endif /* PRISM_KONT_H */
