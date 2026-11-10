/*
 * Portability shims for compiling sylvan (and its Lace scheduler) for WebAssembly.
 * Force-included into every translation unit of the wheel by wasm/packaging/setup.py.
 */
#ifndef AMAYA_WASM_COMPAT_H
#define AMAYA_WASM_COMPAT_H

/* lace.h defines mfence() as x86 inline assembly unless it is already defined. */
#define mfence() __atomic_thread_fence(__ATOMIC_SEQ_CST)

/*
 * sylvan_tls.h uses __thread only on ELF targets. Elsewhere it keeps thread-local values in pthread keys
 * cast through void*, which truncates the 64-bit values sylvan stores there on wasm32 - e.g. the
 * (uint64_t)-1 "no region yet" marker of claim_data_bucket() in sylvan_table.c becomes 0xffffffff, and node
 * allocation then runs past the end of the table bitmap. WebAssembly supports __thread, so provide the ELF
 * variant of the macros and skip sylvan_tls.h (its include guard is TLS_H).
 */
#define TLS_H
#define DECLARE_THREAD_LOCAL(name, type) __thread type name
#define INIT_THREAD_LOCAL(name)
#define SET_THREAD_LOCAL(name, value) name = value
#define LOCALIZE_THREAD_LOCAL(name, type)

#endif
