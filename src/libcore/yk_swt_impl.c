// Copyright 2019 King's College London.
// Created by the Software Development Team <http://soft-dev.org/>.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#include <stdint.h>
#include <stdlib.h>
#include <err.h>
#include <stdbool.h>
#include <stdatomic.h>

struct mir_loc {
    uint64_t crate_hash;
    uint32_t def_idx;
    uint32_t bb_idx;
};

#define TL_TRACE_INIT_CAP       1024
#define TL_TRACE_REALLOC_CAP    1024

// The trace buffer.
static __thread struct mir_loc *trace_buf = NULL;
// The number of elements in the trace buffer.
static __thread size_t trace_buf_len = 0;
// The allocation capacity of the trace buffer (in elements).
static __thread size_t trace_buf_cap = 0;
// Is the current thread tracing?
static __thread bool tracing = false;
// This flag is a lock of sorts, used to detect whether we have re-entered the
// trace recorder function from the same thread. This can happen if a signal
// interrupts this function and the handler brings us back in to it again.
// Arguably the user is mad to do such a thing in a signal handler, but it's
// best to detect this case, than to carry on with an invalid trace.
static __thread volatile atomic_flag in_recorder = ATOMIC_FLAG_INIT;

// Start tracing on the current thread.
// A new trace buffer is allocated and MIR locations are written into it. The
// current thread must not already be tracing.
void
yk_swt_start_tracing_impl() {
    if (tracing) {
        errx(EXIT_FAILURE, "%s: thread already tracing", __func__);
    }

    trace_buf = calloc(TL_TRACE_INIT_CAP, sizeof(struct mir_loc));
    if (trace_buf == NULL) {
        err(EXIT_FAILURE, "%s: calloc: ", __func__);
    }

    trace_buf_cap = TL_TRACE_INIT_CAP;
    tracing = true;
}

// Record a location into the trace buffer if tracing is enabled on the current thread.
// Returns `false` if the reentrant check fails. In this case the in-situ trace should
// be considered invalid. If all is well, returns `true`.
bool
yk_swt_rec_loc_impl(uint64_t crate_hash, uint32_t def_idx, uint32_t bb_idx)
{
    if (atomic_flag_test_and_set_explicit(&in_recorder,
        memory_order_acquire)) {
        return false;
    }

    // If tracing is not currently active, then we do nothing.
    if (!tracing) {
        goto done;
    }

    // Check if we need more space and reallocate if necessary.
    if (trace_buf_len == trace_buf_cap) {
        if (trace_buf_cap >= SIZE_MAX - TL_TRACE_REALLOC_CAP) {
            errx(EXIT_FAILURE, "%s: trace capacity would overflow", __func__);
        }
        size_t new_cap = trace_buf_cap + TL_TRACE_REALLOC_CAP;

        if (new_cap > SIZE_MAX / sizeof(struct mir_loc)) {
            errx(EXIT_FAILURE, "%s: new buffer size would overflow", __func__);
        }
        size_t new_size = new_cap * sizeof(struct mir_loc);

        trace_buf = realloc(trace_buf, new_size);
        if (trace_buf == NULL) {
            err(EXIT_FAILURE, "%s: realloc: ", __func__);
        }

        trace_buf_cap = new_cap;
    }

    struct mir_loc loc = { crate_hash, def_idx, bb_idx };
    trace_buf[trace_buf_len] = loc;
    trace_buf_len ++;

done:
    atomic_flag_clear_explicit(&in_recorder, memory_order_release);
    return true;
}


// Stop tracing on the current thread.
// The current thread must already be tracing. The trace buffer is returned
// and the number of locations it holds is written to `*ret_trace_len`. It is the
// responsibility of the caller to free the trace buffer.
struct mir_loc *
yk_swt_stop_tracing_impl(size_t *ret_trace_len) {
    if (!tracing) {
        errx(EXIT_FAILURE, "%s: thread not tracing", __func__);
    }

    // We hand ownership of the trace to Rust now. Rust is responsible for
    // freeing the trace.
    struct mir_loc *ret_trace = trace_buf;
    trace_buf = NULL;
    *ret_trace_len = trace_buf_len;

    tracing = false;
    trace_buf_len = 0;
    trace_buf_cap = 0;

    return ret_trace;
}
