// Copyright 2019 King's College London.
// Created by the Software Development Team <http://soft-dev.org/>.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use ::ops::Drop;
use libc;

/// Represents a MIR location.
#[repr(C)]
#[derive(Debug)]
pub struct MirLoc {
    /// Unique identifier for the crate.
    pub crate_hash: u64,
    /// The definition index.
    pub def_idx: u32,
    /// The basic block index.
    pub bb_idx: u32,
}

/// Wraps the raw C trace buffer and exposes a more "Rusty" interface to it.
#[derive(Debug)]
#[allow(dead_code)]
pub struct SWTrace {
    /// A heap allocated array of `MirLoc` structs.
    buf: *mut MirLoc,
    /// The number of items in the above array.
    len: usize,
}

impl SWTrace {
    /// Returns the number of MIR locations recorded in the trace.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns the location at index `idx` or `None` if the index is out of bounds.
    pub fn loc<'a>(&'a self, idx: usize) -> &'a MirLoc {
        if idx >= self.len {
            panic!("software trace index out of bounds: len={}, idx={}", self.len, idx);
        } else {
            if idx > isize::max_value() as usize {
                panic!("index too large for ptr arithmetic");
            }
            unsafe { &*self.buf.offset(idx as isize) }
        }
    }
}

impl Drop for SWTrace {
    fn drop(&mut self) {
        libc::free(self.buf);
    }
}

/// Start software tracing on the current thread. The current thread must not already be tracing.
#[cfg_attr(not(stage0), no_trace)]
pub fn start_tracing() {
    extern "C" { fn yk_swt_start_tracing_impl(); }
    unsafe { yk_swt_start_tracing_impl(); }
}

/// Stop software tracing and return the trace, or `None` if the trace was invalidated.
/// The current thread must already be tracing.
#[cfg_attr(not(stage0), no_trace)]
pub fn stop_tracing() -> Option<SWTrace> {
    let len: usize = 0;

    extern "C" { fn yk_swt_stop_tracing_impl(ret_len: &usize) -> *mut MirLoc; }
    let buf = unsafe { yk_swt_stop_tracing_impl(&len) };

    if buf.is_null() {
        None
    } else {
        Some(SWTrace { buf, len })
    }
}
