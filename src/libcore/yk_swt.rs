// Copyright 2018 King's College London.
// Created by the Software Development Team <http://soft-dev.org/>.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/// The software trace recorder function.
/// This is implemented in C so that: the `yk_swt_calls` MIR pass doesn't see inside.
#[allow(dead_code)] // Used only indirectly in a MIR pass.
#[cfg_attr(not(stage0), lang="yk_swt_rec_loc")]
#[cfg_attr(not(stage0), no_trace)]
#[cfg(not(test))]
fn yk_swt_rec_loc(crate_hash: u64, def_idx: u32, bb_idx: u32) {
    extern "C" { fn yk_swt_rec_loc_impl(crate_hash: u64, def_idx: u32, bb_idx: u32); }
    unsafe { yk_swt_rec_loc_impl(crate_hash, def_idx, bb_idx); }
}

/// Invalidate the software trace, if one is being collected.
#[cfg_attr(not(stage0), no_trace)]
pub fn invalidate_trace() {
    extern "C" { fn yk_swt_invalidate_trace_impl(); }
    unsafe { yk_swt_invalidate_trace_impl(); }
}
