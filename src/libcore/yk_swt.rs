// Copyright 2018 King's College London.
// Created by the Software Development Team <http://soft-dev.org/>.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern "Rust" {
    #[cfg_attr(not(stage0), lang="yk_swt_rec_loc")]
    fn yk_swt_rec_loc(crate_hash: u64, def_idx: u32, bb: u32);
}

/// Wrapper function to call the Yorick software trace recorder.
/// The code for the recorder in in libstd, which is not a proper dependency of libcore. We use a
/// "weak language item" to make the call possible, but we need a wrapper because we cannot use
/// weak language items in call terminators in the MIR.
#[allow(dead_code, unused_variables)] // Used only indirectly in a MIR pass.
#[cfg_attr(not(stage0), lang="yk_swt_rec_loc_wrap")]
fn yk_swt_rec_loc_wrap(crate_hash: u64, def_idx: u32, bb: u32) {
    unsafe { yk_swt_rec_loc(crate_hash, def_idx, bb) };
}

