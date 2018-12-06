// Copyright 2018 King's College London.
// Created by the Software Development Team <http://soft-dev.org/>.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/// Software tracing support for Yorick.

use ::cell::RefCell;

/// Describes a MIR basic block location.
#[derive(Debug)]
pub struct MirLoc {
    crate_hash: u64,
    def_idx: u32,
    bb_idx: u32,
}

thread_local! {
    /// Storage for a software trace.
    static SWT_TRACE: RefCell<Vec<MirLoc>> = RefCell::new(Vec::new());
}

/// Records a location into the current trace.
#[cfg_attr(not(stage0), lang="yk_swt_record_loc")]
pub fn record_loc(crate_hash: u64, def_idx: u32, bb_idx: u32) {
    eprintln!("yk_swt_record_loc: {}, {}, {}", crate_hash, def_idx, bb_idx);
    SWT_TRACE.with(|rc| {
        rc.borrow_mut().push(MirLoc { crate_hash, def_idx, bb_idx });
    });
}

/// Empties the trace buffer, returning the contents.
pub fn stop_tracing() -> Vec<MirLoc> {
    SWT_TRACE.with(|rc| {
        rc.replace(Vec::new())
    })
}
