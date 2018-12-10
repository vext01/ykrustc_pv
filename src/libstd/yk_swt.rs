// Copyright 2018 King's College London.
// Created by the Software Development Team <http://soft-dev.org/>.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/// Software tracing support for Yorick.

/// Records a location into the current trace.
#[cfg_attr(not(stage0), lang="yk_swt_record_loc")]
#[allow(unused_variables)]
pub fn record_loc(crate_hash: u64, def_idx: u32, bb_idx: u32) {
}
