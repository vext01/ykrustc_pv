// Copyright 2019 King's College London.
// Created by the Software Development Team <http://soft-dev.org/>.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(yk_swt)]
#![feature(libc)]
#![feature(test)]

extern crate core;
extern crate libc;
extern crate test;

use std::yk_swt::{start_tracing, stop_tracing, SWTrace};
use std::thread;
use test::black_box;

// Run tracing in two separate threads with different work and check that the traces are different.
fn main() {
    let thr2 = thread::spawn(move || {
        start_tracing();
        let _ = work2();
        let raw_trace2 = stop_tracing().unwrap();
        let trace2 = trace_to_vec(&raw_trace2);
        trace2
    });

    start_tracing();
    black_box(work1());
    let raw_trace1 = stop_tracing().unwrap();
    let trace1 = trace_to_vec(&raw_trace1);

    let trace2 = thr2.join().unwrap();

    assert_ne!(trace1, trace2); // They should have been thread local.
}

// Copies a trace into a plain Rust Vec of tuples so we can compare them.
fn trace_to_vec(t: &SWTrace) -> Vec<(u64, u32, u32)> {
    let mut v = Vec::new();
    for i in 0..t.len() {
        let loc = t.loc(i);
        v.push((loc.crate_hash, loc.def_idx, loc.bb_idx));
    }
    v
}

#[inline(never)]
fn work1() -> u64{
    let mut res = 2000;
    for _ in 0..1000 {
        res -= 1;
    }
    res
}

#[inline(never)]
fn work2() -> u64{
    let mut res = 0;
    for i in 0..2000 {
        res += i + 1;
    }
    res
}
