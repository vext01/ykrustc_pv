// Copyright 2018 King's College London.
// Created by the Software Development Team <http://soft-dev.org/>.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// FIXME
#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]
#![allow(unused_mut)]


/// CFG serialiser for Yorick.
/// We use an external crate 'ykpack' to do this.

use rustc::ty::TyCtxt;

use rustc::hir::def_id::DefId;
use rustc::mir::{Mir, TerminatorKind, Operand, Constant, BasicBlock};
use rustc::ty::{TyS, TyKind, Const, LazyConst};
use rustc::util::nodemap::DefIdSet;
use std::path::PathBuf;
use std::fs::File;
use rustc_yk_link::YkExtraLinkObject;
use std::fs;
use ykpack;

const MIR_CFG_SECTION_NAME: &'static str = ".yk_mir_cfg";

/// Serialises the control flow for the given `DefId`s into a ELF object file and returns a handle
/// for linking.
pub fn emit_mir_cfg_section<'a, 'tcx, 'gcx>(
    tcx: &'a TyCtxt<'a, 'tcx, 'gcx>, def_ids: &DefIdSet, exe_filename: PathBuf)
    -> YkExtraLinkObject {

    // Serialise the MIR into a file whose name is derived from the output binary. The filename
    // must be the same between builds of the same binary for the reproducible build tests to pass.
    let mut mir_path: String = exe_filename.to_str().unwrap().to_owned();
    mir_path.push_str(".ykcfg");
    let mut fh = File::create(&mir_path).unwrap();
    let mut enc = ykpack::Encoder::from(&mut fh);

    // To satisfy the reproducible build tests, the CFG must be written out in a deterministic
    // order, thus we sort the `DefId`s first.
    let mut sorted_def_ids: Vec<&DefId> = def_ids.iter().collect();
    sorted_def_ids.sort();

    for def_id in sorted_def_ids {
        if tcx.is_mir_available(*def_id) {
            let pack = process_mir(tcx, def_id, tcx.optimized_mir(*def_id));
            // FIXME error handling.
            enc.serialise(pack).unwrap();
        }
    }

    // Now graft the resulting blob file into an object file.
    let path = PathBuf::from(mir_path);
    let ret = YkExtraLinkObject::new(&path, MIR_CFG_SECTION_NAME);
    fs::remove_file(path).unwrap();

    ret
}

/// Build a list of blocks to serialise for the given MIR.
fn process_mir(tcx: &TyCtxt, def_id: &DefId, mir: &Mir) -> ykpack::Pack {
    let mut ser_blks = Vec::new();

    for (bb, maybe_bb_data) in mir.basic_blocks().iter_enumerated() {
        let bb_data = maybe_bb_data.terminator.as_ref().unwrap();
        let ser_term = match bb_data.kind {
            TerminatorKind::Goto{target: target_bb} =>
                ykpack::Terminator::Goto{target_bb: u32::from(target_bb)},
            TerminatorKind::SwitchInt{targets: ref target_bbs, ..} => {
                let target_bbs = target_bbs.iter().map(|bb| u32::from(*bb)).collect();
                ykpack::Terminator::SwitchInt{target_bbs}
            },
            TerminatorKind::Resume => ykpack::Terminator::Resume,
            TerminatorKind::Abort => ykpack::Terminator::Abort,
            TerminatorKind::Return => ykpack::Terminator::Return,
            TerminatorKind::Unreachable => ykpack::Terminator::Unreachable,
            TerminatorKind::Drop{target: target_bb, unwind: unwind_bb, ..} =>
                ykpack::Terminator::Drop{
                    target_bb: u32::from(target_bb),
                    unwind_bb: unwind_bb.map(|bb| u32::from(bb)),
                },
            TerminatorKind::DropAndReplace{target: target_bb, unwind: unwind_bb, ..} =>
                ykpack::Terminator::DropAndReplace{
                    target_bb: u32::from(target_bb),
                    unwind_bb: unwind_bb.map(|bb| u32::from(bb)),
                },
            TerminatorKind::Call{ref func, cleanup: cleanup_bb, ..} => {
                let ser_oper = if let Operand::Constant(box Constant {
                    literal: LazyConst::Evaluated(Const {
                        ty: &TyS {
                            sty: TyKind::FnDef(target_def_id, _substs), ..
                        }, ..
                    }), ..
                }, ..) = func {
                    // A statically known call target.
                    let ser_target = ykpack::DefId::new(
                        tcx.crate_hash(target_def_id.krate).as_u64(),
                        target_def_id.index.as_raw_u32());
                    ykpack::CallOperand::Fn(ser_target)
                } else {
                    // FIXME -- implement other callables.
                    ykpack::CallOperand::Unknown
                };
                ykpack::Terminator::Call{
                    operand: ser_oper,
                    cleanup_bb: cleanup_bb.map(|bb| u32::from(bb)),
                }
            },
            TerminatorKind::Assert{target: target_bb, cleanup: cleanup_bb, ..} =>
                ykpack::Terminator::Assert{
                    target_bb: u32::from(target_bb),
                    cleanup_bb: cleanup_bb.map(|bb| u32::from(bb)),
                },
            TerminatorKind::Yield{resume: resume_bb, drop: drop_bb, ..} =>
                ykpack::Terminator::Yield{
                    resume_bb: u32::from(resume_bb),
                    drop_bb: drop_bb.map(|bb| u32::from(bb)),
                },
            TerminatorKind::GeneratorDrop => ykpack::Terminator::GeneratorDrop,
            TerminatorKind::FalseEdges{real_target: real_target_bb, ..} =>
                ykpack::Terminator::FalseEdges{real_target_bb: u32::from(real_target_bb)},
            TerminatorKind::FalseUnwind{real_target: real_target_bb, ..} =>
                ykpack::Terminator::FalseUnwind{real_target_bb: u32::from(real_target_bb)},
        };

        // FIXME -- Serialise block statements.
        ser_blks.push(ykpack::BasicBlock::new(Vec::new(), ser_term));
    }

    let ser_def_id =
        ykpack::DefId::new(tcx.crate_hash(def_id.krate).as_u64(), def_id.index.as_raw_u32());
    ykpack::Pack::Mir(ykpack::Mir::new(ser_def_id, ser_blks))
}
