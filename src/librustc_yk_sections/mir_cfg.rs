// Copyright 2018 King's College London.
// Created by the Software Development Team <http://soft-dev.org/>.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(unused_imports, unused_variables, dead_code)]

//! MIR to TIR converter/serialiser.
//!
//! We convert Rust's MIR into our own IR we call "TIR" (tracing IR), which is then stashed away in
//! an ELF section so that the JIT runtime can use it later.
//!
//!  * Unlike MIR, TIR is stored in SSA form.
//!  * We preserve the MIR block structure.
//!
//! Serialisation itself is performed by an external library: ykpack.

use rustc::ty::TyCtxt;

use rustc::hir::def_id::DefId;
use rustc::mir::{
    Mir, TerminatorKind, Operand, Constant, StatementKind, BasicBlock, BasicBlockData, Terminator,
    Place, Rvalue, Statement, Successors
};
use rustc::ty::{TyS, TyKind, Const, LazyConst};
use rustc::util::nodemap::DefIdSet;
use std::path::PathBuf;
use std::fs::File;
use rustc_yk_link::YkExtraLinkObject;
use std::fs;
use std::error::Error;
use rustc_data_structures::indexed_vec::{Idx, IndexVec};
use rustc_data_structures::graph::dominators::Dominators;
use ykpack;

const SECTION_NAME: &'static str = ".yk_cfg";

/// A conversion context holds the state needed to perform the conversion.
struct ConvCx<'a, 'tcx, 'gcx> {
    /// The compiler's god struct. Needed for queries etc.
    tcx: &'a TyCtxt<'a, 'tcx, 'gcx>,
    //// The index of the next TIR variable.
    //next_var: usize,
    //frontier: Dominators,
}

//struct DominatorTree {
//    //bb: BasicBlock,
//    //children: Box<Vec<DominatorTree>>,
//    imm_doms: IndexVec<BasicBlock, BasicBlock>,
//}

//impl DominatorTree {
//    fn new(mir: &Mir) -> Self {
//        let imm_doms = IndexVec::new();
//        let doms = mir.dominators();
//        for bb in mir.basic_blocks() {
//            doms.push(DominatorTree::find_immed_doms(bb, &doms));
//        }
//        Self { imm_doms }
//    }
//
//    fn find_immed_doms(bb: BasicBlock, doms: &Dominators) -> BasicBlock {
//        bb_doms = doms.
//    }
//}

/// Converts and serialises the specified DefIds, returning an linkable ELF object.
pub fn generate_yorick_bytecode<'a, 'tcx, 'gcx>(
    tcx: &'a TyCtxt<'a, 'tcx, 'gcx>, def_ids: &DefIdSet, exe_filename: PathBuf)
    -> Result<YkExtraLinkObject, Box<dyn Error>> {

    // The filename must be the same between builds for the reproducible build tests to pass.
    let mut mir_path: String = exe_filename.to_str().unwrap().to_owned();
    mir_path.push_str(".ykcfg");
    let mut fh = File::create(&mir_path)?;
    let mut enc = ykpack::Encoder::from(&mut fh);

    // To satisfy the reproducible build tests, the CFG must be written out in a deterministic
    // order, thus we sort the `DefId`s first.
    let mut sorted_def_ids: Vec<&DefId> = def_ids.iter().collect();
    sorted_def_ids.sort();

    for def_id in sorted_def_ids {
        if tcx.is_mir_available(*def_id) {
            let mir = tcx.optimized_mir(*def_id);
            let ccx = ConvCx { tcx }; //, next_var: 0, dominators: mir.dominators };

            // Get an initial TIR (not yet in SSA form).
            let pack = (&ccx, def_id, tcx.optimized_mir(*def_id)).to_pack();

            // Compute the dominance frontier for each basic block.
            let fronts = get_dom_fronts(mir);
            // FIXME

            // Add PHI nodes.
            // FIXME

            // Put the finalised TIR to disk.
            enc.serialise(pack)?;
        }
    }
    enc.done()?;

    // Now graft the resulting blob file into an object file.
    let path = PathBuf::from(mir_path);
    let ret = YkExtraLinkObject::new(&path, SECTION_NAME);
    fs::remove_file(path)?;

    Ok(ret)
}

// FIXME rename
struct DominatorFrontiers<'a, 'tcx> {
    mir: &'a Mir<'tcx>,
    doms: Dominators<BasicBlock>,
    df: IndexVec<BasicBlock, Option<Vec<BasicBlock>>>,
}

impl<'a, 'tcx> DominatorFrontiers<'a, 'tcx> {
    fn new(mir: &'a Mir<'tcx>) -> Self {
        let num_blks = mir.basic_blocks().len();
        let mut df = IndexVec::with_capacity(num_blks);
        for _ in 0..num_blks {
            df.push(None);
        }

        Self {
            mir,
            doms: mir.dominators(),
            df,
        }
    }

    /// Compute the dominance frontier. This is the algorithm from Andrew W. Appel's book "Modern
    /// Compiler Implementation in Java (2nd edition)", Chapter 19: Static Single-Assignment.
    /// Upstream rust already provides a way to get the dominators and immediate dominators (and
    /// hence also the dominator tree), so we just have to compute the frontiers.
    fn get(&mut self, n: BasicBlock) -> &Vec<BasicBlock> {
        if self.df[n].is_none() {
            // We haven't yet computed dominator frontiers for this node. Compute them.
            let mut s: Vec<BasicBlock> = Vec::new();

            // Append what Appel calls 'DF_{local}[n]'.
            for y in self.mir.basic_blocks()[n].terminator().successors() {
                if self.doms.immediate_dominator(*y) != n {
                    s.push(*y);
                }
            }

            // The second stage of the algorithm needs the children nodes in the dominator tree.
            let mut children = Vec::new();
            for (b, _) in self.mir.basic_blocks().iter_enumerated() {
                let b = BasicBlock::from_u32(b.as_u32());
                if self.doms.is_dominated_by(b, n) && b != n {
                    children.push(b);
                }
            }

            // Compute what Appel calls `DF_{up}[c]` for each dominator tree child `c` of `n`.
            let mut df_up_cs = Vec::new();
            for c in children {
                for w in self.get(c) {
                    if n == *w || !self.doms.is_dominated_by(*w, n) {
                        df_up_cs.push(*w);
                    }
                }
            }
            
            s.extend(df_up_cs);

            self.df[n] = Some(s);
        }

        self.df[n].as_ref().unwrap()
    }
}

// FIXME, no need to force the fronts -- let it be lazy.
fn get_dom_fronts(mir: &Mir) { //-> IndexVec<BasicBlock, Vec<BasicBlock>> {
    let mut dcx = DominatorFrontiers::new(mir);
    for (bb, _) in mir.basic_blocks().iter_enumerated() {
        dcx.get(bb);
    }
}

/// The trait for converting MIR data structures into a bytecode packs.
trait ToPack<T> {
    fn to_pack(&self) -> T;
}

impl<'tcx> ToPack<ykpack::Pack> for (&ConvCx<'_, 'tcx, '_>, &DefId, &Mir<'tcx>) {
    fn to_pack(&self) -> ykpack::Pack {
        let (ccx, def_id, mir) = self;

        let mut ser_blks = Vec::new();
        for bb_data in mir.basic_blocks() {
            ser_blks.push((*ccx, bb_data).to_pack());
        }

        let ser_def_id = ykpack::DefId::new(
            ccx.tcx.crate_hash(def_id.krate).as_u64(), def_id.index.as_raw_u32());

        ykpack::Pack::Mir(ykpack::Mir::new(ser_def_id, ser_blks))
    }
}

impl ToPack<ykpack::DefId> for (&ConvCx<'_, '_, '_>, &DefId) {
    fn to_pack(&self) -> ykpack::DefId {
        let (ccx, def_id) = self;
        ykpack::DefId {
            crate_hash: ccx.tcx.crate_hash(def_id.krate).as_u64(),
            def_idx: def_id.index.as_raw_u32(),
        }
    }
}

impl<'tcx> ToPack<ykpack::Terminator> for (&ConvCx<'_, 'tcx, '_>, &Terminator<'tcx>) {
    fn to_pack(&self) -> ykpack::Terminator {
        let (ccx, term) = self;

        match term.kind {
            TerminatorKind::Goto{target: target_bb}
            | TerminatorKind::FalseEdges{real_target: target_bb, ..}
            | TerminatorKind::FalseUnwind{real_target: target_bb, ..} =>
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
            TerminatorKind::Call{ref func, cleanup: cleanup_bb, ref destination, .. } => {
                let ser_oper = if let Operand::Constant(box Constant {
                    literal: LazyConst::Evaluated(Const {
                        ty: &TyS {
                            sty: TyKind::FnDef(target_def_id, _substs), ..
                        }, ..
                    }), ..
                }, ..) = func {
                    // A statically known call target.
                    ykpack::CallOperand::Fn((*ccx, &target_def_id).to_pack())
                } else {
                    // FIXME -- implement other callables.
                    ykpack::CallOperand::Unknown
                };

                let ret_bb = destination.as_ref().map(|(_, bb)| u32::from(*bb));
                ykpack::Terminator::Call{
                    operand: ser_oper,
                    cleanup_bb: cleanup_bb.map(|bb| u32::from(bb)),
                    ret_bb: ret_bb,
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
        }
    }
}

impl<'tcx> ToPack<ykpack::BasicBlock> for (&ConvCx<'_, 'tcx, '_>, &BasicBlockData<'tcx>) {
    fn to_pack(&self) -> ykpack::BasicBlock {
        let (ccx, bb_data) = self;

        // FIXME. Implement block contents (currently an empty vector).
        // Unwrap here can't fail, as MIR terminators can only be None during construction.
        ykpack::BasicBlock::new(Vec::new(), (*ccx, bb_data.terminator.as_ref().unwrap()).to_pack())
    }
}

impl<'tcx> ToPack<ykpack::Statement> for (&ConvCx<'_, 'tcx, '_>, &Statement<'tcx>) {
    fn to_pack(&self) -> ykpack::Statement {
        let (ccx, ref stmt) = self;

        match stmt.kind {
            StatementKind::Assign(ref place, ref rval) => {
                let lhs = (*ccx, place).to_pack();
                let rhs = (*ccx, &**rval).to_pack();
                ykpack::Statement::Assign(lhs, rhs)
            },
            _ => ykpack::Statement::Unimplemented,
        }
    }
}

impl<'tcx> ToPack<ykpack::Place> for (&ConvCx<'_, 'tcx, '_>, &Place<'tcx>) {
    fn to_pack(&self) -> ykpack::Place {
        let (ccx, place) = self;

        match *place {
            Place::Local(local_idx) => ykpack::Place::Local(u32::from(local_idx.as_u32())),
            _ => ykpack::Place::Unimplemented, // FIXME
        }
    }
}

impl<'tcx> ToPack<ykpack::Rvalue> for (&ConvCx<'_, 'tcx, '_>, &Rvalue<'tcx>) {
    fn to_pack(&self) -> ykpack::Rvalue {
        let (ccx, rval) = self;

        match *rval {
            Rvalue::Use(Operand::Move(place)) => ykpack::Rvalue::Place((*ccx, place).to_pack()),
            _ => ykpack::Rvalue::Unimplemented, // FIXME
        }
    }
}
