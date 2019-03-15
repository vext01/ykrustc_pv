// Copyright 2018 King's College London.
// Created by the Software Development Team <http://soft-dev.org/>.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! This module converts MIR into Yorick TIR (Tracing IR). TIR is more suitable for the run-time
//! tracer: TIR (unlike MIR) is in SSA form (but it does preserve MIR's block structure).
//!
//! Serialisation itself is performed by an external library: ykpack.

use rustc::ty::TyCtxt;

use rustc::hir::def_id::DefId;
use rustc::mir::{
    Mir, TerminatorKind, Operand, Constant, StatementKind, BasicBlock, BasicBlockData, Terminator,
    Place, Rvalue, Statement, Local, PlaceBase
};
use rustc::ty::{TyS, TyKind, Const, LazyConst};
use rustc::util::nodemap::DefIdSet;
use std::path::PathBuf;
use std::fs::File;
use std::convert::TryFrom;
use rustc_yk_link::YkExtraLinkObject;
use std::fs;
use std::error::Error;
use std::cell::{Cell, RefCell};
use rustc_data_structures::indexed_vec::{IndexVec, Idx};
use rustc_data_structures::graph::dominators::Dominators;
use ykpack;

const SECTION_NAME: &'static str = ".yk_tir";
const TMP_EXT: &'static str = ".yk_tir.tmp";

type TirVarIndex = u32;

/// A conversion context holds the state needed to perform the conversion to (pre-SSA) TIR.
struct ConvCx<'a, 'tcx, 'gcx> {
    /// The compiler's god struct. Needed for queries etc.
    tcx: &'a TyCtxt<'a, 'tcx, 'gcx>,
    /// The definition sites of TIR variable in terms of basic blocks.
    def_sites: RefCell<Vec<Vec<BasicBlock>>>,
    /// The next TIR variable index to be issued.
    next_tir_var: Cell<TirVarIndex>,
    /// A mapping from MIR variables to TIR variables.
    var_map: RefCell<IndexVec<Local, Option<TirVarIndex>>>,
}

impl<'a, 'tcx, 'gcx> ConvCx<'a, 'tcx, 'gcx> {
    fn new(tcx: &'a TyCtxt<'a, 'tcx, 'gcx>, _mir: &Mir<'tcx>) -> Self {
        let var_map = IndexVec::new();

        Self {
            tcx,
            def_sites: RefCell::new(Vec::new()),
            next_tir_var: Cell::new(0),
            var_map: RefCell::new(var_map),
        }
    }

    /// Issues a fresh TIR variable index.
    fn next_tir_var(&self) -> TirVarIndex {
        let var_idx = self.next_tir_var.get();
        self.next_tir_var.set(var_idx + 1);
        var_idx
    }

    /// Get the TIR variable corresponding with the MIR variable, creating a fresh one if needed.
    fn get_tir_var(&self, local: Local) -> TirVarIndex {
        let local_u32 = local.as_u32();
        let mut var_map = self.var_map.borrow_mut();

        // Resize the backing Vec if necessary.
        if var_map.len() <= usize::try_from(local_u32).unwrap() {
            var_map.resize(usize::try_from(local_u32 + 1).unwrap(), None);
        }

        let v = match var_map[local] {
            None => {
                // Make a new variable.
                let var_idx = self.next_tir_var();
                var_map[local] = Some(var_idx);
                var_idx
            }
            Some(tvar) => tvar,
        };

        v
    }

    fn def_sites(self) -> Vec<Vec<BasicBlock>> {
        self.def_sites.into_inner()
    }

    /// Add `bb` as a definition site of the TIR variable `var`.
    fn push_def_site(&self, bb: BasicBlock, var: TirVarIndex) {
        let mut sites = self.def_sites.borrow_mut();
        if sites.len() <= usize::try_from(var).unwrap() {
            sites.resize((var + 1) as usize, Vec::new());
        }
        sites[usize::try_from(var).unwrap()].push(bb);
    }
}

/// Converts and serialises the specified DefIds, returning an linkable ELF object.
pub fn generate_tir<'a, 'tcx, 'gcx>(
    tcx: &'a TyCtxt<'a, 'tcx, 'gcx>, def_ids: &DefIdSet, exe_filename: PathBuf)
    -> Result<YkExtraLinkObject, Box<dyn Error>> {

    // The filename must be the same between builds for the reproducible build tests to pass.
    let mut mir_path: String = exe_filename.to_str().unwrap().to_owned();
    mir_path.push_str(TMP_EXT);
    let mut fh = File::create(&mir_path)?;
    let mut enc = ykpack::Encoder::from(&mut fh);

    // To satisfy the reproducible build tests, the CFG must be written out in a deterministic
    // order, thus we sort the `DefId`s first.
    let mut sorted_def_ids: Vec<&DefId> = def_ids.iter().collect();
    sorted_def_ids.sort();

    for def_id in sorted_def_ids {
        if tcx.is_mir_available(*def_id) {
            info!("generating TIR for {:?}", def_id);

            let mir = tcx.optimized_mir(*def_id);
            let ccx = ConvCx::new(tcx, mir);

            // Get an initial TIR (not yet in SSA form).
            let pre_ssa_pack = (&ccx, def_id, tcx.optimized_mir(*def_id)).to_pack();

            // Add PHI nodes.
            let phied_pack = PhiInserter::new(mir, pre_ssa_pack, ccx.def_sites()).pack();

            // FIXME - rename variables with fresh SSA names.

            // Put the finalised TIR to disk.
            enc.serialise(phied_pack)?;
        }
    }
    enc.done()?;

    // Now graft the resulting blob file into an object file.
    let path = PathBuf::from(mir_path);
    let ret = YkExtraLinkObject::new(&path, SECTION_NAME);
    fs::remove_file(path)?;

    Ok(ret)
}

/// Lazy computation of dominance frontiers.
///
/// See Page 404 of the 2nd edition of the Appel book mention above.
///
/// Since the frontier of one node may depend on the frontiers of other nodes (depending upon their
/// relationships), we cache the frontiers so as to avoid computing things more than once.
struct DominatorFrontiers<'a, 'tcx> {
    /// The MIR we are working on.
    mir: &'a Mir<'tcx>,
    /// The dominators of the above MIR.
    doms: Dominators<BasicBlock>,
    /// The dominance frontiers. Lazily computed. None means as-yet uncomputed.
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

    /// Get the dominance frontier of the given basic block, computing it if we have not already
    /// done so.
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
                    // Force the frontier of `b` into `self.df`. Doing this here avoids a
                    // simultaneous mutable + immutable borrow of `self` in the final stage of the
                    // algorithm.
                    self.get(b);
                }
            }

            // Compute what Appel calls `DF_{up}[c]` for each dominator tree child `c` of `n`.
            let mut df_up_cs = Vec::new();
            for c in children {
                for w in self.df[c].as_ref().unwrap() {
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

/// This struct deals with inserting PHI nodes into the initial pre-SSA TIR pack.
///
/// See the bottom of Page 406 of the 2nd edition of the Appel book mention above.
struct PhiInserter<'a, 'tcx> {
    mir: &'a Mir<'tcx>,
    pack: ykpack::Pack,
    def_sites: Vec<Vec<BasicBlock>>,
}

impl<'a, 'tcx> PhiInserter<'a, 'tcx> {
    fn new(mir: &'a Mir<'tcx>, pack: ykpack::Pack, def_sites: Vec<Vec<BasicBlock>>) -> Self {
        Self {
            mir,
            pack,
            def_sites,
        }
    }

    /// Insert PHI nodes, returning the mutated pack.
    fn pack(mut self) -> ykpack::Pack {
        let mut df = DominatorFrontiers::new(self.mir);

        // We first need a mapping from block to the variables it defines. Appel calls this
        // `A_{orig}`. We can derive this from our definition sites.
        let (a_orig, num_blks) = {
            let ykpack::Pack::Mir(ykpack::Mir{ref blocks, ..}) = self.pack;
            let mut a_orig: IndexVec<BasicBlock, Vec<TirVarIndex>> = IndexVec::with_capacity(blocks.len());
            a_orig.resize(blocks.len(), Vec::default());
            for (a, def_blks) in self.def_sites.iter().enumerate() {
                for bb in def_blks {
                    a_orig[*bb].push(u32::try_from(a).unwrap())
                }
            }

            (a_orig, blocks.len())
        };

        let mut a_phi: Vec<Vec<TirVarIndex>> = Vec::with_capacity(num_blks);
        a_phi.resize(num_blks, Vec::new());
        for (a, def_sites) in self.def_sites.iter().enumerate() {
            let mut w = def_sites.clone();
            while w.len() > 0 {
                let n = w.pop().unwrap();
                for y in df.get(n) {
                    let y_usize = y.index();
                    let a_u32 = u32::try_from(a).unwrap();
                    if !a_phi[y_usize].contains(&a_u32) {
                        a_phi[y_usize].push(a_u32);
                    }
                    if !a_orig[*y].contains(&a_u32) {
                        w.push(*y);
                    }
                }
            }
        }

        // `a_phi` now tells use where to insert PHI nodes.
        {
            let ykpack::Pack::Mir(ykpack::Mir{ref mut blocks, ..}) = self.pack;
            for (bb, mut bb_data) in blocks.iter_mut().enumerate() {
                for a in &a_phi[bb] {
                    let lhs = ykpack::Place::Local(*a);
                    let num_preds = self.mir.predecessors_for(BasicBlock::new(bb)).len();
                    let rhs_vars = (0..num_preds).map(|_| Box::new(lhs.clone())).collect();
                    let rhs = ykpack::Rvalue::Phi(rhs_vars);
                    bb_data.stmts.insert(0, ykpack::Statement::Assign(lhs, rhs));
                }
            }
        }

        self.pack
    }
}

/// The trait for converting MIR data structures into a bytecode packs.
trait ToPack<T> {
    fn to_pack(&mut self) -> T;
}

/// Mir -> Pack
impl<'tcx> ToPack<ykpack::Pack> for (&ConvCx<'_, 'tcx, '_>, &DefId, &Mir<'tcx>) {
    fn to_pack(&mut self) -> ykpack::Pack {
        let (ccx, def_id, mir) = self;

        let mut ser_blks = Vec::new();
        for (bb, bb_data) in mir.basic_blocks().iter_enumerated() {
            ser_blks.push((*ccx, bb, bb_data).to_pack());
        }

        let ser_def_id = ykpack::DefId::new(
            ccx.tcx.crate_hash(def_id.krate).as_u64(), def_id.index.as_raw_u32());

        ykpack::Pack::Mir(ykpack::Mir::new(ser_def_id, ser_blks))
    }
}

/// DefId -> Pack
impl ToPack<ykpack::DefId> for (&ConvCx<'_, '_, '_>, &DefId) {
    fn to_pack(&mut self) -> ykpack::DefId {
        let (ccx, def_id) = self;
        ykpack::DefId {
            crate_hash: ccx.tcx.crate_hash(def_id.krate).as_u64(),
            def_idx: def_id.index.as_raw_u32(),
        }
    }
}

/// Terminator -> Pack
impl<'tcx> ToPack<ykpack::Terminator> for (&ConvCx<'_, 'tcx, '_>, &Terminator<'tcx>) {
    fn to_pack(&mut self) -> ykpack::Terminator {
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

/// BasicBlockData -> Pack
impl<'tcx> ToPack<ykpack::BasicBlock> for (&ConvCx<'_, 'tcx, '_>, BasicBlock, &BasicBlockData<'tcx>) {
    fn to_pack(&mut self) -> ykpack::BasicBlock {
        let (ccx, bb, bb_data) = self;
        let ser_stmts = bb_data.statements.iter().map(|stmt| (*ccx, *bb, stmt).to_pack());
        ykpack::BasicBlock::new(ser_stmts.collect(), (*ccx, bb_data.terminator.as_ref().unwrap()).to_pack())
    }
}

/// Statement -> Pack
impl<'tcx> ToPack<ykpack::Statement> for (&ConvCx<'_, 'tcx, '_>, BasicBlock, &Statement<'tcx>) {
    fn to_pack(&mut self) -> ykpack::Statement {
        let (ccx, bb, ref stmt) = self;

        match stmt.kind {
            StatementKind::Assign(ref place, ref rval) => {
                let lhs = (*ccx, place).to_pack();
                let rhs = (*ccx, &**rval).to_pack();
                if let ykpack::Place::Local(tvar) = lhs {
                    ccx.push_def_site(*bb, tvar);
                }
                ykpack::Statement::Assign(lhs, rhs)
            },
            _ => ykpack::Statement::Unimplemented,
        }
    }
}

/// Place -> Pack
impl<'tcx> ToPack<ykpack::Place> for (&ConvCx<'_, 'tcx, '_>, &Place<'tcx>) {
    fn to_pack(&mut self) -> ykpack::Place {
        let (ccx, place) = self;

        match place {
            Place::Base(PlaceBase::Local(local)) => ykpack::Place::Local(ccx.get_tir_var(*local)),
            _ => ykpack::Place::Unimplemented, // FIXME
        }
    }
}

/// Rvalue -> Pack
impl<'tcx> ToPack<ykpack::Rvalue> for (&ConvCx<'_, 'tcx, '_>, &Rvalue<'tcx>) {
    fn to_pack(&mut self) -> ykpack::Rvalue {
        let (ccx, rval) = self;

        match *rval {
            Rvalue::Use(Operand::Move(place)) => ykpack::Rvalue::Place((*ccx, place).to_pack()),
            _ => ykpack::Rvalue::Unimplemented, // FIXME
        }
    }
}
