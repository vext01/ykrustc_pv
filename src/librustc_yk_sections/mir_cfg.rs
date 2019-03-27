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
use std::fs::{self, File};
use rustc_yk_link::YkExtraLinkObject;
use std::io::Write;
use std::error::Error;
use std::cell::{Cell, RefCell};
use std::mem::size_of;
use std::ops::Drop;
use rustc_data_structures::bit_set::BitSet;
use rustc_data_structures::indexed_vec::{IndexVec, Idx};
use rustc_data_structures::graph::dominators::Dominators;
use ykpack;
use ykpack::LocalIndex as TirLocal;

const SECTION_NAME: &'static str = ".yk_tir";
pub const TMP_EXT: &'static str = "yk_tir.tmp";

/// Describes how to output TIR.
pub enum TirOutput<'a> {
    /// Dumps the TIR to a binary format for inclusion into the executable.
    Binary {
        /// The encoder used to serialise packs.
        enc: ykpack::Encoder<'a>,
        /// The path to the temporary file. So we can delete it later.
        path: PathBuf,
    },
    /// Dump the TIR to textual format for testing or debugging.
    /// This is used when rustc is run with `--emit yk-tir`.
    Textual {
        /// Where to write the textual representation.
        file: &'a mut File,
    },
}

impl<'a> TirOutput<'a> {
    pub fn new_binary(file: &'a mut File, path: PathBuf) -> Self {
        TirOutput::Binary {
            enc: ykpack::Encoder::from(file),
            path,
        )
    }

    pub fn new_textual(file: &'a mut File) -> Self {
        TirOutput::Textual { file }
    }

    fn write_pack(&mut self, pack: ykpack::Pack) -> Result<(), Box<dyn Error>> {
        match self {
            TirOutput::Binary{ref mut enc, ..} => enc.serialise(pack)?,
            TirOutput::Textual{ref mut file, ..} => write!(file, "{}", pack)?,
        }
        Ok(())
    }

    /// Obtain the resulting linkable ELF object, if applicable.
    fn linkable(self) -> Option<YkExtraLinkObject> {
        match self {
            TirOutput::Binary{ref path, ..} => Some(YkExtraLinkObject::new(path, SECTION_NAME)),
            _ => None,
        }
    }
}

impl <'a> Drop for TirOutput<'a> {
    fn drop(&mut self) {
        match self {
            TirOutput::Binary{path, ..} => {
                // By the time we drop, we will have converted the raw binary file into ELF where
                // upon it is no longer needed.
                fs::remove_file(&path).expect("couldn't remove TIR temp file");
            },
            _ => (),
        }
    }
}

/// A conversion context holds the state needed to perform the conversion to (pre-SSA) TIR.
struct ConvCx<'a, 'tcx, 'gcx> {
    /// The compiler's god struct. Needed for queries etc.
    tcx: &'a TyCtxt<'a, 'tcx, 'gcx>,
    /// Maps TIR variables to their definition sites.
    def_sites: RefCell<Vec<BitSet<BasicBlock>>>,
    /// Monotonically increasing number used to give TIR variables a unique ID.
    next_tir_var: Cell<TirLocal>,
    /// A mapping from MIR variables to TIR variables.
    var_map: RefCell<IndexVec<Local, Option<TirLocal>>>,
    /// The number of blocks in the MIR (and therefore in the TIR).
    num_blks: usize,
}

impl<'a, 'tcx, 'gcx> ConvCx<'a, 'tcx, 'gcx> {
    fn new(tcx: &'a TyCtxt<'a, 'tcx, 'gcx>, mir: &Mir<'tcx>) -> Self {
        let var_map = IndexVec::new();

        Self {
            tcx,
            def_sites: RefCell::new(Vec::new()),
            next_tir_var: Cell::new(0),
            var_map: RefCell::new(var_map),
            num_blks: mir.basic_blocks().len(),
        }
    }

    /// Returns a guaranteed unique TIR variable index.
    fn new_tir_var(&self) -> TirLocal {
        let var_idx = self.next_tir_var.get();
        self.next_tir_var.set(var_idx + 1);
        var_idx
    }

    /// Get the TIR variable for the specified MIR variable, creating a fresh variable if needed.
    fn tir_var(&self, local: Local) -> TirLocal {
        let local_u32 = local.as_u32();
        let mut var_map = self.var_map.borrow_mut();

        // Resize the backing Vec if necessary.
        // Vector indices are `usize`, but variable indices are `u32`, so converting from a
        // variable index to a vector index is always safe if a `usize` can express all `u32`s.
        assert!(size_of::<usize>() >= size_of::<u32>());
        if var_map.len() <= local_u32 as usize {
            var_map.resize(local_u32.checked_add(1).unwrap() as usize, None);
        }

        var_map[local].unwrap_or_else(|| {
            let var_idx = self.new_tir_var();
            var_map[local] = Some(var_idx);
            var_idx
        })
    }

    fn def_sites(self) -> Vec<BitSet<BasicBlock>> {
        self.def_sites.into_inner()
    }

    /// Add `bb` as a definition site of the TIR variable `var`.
    fn push_def_site(&self, bb: BasicBlock, var: TirLocal) {
        let mut sites = self.def_sites.borrow_mut();
        // This conversion is safe because `var` was generated by `tir_var()` which guarantees that
        // a `u32` can fit in a `usize`.
        let var_usize = var as usize;
        if sites.len() <= var_usize {
            // By performing the checked addition on the original `u32` we ensure the indices in
            // `self.def_sites` are never outside of what a `u32` can express.
            sites.resize(var.checked_add(1).unwrap() as usize,
                BitSet::new_empty(self.num_blks));
        }
        sites[var_usize].insert(bb);
    }
}

/// Converts and serialises the specified DefIds, returning an linkable ELF object.
pub fn generate_tir<'a, 'tcx, 'gcx>(
    tcx: &'a TyCtxt<'a, 'tcx, 'gcx>, def_ids: &DefIdSet, mut output: TirOutput)
    -> Result<Option<YkExtraLinkObject>, Box<dyn Error>> {

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

            output.write_pack(phied_pack)?;
        }
    }

    Ok(output.linkable())
}

/// Lazy computation of dominance frontiers.
///
/// See p404 of the 2nd edition of the Appel book mentioned above.
///
/// Since the frontier of one node may depend on the frontiers of other nodes (depending upon their
/// relationships), we cache the frontiers so as to avoid computing things more than once.
struct DominatorFrontiers<'a, 'tcx> {
    /// The MIR we are working on.
    mir: &'a Mir<'tcx>,
    /// The dominators of the above MIR.
    doms: Dominators<BasicBlock>,
    /// The dominance frontier cache. Lazily computed. `None` means as-yet uncomputed.
    df: IndexVec<BasicBlock, Option<BitSet<BasicBlock>>>,
    /// The number of MIR (and thus TIR) blocks.
    num_blks: usize,
}

impl<'a, 'tcx> DominatorFrontiers<'a, 'tcx> {
    fn new(mir: &'a Mir<'tcx>) -> Self {
        let num_blks = mir.basic_blocks().len();
        let df = IndexVec::from_elem_n(None, num_blks);

        Self {
            mir,
            doms: mir.dominators(),
            df,
            num_blks: mir.basic_blocks().len(),
        }
    }

    /// Get the dominance frontier of the given basic block, computing it if we have not already
    /// done so. Since computing the frontiers for a full CFG requests the same frontiers
    /// repeatedly, the requested frontier (and its dependencies) are inserted into a cache to
    /// avoid duplicate computations.
    fn frontier(&mut self, n: BasicBlock) -> &BitSet<BasicBlock> {
        if self.df[n].is_none() {
            // We haven't yet computed dominator frontiers for this node. Compute them.
            let mut s: BitSet<BasicBlock> = BitSet::new_empty(self.num_blks);

            // Append what Appel calls 'DF_{local}[n]'.
            for y in self.mir.basic_blocks()[n].terminator().successors() {
                if self.doms.immediate_dominator(*y) != n {
                    s.insert(*y);
                }
            }

            // The second stage of the algorithm needs the children nodes in the dominator tree.
            let mut children = Vec::new();
            for (b, _) in self.mir.basic_blocks().iter_enumerated() {
                let b = BasicBlock::from_u32(b.as_u32());
                if self.doms.is_dominated_by(b, n) && b != n {
                    children.push(b);
                    // Force the frontier of `b` into the cache (`self.df`). Doing this here avoids
                    // a simultaneous mutable + immutable borrow of `self` in the final stage of
                    // the algorithm.
                    self.frontier(b);
                }
            }

            // Append what Appel calls `DF_{up}[c]` for each dominator tree child `c` of `n`.
            for c in children {
                for w in self.df[c].as_ref().unwrap().iter() {
                    if n == w || !self.doms.is_dominated_by(w, n) {
                        s.insert(w);
                    }
                }
            }
            self.df[n] = Some(s);
        }

        self.df[n].as_ref().unwrap()
    }
}

/// This struct deals with inserting PHI nodes into the initial pre-SSA TIR pack.
///
/// See the bottom of p406 of the 2nd edition of the Appel book mentioned above.
struct PhiInserter<'a, 'tcx> {
    mir: &'a Mir<'tcx>,
    pack: ykpack::Pack,
    def_sites: Vec<BitSet<BasicBlock>>,
}

impl<'a, 'tcx> PhiInserter<'a, 'tcx> {
    fn new(mir: &'a Mir<'tcx>, pack: ykpack::Pack, def_sites: Vec<BitSet<BasicBlock>>) -> Self {
        Self {
            mir,
            pack,
            def_sites,
        }
    }

    /// Insert PHI nodes, returning the mutated pack.
    fn pack(mut self) -> ykpack::Pack {
        let mut df = DominatorFrontiers::new(self.mir);
        let num_tir_vars = self.def_sites.len();

        // We first need a mapping from block to the variables it defines. Appel calls this
        // `A_{orig}`. We can derive this from our definition sites.
        let (a_orig, num_tir_blks) = {
            let ykpack::Pack::Mir(ykpack::Mir{ref blocks, ..}) = self.pack;
            let num_tir_blks = blocks.len();

            let mut a_orig: IndexVec<BasicBlock, BitSet<TirLocal>> =
                IndexVec::from_elem_n(BitSet::new_empty(num_tir_vars), num_tir_blks);
            for (a, def_blks) in self.def_sites.iter().enumerate() {
                for bb in def_blks.iter() {
                    // `def_sites` is guaranteed to have at most `u32::max_value()` items.
                    a_orig[bb].insert(a as u32);
                }
            }
            (a_orig, num_tir_blks)
        };

        let mut a_phi: Vec<BitSet<TirLocal>> = Vec::with_capacity(num_tir_blks);
        a_phi.resize(num_tir_blks, BitSet::new_empty(num_tir_vars));
        // We don't need the elements of `def_sites` again past this point, so we can take them out
        // of `def_sites` with a draining iterator and mutate in-place.
        for (a, mut w) in self.def_sites.drain(..).enumerate() {
            while !w.is_empty() {
                let n = bitset_pop(&mut w);
                for y in df.frontier(n).iter() {
                    let y_usize = y.index();
                    // `self.def_sites` is guaranteed to only contain indices expressible by `u32`.
                    let a_u32 = a as u32;
                    if !a_phi[y_usize].contains(a_u32) {
                        // Appel would insert the Phi node here. We use a second pass to keep the
                        // borrow checker happy (self is already borrowed in this loop).
                        a_phi[y_usize].insert(a_u32);
                        if !a_orig[y].contains(a_u32) {
                            w.insert(y);
                        }
                    }
                }
            }
        }

        // `a_phi` now tells use where to insert PHI nodes.
        {
            let ykpack::Pack::Mir(ykpack::Mir{ref mut blocks, ..}) = self.pack;
            for (bb, mut bb_data) in blocks.iter_mut().enumerate() {
                for a in a_phi[bb].iter() {
                    let lhs = ykpack::Place::Local(a);
                    let num_preds = self.mir.predecessors_for(BasicBlock::new(bb)).len();
                    let rhs_vars = (0..num_preds).map(|_| lhs.clone()).collect();
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

        ykpack::Pack::Mir(ykpack::Mir::new(ser_def_id, ccx.tcx.item_path_str(**def_id), ser_blks))
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
impl<'tcx> ToPack<ykpack::BasicBlock> for
    (&ConvCx<'_, 'tcx, '_>, BasicBlock, &BasicBlockData<'tcx>)
{
    fn to_pack(&mut self) -> ykpack::BasicBlock {
        let (ccx, bb, bb_data) = self;
        let ser_stmts = bb_data.statements.iter().map(|stmt| (*ccx, *bb, stmt).to_pack());
        ykpack::BasicBlock::new(ser_stmts.collect(),
            (*ccx, bb_data.terminator.as_ref().unwrap()).to_pack())
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
            Place::Base(PlaceBase::Local(local)) => ykpack::Place::Local(ccx.tir_var(*local)),
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

/// At the time of writing, you can't pop from a `BitSet`.
fn bitset_pop<T>(s: &mut BitSet<T>) -> T where T: Eq + Idx + Clone {
    let e = s.iter().next().unwrap().clone();
    let removed = s.remove(e);
    debug_assert!(removed);
    e
}
