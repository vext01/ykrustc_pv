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

#![allow(unused_variables,dead_code,unused_imports)]
//#![feature(vec_resize_default)]

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
use rustc_yk_link::YkExtraLinkObject;
use std::fs;
use std::io::Write;
use std::error::Error;
use std::cell::{Cell, RefCell};
use std::mem::size_of;
use std::convert::TryFrom;
use rustc_data_structures::bit_set::BitSet;
use rustc_data_structures::indexed_vec::{IndexVec, Idx};
use rustc_data_structures::graph::dominators::{Dominators, DominatorFrontiers};
use rustc_data_structures::graph::WithSuccessors;
use ykpack;
use ykpack::LocalIndex as TirLocal;
use ykpack::BasicBlockIndex as TirBasicBlockIndex;
use rustc_data_structures::fx::FxHashSet;

const SECTION_NAME: &'static str = ".yk_tir";
const TMP_EXT: &'static str = ".yk_tir.tmp";

/// Describes how to output MIR.
pub enum TirMode {
    /// Write MIR into an object file for linkage. The inner path should be the path to the main
    /// executable (from this we generate a filename for the resulting object).
    Default(PathBuf),
    /// Write MIR in textual form the specified path.
    TextDump(PathBuf),
}

static BOTTOM: u32 = 0;
static PRE_SSA_RET_VAR: u32 = 1;

/// A conversion context holds the state needed to perform the conversion to (pre-SSA) TIR.
struct ConvCx<'a, 'tcx, 'gcx> {
    /// The compiler's god struct. Needed for queries etc.
    tcx: &'a TyCtxt<'a, 'tcx, 'gcx>,
    /// Maps TIR variables to their definition sites.
    def_sites: RefCell<Vec<BitSet<BasicBlock>>>,
    /// Maps each block to the variable it defines. This is what Appel calls `A_{orig}`.
    block_defines: RefCell<IndexVec<BasicBlock, FxHashSet<TirLocal>>>,
    /// Monotonically increasing number used to give TIR variables a unique ID.
    next_tir_var: Cell<TirLocal>,
    /// A mapping from MIR variables to TIR variables.
    var_map: RefCell<IndexVec<Local, Option<TirLocal>>>,
    /// The number of blocks in the MIR (and therefore in the TIR).
    num_blks: usize,
    /// FIXME
    mir_args: Vec<Local>,
    //num_args: usize,
}

impl<'a, 'tcx, 'gcx> ConvCx<'a, 'tcx, 'gcx> {
    fn new(tcx: &'a TyCtxt<'a, 'tcx, 'gcx>, mir: &Mir<'tcx>) -> Self {
        let num_blks = mir.basic_blocks().len();
        //let mut next_tir_var = 0;

        // Return value has to be in a place where we can find it later.
        //var_map.push(0);

        // FIXME document invariant.
        // let args_iter = mir.args_iter();
        // let num_args = args_iter.clone().count();
        // let mut var_map = IndexVec::from([None; num_args]);
        // for mir_arg in args_iter {
        //     var_map[mir_arg] = next_tir_var;
        //     next_tir_var += 1;
        // }
        //

        Self {
            tcx,
            def_sites: RefCell::new(Vec::new()),
            block_defines: RefCell::new(IndexVec::from_elem_n(FxHashSet::default(), num_blks)),
            next_tir_var: Cell::new(2), // Zero is always the return value in pre-SSA TIR. FIXME say why.
            var_map: RefCell::new(IndexVec::from_elem_n(Some(PRE_SSA_RET_VAR), 1)), // Pre-filled with return value.
            num_blks: num_blks,
            mir_args: mir.args_iter().collect(), // FIXME could be optimised.
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

    /// Finalise the conversion context, returning the definition sites, the block defines mapping,
    /// and the number of TIR variables.
    fn done(self) -> (Vec<BitSet<BasicBlock>>, IndexVec<BasicBlock, FxHashSet<TirLocal>>, u32) {
        (self.def_sites.into_inner(), self.block_defines.into_inner(), self.next_tir_var.into_inner())
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

        // Also push into the inverse mapping (blocks to defined vars).
        self.block_defines.borrow_mut()[bb].insert(var);
    }
}

/// Writes TIR to file for the specified DefIds, possibly returning a linkable ELF object.
pub fn generate_tir<'a, 'tcx, 'gcx>(
    tcx: &'a TyCtxt<'a, 'tcx, 'gcx>, def_ids: &DefIdSet, mode: TirMode)
    -> Result<Option<YkExtraLinkObject>, Box<dyn Error>>
{
    let tir_path = do_generate_tir(tcx, def_ids, &mode)?;
    match mode {
        TirMode::Default(_) => {
            // In this case the file at `tir_path` is a raw binary file which we use to make an
            // object file for linkage.
            let obj = YkExtraLinkObject::new(&tir_path, SECTION_NAME);
            // Now we have our object, we can remove the temp file. It's not the end of the world
            // if we can't remove it, so we allow this to fail.
            fs::remove_file(tir_path).ok();
            Ok(Some(obj))
        },
        TirMode::TextDump(_) => {
            // In this case we have no object to link, and we keep the file at `tir_path` around,
            // as this is the text dump the user asked for.
            Ok(None)
        }
    }
}

fn do_generate_tir<'a, 'tcx, 'gcx>(
    tcx: &'a TyCtxt<'a, 'tcx, 'gcx>, def_ids: &DefIdSet, mode: &TirMode)
    -> Result<PathBuf, Box<dyn Error>>
{
    let (tir_path, mut default_file, textdump_file) = match mode {
        TirMode::Default(exe_path) => {
            // The default mode of operation dumps TIR in binary format to a temporary file, which
            // is later converted into an ELF object. Note that the temporary file name must be the
            // same between builds for the reproducible build tests to pass.
            let mut tir_path = exe_path.clone();
            tir_path.set_extension(TMP_EXT);
            let mut file = File::create(&tir_path)?;
            (tir_path, Some(file), None)
        },
        TirMode::TextDump(dump_path) => {
            // In text dump mode we just write lines to a file and we don't need an encoder.
            let mut file = File::create(&dump_path)?;
            (dump_path.clone(), None, Some(file))
        },
    };

    let mut enc = match default_file {
        Some(ref mut f) => Some(ykpack::Encoder::from(f)),
        _ => None,
    };

    // To satisfy the reproducible build tests, the CFG must be written out in a deterministic
    // order, thus we sort the `DefId`s first.
    let mut sorted_def_ids: Vec<&DefId> = def_ids.iter().collect();
    sorted_def_ids.sort();

    for def_id in sorted_def_ids {
        info!("Def Id: {:?}", def_id);
        if tcx.is_mir_available(*def_id) {
            info!("generating TIR for {:?}", def_id);

            let mir = tcx.optimized_mir(*def_id);
            let doms = mir.dominators();
            let ccx = ConvCx::new(tcx, mir);

            info!("generate pre-ssa TIR");
            let mut pack = (&ccx, def_id, tcx.optimized_mir(*def_id)).to_pack();
            {
                let ykpack::Pack::Mir(ykpack::Mir{ref mut blocks, ..}) = pack;
                let (def_sites, block_defines, num_tir_vars) = ccx.done();

                info!("insert PHIs");
                insert_phis(blocks, &doms, mir, def_sites, block_defines);

                info!("rename vars");
                RenameCx::new(num_tir_vars).rename_all(&doms, &mir, blocks);
            }

            info!("write");
            if let Some(ref mut e) = enc {
                e.serialise(pack)?;
            } else {
                write!(textdump_file.as_ref().unwrap(), "{}", pack)?;
            }
        }
    }

    if let Some(e) = enc {
        // Now finalise the encoder and convert the resulting blob file into an object file for
        // linkage into the main binary. Once we've converted, we no longer need the original file.
        e.done()?;
    }

    Ok(tir_path)
}

/// Insert PHI nodes into the initial pre-SSA TIR pack.
///
/// Algorithm reference:
/// Bottom of p406 of 'Modern Compiler Implementation in Java (2nd ed.)' by Andrew Appel.
fn insert_phis(blocks: &mut Vec<ykpack::BasicBlock>, doms: &Dominators<BasicBlock>,
               mir: &Mir, mut def_sites: Vec<BitSet<BasicBlock>>,
               a_orig: IndexVec<BasicBlock, FxHashSet<TirLocal>>) {
    let df = DominatorFrontiers::new(mir, &doms);
    let num_tir_vars = def_sites.len();
    let num_tir_blks = a_orig.len();

    let mut a_phi: Vec<BitSet<TirLocal>> = Vec::with_capacity(num_tir_blks);
    a_phi.resize(num_tir_blks, BitSet::new_empty(num_tir_vars));

    // We don't need the elements of `def_sites` again past this point, so we can take them out
    // of `def_sites` with a draining iterator and mutate in-place.
    for (a, mut w) in def_sites.drain(..).enumerate() {
        while !w.is_empty() {
            let n = bitset_pop(&mut w);
            for y in df.frontier(n).iter() {
                let y_usize = y.index();
                // `def_sites` is guaranteed to only contain indices expressible by `u32`.
                let a_u32 = a as u32;
                if !a_phi[y_usize].contains(a_u32) {
                    a_phi[y_usize].insert(a_u32);
                    if !a_orig[y].contains(&a_u32) {
                        // The assertion in `tir_var()` has already checked the cast is safe.
                        insert_phi(&mut blocks[y_usize], a as u32, mir.predecessors_for(y).len());
                        w.insert(y);
                    }
                }
            }
        }
    }
}

type TirStatementIndex = usize;

#[derive(Clone, Debug)]
struct ReachLoc {
    bb: TirBasicBlockIndex,
    si: TirStatementIndex,
}

/// This is the variable renaming scheme outlined in Algorithm 19.7 on p409 of the Appel book. We
/// do the renaming in-place. Appel computes a <original variable name, SSA version> pair for each
/// new variable definition. For simplicity and efficiency we use a plain old integer. This just
/// means we have one counter instead of many.
struct RenameCx {
    next_fresh_var: TirLocal,
    reaching_defs: Vec<TirLocal>,
    def_sites: Vec<Option<ReachLoc>>,
}

//const DUMMY_REACH_LOC: ReachLoc = ReachLoc {bb: 0, si: 0};

impl RenameCx {
    fn new(num_tir_vars: u32) -> Self {
        Self {
            next_fresh_var: 1,
            // We will use at least as many variables as there are in the incoming TIR.
            // FIXME plus one
            reaching_defs: vec![BOTTOM; num_tir_vars as usize],
            def_sites: vec![None; num_tir_vars as usize],
        }
    }

    fn fresh_var(&mut self) -> TirLocal {
        let ret = self.next_fresh_var;
        self.next_fresh_var.checked_add(1);
        if self.reaching_defs.len() < usize::try_from(self.next_fresh_var).unwrap() {
            self.reaching_defs.resize_with(usize::try_from(self.next_fresh_var).unwrap(), || BOTTOM);
        }
        ret
    }

    fn add_def_site(&mut self, var: TirLocal, loc: ReachLoc) {
        let required_sz = usize::try_from(var.checked_add(1).unwrap()).unwrap();
        if self.def_sites.len() < required_sz {
            self.def_sites.resize_with(required_sz, || None)
        }
        let var_usize = usize::try_from(var).unwrap();
        self.def_sites[var_usize] = Some(loc);
    }

    fn rename_all(mut self, doms: &Dominators<BasicBlock>, mir: &Mir,
        blks: &mut Vec<ykpack::BasicBlock>)
    {
        info!("rename all");
        info!("blks:");

        for (i, b) in blks.iter().enumerate() {
            info!("\nbb{}:\n{:?}", i, b);
        }

        self.rename(doms, mir, blks, 0); // We start with the entry block and it ripples down.
    }

    fn rename(&mut self, doms: &Dominators<BasicBlock>, mir: &Mir,
        blks: &mut Vec<ykpack::BasicBlock>, bb: TirBasicBlockIndex)
    {
        info!("rename for {:?}", bb);

        let bb_usize = usize::try_from(bb).unwrap();
        {
            info!("block {}: {}", bb, blks[bb_usize]);
        }

        {
            for (i_idx, i) in &mut blks[bb_usize].stmts.iter_mut().enumerate() {
                info!("\nstatement {}: {}", i_idx, i);
                let i_loc = ReachLoc{bb: bb, si: i_idx};

                info!("PHASE: non-phi uses");
                if !i.is_phi() {
                    for v in i.uses_vars_mut().iter_mut() {
                        info!("uses var {:?}", v);
                        self.update_reaching_def(doms, **v, &i_loc);
                        **v = self.reaching_defs[usize::try_from(**v).unwrap()];
                    }
                }

                info!("PHASE: defs");
                for v in i.defs_vars_mut().iter_mut() {
                    info!("defs var={:?}", v);
                    self.update_reaching_def(doms, **v, &i_loc);

                    let vp = self.fresh_var();
                    self.add_def_site(vp, i_loc.clone());
                    info!("fresh_var={:?}", vp);

                    let vp_usize = usize::try_from(vp).unwrap();
                    let v_usize = usize::try_from(**v).unwrap();

                    **v = vp;
                    self.reaching_defs[vp_usize] = self.reaching_defs[v_usize];
                    self.reaching_defs[v_usize] = vp;
                }
            }
        }

        info!("PHASE: successors for {:?}: {:?}", bb, mir.successors(BasicBlock::from_u32(bb)));
        for succ in mir.successors(BasicBlock::from_u32(bb)) {
            let succ_usize = succ.as_usize(); //usize::try_from(succ).unwrap();
            for (phi_idx, phi) in &mut blks[succ_usize].stmts.iter_mut().enumerate()
                .filter(|(_, i)| i.is_phi())
            {
                let phi_loc = ReachLoc{bb: succ.as_u32(), si: phi_idx};
                for v in phi.uses_vars_mut() {
                    self.update_reaching_def(doms, *v, &phi_loc);
                    *v = self.reaching_defs[usize::try_from(*v).unwrap()];
                }
            }
        }

        info!("PHASE: recurse for {:?}: {:?}", bb, doms.immediately_dominates(BasicBlock::from_u32(bb)));
        info!("DOM TREE: {:?}", doms.all_immediate_dominators());
        for next_bb in doms.immediately_dominates(BasicBlock::from_u32(bb)) {
            self.rename(doms, mir, blks, next_bb.as_u32());
        }
    }

    fn update_reaching_def(&mut self, doms: &Dominators<BasicBlock>, v: TirLocal, i: &ReachLoc) {
        info!("update reaching: {}, {:?}", v, i);
        let v_usize = usize::try_from(v).unwrap();
        info!("unwrapped1");

        let final_r = {
            let mut r = &self.reaching_defs[v_usize];
            info!("loop pre: {:?}", r);
            while !(*r == BOTTOM || Self::def_dominates(doms, &self.def_sites[v_usize].as_ref().expect("None def site"), i)) {
                info!("top of loop: {:?}", r);
                info!("reaching_defs: {:?}", self.reaching_defs);
                let old_r = r;
                r = &self.reaching_defs[usize::try_from(*r).unwrap()];
                info!("unwrapped3");
                assert!(r != old_r, "detected cycle in update_reaching_def");
            };
            *r
        };

        info!("done updating defs. new one is: {:?}", final_r);
        self.reaching_defs[v_usize] = final_r;
        info!("donex");
    }

    // Does a definition at `r` dominate the instruction `i`?
    fn def_dominates(doms: &Dominators<BasicBlock>, r: &ReachLoc, i: &ReachLoc) -> bool {
        info!("def_dominates: {:?}, {:?}", r, i);
        info!("{:?}", doms.all_immediate_dominators());
        if r.bb == i.bb {
            // If the locations are in the same block, `r` dominates if it comes before `i`.
            info!("{:?}", r.si <= i.si);
            r.si <= i.si
        } else {
            // The locations are in different blocks, so ask the CFG which block dominates.
            info!("{:?}", doms.is_dominated_by(BasicBlock::from_u32(i.bb), BasicBlock::from_u32(r.bb)));
            doms.is_dominated_by(BasicBlock::from_u32(i.bb), BasicBlock::from_u32(r.bb))
        }
    }
}

fn insert_phi(block: &mut ykpack::BasicBlock, var: TirLocal, arity: usize) {
    let lhs = ykpack::Place::Local(var);
    let rhs_vars = (0..arity).map(|_| lhs.clone()).collect();
    let rhs = ykpack::Rvalue::Phi(rhs_vars);
    block.stmts.insert(0, ykpack::Statement::Assign(lhs, rhs));
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
            TerminatorKind::Return => ykpack::Terminator::Return(PRE_SSA_RET_VAR),
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
        let mut ser_stmts = Vec::new();

        // FIXME comment
        // if bb.as_u32() == 0 {
        //     ser_stmts.push(ykpack::Statement::DefArg(1)); // FIXME say why
        //     for a in &ccx.mir_args {
        //         ser_stmts.push(ykpack::Statement::DefArg(ccx.tir_var(*a)));
        //     }
        // }

        ser_stmts.extend(bb_data.statements.iter().map(|stmt| (*ccx, *bb, stmt).to_pack()));
        ykpack::BasicBlock::new(ser_stmts, (*ccx, bb_data.terminator.as_ref().unwrap()).to_pack())
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
