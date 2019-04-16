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
//! The conversion happens in stages:
//!
//! 1) The MIR is lowered into an initial TIR.
//! 2) PHI nodes are inserted.
//! 3) Variables are renamed and we arrive at SSA TIR.
//! 4) The finalised SSA TIR is serialised using ykpack.

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

/// ⊥, i.e. undefined. We need a notion of undefined for SSA variable renaming step. Although it
/// would have been cleaner to have used `None` to represent this, it would also have meant we
/// ended up serialising lot's of `Some` values to TIR. At the end of the conversion, there will be
/// no `None`s, so serialising `Some`s would just waste space.
static BOTTOM: TirLocal = 0;

/// The pre-SSA return value variable. In the pre-SSA TIR, we need the return value to reside at an
/// easily locatable variable index so that later we can easily convert from MIR's implicit return
/// values, to TIR's explicit return values. In MIR, a return terminator implicitly returns
/// variable 0. Implicit return values are not possible for TIR, as the actual value we need to
/// return depends upon which SSA definition reaches the return terminator.
static PRE_SSA_RET_VAR: TirLocal = 1;

/// Describes how to output MIR.
pub enum TirMode {
    /// Write MIR into an object file for linkage. The inner path should be the path to the main
    /// executable (from this we generate a filename for the resulting object).
    Default(PathBuf),
    /// Write MIR in textual form the specified path.
    TextDump(PathBuf),
}

/// A conversion context holds the state needed to perform the conversion to the intial TIR.
struct ConvCx<'a, 'tcx, 'gcx> {
    /// The compiler's god struct. Needed for queries etc.
    tcx: &'a TyCtxt<'a, 'tcx, 'gcx>,
    /// Maps TIR variables to their definition sites.
    def_sites: RefCell<Vec<BitSet<BasicBlock>>>,
    /// Maps each block to the variable it defines. This is what Appel calls `A_{orig}`.
    block_defines: RefCell<IndexVec<BasicBlock, FxHashSet<TirLocal>>>,
    /// Monotonically increasing number used to give TIR variables a unique ID.
    /// Note that a couple of variables have a special meaning. See `BOTTOM` and `PRE_SSA_RET_VAR`.
    next_tir_var: Cell<TirLocal>,
    /// A mapping from MIR variables to TIR variables.
    var_map: RefCell<IndexVec<Local, Option<TirLocal>>>,
    /// The number of blocks in the MIR (and therefore in the TIR).
    num_blks: usize,
    /// The incoming MIR arguments.
    mir_args: Vec<Local>,
}

impl<'a, 'tcx, 'gcx> ConvCx<'a, 'tcx, 'gcx> {
    fn new(tcx: &'a TyCtxt<'a, 'tcx, 'gcx>, mir: &Mir<'tcx>) -> Self {
        let num_blks = mir.basic_blocks().len();
        Self {
            tcx,
            def_sites: RefCell::new(Vec::new()),
            block_defines: RefCell::new(IndexVec::from_elem_n(FxHashSet::default(), num_blks)),
            // Since we have reserved two variables (BOTTOM and PRE_SSA_RET_VAR), the next new TIR
            // variable we will give out is index two.
            next_tir_var: Cell::new(2),
            // The initial mapping ties the implicit MIR return value (0) to PRE_SSA_RET_VAR.
            var_map: RefCell::new(IndexVec::from_elem_n(Some(PRE_SSA_RET_VAR), 1)),
            num_blks: num_blks,
            mir_args: mir.args_iter().collect(),
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

    /// Finalise the conversion context, returning a tuple of:
    ///  - The definition sites.
    ///  - The block defines mapping.
    ///  - The next available TIR variable index.
    fn done(self) -> (Vec<BitSet<BasicBlock>>, IndexVec<BasicBlock, FxHashSet<TirLocal>>, u32) {
        (self.def_sites.into_inner(), self.block_defines.into_inner(),
            self.next_tir_var.into_inner())
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
        if tcx.is_mir_available(*def_id) {
            info!("Generating TIR for {:?}", def_id);

            let mir = tcx.optimized_mir(*def_id);
            let doms = mir.dominators();
            let ccx = ConvCx::new(tcx, mir);

            info!("Starting MIR:\n{:?}\n", mir);
            let mut pack = (&ccx, def_id, tcx.optimized_mir(*def_id)).to_pack();
            info!("Initial TIR:\n{}\n", pack);
            {
                let (def_sites, block_defines, next_tir_var) = ccx.done();

                {
                    let ykpack::Pack::Mir(ykpack::Mir{ref mut blocks, ..}) = pack;
                    insert_phis(blocks, &doms, mir, def_sites, block_defines);
                }
                info!("TIR with PHI nodes:\n{}\n", pack);

                {
                    let ykpack::Pack::Mir(ykpack::Mir{ref mut blocks, ..}) = pack;
                    RenameCx::new(next_tir_var).rename_all(&doms, &mir, blocks);
                }
                info!("Final SSA TIR:\n{}\n", pack.clone());
            }

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

fn insert_phi(block: &mut ykpack::BasicBlock, var: TirLocal, arity: usize) {
    let lhs = ykpack::Place::Local(var);
    let rhs_vars = (0..arity).map(|_| lhs.clone()).collect();
    let rhs = ykpack::Rvalue::Phi(rhs_vars);
    block.stmts.insert(0, ykpack::Statement::Assign(lhs, rhs));
}

/// A statement location.
#[derive(Clone, Debug)]
struct StmtLoc {
    /// The block containing the statement.
    bb: TirBasicBlockIndex,
    /// The statement index.
    si: usize,
}

/// This is the variable renaming algorithm from the "Static Single Assignment Book" by J. Singer
/// and others. See Section 3.1.3 on p33.
struct RenameCx {
    /// A counter used to give new TIR variables a unique identifier.
    next_fresh_var: TirLocal,
    /// Records chains of SSA variable definitions.
    reaching_defs: Vec<TirLocal>,
    /// Records the statement at which each SSA variable is defined.
    def_sites: Vec<Option<StmtLoc>>,
}

impl RenameCx {
    /// Make a new renaming context. To prevent variable naming clashes, the `next_fresh_var`
    /// argument should be one more than the last variable the previous step of the conversion
    /// created.
    fn new(next_fresh_var: u32) -> Self {
        // We start with space for the variables we know about so far. The vectors will grow as new
        // SSA variables are instantiated.
        let vec_size = usize::try_from(next_fresh_var).unwrap();
        Self {
            next_fresh_var,
            reaching_defs: vec![BOTTOM; vec_size],
            def_sites: vec![None; vec_size],
        }
    }

    /// Create a new SSA variable.
    fn fresh_var(&mut self) -> TirLocal {
        let ret = self.next_fresh_var;
        self.next_fresh_var = self.next_fresh_var.checked_add(1).unwrap();
        if self.reaching_defs.len() < usize::try_from(self.next_fresh_var).unwrap() {
            self.reaching_defs.resize_with(usize::try_from(self.next_fresh_var).unwrap(), || BOTTOM);
        }
        ret
    }

    /// Record the location at which an instruction is defined.
    fn record_def_site(&mut self, var: TirLocal, loc: StmtLoc) {
        let required_sz = usize::try_from(var.checked_add(1).unwrap()).unwrap();
        if self.def_sites.len() < required_sz {
            self.def_sites.resize_with(required_sz, || None)
        }
        let var_usize = usize::try_from(var).unwrap();
        self.def_sites[var_usize] = Some(loc);
    }

    /// Entry point for variable renaming.
    fn rename_all(mut self, doms: &Dominators<BasicBlock>, mir: &Mir,
        blks: &mut Vec<ykpack::BasicBlock>)
    {
        self.rename(doms, mir, blks, 0); // We start with the entry block and it ripples down.
    }

    /// Rename the variables in the block `bb`. This is recursive.
    fn rename(&mut self, doms: &Dominators<BasicBlock>, mir: &Mir,
        blks: &mut Vec<ykpack::BasicBlock>, bb: TirBasicBlockIndex)
    {
        let bb_usize = usize::try_from(bb).unwrap();
        let num_stmts = blks[bb_usize].stmts.len();

        {
            for (i_idx, i) in &mut blks[bb_usize].stmts.iter_mut().enumerate() {
                let i_loc = StmtLoc{bb: bb, si: i_idx};

                // Update variable uses in non-phi instructions.
                if !i.is_phi() {
                    for v in i.uses_vars_mut().iter_mut() {
                        self.update_reaching_def(doms, **v, &i_loc);
                        **v = self.reaching_defs[usize::try_from(**v).unwrap()];
                    }
                }

                // Update variable definitions in instructions (including PHIs this time).
                for v in i.defs_vars_mut().iter_mut() {
                    self.update_reaching_def(doms, **v, &i_loc);

                    let vp = self.fresh_var();
                    self.record_def_site(vp, i_loc.clone());

                    let vp_usize = usize::try_from(vp).unwrap();
                    let v_usize = usize::try_from(**v).unwrap();

                    **v = vp;
                    self.reaching_defs[vp_usize] = self.reaching_defs[v_usize];
                    self.reaching_defs[v_usize] = vp;
                }
            }

            // In the algorithm in the book, control flow constructs are assumed to be regular
            // statements, but in TIR control flow is performed by block terminators. The
            // terminators still contain variables which need to be renamed. You can think of this
            // as one extra iteration of the above loop, where we pretend the block terminator is a
            // statement on the end of the block. We know that terminators never define any new
            // variables, so we skip the step where new SSA variables may be introduced.
            let term = &mut blks[bb_usize].term;
            let term_loc = StmtLoc{bb: bb, si: num_stmts};
            for v in term.uses_vars_mut().iter_mut() {
                self.update_reaching_def(doms, **v, &term_loc);
                **v = self.reaching_defs[usize::try_from(**v).unwrap()];
            }
        }

        // Update variables used in PHI instructions in immediate successors.
        info!("Update PHIs");
        for succ in mir.successors(BasicBlock::from_u32(bb)) {
            let succ_usize = succ.as_usize();
            for (phi_idx, phi) in &mut blks[succ_usize].stmts.iter_mut().enumerate()
                .filter(|(_, i)| i.is_phi())
            {
                info!("phi: {:?}", phi);
                let phi_loc = StmtLoc{bb: succ.as_u32(), si: phi_idx};
                for v in phi.uses_vars_mut() {
                    info!("uses {:?}", v);
                    self.update_reaching_def(doms, *v, &phi_loc);
                    info!("rewrites to {:?}", self.reaching_defs[usize::try_from(*v).unwrap()]);
                    *v = self.reaching_defs[usize::try_from(*v).unwrap()];
                }
            }
        }

        // Continue walking the dominator tree in depth-first pre-order.
        for next_bb in doms.immediately_dominates(BasicBlock::from_u32(bb)) {
            self.rename(doms, mir, blks, next_bb.as_u32());
        }
    }

    /// Update `self.reaching_defs` for the variable `v` at location `i`.
    fn update_reaching_def(&mut self, doms: &Dominators<BasicBlock>, v: TirLocal, i: &StmtLoc) {
        let v_usize = usize::try_from(v).unwrap();

        let final_r = {
            let mut r = &self.reaching_defs[v_usize];
            let r_usize = usize::try_from(*r).unwrap();
            while !(*r == BOTTOM || Self::def_dominates(doms, &self.def_sites[r_usize], i)) {
                let old_r = r;
                r = &self.reaching_defs[r_usize];
                assert!(r != old_r, "detected cycle in update_reaching_def");
            };
            *r
        };
        self.reaching_defs[v_usize] = final_r;
    }

    // Does a definition at `r` dominate the instruction `i`?
    fn def_dominates(doms: &Dominators<BasicBlock>, opt_r: &Option<StmtLoc>, i: &StmtLoc) -> bool {
        if let Some(r) = opt_r {
            if r.bb == i.bb {
                // If the locations are in the same block, `r` dominates if it comes before `i`.
                r.si <= i.si
            } else {
                // The locations are in different blocks, so ask the CFG which block dominates.
                doms.is_dominated_by(BasicBlock::from_u32(i.bb), BasicBlock::from_u32(r.bb))
            }
        } else {
            // If the variable isn't defined yet, it's definition can't dominate anything.
            // FIXME can this even happen?
            warn!("undefined var");
            false
        }
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

        // If we are lowering the first block, we insert a special `DefArgs` instruction, which
        // provides the SSA conversion with a definition site for the TIR arguments.
        if bb.as_u32() == 0 {
             let args = ccx.mir_args.iter().map(|a| ccx.tir_var(*a)).collect();
             ser_stmts.push(ykpack::Statement::DefArgs(args));
        }

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
