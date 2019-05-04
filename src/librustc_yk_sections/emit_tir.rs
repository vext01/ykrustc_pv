// Created by the Software Development Team <http://soft-dev.org/>.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! This module converts MIR into Yorick TIR (Tracing IR).
//! Note that we preserve the MIR block structure when lowering to TIR.
//!
//! Serialisation itself is performed by an external library: ykpack.

use rustc::ty::TyCtxt;

use rustc::hir::def_id::DefId;
use rustc::mir::{
    Mir, TerminatorKind, Operand, Constant, StatementKind, BasicBlock, BasicBlockData, Terminator,
    Place, Rvalue, Statement, Local, PlaceBase, BorrowKind, BinOp, UnOp, NullOp, Projection,
    AggregateKind
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
use std::marker::PhantomData;
use rustc_data_structures::bit_set::BitSet;
use rustc_data_structures::indexed_vec::IndexVec;
use rustc::mir::interpret::{Scalar, ConstValue};
use ykpack;
use ykpack::LocalIndex as TirLocal;
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

/// A conversion context holds the state needed to perform the TIR lowering.
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
}

impl<'a, 'tcx, 'gcx> ConvCx<'a, 'tcx, 'gcx> {
    fn new(tcx: &'a TyCtxt<'a, 'tcx, 'gcx>, mir: &Mir<'tcx>) -> Self {
        let var_map = IndexVec::new();
        let num_blks = mir.basic_blocks().len();

        Self {
            tcx,
            def_sites: RefCell::new(Vec::new()),
            block_defines: RefCell::new(IndexVec::from_elem_n(FxHashSet::default(), num_blks)),
            next_tir_var: Cell::new(0),
            var_map: RefCell::new(var_map),
            num_blks: num_blks,
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
            let file = File::create(&tir_path)?;
            (tir_path, Some(file), None)
        },
        TirMode::TextDump(dump_path) => {
            // In text dump mode we just write lines to a file and we don't need an encoder.
            let file = File::create(&dump_path)?;
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
            let mir = tcx.optimized_mir(*def_id);
            let ccx = ConvCx::new(tcx, mir);
            let pack = (&ccx, def_id, tcx.optimized_mir(*def_id)).to_pack();

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
                // In MIR, a call instruction accepts an arbitrary operand, but in TIR we special
                // case the call targets.
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
        ykpack::BasicBlock::new(ser_stmts.filter(|s| *s != ykpack::Statement::Nop).collect(),
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
                if let ykpack::Place::Base(ykpack::PlaceBase::Local(tvar)) = lhs {
                    ccx.push_def_site(*bb, tvar);
                }
                ykpack::Statement::Assign(lhs, rhs)
            },
            StatementKind::SetDiscriminant{ref place, ref variant_index} =>
                ykpack::Statement::SetDiscriminant((*ccx, place).to_pack(), variant_index.as_u32()),
            // StorageLive/Dead not useful to the tracer. Ignore them.
            StatementKind::StorageLive(..)
            | StatementKind::StorageDead(..) => ykpack::Statement::Nop,
            StatementKind::InlineAsm{..} => ykpack::Statement::Unimplemented,
            // These MIR statements all codegen to nothing, and are thus nops for us too. See
            // codegen_statement() in librustc_codegen_ssa for proof.
            StatementKind::Retag(..)
            | StatementKind::AscribeUserType(..)
            | StatementKind::FakeRead(..)
            | StatementKind::Nop => ykpack::Statement::Nop,
        }
    }
}

/// Place -> Pack
impl<'tcx> ToPack<ykpack::Place> for (&ConvCx<'_, 'tcx, '_>, &Place<'tcx>) {
    fn to_pack(&mut self) -> ykpack::Place {
        let (ccx, place) = self;

        match place {
            Place::Base(pb) => ykpack::Place::Base((*ccx, pb).to_pack()),
            Place::Projection(pj) => ykpack::Place::Projection((*ccx, pj.as_ref()).to_pack()),
        }
    }
}

/// Projection -> Pack
/// In Rust, projections are parameterised, but there is only ever one concrete instantiation, so
/// we lower to a concrete `PlaceProjection`.
impl<'tcx, T> ToPack<ykpack::PlaceProjection>
    for (&ConvCx<'_, 'tcx, '_>, &Projection<'tcx, Place<'tcx>, Local, T>)
{
    fn to_pack(&mut self) -> ykpack::PlaceProjection {
        let (ccx, pj) = self;

        ykpack::PlaceProjection {
            base: Box::new((*ccx, &pj.base).to_pack()),
            elem: ykpack::ProjectionElem::Unimplemented(PhantomData), // FIXME
        }
    }
}

/// PlaceBase -> Pack
impl<'tcx> ToPack<ykpack::PlaceBase> for (&ConvCx<'_, 'tcx, '_>, &PlaceBase<'tcx>) {
    fn to_pack(&mut self) -> ykpack::PlaceBase {
        let (ccx, pb) = self;

        match pb {
            PlaceBase::Local(local) => ykpack::PlaceBase::Local(ccx.tir_var(*local)),
            PlaceBase::Static(s) => ykpack::PlaceBase::Static((*ccx, &s.as_ref().def_id).to_pack()),
            PlaceBase::Promoted(bx) => ykpack::PlaceBase::Promoted(bx.0.as_u32()),
        }
    }
}

/// Operand -> Pack
impl<'tcx> ToPack<ykpack::Operand> for (&ConvCx<'_, 'tcx, '_>, &Operand<'tcx>) {
    fn to_pack(&mut self) -> ykpack::Operand {
        let (ccx, op) = self;

        match *op {
            Operand::Move(place) | Operand::Copy(place)
                => ykpack::Operand::Place((*ccx, place).to_pack()),
            Operand::Constant(cst) => ykpack::Operand::Constant((*ccx, cst.as_ref()).to_pack()),
        }
    }
}

/// Rvalue -> Pack
impl<'tcx> ToPack<ykpack::Rvalue> for (&ConvCx<'_, 'tcx, '_>, &Rvalue<'tcx>) {
    fn to_pack(&mut self) -> ykpack::Rvalue {
        let (ccx, rval) = self;

        match *rval {
            Rvalue::Use(oper) => ykpack::Rvalue::Use((*ccx, oper).to_pack()),
            Rvalue::Repeat(oper, len) => ykpack::Rvalue::Repeat((*ccx, oper).to_pack(), *len),
            Rvalue::Ref(_region, borrow_kind, place) => ykpack::Rvalue::Ref(
                (*ccx, borrow_kind).to_pack(),
                (*ccx, place).to_pack()),
            Rvalue::Len(place) => ykpack::Rvalue::Len((*ccx, place).to_pack()),
            // Since TIR is currently untyped we consider a cast as a simple variable use.
            Rvalue::Cast(_, oper, _) => ykpack::Rvalue::Use((*ccx, oper).to_pack()),
            Rvalue::BinaryOp(bop, o1, o2) => ykpack::Rvalue::BinaryOp(
                (*ccx, bop).to_pack(),
                (*ccx, o1).to_pack(),
                (*ccx, o2).to_pack()),
            Rvalue::CheckedBinaryOp(bop, o1, o2) => ykpack::Rvalue::CheckedBinaryOp(
                (*ccx, bop).to_pack(),
                (*ccx, o1).to_pack(),
                (*ccx, o2).to_pack()),
            Rvalue::NullaryOp(null_op, _) => ykpack::Rvalue::NullaryOp((*ccx, null_op).to_pack()),
            Rvalue::UnaryOp(un_op, op) =>
                ykpack::Rvalue::UnaryOp((*ccx, un_op).to_pack(), (*ccx, op).to_pack()),
            Rvalue::Discriminant(place) => ykpack::Rvalue::Discriminant((*ccx, place).to_pack()),
            Rvalue::Aggregate(ag_kind, ops) => ykpack::Rvalue::Aggregate(
                (*ccx, ag_kind.as_ref()).to_pack(),
                ops.iter().map(|op| (*ccx, op).to_pack()).collect()),
        }
    }
}

/// AggregateKind -> Pack
impl<'tcx> ToPack<ykpack::AggregateKind> for (&ConvCx<'_, 'tcx, '_>, &AggregateKind<'tcx>) {
    fn to_pack(&mut self) -> ykpack::AggregateKind {
        let (ccx, ak) = self;
        match *ak {
            AggregateKind::Array(_) => ykpack::AggregateKind::Array,
            AggregateKind::Tuple => ykpack::AggregateKind::Tuple,
            AggregateKind::Adt{..} => ykpack::AggregateKind::Unimplemented,
            AggregateKind::Closure(def_id, _) =>
                ykpack::AggregateKind::Closure((*ccx, def_id).to_pack()),
            AggregateKind::Generator(def_id, ..) =>
                ykpack::AggregateKind::Generator((*ccx, def_id).to_pack()),
        }
    }
}

/// BorrowKind -> Pack
impl<'tcx> ToPack<ykpack::BorrowKind> for (&ConvCx<'_, 'tcx, '_>, &BorrowKind) {
    fn to_pack(&mut self) -> ykpack::BorrowKind {
        let (_ccx, bk) = self;
        match *bk {
            BorrowKind::Shared => ykpack::BorrowKind::Shared,
            BorrowKind::Shallow => ykpack::BorrowKind::Shallow,
            BorrowKind::Unique => ykpack::BorrowKind::Unique,
            BorrowKind::Mut{..} => ykpack::BorrowKind::Mut,
        }
    }
}

/// BinOp -> Pack
impl<'tcx> ToPack<ykpack::BinOp> for (&ConvCx<'_, 'tcx, '_>, &BinOp) {
    fn to_pack(&mut self) -> ykpack::BinOp {
        let (_ccx, op) = self;
        match *op {
            BinOp::Add => ykpack::BinOp::Add,
            BinOp::Sub => ykpack::BinOp::Sub,
            BinOp::Mul => ykpack::BinOp::Mul,
            BinOp::Div => ykpack::BinOp::Div,
            BinOp::Rem => ykpack::BinOp::Rem,
            BinOp::BitXor => ykpack::BinOp::BitXor,
            BinOp::BitAnd => ykpack::BinOp::BitAnd,
            BinOp::BitOr => ykpack::BinOp::BitOr,
            BinOp::Shl => ykpack::BinOp::Shl,
            BinOp::Shr => ykpack::BinOp::Shr,
            BinOp::Eq => ykpack::BinOp::Eq,
            BinOp::Lt => ykpack::BinOp::Lt,
            BinOp::Le => ykpack::BinOp::Le,
            BinOp::Ne => ykpack::BinOp::Ne,
            BinOp::Ge => ykpack::BinOp::Ge,
            BinOp::Gt => ykpack::BinOp::Gt,
            BinOp::Offset => ykpack::BinOp::Offset,
        }
    }
}

/// NullOp -> Pack
impl<'tcx> ToPack<ykpack::NullOp> for (&ConvCx<'_, 'tcx, '_>, &NullOp) {
    fn to_pack(&mut self) -> ykpack::NullOp {
        let (_ccx, op) = self;
        match *op {
            NullOp::SizeOf => ykpack::NullOp::SizeOf,
            NullOp::Box => ykpack::NullOp::Box,
        }
    }
}

/// UnOp -> Pack
impl<'tcx> ToPack<ykpack::UnOp> for (&ConvCx<'_, 'tcx, '_>, &UnOp) {
    fn to_pack(&mut self) -> ykpack::UnOp {
        let (_ccx, op) = self;
        match *op {
            UnOp::Not => ykpack::UnOp::Not,
            UnOp::Neg => ykpack::UnOp::Neg,
        }
    }
}

/// Constant -> Pack
impl<'tcx> ToPack<ykpack::Constant> for (&ConvCx<'_, 'tcx, '_>, &Constant<'tcx>) {
    fn to_pack(&mut self) -> ykpack::Constant {
        let (ccx, cst) = self;
        (*ccx, cst.literal).to_pack()
    }
}

/// LazyConst -> Pack
impl<'tcx> ToPack<ykpack::Constant> for (&ConvCx<'_, 'tcx, '_>, &LazyConst<'tcx>) {
    fn to_pack(&mut self) -> ykpack::Constant {
        let (ccx, lconst) = self;
        if let LazyConst::Evaluated(cst) = lconst {
            (*ccx, cst).to_pack()
        } else {
            // In the final MIR everything should be evaluated.
            //panic!("Encountered unevaluated constant!");
            ykpack::Constant::Unimplemented
        }
    }
}

/// Const -> Pack
impl<'tcx> ToPack<ykpack::Constant> for (&ConvCx<'_, 'tcx, '_>, &Const<'tcx>) {
    fn to_pack(&mut self) -> ykpack::Constant {
        let (ccx, cst) = self;
        (*ccx, &cst.val).to_pack()
    }
}

/// ConstValue -> Pack
impl<'tcx> ToPack<ykpack::Constant> for (&ConvCx<'_, 'tcx, '_>, &ConstValue<'tcx>) {
    fn to_pack(&mut self) -> ykpack::Constant {
        let (ccx, cv) = self;
        match cv {
            ConstValue::Scalar(s) => ykpack::Constant::Scalar((*ccx, s).to_pack()),
            _ => ykpack::Constant::Unimplemented,
        }
    }
}

/// Scalar -> Pack
impl<'tcx> ToPack<ykpack::Scalar> for (&ConvCx<'_, 'tcx, '_>, &Scalar) {
    fn to_pack(&mut self) -> ykpack::Scalar {
        let (_ccx, sc) = self;
        match sc {
            Scalar::Bits{size, bits} => ykpack::Scalar::bits_from_u128(*size, *bits),
            _ => ykpack::Scalar::Unimplemented,
        }
    }
}
