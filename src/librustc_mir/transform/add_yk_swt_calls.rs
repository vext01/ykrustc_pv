// XXX license

use rustc::ty::{self, TyCtxt};
use rustc::mir::*; // XXX yuck
use rustc::ty::subst::Substs;
use rustc_data_structures::indexed_vec::Idx;
use syntax_pos::DUMMY_SP;
use transform::{MirPass, MirSource};
//use rustc::mir::Place;

/// A MIR pass which, for each basic inserts a call to `std::yk_swt::record_loc_fn`, passing block
/// location information.
pub struct AddYkSWTCalls;

impl MirPass for AddYkSWTCalls {
    fn run_pass<'a, 'tcx>(&self,
                          tcx: TyCtxt<'a, 'tcx, 'tcx>,
                          _src: MirSource,
                          mir: &mut Mir<'tcx>) {
        // Find the libstd crate number.
        let mut std_crate_num = None;
        for c in tcx.crates().iter() {
            match &*tcx.crate_name(*c).to_string() {
                "std" => {
                    std_crate_num = Some(c.clone());
                    break;
                },
                _ => (),
            }
        }
        let std_crate_num = std_crate_num.unwrap();

        // Set up the call to our trace location recording function in libstd.
        let rec_fn_defid = tcx.get_lang_items(std_crate_num).yk_swt_record_loc_fn().unwrap();
        let rec_fn_substs = Substs::identity_for_item(tcx, rec_fn_defid);
        let rec_fn_ty = tcx.mk_fn_def(rec_fn_defid, rec_fn_substs);

        let unit_ty = tcx.mk_unit();
        //let unit_ty = tcx.types.unit;
        let u32_ty = tcx.types.u32;
        let u64_ty = tcx.types.u64;

        let num_blocks = mir.basic_blocks().len();
        let mut new_blocks = Vec::new();
        let mut replace_blocks = Vec::new();
        let num_local_decls = mir.local_decls.len();
        let mut new_local_decls = Vec::new();
        //let mut num_local_decls = mir.local_decls.len();

        for (bb, bb_data) in mir.basic_blocks_mut().iter_enumerated() {
            // Copy the old block.
            let new_blk = bb_data.clone();
            let new_blk_idx = BasicBlock::new(num_blocks + new_blocks.len());
            new_blocks.push(new_blk);

            // Storage area for the unit return type of the recorder function.
            let ret_val = LocalDecl::new_temp(unit_ty, DUMMY_SP);
            let ret_place = Place::Local(Local::new(num_local_decls + new_local_decls.len()));
            new_local_decls.push(ret_val);

            // Arguments for the recorder function.
            let arg1 = LocalDecl::new_temp(u64_ty, DUMMY_SP);
            //let arg1_local = Place::Local(Local::new(mir.local_decls.len()));
            new_local_decls.push(arg1);
            let arg1_oper = Operand::Constant(box Constant {
                span: DUMMY_SP,
                ty: u64_ty,
                user_ty: None,
                literal: ty::Const::from_usize(tcx, 0),
            });

            let arg2 = LocalDecl::new_temp(u32_ty, DUMMY_SP);
            //let arg2_local = Place::Local(Local::new(mir.local_decls.len()));
            new_local_decls.push(arg2);
            let arg2_oper = Operand::Constant(box Constant {
                span: DUMMY_SP,
                ty: u32_ty,
                user_ty: None,
                literal: ty::Const::from_usize(tcx, 0),
            });

            let arg3 = LocalDecl::new_temp(u32_ty, DUMMY_SP);
            //let arg3_local = Place::Local(Local::new(mir.local_decls.len()));
            new_local_decls.push(arg3);
            let arg3_oper = Operand::Constant(box Constant {
                span: DUMMY_SP,
                ty: u32_ty,
                user_ty: None,
                literal: ty::Const::from_usize(tcx, 0),
            });

            // XXX
            //let zero_u64 = Box::new(Constant {
            //    span: DUMMY_SP,
            //    ty: u64_ty,
            //    user_ty: None,
            //    literal: ty::Const::from_usize(tcx, 0),
            //});

            //let zero_u32 = Box::new(Constant {
            //    span: DUMMY_SP,
            //    ty: u64_ty,
            //    user_ty: None,
            //    literal: ty::Const::from_usize(tcx, 0),
            //});

            // build rvalues
            //let rval1 = Box::new(Rvalue::Use(Operand::Constant(zero_u64)));
            //let rval2 = Box::new(Rvalue::Use(Operand::Constant(zero_u32)));
            //let rval3 = Box::new(Rvalue::Use(Operand::Constant(zero_u32)));

            // build statements
            //let s1 = Statement { source_info: arg1.source_info, kind: StatementKind::Assign(arg1_local, rval1) };
            //let s2 = Statement { source_info: arg2.source_info, kind: StatementKind::Assign(arg2_local, rval2) };
            //let s3 = Statement { source_info: arg3.source_info, kind: StatementKind::Assign(arg3_local, rval3) };

            let rec_fn_oper = Operand::Constant(box Constant {
                span: DUMMY_SP,
                ty: rec_fn_ty,
                user_ty: None,
                literal: ty::Const::zero_sized(tcx, rec_fn_ty),
            });

            let term_kind = TerminatorKind::Call {
                func: rec_fn_oper,
                // XXX make the args into Operands
                args: vec![arg1_oper, arg2_oper, arg3_oper],
                // XXX make the ret_val into a Place
                destination: Some((ret_place, new_blk_idx)),
                cleanup: None,
                from_hir_call: false,
            };

            // Construct a new block to replace the original one.
            let replace_block = BasicBlockData {
                statements: vec![], //s1, s2, s3],
                terminator: Some(Terminator {
                    source_info: SourceInfo { span: DUMMY_SP, scope: OUTERMOST_SOURCE_SCOPE },
                    kind: term_kind
                }),
                is_cleanup: false
            };
            replace_blocks.push((bb.clone(), replace_block));
        }

        // Add new blocks and replace old ones.
        mir.basic_blocks_mut().extend(new_blocks);
        mir.local_decls.extend(new_local_decls);
        for (bb, bb_data) in replace_blocks {
            mir.basic_blocks_mut()[bb] = bb_data;
        }
    }
}
