// XXX license

use rustc::ty::{self, TyCtxt};
use rustc::mir::*; // XXX yuck
use rustc::ty::subst::Substs;
use rustc_data_structures::indexed_vec::Idx;
use syntax_pos::DUMMY_SP;
use transform::{MirPass, MirSource};
use rustc::hir::def_id::{DefIndex, LOCAL_CRATE};
//use rustc::mir::Place;

/// A MIR pass which, for each basic inserts a call to `std::yk_swt::record_loc_fn`, passing block
/// location information.
pub struct AddYkSWTCalls(pub DefIndex);

impl MirPass for AddYkSWTCalls {
    fn run_pass<'a, 'tcx>(&self,
                          tcx: TyCtxt<'a, 'tcx, 'tcx>,
                          _src: MirSource,
                          mir: &mut Mir<'tcx>) {
        // Find the libstd crate number.
        let mut std_crate_num = None;
        eprintln!("searching for crates");
        for c in tcx.all_crate_nums(LOCAL_CRATE).iter() {
            eprintln!("crate name: {:?}", tcx.crate_name(*c));
            match &*tcx.crate_name(*c).to_string() {
                "libstd" => {
                    std_crate_num = Some(c.clone());
                    break;
                },
                _ => (),
            }
        }
        eprintln!("searching for crates done");
        let std_crate_num = std_crate_num.expect("couldn't find std crate num");

        // Find our recorder function lang item.
        let rec_fn_defid = tcx.get_lang_items(std_crate_num).yk_swt_record_loc_fn()
            .expect("couldn't find yk recorder func");
        let rec_fn_substs = Substs::identity_for_item(tcx, rec_fn_defid);
        let rec_fn_ty = tcx.mk_fn_def(rec_fn_defid, rec_fn_substs);

        // Types.
        let unit_ty = tcx.mk_unit();
        let u32_ty = tcx.types.u32;
        let u64_ty = tcx.types.u64;

        // Each original block is replaced by a new block which calls the recorder function.
        let mut replace_blocks = Vec::new();

        // Each original block is copied. The recorder funcion then returns to a copy.
        let mut copied_blocks = Vec::new();

        // New local declarations are required to set up the calls.
        let mut new_local_decls = Vec::new();

        let num_orig_blocks = mir.basic_blocks().len();
        let num_orig_local_decls = mir.local_decls.len();
        let local_crate_hash = tcx.crate_hash(LOCAL_CRATE).as_u64();

        for (bb, bb_data) in mir.basic_blocks_mut().iter_enumerated() {
            // Copy the original block and compute its index once pushed into the MIRs block vector.
            let new_blk = bb_data.clone();
            let new_blk_idx = BasicBlock::new(num_orig_blocks + copied_blocks.len());
            copied_blocks.push(new_blk);

            // Prepare to call the recorder function.
            let ret_val = LocalDecl::new_temp(unit_ty, DUMMY_SP);
            let ret_place = Place::Local(Local::new(num_orig_local_decls + new_local_decls.len()));
            new_local_decls.push(ret_val);

            let crate_hash_decl = LocalDecl::new_temp(u64_ty, DUMMY_SP);
            new_local_decls.push(crate_hash_decl);
            let crate_hash_oper = Operand::Constant(box Constant {
                span: DUMMY_SP,
                ty: u64_ty,
                user_ty: None,
                literal: ty::Const::from_usize(tcx, local_crate_hash),
            });

            let def_idx_decl = LocalDecl::new_temp(u32_ty, DUMMY_SP);
            new_local_decls.push(def_idx_decl);
            let def_idx_oper = Operand::Constant(box Constant {
                span: DUMMY_SP,
                ty: u32_ty,
                user_ty: None,
                literal: ty::Const::from_usize(tcx, self.0.as_raw_u32() as u64),
            });

            let bb_decl = LocalDecl::new_temp(u32_ty, DUMMY_SP);
            new_local_decls.push(bb_decl);
            let bb_oper = Operand::Constant(box Constant {
                span: DUMMY_SP,
                ty: u32_ty,
                user_ty: None,
                literal: ty::Const::from_usize(tcx, bb.index() as u64),
            });

            let rec_fn_oper = Operand::Constant(box Constant {
                span: DUMMY_SP,
                ty: rec_fn_ty,
                user_ty: None,
                literal: ty::Const::zero_sized(tcx, rec_fn_ty),
            });

            let term_kind = TerminatorKind::Call {
                func: rec_fn_oper,
                args: vec![crate_hash_oper, def_idx_oper, bb_oper],
                destination: Some((ret_place, new_blk_idx)),
                cleanup: None,
                from_hir_call: false,
            };

            // Construct a new block to replace the original one.
            let replace_block = BasicBlockData {
                statements: vec![],
                terminator: Some(Terminator {
                    source_info: SourceInfo { span: DUMMY_SP, scope: OUTERMOST_SOURCE_SCOPE },
                    kind: term_kind
                }),
                is_cleanup: false
            };
            replace_blocks.push((bb.clone(), replace_block));
        }

        // Finally, commit our transformations.
        mir.basic_blocks_mut().extend(copied_blocks);
        mir.local_decls.extend(new_local_decls);
        for (bb, bb_data) in replace_blocks {
            mir.basic_blocks_mut()[bb] = bb_data;
        }
    }
}
