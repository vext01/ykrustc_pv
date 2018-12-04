// Copyright 2018 King's College London.
// Created by the Software Development Team <http://soft-dev.org/>.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rustc::ty::{self, TyCtxt, List};
use rustc::mir::{Operand, LocalDecl, Place, SourceInfo, BasicBlock, Local, BasicBlockData,
    TerminatorKind, Terminator, OUTERMOST_SOURCE_SCOPE, Constant, Mir};
use rustc_data_structures::indexed_vec::Idx;
use syntax_pos::DUMMY_SP;
use transform::{MirPass, MirSource};
use rustc::hir;
use rustc::hir::def_id::{DefIndex, LOCAL_CRATE};
use rustc::hir::map::blocks::FnLikeNode;

/// A MIR pass which, for each basic inserts a call to `std::yk_swt::record_loc_fn`, passing block
/// location information.
pub struct AddYkSWTCalls(pub DefIndex);

impl MirPass for AddYkSWTCalls {
    fn run_pass<'a, 'tcx>(&self,
                          tcx: TyCtxt<'a, 'tcx, 'tcx>,
                          src: MirSource,
                          mir: &mut Mir<'tcx>) {
        if !should_annotate(tcx, src) {
            return;
        }

        // Find the recorder function language item.
        // The item is in libstd, but if we are compiling libcore, then we have to locate the
        // wrapper for the weak language item instead (libcore cannot depend on libstd).
        let rec_fn_defid = if tcx.crate_name(LOCAL_CRATE) == "core" {
            tcx.get_lang_items(LOCAL_CRATE).yk_swt_record_loc_wrapper_fn()
                .expect("couldn't find yk recorder func wrapper")
        } else {
            let mut std_crate_num = None;
            for c in tcx.all_crate_nums(LOCAL_CRATE).iter() {
                match &*tcx.crate_name(*c).to_string() {
                    "std" => {
                        std_crate_num = Some(c.clone());
                        break;
                    },
                    _ => (),
                }
            }
            let std_crate_num = std_crate_num.expect("couldn't find std crate num");
            tcx.get_lang_items(std_crate_num).yk_swt_record_loc_fn()
                .expect("couldn't find yk recorder func")
        };

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

            let crate_hash_oper = Operand::Constant(box Constant {
                span: DUMMY_SP,
                ty: u64_ty,
                user_ty: None,
                literal: ty::Const::from_usize(tcx, local_crate_hash),
            });

            let def_idx_oper = Operand::Constant(box Constant {
                span: DUMMY_SP,
                ty: u32_ty,
                user_ty: None,
                literal: ty::Const::from_usize(tcx, self.0.as_raw_u32() as u64),
            });

            let bb_oper = Operand::Constant(box Constant {
                span: DUMMY_SP,
                ty: u32_ty,
                user_ty: None,
                literal: ty::Const::from_usize(tcx, bb.index() as u64),
            });

            let rec_fn_oper = Operand::function_handle(tcx, rec_fn_defid,
                List::empty(), DUMMY_SP);

            let term_kind = TerminatorKind::Call {
                func: rec_fn_oper,
                args: vec![crate_hash_oper, def_idx_oper, bb_oper],
                destination: Some((ret_place, new_blk_idx)),
                cleanup: None,
                from_hir_call: false,
            };

            // Construct a new block to replace the original one.
            let source_info = bb_data.terminator.clone().map(|t| t.source_info)
                .or(Some(SourceInfo { span: DUMMY_SP, scope: OUTERMOST_SOURCE_SCOPE })).unwrap();
            let replace_block = BasicBlockData {
                statements: vec![],
                terminator: Some(Terminator {
                    source_info,
                    kind: term_kind
                }),
                is_cleanup: false
            };
            replace_blocks.push(replace_block);
        }

        // Finally, commit our transformations.
        mir.basic_blocks_mut().extend(copied_blocks);
        mir.local_decls.extend(new_local_decls);
        for (bb, bb_data) in replace_blocks.drain(..).enumerate() {
            mir.basic_blocks_mut()[BasicBlock::new(bb)] = bb_data;
        }
    }
}

fn should_annotate(tcx: TyCtxt<'a, 'tcx, 'tcx>, src: MirSource) -> bool {
    // We can't add calls to promoted items.
    if let Some(_) = src.promoted {
        return false;
    }

    // We can't add calls to consant functions.
    let node_id = tcx.hir.as_local_node_id(src.def_id)
        .expect("Failed to get node id");
    if let Some(fn_like) = FnLikeNode::from_node(tcx.hir.get(node_id)) {
        fn_like.constness() != hir::Constness::Const
    } else {
        false
    }
}
