use std::collections::BTreeMap;

use move_model::model::{FunId, FunctionEnv, QualifiedId};

use crate::{
    exp_generator::ExpGenerator,
    function_data_builder::FunctionDataBuilder,
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    move_loop_invariants::MoveLoopInvariantsProcessor,
    number_operation::GlobalNumberOperationState,
    stackless_bytecode::{AssignKind, Bytecode, Operation},
};

pub struct ReplacementAnalysisProcessor();

impl ReplacementAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }

    fn is_fn(code: &Bytecode, qid: QualifiedId<FunId>) -> Option<(&Vec<usize>, &Vec<usize>)> {
        match code {
            Bytecode::Call(_, dest, Operation::Function(mid, fid, _), srcs, _) => {
                if qid == mid.qualified(*fid) {
                    return Some((dest, srcs));
                }
            }
            _ => {}
        }

        None
    }

    pub fn find_ref_val_patterns(
        func_env: &FunctionEnv,
        code: &[Bytecode],
    ) -> BTreeMap<usize, (Vec<usize>, Vec<usize>)> {
        if code.len() < 2 {
            return BTreeMap::new();
        }

        let mut matches = BTreeMap::new();
        for i in 0..code.len() - 1 {
            if let Some((dest_val, srcs_val)) =
                Self::is_fn(&code[i], func_env.module_env.env.prover_val_qid())
            {
                if let Some((dest_ref, srcs_ref)) =
                    Self::is_fn(&code[i + 1], func_env.module_env.env.prover_ref_qid())
                {
                    if dest_val == srcs_ref {
                        matches.insert(i, (dest_ref.clone(), srcs_val.clone()));
                    }
                }
            }
        }

        matches
    }

    pub fn replace_patterns(
        patterns: BTreeMap<usize, (Vec<usize>, Vec<usize>)>,
        func_env: &FunctionEnv,
        data: FunctionData,
    ) -> FunctionData {
        if patterns.is_empty() {
            return data;
        }

        let mut new_data = data.clone();
        new_data.code = vec![]; // NOTE: for some reason it doesnt work properly without copy + erase

        let mut builder = FunctionDataBuilder::new(func_env, new_data);
        for (offset, bc) in data.code.into_iter().enumerate() {
            if patterns.contains_key(&offset) {
                continue;
            } else if offset > 0 && patterns.contains_key(&(offset - 1)) {
                // NOTE: we replace call only with an Assign because it automatically dereferences var
                let (dest, srcs) = patterns.get(&(offset - 1)).unwrap();
                builder.emit(Bytecode::Assign(
                    bc.get_attr_id(),
                    dest[0],
                    srcs[0],
                    AssignKind::Copy,
                ));
            } else {
                builder.emit(bc);
            }
        }

        builder.data
    }

    pub fn replace_patterns_with_params(
        func_env: &FunctionEnv,
        data: FunctionData,
    ) -> FunctionData {
        let mut builder = FunctionDataBuilder::new(func_env, data);
        let code = std::mem::take(&mut builder.data.code);
        let original_params = func_env.get_parameter_count();

        let patterns = Self::find_ref_val_patterns(func_env, &code);
        println!("Found patterns for replacement: {:?}", patterns.keys());
        if patterns.is_empty() {
            builder.data.code = code;
            return builder.data;
        }

        let mut param_to_extra: BTreeMap<usize, usize> = BTreeMap::new();
        let mut next_param_idx = original_params;

        for (_, (_, srcs)) in &patterns {
            println!("Processing pattern with sources: {:?}", srcs);
            let param_idx = match MoveLoopInvariantsProcessor::trace_to_parameter(
                srcs[0],
                original_params,
                &code,
            ) {
                Some(idx) => idx,
                None => continue,
            };

            println!(
                "Pattern source {:?} traced to parameter idx {}",
                srcs[0], param_idx
            );

            if param_to_extra.contains_key(&param_idx) {
                continue;
            }

            let param_ty = builder.get_local_type(param_idx).clone();
            println!(
                "Adding extra parameter of type {:?} for param idx {}",
                param_ty, param_idx
            );
            builder.add_parameter(param_ty.clone());

            // Update number operation state for the extra argument
            func_env
                .module_env
                .env
                .update_extension::<GlobalNumberOperationState>(|state| {
                    state.update_func_oper_state_for_extra_args(
                        func_env.get_qualified_id().module_id,
                        func_env.get_id(),
                        next_param_idx,
                        &[param_ty],
                    );
                });

            param_to_extra.insert(param_idx, next_param_idx);
            next_param_idx += 1;
        }

        for (offset, bc) in code.into_iter().enumerate() {
            if patterns.contains_key(&offset) {
                continue;
            } else if offset > 0 && patterns.contains_key(&(offset - 1)) {
                let (_, srcs) = patterns.get(&(offset - 1)).unwrap();
                // Trace source to parameter and lookup extra param
                if let Some(param_idx) = MoveLoopInvariantsProcessor::trace_to_parameter(
                    srcs[0],
                    original_params,
                    &builder.data.code,
                ) {
                    if let Some(extra_param_idx) = param_to_extra.get(&param_idx) {
                        builder.emit(Bytecode::Assign(
                            bc.get_attr_id(),
                            *extra_param_idx,
                            srcs[0],
                            AssignKind::Copy,
                        ));
                        continue;
                    }
                }
                builder.emit(bc);
            } else {
                builder.emit(bc);
            }
        }

        builder.data
    }
}

impl FunctionTargetProcessor for ReplacementAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        if func_env.is_native() {
            return data;
        }

        if targets.is_loop_inv_func(&func_env.get_qualified_id()) {
            println!(
                "ReplacementAnalysisProcessor: replacing patterns with params in loop invariant function {:?}",
                func_env.get_full_name_str()
            );
            data.code.iter().for_each(|f| println!("-> {:?}", f));
            return Self::replace_patterns_with_params(func_env, data);
        }

        let patterns = Self::find_ref_val_patterns(func_env, &data.code);
        Self::replace_patterns(patterns, func_env, data)
    }

    fn name(&self) -> String {
        "replacement_analysis".to_string()
    }
}
