use bimap::BiBTreeMap;
use codespan_reporting::diagnostic::Severity;
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet, HashMap};

use move_model::{model::{FunId, FunctionEnv, GlobalEnv, QualifiedId}, ty::{PrimitiveType, Type}};

use crate::{
    exp_generator::ExpGenerator,
    function_data_builder::FunctionDataBuilder,
    function_target::{FunctionData, FunctionTarget},
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    stackless_bytecode::{Bytecode, Label, Operation},
};

pub struct MoveLoopInvariantsProcessor {}

#[derive(Clone, Default, Debug)]
pub struct TargetedLoopInfo {
    offsets: BiBTreeMap<usize, usize>
}

pub fn get_info(target: &FunctionTarget<'_>) -> TargetedLoopInfo {
    target
        .get_annotations()
        .get::<TargetedLoopInfo>()
        .cloned()
        .unwrap_or_default()
}

impl FunctionTargetProcessor for MoveLoopInvariantsProcessor {
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

        let invariants = get_invariant_span_bimap(&func_env.module_env.env, &data.code);
        let loop_info = Self::analyze_loops(&data.code);

        let loop_inv_functions = targets
            .get_loop_invariants(&func_env.get_qualified_id());

        if !invariants.is_empty() && loop_inv_functions.is_some() {
            func_env.module_env.env.diag(
                Severity::Error,
                &func_env.get_loc(),
                "Cannot use both classical loop invariants (invariant_begin/invariant_end) and new loop invariant functions. Please use only one type.",
            );
            return data;
        }

        if !invariants.is_empty() {
            Self::handle_classical_loop_invariants(func_env, data, invariants)
        } else if let Some(invs) = loop_inv_functions {
            if loop_info.len() < invariants.len() {
                func_env.module_env.env.diag(
                    Severity::Error,
                    &func_env.get_loc(),
                    "Number of loop invariant functions exceeds number of loops in the function",
                );
            }

            let (mut new_data, offsets) = Self::handle_targeted_loop_invariant_functions(func_env, data, invs, &loop_info);

            let info = new_data
                .annotations
                .get_or_default_mut::<TargetedLoopInfo>(true);

            info.offsets = offsets;

            new_data
        } else {
            data
        }
    }

    fn name(&self) -> String {
        "move_loop_invariant".to_string()
    }
}

impl MoveLoopInvariantsProcessor {
    fn match_invariant_arguments(
        builder: &FunctionDataBuilder,
        loop_inv_env: &FunctionEnv,
    ) -> Vec<usize> {
        let mut args = vec![];

        for param in loop_inv_env.get_parameters() {
            let param_name = param.0;
            let param_name_str = builder.fun_env.symbol_pool().string(param_name);

            let mut found_idx = None;
            if let Some(&local_idx) = builder.data.name_to_index.get(&param_name) {
                found_idx = Some(local_idx);
            } else {
                for (name, &idx) in &builder.data.name_to_index {
                    let name_str = builder.fun_env.symbol_pool().string(*name);
                    if let Some(base_name) = name_str.split('#').next() {
                        if base_name == param_name_str.as_ref() {
                            found_idx = Some(idx);
                            break;
                        }
                    }
                }
            }

            if let Some(idx) = found_idx {
                args.push(idx);
            } else {
                builder.fun_env.module_env.env.diag(
                    Severity::Error,
                    &builder.fun_env.get_loc(),
                    &format!(
                        "Loop invariant function {} expects parameter '{}' which is not found in function {}",
                        loop_inv_env.get_full_name_str(),
                        param_name_str,
                        builder.fun_env.get_full_name_str()
                    ),
                );
            }
        }

        args
    }

    fn handle_classical_loop_invariants(
        func_env: &FunctionEnv,
        data: FunctionData,
        invariants: BiBTreeMap<usize, usize>,
    ) -> FunctionData {
        let mut builder = FunctionDataBuilder::new(func_env, data);
        let code = std::mem::take(&mut builder.data.code);
        let invariant_labels = invariants
            .iter()
            .map(|(begin, end)| {
                if matches!(code[*end + 1], Bytecode::Label(..)) {
                    // TODO: check if the label is the header of a loop
                    (*begin, code[*end + 1].clone())
                } else {
                    panic!("A loop invariant should end with a label")
                }
            })
            .collect::<BTreeMap<_, _>>();
        for (offset, bc) in code.into_iter().enumerate() {
            if let Some(label_bc) = invariant_labels.get(&offset) {
                builder.emit(label_bc.clone());
            }
            if offset > 0 && invariants.contains_right(&(offset - 1)) {
                continue;
            }
            builder.emit(bc);
        }

        builder.data
    }

    pub fn build_label_to_offset_map(code: &[Bytecode]) -> HashMap<Label, usize> {
        code.iter()
            .enumerate()
            .filter_map(|(offset, bc)| match bc {
                Bytecode::Label(_, label) => Some((*label, offset)),
                _ => None,
            })
            .collect()
    }

    pub fn find_backward_jumps(code: &[Bytecode]) -> Vec<(usize, usize)> {
        let label_map = Self::build_label_to_offset_map(code);
        let mut backward_jumps = Vec::new();

        for (offset, bc) in code.iter().enumerate() {
            let target_labels: Vec<Label> = match bc {
                Bytecode::Jump(_, label) => vec![*label],
                Bytecode::Branch(_, true_label, false_label, _) => vec![*true_label, *false_label],
                Bytecode::VariantSwitch(_, _, labels) => labels.clone(),
                _ => continue,
            };

            for target_label in target_labels {
                if let Some(&target_offset) = label_map.get(&target_label) {
                    if target_offset <= offset {
                        backward_jumps.push((offset, target_offset));
                    }
                }
            }
        }

        backward_jumps
    }

    pub fn analyze_loops(code: &[Bytecode]) -> BTreeMap<usize, Vec<usize>> {
        let backward_jumps = Self::find_backward_jumps(code);
        let mut loop_info: BTreeMap<usize, Vec<usize>> = BTreeMap::new();

        for (from_offset, to_offset) in backward_jumps {
            loop_info
                .entry(to_offset)
                .or_default()
                .push(from_offset);
        }

        loop_info
    }

    pub fn handle_targeted_loop_invariant_functions(
        func_env: &FunctionEnv,
        data: FunctionData,
        invariants: &BTreeSet<(QualifiedId<FunId>, Option<String>)>,
        loop_info: &BTreeMap<usize, Vec<usize>>
    ) -> (FunctionData, BiBTreeMap<usize, usize>) {
        let mut builder = FunctionDataBuilder::new(func_env, data);
        let code = std::mem::take(&mut builder.data.code);

        let mut loop_header_to_invariant: BTreeMap<usize, QualifiedId<FunId>> = BTreeMap::new();
        for (qid, label) in invariants {
            let idx = label.as_deref().unwrap_or("0").parse::<usize>().unwrap();
            let header_offset = loop_info.iter().nth(idx).map(|(k, _)| *k).unwrap();
            loop_header_to_invariant.insert(header_offset, qid.clone());
        }

        let mut offsets = BiBTreeMap::new();

        for (offset, bc) in code.into_iter().enumerate() {
            builder.emit(bc);

            if let Some(qid) = loop_header_to_invariant.get(&offset) {
                let attr_id = builder.new_attr();
                let ensures_attr_id = builder.new_attr();

                let args = Self::match_invariant_arguments(
                    &builder,
                    &func_env.module_env.env.get_function(*qid),
                );
                let temp = builder.new_temp(Type::Primitive(PrimitiveType::Bool));

                builder.emit(Bytecode::Call(
                    attr_id,
                    [temp].to_vec(),
                    Operation::apply_fun_qid(qid, vec![]),
                    args,
                    None,
                ));

                builder.emit(Bytecode::Call(
                    ensures_attr_id,
                    vec![],
                    Operation::apply_fun_qid(
                        &func_env.module_env.env.ensures_qid(), 
                        vec![],
                    ),
                    [temp].to_vec(),
                    None,
                ));

                offsets.insert(offset + 1, offset + 2);
            }
        }

        (builder.data, offsets)
    }

    pub fn new() -> Box<Self> {
        Box::new(Self {})
    }
}

// Returns a bimap between the begin offset of an invariant and the end offset
// of the invariant.
fn get_invariant_span_bimap(env: &GlobalEnv, code: &[Bytecode]) -> BiBTreeMap<usize, usize> {
    let invariant_begin_function = Operation::apply_fun_qid(&env.invariant_begin_qid(), vec![]);
    let invariant_end_function = Operation::apply_fun_qid(&env.invariant_end_qid(), vec![]);
    let begin_offsets = code.iter().enumerate().filter_map(|(i, bc)| match bc {
        Bytecode::Call(_, _, op, _, _) if *op == invariant_begin_function => Some(i),
        _ => None,
    });
    let end_offsets = code.iter().enumerate().filter_map(|(i, bc)| match bc {
        Bytecode::Call(_, _, op, _, _) if *op == invariant_end_function => Some(i),
        _ => None,
    });
    begin_offsets
        // TODO: check if the begin offsets and end offsets are well paired
        .zip_eq(end_offsets)
        .collect()
}

pub fn get_all_invariants(env: &GlobalEnv, target: &FunctionTarget<'_>, code: &[Bytecode]) -> BiBTreeMap<usize, usize> {
    let mut result = get_invariant_span_bimap(env, code);
    result.extend(get_info(target).offsets);
    result
}
