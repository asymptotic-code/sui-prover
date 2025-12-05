use bimap::BiBTreeMap;
use codespan_reporting::diagnostic::Severity;
use itertools::Itertools;
use std::{
    collections::{BTreeMap, BTreeSet},
    vec,
};

use move_model::{
    model::{FunId, FunctionEnv, GlobalEnv, QualifiedId},
    ty::{PrimitiveType, Type},
};

use crate::{
    deterministic_analysis,
    exp_generator::ExpGenerator,
    function_data_builder::FunctionDataBuilder,
    function_target::{FunctionData, FunctionTarget},
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant},
    helpers::loop_helpers::find_loops_headers,
    no_abort_analysis,
    stackless_bytecode::{AttrId, Bytecode, Label, Operation},
};

pub struct MoveLoopInvariantsProcessor {}

#[derive(Clone, Default, Debug)]
pub struct TargetedLoopInfo {
    pub attrs: BTreeSet<Vec<AttrId>>,
}

pub fn get_info(target: &FunctionTarget<'_>) -> TargetedLoopInfo {
    target
        .get_annotations()
        .get::<TargetedLoopInfo>()
        .cloned()
        .unwrap()
}

impl FunctionTargetProcessor for MoveLoopInvariantsProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        mut data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        if func_env.is_native() {
            return data;
        }

        let info = data
            .annotations
            .get_or_default_mut::<TargetedLoopInfo>(true);

        let invariants = Self::get_invariant_span_bimap(&func_env.module_env.env, &data.code);
        let loop_info = find_loops_headers(func_env, &data)
            .keys()
            .cloned()
            .collect::<Vec<_>>();

        let loop_inv_functions = targets.get_loop_invariants(&func_env.get_qualified_id());

        if !invariants.is_empty() && loop_inv_functions.is_some() {
            func_env.module_env.env.diag(
                Severity::Error,
                &func_env.get_loc(),
                "Cannot use both inlined loop invariants and loop invariant functions. Please use only one type.",
            );
            return data;
        }

        if invariants.is_empty() && loop_inv_functions.is_none() {
            return data;
        }

        let (mut new_data, attrs) = if let Some(invs) = loop_inv_functions {
            if !Self::is_valid_inv_function(&targets, invs, &loop_info, func_env) {
                return data;
            }

            Self::handle_targeted_loop_invariant_functions(func_env, data, invs, &loop_info)
        } else {
            Self::handle_classical_loop_invariants(func_env, data, invariants)
        };

        let info = new_data
            .annotations
            .get_or_default_mut::<TargetedLoopInfo>(true);

        info.attrs = attrs;

        new_data
    }

    fn name(&self) -> String {
        "move_loop_invariant".to_string()
    }
}

impl MoveLoopInvariantsProcessor {
    fn is_valid_inv_function(
        targets: &FunctionTargetsHolder,
        invs: &BiBTreeMap<QualifiedId<FunId>, usize>,
        loops: &Vec<Label>,
        func_env: &FunctionEnv,
    ) -> bool {
        let env = func_env.module_env.env;
        for (qid, label) in invs {
            if *label >= loops.len() {
                env.diag(
                    Severity::Error,
                    &func_env.get_loc(),
                    &format!(
                        "Loop Invariant Label {} exceeds number of loops in function {}",
                        label,
                        func_env.get_full_name_str()
                    ),
                );
            }

            let inv_env = env.get_function(*qid);
            let inv_data = targets.get_data(&qid, &FunctionVariant::Baseline).unwrap();

            if !no_abort_analysis::get_info(inv_data).does_not_abort
                && !targets.is_abort_check_fun(&qid)
            {
                env.diag(
                    Severity::Error,
                    &inv_env.get_loc(),
                    "Invariant function should not abort",
                );
            }

            if !deterministic_analysis::get_info(inv_data).is_deterministic {
                env.diag(
                    Severity::Error,
                    &inv_env.get_loc(),
                    "Invariant function should be deterministic",
                );
            }

            for pt in inv_env.get_parameter_types() {
                if pt.is_mutable_reference() {
                    env.diag(
                        Severity::Error,
                        &inv_env.get_loc(),
                        "Mutable references are not allowed in loop invariant functions",
                    );
                }
            }

            if inv_env.get_return_count() != 1 {
                env.diag(
                    Severity::Error,
                    &inv_env.get_loc(),
                    "Loop invariant functions must have exactly one return value",
                );
            }

            if !inv_env.get_return_type(0).is_bool() {
                env.diag(
                    Severity::Error,
                    &inv_env.get_loc(),
                    "Loop invariant functions must return a boolean value",
                );
            }
        }

        !env.has_errors()
    }

    fn is_assignment_before(offset: usize, var_idx: usize, code: &[Bytecode]) -> bool {
        for i in 0..offset {
            match &code[i] {
                Bytecode::Assign(_, dest, _, _) if *dest == var_idx => {
                    return true;
                }
                _ => {}
            }
        }
        false
    }

    fn vars_in_scope(offset: usize, builder: &FunctionDataBuilder) -> Vec<(String, usize)> {
        let all_names = builder
            .data
            .name_to_index
            .iter()
            .filter_map(|(name, &local_idx)| {
                if !Self::is_assignment_before(offset, local_idx, &builder.data.code)
                    && local_idx >= builder.fun_env.get_parameter_count()
                // !is_parameter
                {
                    return None;
                }
                let name_str = builder.fun_env.symbol_pool().string(*name).to_string();
                Some((name_str, local_idx))
            })
            .collect::<Vec<(String, usize)>>();

        let pure_names: Vec<String> = all_names
            .iter()
            .map(|(name, _)| {
                if name.contains('#') {
                    name.split('#').next().unwrap().to_string()
                } else {
                    name.to_string()
                }
            })
            .collect();

        let duplicate_pure_names: Vec<&String> = pure_names
            .iter()
            .filter(|name| pure_names.iter().filter(|n| n == name).count() > 1)
            .collect();

        return all_names
            .iter()
            .map(|(name, idx)| {
                // Note: builder.data.name_to_index usually looks like
                // n -> 0, i#1#0 -> 1, s#1#0 -> 2
                let final_name = if name.contains('#') {
                    let pure = name.split('#').next().unwrap().to_string();
                    if duplicate_pure_names.contains(&&pure) {
                        format!("{}__{}", pure, name.split('#').last().unwrap()).to_string()
                    } else {
                        pure.to_string()
                    }
                } else {
                    name.to_string()
                };

                (final_name, *idx)
            })
            .collect::<Vec<(String, usize)>>();
    }

    fn match_invariant_arguments(
        builder: &FunctionDataBuilder,
        loop_inv_env: &FunctionEnv,
        offset: usize,
    ) -> Vec<usize> {
        let mut args = vec![];
        let scope_vars = Self::vars_in_scope(offset, builder);

        for param in loop_inv_env.get_parameters() {
            let param_name_str = builder.fun_env.symbol_pool().string(param.0);

            let found_idx = if let Some(&local_idx) = builder.data.name_to_index.get(&param.0) {
                Some(local_idx)
            } else {
                scope_vars
                    .iter()
                    .find(|(name, _)| param_name_str.as_ref() == name)
                    .map(|(_, idx)| *idx)
            };

            if let Some(idx) = found_idx {
                if param.1.skip_reference() != builder.get_local_type(idx).skip_reference() {
                    builder.fun_env.module_env.env.diag(
                        Severity::Error,
                        &builder.fun_env.get_loc(),
                        &format!(
                            "Loop invariant function {} expects some type for '{}' parameter in function {}",
                            loop_inv_env.get_full_name_str(),
                            param_name_str,
                            builder.fun_env.get_full_name_str()
                        ),
                    );
                }

                args.push(idx);
            } else {
                builder.fun_env.module_env.env.diag(
                    Severity::Error,
                    &builder.fun_env.get_loc(),
                    &format!(
                        "Loop invariant function {} expects parameter '{}' which is not found in function {}.\nAvailable variables: ( {} )",
                        loop_inv_env.get_full_name_str(),
                        param_name_str,
                        builder.fun_env.get_full_name_str(),
                        scope_vars
                        .iter()
                        .map(|(name, idx)|
                            format!(
                                "{}: {}",
                                name,
                                builder
                                    .get_local_type(*idx)
                                    .display(&builder.fun_env.module_env.env.get_type_display_ctx())
                                    .to_string()
                            )
                        ).join(", ")
                    ),
                );
            }
        }

        args
    }

    // Returns a bimap between the begin offset of an invariant and the end offset of the invariant.
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

    fn handle_classical_loop_invariants(
        func_env: &FunctionEnv,
        data: FunctionData,
        invariants: BiBTreeMap<usize, usize>,
    ) -> (FunctionData, BTreeSet<Vec<AttrId>>) {
        let mut builder: FunctionDataBuilder<'_> = FunctionDataBuilder::new(func_env, data);
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

        let mut attrs: BTreeSet<Vec<AttrId>> = BTreeSet::new();

        for (begin, end) in invariants.iter() {
            let mut vrange = vec![];
            for i in (*begin + 1)..=(*end - 1) {
                vrange.push(code[i].get_attr_id());
            }
            attrs.insert(vrange);
        }

        for (offset, bc) in code.into_iter().enumerate() {
            if let Some(label_bc) = invariant_labels.get(&offset) {
                builder.emit(label_bc.clone());
            }

            if invariants.contains_left(&offset) || invariants.contains_right(&offset) {
                continue;
            }
            if offset > 0 && invariants.contains_right(&(offset - 1)) {
                continue;
            }

            builder.emit(bc);
        }

        (builder.data, attrs)
    }

    fn find_label_offset(code: &[Bytecode], label: Label) -> Option<usize> {
        code.iter()
            .position(|bc| matches!(bc, Bytecode::Label(_, l) if *l == label))
    }

    pub fn handle_targeted_loop_invariant_functions(
        func_env: &FunctionEnv,
        data: FunctionData,
        invariants: &BiBTreeMap<QualifiedId<FunId>, usize>,
        loop_info: &Vec<Label>,
    ) -> (FunctionData, BTreeSet<Vec<AttrId>>) {
        let mut builder = FunctionDataBuilder::new(func_env, data);
        let code = std::mem::take(&mut builder.data.code);

        let mut loop_header_to_invariant: BTreeMap<usize, QualifiedId<FunId>> = BTreeMap::new();
        for (qid, label) in invariants {
            let header_offset =
                Self::find_label_offset(&code, *loop_info.iter().nth(*label).unwrap()).unwrap();
            loop_header_to_invariant.insert(header_offset, qid.clone());
        }

        let mut attrs: BTreeSet<Vec<AttrId>> = BTreeSet::new();

        for (offset, bc) in code.into_iter().enumerate() {
            builder.emit(bc);

            if let Some(qid) = loop_header_to_invariant.get(&offset) {
                let mut args = Self::match_invariant_arguments(
                    &builder,
                    &func_env.module_env.env.get_function(*qid),
                    offset,
                );
                let temp = builder.new_temp(Type::Primitive(PrimitiveType::Bool));

                let mut first_attr_id = None;

                for i in 0..args.len() {
                    if builder.get_local_type(args[i]).is_mutable_reference() {
                        let attr = builder.new_attr();

                        if first_attr_id.is_none() {
                            first_attr_id = Some(attr);
                        }

                        let ty = builder
                            .new_temp(builder.get_local_type(args[i]).skip_reference().clone());
                        builder.emit(Bytecode::Call(
                            attr,
                            [ty].to_vec(),
                            Operation::ReadRef,
                            vec![args[i]],
                            None,
                        ));
                        args[i] = ty;
                    }
                }

                let call_attr_id = builder.new_attr();
                let ensures_attr_id = builder.new_attr();

                if first_attr_id.is_none() {
                    first_attr_id = Some(call_attr_id);
                }

                builder.emit(Bytecode::Call(
                    call_attr_id,
                    [temp].to_vec(),
                    Operation::apply_fun_qid(qid, vec![]),
                    args,
                    None,
                ));

                builder.emit(Bytecode::Call(
                    ensures_attr_id,
                    vec![],
                    Operation::apply_fun_qid(&func_env.module_env.env.ensures_qid(), vec![]),
                    [temp].to_vec(),
                    None,
                ));

                attrs.insert(vec![first_attr_id.unwrap(), ensures_attr_id]);
            }
        }

        (builder.data, attrs)
    }

    pub fn new() -> Box<Self> {
        Box::new(Self {})
    }
}
