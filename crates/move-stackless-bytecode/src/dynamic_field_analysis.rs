// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use crate::{
    exp_generator::ExpGenerator,
    function_data_builder::FunctionDataBuilder,
    function_target::{FunctionData, FunctionTarget},
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant},
    stackless_bytecode::{Bytecode, Operation},
};

use codespan_reporting::diagnostic::{Diagnostic, Label, Severity};
use itertools::Itertools;
use move_model::{
    model::{FunctionEnv, GlobalEnv},
    ty::Type,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

/// Stores dynamic field type information for a specific function
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct DynamicFieldInfo {
    dynamic_field_mappings: BTreeMap<Type, BTreeSet<NameValueInfo>>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum NameValueInfo {
    NameValue {
        name: Type,
        value: Type,
        is_mut: bool,
    },
    NameOnly(Type),
}

impl NameValueInfo {
    pub fn as_name_value(&self) -> Option<(&Type, &Type)> {
        match self {
            NameValueInfo::NameValue {
                name,
                value,
                is_mut: _,
            } => Some((name, value)),
            NameValueInfo::NameOnly(..) => None,
        }
    }
}

impl DynamicFieldInfo {
    pub fn new() -> Self {
        Self {
            dynamic_field_mappings: BTreeMap::new(),
        }
    }

    /// Creates a DynamicFieldInfo with a single mapping from the given type to a single dynamic field type.
    /// This is a convenience method for creating simple dynamic field entries.
    pub fn singleton(ty: Type, name_value_info: NameValueInfo) -> Self {
        Self {
            dynamic_field_mappings: BTreeMap::from([(ty, BTreeSet::from([name_value_info]))]),
        }
    }

    pub fn dynamic_fields(&self) -> &BTreeMap<Type, BTreeSet<NameValueInfo>> {
        &self.dynamic_field_mappings
    }

    pub fn dynamic_field_names_values(
        &self,
        ty: &Type,
    ) -> impl Iterator<Item = (&Type, &Type)> + '_ {
        self.dynamic_field_mappings
            .get(ty)
            .into_iter()
            .flat_map(|x| x.iter())
            .filter_map(|name_value_info| name_value_info.as_name_value())
            .unique()
    }

    /// union two DynamicFieldTypeInfo
    pub fn union(&self, other: &Self) -> Self {
        let mut new_info = self.clone();
        for (ty, name_value_set) in other.dynamic_field_mappings.iter() {
            new_info
                .dynamic_field_mappings
                .entry(ty.clone())
                .or_insert_with(BTreeSet::new)
                .extend(name_value_set.iter().cloned());
        }
        new_info
    }

    /// Create a new DynamicFieldTypeInfo with types instantiated using the given type arguments
    pub fn instantiate(&self, type_inst: &[Type]) -> Self {
        Self {
            dynamic_field_mappings: self
                .dynamic_field_mappings
                .iter()
                .map(|(ty, name_value_set)| {
                    (
                        ty.instantiate(type_inst),
                        name_value_set
                            .iter()
                            .map(|name_value_info| match name_value_info {
                                NameValueInfo::NameValue {
                                    name,
                                    value,
                                    is_mut,
                                } => NameValueInfo::NameValue {
                                    name: name.instantiate(type_inst),
                                    value: value.instantiate(type_inst),
                                    is_mut: *is_mut,
                                },
                                NameValueInfo::NameOnly(name) => {
                                    NameValueInfo::NameOnly(name.instantiate(type_inst))
                                }
                            })
                            .collect(),
                    )
                })
                .collect(),
        }
    }

    pub fn iter_union(info: impl Iterator<Item = Self>) -> Self {
        info.fold(Self::new(), |acc, info| acc.union(&info))
    }
}

/// Get the information computed by this analysis for the global environment
pub fn get_env_info(env: &GlobalEnv) -> Rc<DynamicFieldInfo> {
    env.get_extension::<DynamicFieldInfo>().unwrap()
}

/// Get the information computed by this analysis for a function
pub fn get_fun_info(data: &FunctionData) -> &DynamicFieldInfo {
    data.annotations.get::<DynamicFieldInfo>().unwrap()
}

/// Collect dynamic field type information from a function's bytecode
pub fn collect_dynamic_field_info(
    targets: &FunctionTargetsHolder,
    builder: &mut FunctionDataBuilder,
    code: Vec<Bytecode>,
) -> DynamicFieldInfo {
    let dynamic_field_name_value_fun_qids = vec![
        // dynamic field operations
        builder.fun_env.module_env.env.dynamic_field_borrow_qid(),
        builder
            .fun_env
            .module_env
            .env
            .dynamic_field_exists_with_type_qid(),
        // dynamic object field operations
        builder
            .fun_env
            .module_env
            .env
            .dynamic_object_field_borrow_qid(),
        builder
            .fun_env
            .module_env
            .env
            .dynamic_object_field_exists_with_type_qid(),
    ]
    .into_iter()
    .filter_map(|x| x)
    .collect_vec();
    let dynamic_field_name_value_fun_mut_qids = vec![
        // dynamic field operations
        builder.fun_env.module_env.env.dynamic_field_add_qid(),
        builder
            .fun_env
            .module_env
            .env
            .dynamic_field_borrow_mut_qid(),
        builder.fun_env.module_env.env.dynamic_field_remove_qid(),
        builder
            .fun_env
            .module_env
            .env
            .dynamic_field_remove_if_exists_qid(),
        // dynamic object field operations
        builder
            .fun_env
            .module_env
            .env
            .dynamic_object_field_add_qid(),
        builder
            .fun_env
            .module_env
            .env
            .dynamic_object_field_borrow_mut_qid(),
        builder
            .fun_env
            .module_env
            .env
            .dynamic_object_field_remove_qid(),
        builder
            .fun_env
            .module_env
            .env
            .dynamic_object_field_remove_if_exists_qid(),
    ]
    .into_iter()
    .filter_map(|x| x)
    .collect_vec();
    let dynamic_field_name_only_fun_qids = vec![
        // dynamic field operations
        builder.fun_env.module_env.env.dynamic_field_exists_qid(),
        // dynamic object field operations
        builder
            .fun_env
            .module_env
            .env
            .dynamic_object_field_exists_qid(),
    ]
    .into_iter()
    .filter_map(|x| x)
    .collect_vec();
    let all_dynamic_field_fun_qids = [
        &dynamic_field_name_value_fun_qids,
        &dynamic_field_name_value_fun_mut_qids,
        &dynamic_field_name_only_fun_qids,
    ]
    .into_iter()
    .cloned()
    .flatten()
    .collect_vec();

    // compute map of temp index that load object ids to type of object
    let uid_info = compute_uid_info(&builder.get_target(), &code);

    let info = DynamicFieldInfo::iter_union(code.iter().filter_map(|bc| match bc {
        Bytecode::Call(_, _, Operation::Function(module_id, fun_id, type_inst), srcs, _) => {
            let callee_id = module_id.qualified(*fun_id);

            let uid_object_type_not_found_error = || {
                // TODO: remove this once we don't include modules/functions not included in verification
                let excluded_modules = vec![
                    "0x2::dynamic_field",
                    "0x2::dynamic_object_field",
                    "0x2::kiosk_extension",
                    "0x2::versioned",
                ];
                if excluded_modules
                    .contains(&builder.fun_env.module_env.get_full_name_str().as_str())
                {
                    return;
                }

                let loc = builder.get_loc(bc.get_attr_id());
                builder.fun_env.module_env.env.add_diag(
                    Diagnostic::new(Severity::Error)
                        .with_code("E0022")
                        .with_message(&format!("UID object type not found: {}", srcs[0]))
                        .with_labels(vec![Label::primary(loc.file_id(), loc.span())]),
                );
            };

            if callee_id == builder.fun_env.get_qualified_id() {
                return None;
            }

            if dynamic_field_name_value_fun_qids.contains(&callee_id) {
                if let Some((_, obj_type)) = uid_info.get(&srcs[0]) {
                    return Some(DynamicFieldInfo::singleton(
                        obj_type.clone(),
                        NameValueInfo::NameValue {
                            name: type_inst[0].clone(),
                            value: type_inst[1].clone(),
                            is_mut: false,
                        },
                    ));
                } else {
                    uid_object_type_not_found_error();
                }
            }

            if dynamic_field_name_value_fun_mut_qids.contains(&callee_id) {
                if let Some((_, obj_type)) = uid_info.get(&srcs[0]) {
                    return Some(DynamicFieldInfo::singleton(
                        obj_type.clone(),
                        NameValueInfo::NameValue {
                            name: type_inst[0].clone(),
                            value: type_inst[1].clone(),
                            is_mut: true,
                        },
                    ));
                } else {
                    uid_object_type_not_found_error();
                }
            }

            if dynamic_field_name_only_fun_qids.contains(&callee_id) {
                if let Some((_, obj_type)) = uid_info.get(&srcs[0]) {
                    return Some(DynamicFieldInfo::singleton(
                        obj_type.clone(),
                        NameValueInfo::NameOnly(type_inst[0].clone()),
                    ));
                } else {
                    uid_object_type_not_found_error();
                }
            }

            let fun_id_with_info = targets
                .get_callee_spec_qid(&builder.fun_env.get_qualified_id(), &callee_id)
                .unwrap_or(&callee_id);

            // native or intrinsic functions do not access dynamic fields
            if builder
                .fun_env
                .module_env
                .env
                .get_function(*fun_id_with_info)
                .is_native()
            {
                return None;
            }

            let data = targets
                .get_data(fun_id_with_info, &FunctionVariant::Baseline)
                .expect(&format!(
                    "callee `{}` was filtered out",
                    builder.fun_env.get_full_name_str()
                ));
            let info = get_fun_info(data);

            Some(info.instantiate(type_inst))
        }
        _ => None,
    }));

    for bc in code {
        match bc {
            Bytecode::Call(
                attr_id,
                dests,
                Operation::Function(module_id, fun_id, type_inst),
                mut srcs,
                aa,
            ) if all_dynamic_field_fun_qids.contains(&module_id.qualified(fun_id)) => {
                // srcs[0] = uid_info.get(&srcs[0]).unwrap().0;
                srcs[0] = uid_info.get(&srcs[0]).map(|x| x.0).unwrap_or(srcs[0]);
                if !dynamic_field_name_value_fun_mut_qids.contains(&module_id.qualified(fun_id))
                    && builder.get_local_type(srcs[0]).is_mutable_reference()
                {
                    srcs[0] = builder.emit_let_read_ref(srcs[0]);
                }
                builder.emit(Bytecode::Call(
                    attr_id,
                    dests,
                    Operation::Function(module_id, fun_id, type_inst),
                    srcs,
                    aa,
                ));
            }
            _ => builder.emit(bc),
        }
    }

    info
}

/// Computes a mapping from temporary indices to the objects and types of objects they reference
fn compute_uid_info(
    fun_target: &FunctionTarget,
    code: &[Bytecode],
) -> BTreeMap<usize, (usize, Type)> {
    code.iter()
        // First collect all potential UID type mappings, grouped by temporary index
        .filter_map(|bc| match bc {
            Bytecode::Call(
                attr_id,
                dests,
                Operation::BorrowField(mid, sid, tys, offset),
                srcs,
                _,
            ) if fun_target
                .global_env()
                .get_struct(mid.qualified(*sid))
                .get_abilities()
                .has_key()
                && *offset == 0
                && !dests.is_empty() =>
            {
                Some((
                    dests[0],
                    (srcs[0], Type::Datatype(*mid, *sid, tys.clone()), *attr_id),
                ))
            }
            Bytecode::Call(attr_id, dests, Operation::GetField(mid, sid, tys, offset), srcs, _)
                if fun_target
                    .global_env()
                    .get_struct(mid.qualified(*sid))
                    .get_abilities()
                    .has_key()
                    && *offset == 0
                    && !dests.is_empty() =>
            {
                Some((
                    dests[0],
                    (srcs[0], Type::Datatype(*mid, *sid, tys.clone()), *attr_id),
                ))
            }
            _ => None,
        })
        .into_group_map()
        .into_iter()
        .filter_map(|(temp_idx, types)| {
            // Report errors if there are duplicates
            if types.len() == 1 {
                Some((temp_idx, (types[0].0.clone(), types[0].1.clone())))
            } else {
                let labels = types
                    .iter()
                    .map(|(_, _, attr_id)| {
                        let loc = fun_target.get_bytecode_loc(*attr_id);
                        Label::primary(loc.file_id(), loc.span())
                    })
                    .collect();
                fun_target.global_env().add_diag(
                    Diagnostic::new(Severity::Error)
                        .with_code("E0021")
                        .with_message(&format!("Multiple UID object types: {}", temp_idx))
                        .with_labels(labels),
                );
                None
            }
        })
        .collect()
}

pub struct DynamicFieldAnalysisProcessor();

impl DynamicFieldAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }
}

impl FunctionTargetProcessor for DynamicFieldAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        fun_env: &FunctionEnv,
        mut data: FunctionData,
        scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        if fun_env.is_intrinsic() {
            data.annotations.set(DynamicFieldInfo::new(), true);
            return data;
        }

        let mut builder = FunctionDataBuilder::new(fun_env, data);
        let code = std::mem::take(&mut builder.data.code);

        // Collect the dynamic field info
        let info = collect_dynamic_field_info(targets, &mut builder, code);

        builder
            .data
            .annotations
            .set_with_fixedpoint_check(info, scc_opt.is_some());

        builder.data
    }

    fn finalize(&self, env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {
        // Collect and combine all functions' dynamic field info
        let combined_info = DynamicFieldInfo::iter_union(targets.specs().filter_map(|fun_id| {
            targets
                .get_data(&fun_id, &FunctionVariant::Baseline)
                .and_then(|data| {
                    data.annotations
                        .get::<DynamicFieldInfo>()
                        .map(|info| info.clone())
                })
        }));

        // Set the combined info in the environment
        env.set_extension(combined_info);
    }

    fn name(&self) -> String {
        "dynamic_field_analysis_processor".to_string()
    }
}
