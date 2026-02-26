// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use crate::{
    exp_generator::ExpGenerator,
    function_data_builder::FunctionDataBuilder,
    function_target::{FunctionData, FunctionTarget},
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant},
    reaching_def_analysis::{ReachingDefProcessor, ReachingDefState},
    stackless_bytecode::{Bytecode, Operation},
    verification_analysis::get_info,
};

use codespan_reporting::diagnostic::{Diagnostic, Label, Severity};
use itertools::Itertools;
use move_model::{
    model::{DatatypeId, FunctionEnv, GlobalEnv, QualifiedId, StructEnv},
    ty::Type,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct DynamicFieldInfo {
    dynamic_field_mappings: BTreeMap<Type, BTreeSet<NameValueInfo>>,
    uid_info: BTreeMap<usize, (usize, Type)>,
    uid_param_object_types: BTreeMap<usize, BTreeSet<Type>>,
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

    pub fn name(&self) -> &Type {
        match self {
            NameValueInfo::NameValue { name, .. } => name,
            NameValueInfo::NameOnly(name) => name,
        }
    }
}

impl DynamicFieldInfo {
    pub fn new() -> Self {
        Self {
            dynamic_field_mappings: BTreeMap::new(),
            uid_info: BTreeMap::new(),
            uid_param_object_types: BTreeMap::new(),
        }
    }

    pub fn singleton(ty: Type, name_value_info: NameValueInfo) -> Self {
        Self {
            dynamic_field_mappings: BTreeMap::from([(ty, BTreeSet::from([name_value_info]))]),
            uid_info: BTreeMap::new(),
            uid_param_object_types: BTreeMap::new(),
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

    pub fn union(&self, other: &Self) -> Self {
        let mut new_info = self.clone();
        for (ty, name_value_set) in other.dynamic_field_mappings.iter() {
            new_info
                .dynamic_field_mappings
                .entry(ty.clone())
                .or_insert_with(BTreeSet::new)
                .extend(name_value_set.iter().cloned());
        }
        for (param_idx, obj_types) in other.uid_param_object_types.iter() {
            new_info
                .uid_param_object_types
                .entry(*param_idx)
                .or_insert_with(BTreeSet::new)
                .extend(obj_types.iter().cloned());
        }
        new_info
    }

    pub fn instantiate(&self, type_inst: &[Type]) -> Self {
        Self {
            uid_info: BTreeMap::new(),
            uid_param_object_types: BTreeMap::new(),
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

pub fn get_env_info(env: &GlobalEnv) -> Rc<DynamicFieldInfo> {
    env.get_extension::<DynamicFieldInfo>().unwrap()
}

pub fn get_fun_info(data: &FunctionData) -> &DynamicFieldInfo {
    data.annotations.get::<DynamicFieldInfo>().unwrap()
}

pub fn get_function_return_local_pos(local_idx: usize, code: &[Bytecode]) -> Option<usize> {
    let mut return_pos = None;
    for bc in code.into_iter() {
        if return_pos.is_some() {
            return None;
        }

        match bc {
            Bytecode::Ret(_, rets) => {
                for (i, ret) in rets.iter().enumerate() {
                    if *ret == local_idx {
                        return_pos = Some(i);
                    }
                }
            }
            _ => {}
        }
    }

    return_pos
}

fn collect_dynamic_field_info(
    targets: &FunctionTargetsHolder,
    builder: &mut FunctionDataBuilder,
    verified_or_inlined: bool,
) -> DynamicFieldInfo {
    let dynamic_field_name_value_fun_qids = vec![
        builder.fun_env.module_env.env.dynamic_field_borrow_qid(),
        builder
            .fun_env
            .module_env
            .env
            .dynamic_field_exists_with_type_qid(),
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
    ]
    .into_iter()
    .filter_map(|x| x)
    .collect_vec();
    let dynamic_field_name_only_fun_qids = vec![
        builder.fun_env.module_env.env.dynamic_field_exists_qid(),
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

    let uid_qid = builder.fun_env.module_env.env.uid_qid();

    let uid_info = compute_uid_info(&builder.get_target(), targets, &builder.data.code);

    let alias_info =
        ReachingDefProcessor::analyze_reaching_definitions(&builder.fun_env, &builder.data);

    let mut info = DynamicFieldInfo::iter_union(builder.data.code.iter().enumerate().filter_map(
        |(offset, bc)| match bc {
            Bytecode::Call(_, _, Operation::Function(module_id, fun_id, type_inst), srcs, _) => {
                let callee_id = module_id.qualified(*fun_id);

                let uid_object_type_not_found_error = || {
                    if !verified_or_inlined
                        && !builder
                            .fun_env
                            .get_return_types()
                            .iter()
                            .any(|x| x.is_mutable_reference())
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

                let has_type_params = !builder.fun_env.get_type_parameters().is_empty();

                if dynamic_field_name_value_fun_qids.contains(&callee_id) {
                    if let Some((_, obj_type)) = get_uid_object_type_impl(
                        &uid_info,
                        &alias_info,
                        srcs[0],
                        offset,
                        has_type_params,
                        uid_qid,
                    ) {
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
                    if let Some((_, obj_type)) = get_uid_object_type_impl(
                        &uid_info,
                        &alias_info,
                        srcs[0],
                        offset,
                        has_type_params,
                        uid_qid,
                    ) {
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
                    if let Some((_, obj_type)) = get_uid_object_type_impl(
                        &uid_info,
                        &alias_info,
                        srcs[0],
                        offset,
                        has_type_params,
                        uid_qid,
                    ) {
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

                let func_env = builder
                    .fun_env
                    .module_env
                    .env
                    .get_function(*fun_id_with_info);

                if func_env.is_native() || get_info(&builder.get_target()).reachable {
                    return None;
                }

                let callee_data = targets
                    .get_data(fun_id_with_info, &FunctionVariant::Baseline)
                    .expect(&format!(
                        "callee `{}` of `{}` was filtered out",
                        func_env.get_full_name_str(),
                        builder.fun_env.get_full_name_str()
                    ));
                let callee_info = get_fun_info(callee_data);

                let substituted_info =
                    substitute_uid_params(callee_info, &uid_info, &alias_info, srcs, offset);

                Some(substituted_info.instantiate(type_inst))
            }
            _ => None,
        },
    ));

    info.uid_info = uid_info.clone();

    let mut parents_with_uid_param_calls: BTreeSet<usize> = BTreeSet::new();
    for bc in builder.data.code.iter() {
        if let Bytecode::Call(_, _, Operation::Function(module_id, callee_fun_id, _), srcs, _) = bc
        {
            let callee_id = module_id.qualified(*callee_fun_id);
            if callee_id == builder.fun_env.get_qualified_id() {
                continue;
            }
            if let Some(callee_data) = targets.get_data(&callee_id, &FunctionVariant::Baseline) {
                let callee_info = get_fun_info(callee_data);
                for (param_idx, (obj_local, _)) in &callee_info.uid_info {
                    if param_idx == obj_local && *param_idx < srcs.len() {
                        let uid_temp = srcs[*param_idx];
                        if let Some((parent, _)) = uid_info.get(&uid_temp) {
                            parents_with_uid_param_calls.insert(*parent);
                        }
                    }
                }
            }
        }
    }

    let code = std::mem::take(&mut builder.data.code);
    for (offset, bc) in code.into_iter().enumerate() {
        match bc {
            Bytecode::Call(
                attr_id,
                dests,
                Operation::Function(module_id, fun_id, mut type_inst),
                mut srcs,
                aa,
            ) if all_dynamic_field_fun_qids.contains(&module_id.qualified(fun_id)) => {
                if let Some((obj_local, obj_type)) =
                    get_uid_object_type(&uid_info, &alias_info, srcs[0], offset)
                {
                    let use_uid_type = parents_with_uid_param_calls.contains(obj_local)
                        || parents_with_uid_param_calls.iter().any(|parent| {
                            alias_info.values().any(|state| {
                                let obj_local_defs =
                                    ReachingDefProcessor::all_aliases(state, obj_local);
                                let parent_defs = ReachingDefProcessor::all_aliases(state, parent);
                                !obj_local_defs.is_disjoint(&parent_defs)
                                    || obj_local_defs.contains(parent)
                                    || parent_defs.contains(obj_local)
                            })
                        });

                    if use_uid_type {
                        if let Some(uid_qid) = builder.fun_env.module_env.env.uid_qid() {
                            type_inst.push(Type::Datatype(uid_qid.module_id, uid_qid.id, vec![]));
                        }
                    } else {
                        srcs[0] = *obj_local;
                        if !dynamic_field_name_value_fun_mut_qids
                            .contains(&module_id.qualified(fun_id))
                            && builder.get_local_type(srcs[0]).is_mutable_reference()
                        {
                            srcs[0] = builder.emit_let_read_ref(srcs[0]);
                        }
                        type_inst.push(obj_type.clone());
                    }
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

fn substitute_uid_params(
    callee_info: &DynamicFieldInfo,
    caller_uid_info: &BTreeMap<usize, (usize, Type)>,
    alias_info: &BTreeMap<u16, ReachingDefState>,
    srcs: &[usize],
    offset: usize,
) -> DynamicFieldInfo {
    let mut result = callee_info.clone();

    for (temp_idx, (obj_local, uid_type)) in &callee_info.uid_info {
        if temp_idx == obj_local && *temp_idx < srcs.len() {
            let src_idx = srcs[*temp_idx];
            if let Some((_, actual_obj_type)) =
                get_uid_object_type(caller_uid_info, alias_info, src_idx, offset)
            {
                if let Some(uid_name_values) = callee_info.dynamic_field_mappings.get(uid_type) {
                    result
                        .dynamic_field_mappings
                        .entry(actual_obj_type.clone())
                        .or_insert_with(BTreeSet::new)
                        .extend(uid_name_values.iter().cloned());
                }
            }
        }
    }

    result
}

fn compute_uid_info(
    fun_target: &FunctionTarget,
    targets: &FunctionTargetsHolder,
    code: &[Bytecode],
) -> BTreeMap<usize, (usize, Type)> {
    let env = fun_target.global_env();

    let uid_params: BTreeMap<usize, (usize, Type)> = if let Some(uid_qid) = env.uid_qid() {
        (0..fun_target.get_parameter_count())
            .filter_map(|idx| {
                let ty = fun_target.get_local_type(idx);
                let inner_ty = ty.skip_reference();
                if let Some((qid, tys)) = inner_ty.get_datatype() {
                    if qid == uid_qid {
                        return Some((
                            idx,
                            (idx, Type::Datatype(qid.module_id, qid.id, tys.to_vec())),
                        ));
                    }
                }
                None
            })
            .collect()
    } else {
        BTreeMap::new()
    };

    let from_bytecode: BTreeMap<usize, (usize, Type)> = code
        .iter()
        .filter_map(|bc| match bc {
            Bytecode::Call(
                attr_id,
                dests,
                Operation::BorrowField(mid, sid, tys, offset),
                srcs,
                _,
            ) if is_uid_field_access(
                &fun_target.global_env().get_struct(mid.qualified(*sid)),
                *offset,
            ) && !dests.is_empty() =>
            {
                Some((
                    dests[0],
                    (srcs[0], Type::Datatype(*mid, *sid, tys.clone()), *attr_id),
                ))
            }
            Bytecode::Call(attr_id, dests, Operation::GetField(mid, sid, tys, offset), srcs, _)
                if is_uid_field_access(
                    &fun_target.global_env().get_struct(mid.qualified(*sid)),
                    *offset,
                ) && !dests.is_empty() =>
            {
                Some((
                    dests[0],
                    (srcs[0], Type::Datatype(*mid, *sid, tys.clone()), *attr_id),
                ))
            }
            Bytecode::Call(attr_id, dests, Operation::Function(mid, fid, tys), srcs, _)
                if !dests.is_empty() =>
            {
                let callee_id = mid.qualified(*fid);
                if get_info(fun_target).reachable
                    || callee_id == fun_target.global_env().type_inv_qid()
                {
                    return None;
                }

                let callee_data = targets
                    .get_data(&callee_id, &FunctionVariant::Baseline)
                    .expect(&format!(
                        "callee `{}` was filtered out",
                        fun_target
                            .global_env()
                            .get_function(callee_id)
                            .get_full_name_str()
                    ));
                let callee_mapping = &get_fun_info(callee_data).uid_info;

                for key in callee_mapping.keys() {
                    if let Some(ret_pos) = get_function_return_local_pos(*key, &callee_data.code) {
                        let (_, obj_type) = callee_mapping.get(key).unwrap();
                        return Some((
                            dests[ret_pos],
                            (srcs[0], obj_type.instantiate(tys), *attr_id),
                        ));
                    }
                }

                None
            }
            _ => None,
        })
        .into_group_map()
        .into_iter()
        .filter_map(|(temp_idx, types)| {
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
        .collect();

    let mut result = uid_params;
    result.extend(from_bytecode);

    for bc in code {
        match bc {
            Bytecode::Call(_, dests, Operation::FreezeRef, srcs, _)
            | Bytecode::Call(_, dests, Operation::ReadRef, srcs, _) => {
                if !dests.is_empty() && !srcs.is_empty() {
                    if let Some((obj_local, obj_type)) = result.get(&srcs[0]).cloned() {
                        result.entry(dests[0]).or_insert((obj_local, obj_type));
                    }
                }
            }
            Bytecode::Assign(_, dest, src, _) => {
                if let Some((obj_local, obj_type)) = result.get(src).cloned() {
                    result.entry(*dest).or_insert((obj_local, obj_type));
                }
            }
            _ => {}
        }
    }

    result
}

fn is_uid_field_access(struct_env: &StructEnv<'_>, offset: usize) -> bool {
    (struct_env.get_abilities().has_key() && offset == 0)
        || Some(offset) == single_uid_field_offset(struct_env)
}

fn single_uid_field_offset(struct_env: &StructEnv<'_>) -> Option<usize> {
    if struct_env.module_env.env.uid_qid().is_none() {
        return None;
    }
    struct_env
        .get_fields()
        .enumerate()
        .filter_map(|(offset, field)| {
            if field
                .get_type()
                .get_datatype()
                .map(|(field_type_qid, _)| field_type_qid)
                == struct_env.module_env.env.uid_qid()
            {
                Some(offset)
            } else {
                None
            }
        })
        .exactly_one()
        .ok()
}

fn get_uid_object_type<'a>(
    uid_info: &'a BTreeMap<usize, (usize, Type)>,
    alias_info: &'a BTreeMap<u16, ReachingDefState>,
    temp_idx: usize,
    off: usize,
) -> Option<&'a (usize, Type)> {
    get_uid_object_type_impl(uid_info, alias_info, temp_idx, off, false, None)
}

fn get_uid_object_type_impl<'a>(
    uid_info: &'a BTreeMap<usize, (usize, Type)>,
    alias_info: &'a BTreeMap<u16, ReachingDefState>,
    temp_idx: usize,
    off: usize,
    skip_uid_params: bool,
    uid_qid: Option<QualifiedId<DatatypeId>>,
) -> Option<&'a (usize, Type)> {
    let should_skip = |obj_type: &Type| -> bool {
        if !skip_uid_params {
            return false;
        }
        if let Some(uid_qid) = uid_qid {
            if let Some((qid, _)) = obj_type.get_datatype() {
                return qid == uid_qid;
            }
        }
        false
    };

    uid_info
        .get(&temp_idx)
        .filter(|(_, obj_type)| !should_skip(obj_type))
        .or_else(|| {
            alias_info.get(&(off as u16)).and_then(|state| {
                ReachingDefProcessor::all_aliases(state, &temp_idx)
                    .iter()
                    .filter_map(|alias| {
                        uid_info
                            .get(alias)
                            .filter(|(_, obj_type)| !should_skip(obj_type))
                    })
                    .exactly_one()
                    .ok()
            })
        })
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
        if fun_env.is_native() || fun_env.is_intrinsic() {
            data.annotations.set(DynamicFieldInfo::new(), true);
            return data;
        }

        let info = get_info(&FunctionTarget::new(&fun_env, &data));
        if !info.accessible() {
            data.annotations.set(DynamicFieldInfo::new(), true);
            return data;
        }

        let mut builder = FunctionDataBuilder::new(fun_env, data);

        let info = collect_dynamic_field_info(targets, &mut builder, info.verified || info.inlined);

        builder
            .data
            .annotations
            .set_with_fixedpoint_check(info, scc_opt.is_some());

        builder.data
    }

    fn finalize(&self, env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {
        let uid_param_types = collect_uid_param_info(env, targets);

        for (callee_id, param_types) in &uid_param_types {
            if let Some(data) = targets.get_data_mut(callee_id, &FunctionVariant::Baseline) {
                if let Some(callee_info) = data.annotations.get::<DynamicFieldInfo>().cloned() {
                    let mut updated_info = callee_info.clone();

                    for (param_idx, obj_types) in param_types {
                        if let Some((obj_local, uid_type)) = callee_info.uid_info.get(param_idx) {
                            if obj_local == param_idx {
                                if let Some(name_values) =
                                    callee_info.dynamic_field_mappings.get(uid_type)
                                {
                                    for obj_type in obj_types {
                                        updated_info
                                            .dynamic_field_mappings
                                            .entry(obj_type.clone())
                                            .or_insert_with(BTreeSet::new)
                                            .extend(name_values.iter().cloned());

                                        updated_info
                                            .uid_param_object_types
                                            .entry(*param_idx)
                                            .or_insert_with(BTreeSet::new)
                                            .insert(obj_type.clone());
                                    }
                                }
                            }
                        }
                    }

                    data.annotations.set(updated_info, true);
                }
            }
        }

        let combined_info = DynamicFieldInfo::iter_union(targets.get_funs().filter_map(|fun_id| {
            targets
                .get_data(&fun_id, &FunctionVariant::Baseline)
                .and_then(|data| {
                    data.annotations
                        .get::<DynamicFieldInfo>()
                        .map(|info| info.clone())
                })
        }));

        env.set_extension(combined_info);
    }

    fn name(&self) -> String {
        "dynamic_field_analysis_processor".to_string()
    }
}

fn collect_uid_param_info(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
) -> BTreeMap<QualifiedId<move_model::model::FunId>, BTreeMap<usize, BTreeSet<Type>>> {
    let mut param_types: BTreeMap<
        QualifiedId<move_model::model::FunId>,
        BTreeMap<usize, BTreeSet<Type>>,
    > = BTreeMap::new();

    for fun_id in targets.get_funs() {
        if let Some(data) = targets.get_data(&fun_id, &FunctionVariant::Baseline) {
            let fun_env = env.get_function(fun_id);
            if fun_env.is_native() || fun_env.is_intrinsic() {
                continue;
            }

            let caller_info = match data.annotations.get::<DynamicFieldInfo>() {
                Some(info) => info,
                None => continue,
            };

            let alias_info = ReachingDefProcessor::analyze_reaching_definitions(&fun_env, data);

            for (offset, bc) in data.code.iter().enumerate() {
                if let Bytecode::Call(
                    _,
                    _,
                    Operation::Function(module_id, callee_fun_id, _type_inst),
                    srcs,
                    _,
                ) = bc
                {
                    let callee_id = module_id.qualified(*callee_fun_id);

                    if callee_id == fun_id {
                        continue;
                    }

                    let callee_data = match targets.get_data(&callee_id, &FunctionVariant::Baseline)
                    {
                        Some(d) => d,
                        None => continue,
                    };
                    let callee_info = match callee_data.annotations.get::<DynamicFieldInfo>() {
                        Some(info) => info,
                        None => continue,
                    };

                    for (param_idx, (obj_local, _uid_type)) in &callee_info.uid_info {
                        if param_idx == obj_local && *param_idx < srcs.len() {
                            let src_idx = srcs[*param_idx];
                            if let Some((_, actual_obj_type)) = get_uid_object_type(
                                &caller_info.uid_info,
                                &alias_info,
                                src_idx,
                                offset,
                            ) {
                                if let Some((local, _)) = caller_info.uid_info.get(&src_idx) {
                                    if *local == src_idx {
                                        continue;
                                    }
                                }

                                param_types
                                    .entry(callee_id)
                                    .or_insert_with(BTreeMap::new)
                                    .entry(*param_idx)
                                    .or_insert_with(BTreeSet::new)
                                    .insert(actual_obj_type.clone());
                            }
                        }
                    }
                }
            }
        }
    }

    param_types
}
