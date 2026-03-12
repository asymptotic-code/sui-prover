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
    model::{FunctionEnv, GlobalEnv, StructEnv},
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

    pub fn is_open(&self) -> bool {
        match self {
            NameValueInfo::NameValue { name, value, .. } => name.is_open() || value.is_open(),
            NameValueInfo::NameOnly(name) => name.is_open(),
        }
    }

    pub fn instantiate(&self, type_inst: &[Type]) -> Self {
        match self {
            NameValueInfo::NameValue {
                name,
                value,
                is_mut,
            } => NameValueInfo::NameValue {
                name: name.instantiate(type_inst),
                value: value.instantiate(type_inst),
                is_mut: *is_mut,
            },
            NameValueInfo::NameOnly(name) => NameValueInfo::NameOnly(name.instantiate(type_inst)),
        }
    }
}

impl DynamicFieldInfo {
    pub fn new() -> Self {
        Self {
            dynamic_field_mappings: BTreeMap::new(),
            uid_info: BTreeMap::new(),
        }
    }

    pub fn singleton(ty: Type, name_value_info: NameValueInfo) -> Self {
        Self {
            dynamic_field_mappings: BTreeMap::from([(ty, BTreeSet::from([name_value_info]))]),
            uid_info: BTreeMap::new(),
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
        new_info
    }

    pub fn instantiate(&self, type_inst: &[Type]) -> Self {
        Self {
            uid_info: BTreeMap::new(),
            dynamic_field_mappings: self
                .dynamic_field_mappings
                .iter()
                .map(|(ty, name_value_set)| {
                    (
                        ty.instantiate(type_inst),
                        name_value_set
                            .iter()
                            .map(|nv| nv.instantiate(type_inst))
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

                if callee_id == builder.fun_env.get_qualified_id() {
                    return None;
                }

                let uid_fallback_type = || -> Option<Type> {
                    let uid_qid = uid_qid?;
                    if verified_or_inlined
                        || builder
                            .fun_env
                            .get_return_types()
                            .iter()
                            .any(|x| x.is_mutable_reference())
                    {
                        let loc = builder.get_loc(bc.get_attr_id());
                        builder.fun_env.module_env.env.add_diag(
                            Diagnostic::new(Severity::Warning)
                                .with_message("UID object type not found, dynamic fields will be placed under UID")
                                .with_labels(vec![Label::primary(loc.file_id(), loc.span())]),
                        );
                    }
                    Some(Type::Datatype(uid_qid.module_id, uid_qid.id, vec![]))
                };

                if dynamic_field_name_value_fun_qids.contains(&callee_id) {
                    let obj_type = get_uid_object_type(&uid_info, &alias_info, srcs[0], offset)
                        .map(|(_, t)| t.clone())
                        .or_else(&uid_fallback_type);
                    if let Some(obj_type) = obj_type {
                        return Some(DynamicFieldInfo::singleton(
                            obj_type,
                            NameValueInfo::NameValue {
                                name: type_inst[0].clone(),
                                value: type_inst[1].clone(),
                                is_mut: false,
                            },
                        ));
                    }
                }

                if dynamic_field_name_value_fun_mut_qids.contains(&callee_id) {
                    let obj_type = get_uid_object_type(&uid_info, &alias_info, srcs[0], offset)
                        .map(|(_, t)| t.clone())
                        .or_else(&uid_fallback_type);
                    if let Some(obj_type) = obj_type {
                        return Some(DynamicFieldInfo::singleton(
                            obj_type,
                            NameValueInfo::NameValue {
                                name: type_inst[0].clone(),
                                value: type_inst[1].clone(),
                                is_mut: true,
                            },
                        ));
                    }
                }

                if dynamic_field_name_only_fun_qids.contains(&callee_id) {
                    let obj_type = get_uid_object_type(&uid_info, &alias_info, srcs[0], offset)
                        .map(|(_, t)| t.clone())
                        .or_else(&uid_fallback_type);
                    if let Some(obj_type) = obj_type {
                        return Some(DynamicFieldInfo::singleton(
                            obj_type,
                            NameValueInfo::NameOnly(type_inst[0].clone()),
                        ));
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

                Some(callee_info.instantiate(type_inst))
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
                } else if !type_inst.iter().any(|t| t.is_open()) {
                    // Fallback: push UID type only for concrete df calls where parent
                    // is unknown. Generic calls get concrete types via monomorphization.
                    if let Some(uid_qid) = builder.fun_env.module_env.env.uid_qid() {
                        type_inst.push(Type::Datatype(uid_qid.module_id, uid_qid.id, vec![]));
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
    uid_info.get(&temp_idx).or_else(|| {
        alias_info.get(&(off as u16)).and_then(|state| {
            ReachingDefProcessor::all_aliases(state, &temp_idx)
                .iter()
                .filter_map(|alias| uid_info.get(alias))
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
        let mut combined_info =
            DynamicFieldInfo::iter_union(targets.get_funs().filter_map(|fun_id| {
                targets
                    .get_data(&fun_id, &FunctionVariant::Baseline)
                    .and_then(|data| {
                        data.annotations
                            .get::<DynamicFieldInfo>()
                            .map(|info| info.clone())
                    })
            }));

        // Propagate UID-keyed entries through the call graph.
        // Generic functions with UID params (e.g. borrow_mut<T>(&mut UID, ...))
        // have UID → {u64, T} entries with open types. Callee info propagation
        // is skipped for reachable functions, so concrete instantiations from
        // callers (e.g. borrow_mut<Validator>) don't appear in annotations.
        // This pass transitively instantiates UID entries through the call graph
        // to collect concrete entries like UID → {u64, Validator}.
        let uid_qid = env.uid_qid();
        if let Some(uid_qid) = uid_qid {
            let uid_type = Type::Datatype(uid_qid.module_id, uid_qid.id, vec![]);

            // Collect initial UID entries per function
            let funs: Vec<_> = targets.get_funs().collect();
            let mut uid_entries: BTreeMap<_, BTreeSet<NameValueInfo>> = BTreeMap::new();
            for &fun_id in &funs {
                if let Some(data) = targets.get_data(&fun_id, &FunctionVariant::Baseline) {
                    if let Some(info) = data.annotations.get::<DynamicFieldInfo>() {
                        if let Some(entries) = info.dynamic_field_mappings.get(&uid_type) {
                            if !entries.is_empty() {
                                uid_entries.insert(fun_id, entries.clone());
                            }
                        }
                    }
                }
            }

            // Propagate: if a callee has UID entries, the caller inherits them
            // (instantiated with the call's type args). Repeat until fixpoint.
            if !uid_entries.is_empty() {
                loop {
                    let mut changed = false;
                    for &fun_id in &funs {
                        if let Some(data) = targets.get_data(&fun_id, &FunctionVariant::Baseline) {
                            let mut new_entries = BTreeSet::new();
                            for bc in &data.code {
                                if let Bytecode::Call(
                                    _,
                                    _,
                                    Operation::Function(mid, fid, type_inst),
                                    _,
                                    _,
                                ) = bc
                                {
                                    let callee_id = mid.qualified(*fid);
                                    if callee_id == fun_id {
                                        continue;
                                    }
                                    if let Some(callee_entries) =
                                        uid_entries.get(&callee_id).cloned()
                                    {
                                        for nv in &callee_entries {
                                            new_entries.insert(nv.instantiate(type_inst));
                                        }
                                    }
                                }
                            }
                            if !new_entries.is_empty() {
                                let entry = uid_entries.entry(fun_id).or_insert_with(BTreeSet::new);
                                let old_len = entry.len();
                                entry.extend(new_entries);
                                if entry.len() > old_len {
                                    changed = true;
                                }
                            }
                        }
                    }
                    if !changed {
                        break;
                    }
                }

                // Add concrete UID entries to combined info
                let concrete_entries: BTreeSet<NameValueInfo> = uid_entries
                    .values()
                    .flat_map(|entries| entries.iter())
                    .filter(|nv| !nv.is_open())
                    .cloned()
                    .collect();
                if !concrete_entries.is_empty() {
                    combined_info
                        .dynamic_field_mappings
                        .entry(uid_type.clone())
                        .or_insert_with(BTreeSet::new)
                        .extend(concrete_entries);
                }
            }

            // Remove open-typed UID entries. Generic functions create UID → {K, V}
            // with unresolved type params that cause ill-founded Boogie types.
            // Non-UID entries (e.g. Versioned → {u64, T}) are kept as the Boogie
            // backend handles them correctly for generic spec functions.
            combined_info
                .dynamic_field_mappings
                .retain(|ty, name_values| {
                    if let Some((qid, _)) = ty.get_datatype() {
                        if qid == uid_qid {
                            name_values.retain(|nv| !nv.is_open());
                            return !name_values.is_empty();
                        }
                    }
                    !ty.is_open()
                });
        }

        env.set_extension(combined_info);
    }

    fn name(&self) -> String {
        "dynamic_field_analysis_processor".to_string()
    }
}
