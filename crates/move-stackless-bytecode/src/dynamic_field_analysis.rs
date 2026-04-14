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
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

/// Stores dynamic field type information for a specific function
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

    /// Creates a DynamicFieldInfo with a single mapping from the given type to a single dynamic field type.
    /// This is a convenience method for creating simple dynamic field entries.
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

/// Checks whether a type transitively contains the given struct through its fields.
pub fn type_transitively_contains_struct(
    env: &GlobalEnv,
    ty: &Type,
    target_qid: &QualifiedId<DatatypeId>,
    visited: &mut BTreeSet<QualifiedId<DatatypeId>>,
) -> bool {
    if let Some((qid, type_args)) = ty.get_datatype() {
        if qid == *target_qid {
            return true;
        }
        if !visited.insert(qid) {
            return false;
        }
        let module_env = env.get_module(qid.module_id);
        if let Some(struct_env) = module_env.find_struct(qid.id.symbol()) {
            for field in struct_env.get_fields() {
                let field_ty = field.get_type().instantiate(type_args);
                if type_transitively_contains_struct(env, &field_ty, target_qid, visited) {
                    return true;
                }
            }
        }
    } else if let Type::Vector(elem_ty) = ty {
        return type_transitively_contains_struct(env, elem_ty, target_qid, visited);
    }
    false
}

/// Get the information computed by this analysis for the global environment
pub fn get_env_info(env: &GlobalEnv) -> Rc<DynamicFieldInfo> {
    env.get_extension::<DynamicFieldInfo>().unwrap()
}

/// Get the information computed by this analysis for a function
pub fn get_fun_info(data: &FunctionData) -> &DynamicFieldInfo {
    data.annotations.get::<DynamicFieldInfo>().unwrap()
}

pub fn get_function_return_local_pos(local_idx: usize, code: &[Bytecode]) -> Option<usize> {
    let mut return_pos = None;
    for bc in code.into_iter() {
        if return_pos.is_some() {
            // if function have few return statments
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

/// Collect all dynamic field function QualifiedIds from the environment
fn collect_df_qids(env: &GlobalEnv) -> DfQids {
    let name_value = vec![
        // dynamic field operations
        env.dynamic_field_borrow_qid(),
        env.dynamic_field_exists_with_type_qid(),
        // dynamic object field operations
        env.dynamic_object_field_borrow_qid(),
        env.dynamic_object_field_exists_with_type_qid(),
    ]
    .into_iter()
    .flatten()
    .collect_vec();
    let name_value_mut = vec![
        // dynamic field operations
        env.dynamic_field_add_qid(),
        env.dynamic_field_borrow_mut_qid(),
        env.dynamic_field_remove_qid(),
        env.dynamic_field_remove_if_exists_qid(),
        // dynamic object field operations
        env.dynamic_object_field_add_qid(),
        env.dynamic_object_field_borrow_mut_qid(),
        env.dynamic_object_field_remove_qid(),
    ]
    .into_iter()
    .flatten()
    .collect_vec();
    let name_only = vec![
        // dynamic field operations
        env.dynamic_field_exists_qid(),
        // dynamic object field operations
        env.dynamic_object_field_exists_qid(),
    ]
    .into_iter()
    .flatten()
    .collect_vec();
    let all = [&name_value, &name_value_mut, &name_only]
        .into_iter()
        .cloned()
        .flatten()
        .collect_vec();
    DfQids {
        name_value,
        name_value_mut,
        name_only,
        all,
    }
}

struct DfQids {
    name_value: Vec<QualifiedId<move_model::model::FunId>>,
    name_value_mut: Vec<QualifiedId<move_model::model::FunId>>,
    name_only: Vec<QualifiedId<move_model::model::FunId>>,
    all: Vec<QualifiedId<move_model::model::FunId>>,
}

/// Collect dynamic field type information from a function's bytecode
fn collect_dynamic_field_info(
    targets: &FunctionTargetsHolder,
    builder: &mut FunctionDataBuilder,
    verified_or_inlined: bool,
    use_uid: bool,
) -> DynamicFieldInfo {
    let env = builder.fun_env.module_env.env;
    let df_qids = collect_df_qids(env);
    let uid_type = env
        .uid_qid()
        .map(|qid| Type::Datatype(qid.module_id, qid.id, vec![]));

    // compute map of temp index that load object ids to type of object
    let uid_info = compute_uid_info(&builder.get_target(), targets, &builder.data.code);

    let alias_info =
        ReachingDefProcessor::analyze_reaching_definitions(&builder.fun_env, &builder.data);

    let mut info = DynamicFieldInfo::iter_union(builder.data.code.iter().enumerate().filter_map(
        |(offset, bc)| match bc {
            Bytecode::Call(_, _, Operation::Function(module_id, fun_id, type_inst), srcs, _) => {
                let callee_id = module_id.qualified(*fun_id);

                // Determine the object type for this df call.
                // When use_uid is set (detected in initialize), always use UID type.
                // Otherwise, look up the parent object type, falling back to UID
                // with a warning when the parent can't be determined.
                let get_obj_type = |offset: usize| -> Option<Type> {
                    if use_uid {
                        return uid_type.clone();
                    }
                    if let Some((_, obj_type)) =
                        get_uid_object_type(&uid_info, &alias_info, srcs[0], offset)
                    {
                        return Some(obj_type.clone());
                    }
                    // UID fallback: emit warning when parent is unknown
                    let uid_qid = env.uid_qid()?;
                    if verified_or_inlined
                        || builder
                            .fun_env
                            .get_return_types()
                            .iter()
                            .any(|x| x.is_mutable_reference())
                    {
                        let loc = builder.get_loc(bc.get_attr_id());
                        env.add_diag(
                            Diagnostic::new(Severity::Warning)
                                .with_message(
                                    "UID object type not found, dynamic fields will be placed under UID",
                                )
                                .with_labels(vec![Label::primary(loc.file_id(), loc.span())]),
                        );
                    }
                    Some(Type::Datatype(uid_qid.module_id, uid_qid.id, vec![]))
                };

                if callee_id == builder.fun_env.get_qualified_id() {
                    return None;
                }

                if df_qids.name_value.contains(&callee_id) {
                    if let Some(obj_type) = get_obj_type(offset) {
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

                if df_qids.name_value_mut.contains(&callee_id) {
                    if let Some(obj_type) = get_obj_type(offset) {
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

                if df_qids.name_only.contains(&callee_id) {
                    if let Some(obj_type) = get_obj_type(offset) {
                        return Some(DynamicFieldInfo::singleton(
                            obj_type,
                            NameValueInfo::NameOnly(type_inst[0].clone()),
                        ));
                    }
                }

                let fun_id_with_info = targets
                    .get_callee_spec_qid(&builder.fun_env.get_qualified_id(), &callee_id)
                    .unwrap_or(&callee_id);

                let func_env = env.get_function(*fun_id_with_info);

                if func_env.is_native() || func_env.is_intrinsic() {
                    return None;
                }

                let info = targets
                    .get_data(fun_id_with_info, &FunctionVariant::Baseline)
                    .map(|data| get_fun_info(data))?;
                Some(info.instantiate(type_inst))
            }
            _ => None,
        },
    ));

    info.uid_info = uid_info;

    let code = std::mem::take(&mut builder.data.code);
    for (offset, bc) in code.into_iter().enumerate() {
        match bc {
            Bytecode::Call(
                attr_id,
                dests,
                Operation::Function(module_id, fun_id, mut type_inst),
                mut srcs,
                aa,
            ) if df_qids.all.contains(&module_id.qualified(fun_id)) => {
                if use_uid {
                    // All df operations use UID type directly
                    if let Some(ref uid_ty) = uid_type {
                        type_inst.push(uid_ty.clone());
                    }
                } else if let Some((obj_local, obj_type)) =
                    get_uid_object_type(&info.uid_info, &alias_info, srcs[0], offset)
                {
                    srcs[0] = *obj_local;
                    if !df_qids
                        .name_value_mut
                        .contains(&module_id.qualified(fun_id))
                        && builder.get_local_type(srcs[0]).is_mutable_reference()
                    {
                        srcs[0] = builder.emit_let_read_ref(srcs[0]);
                    }
                    type_inst.push(obj_type.clone());
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

/// Like `compute_uid_info` but runs before `process` (no callee annotations available).
/// Computes callee uid_info on-the-fly instead of reading annotations.
fn compute_uid_info_local(
    fun_target: &FunctionTarget,
    targets: &FunctionTargetsHolder,
    code: &[Bytecode],
) -> BTreeMap<usize, (usize, Type)> {
    let env = fun_target.global_env();
    code.iter()
        .filter_map(|bc| match bc {
            Bytecode::Call(
                attr_id,
                dests,
                Operation::BorrowField(mid, sid, tys, offset),
                srcs,
                _,
            ) if is_uid_field_access(&env.get_struct(mid.qualified(*sid)), *offset)
                && !dests.is_empty() =>
            {
                Some((
                    dests[0],
                    (srcs[0], Type::Datatype(*mid, *sid, tys.clone()), *attr_id),
                ))
            }
            Bytecode::Call(attr_id, dests, Operation::GetField(mid, sid, tys, offset), srcs, _)
                if is_uid_field_access(&env.get_struct(mid.qualified(*sid)), *offset)
                    && !dests.is_empty() =>
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
                if callee_id == fun_target.global_env().type_inv_qid() {
                    return None;
                }

                let callee_data = targets.get_data(&callee_id, &FunctionVariant::Baseline)?;
                let callee_env = env.get_function(callee_id);
                let callee_target = FunctionTarget::new(&callee_env, callee_data);
                let callee_uid_info =
                    compute_uid_info_local(&callee_target, targets, &callee_data.code);

                for key in callee_uid_info.keys() {
                    if let Some(ret_pos) = get_function_return_local_pos(*key, &callee_data.code) {
                        let (_, obj_type) = callee_uid_info.get(key).unwrap();
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
                Some((temp_idx, (types[0].0, types[0].1.clone())))
            } else {
                None
            }
        })
        .collect()
}

/// Computes a mapping from temporary indices to the objects and types of objects they reference
fn compute_uid_info(
    fun_target: &FunctionTarget,
    targets: &FunctionTargetsHolder,
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

/// Checks if a field access at the given offset is accessing the single UID field.
/// Returns true if:
/// - The struct has the `key` ability and the offset is 0, OR
/// - The offset matches the single UID field offset
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
    // First check if temp_idx is directly in uid_info
    uid_info.get(&temp_idx).or_else(|| {
        // Otherwise, check if we can find it through alias information
        alias_info.get(&(off as u16)).and_then(|state| {
            ReachingDefProcessor::all_aliases(state, &temp_idx)
                .iter()
                .filter_map(|alias| uid_info.get(alias))
                .exactly_one()
                .ok()
        })
    })
}

pub struct DynamicFieldAnalysisProcessor {
    use_uid: Cell<bool>,
}

impl DynamicFieldAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self {
            use_uid: Cell::new(false),
        })
    }
}

impl FunctionTargetProcessor for DynamicFieldAnalysisProcessor {
    fn initialize(&self, env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {
        if env.uid_qid().is_none() {
            return;
        }
        let df_qids = collect_df_qids(env);

        // Check if any accessible function has a df call where the parent
        // object type can't be resolved locally. When that happens, fall back
        // to UID type for ALL df operations for consistency.
        let mut use_uid = false;
        for fun_id in targets.get_funs().collect_vec() {
            let fun_env = env.get_function(fun_id);
            if fun_env.is_native() || fun_env.is_intrinsic() {
                continue;
            }
            let data = match targets.get_data(&fun_id, &FunctionVariant::Baseline) {
                Some(d) => d,
                None => continue,
            };
            let target = FunctionTarget::new(&fun_env, data);
            let info = get_info(&target);
            if !info.accessible() {
                continue;
            }

            let uid_info = compute_uid_info_local(&target, targets, &data.code);
            let alias_info = ReachingDefProcessor::analyze_reaching_definitions(&fun_env, data);

            for (offset, bc) in data.code.iter().enumerate() {
                if let Bytecode::Call(attr_id, _, Operation::Function(mid, fid, _), srcs, _) = bc {
                    if df_qids.all.contains(&mid.qualified(*fid))
                        && get_uid_object_type(&uid_info, &alias_info, srcs[0], offset).is_none()
                    {
                        use_uid = true;
                        let loc = target.get_bytecode_loc(*attr_id);
                        env.add_diag(
                            Diagnostic::new(Severity::Warning)
                                .with_message(
                                    "UID object type not found, dynamic fields will be placed under UID",
                                )
                                .with_labels(vec![Label::primary(loc.file_id(), loc.span())]),
                        );
                    }
                }
            }
        }

        self.use_uid.set(use_uid);
    }

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

        let use_uid = self.use_uid.get();

        let mut builder = FunctionDataBuilder::new(fun_env, data);

        // Collect the dynamic field info
        let info = collect_dynamic_field_info(
            targets,
            &mut builder,
            info.verified || info.inlined,
            use_uid,
        );

        builder
            .data
            .annotations
            .set_with_fixedpoint_check(info, scc_opt.is_some());

        builder.data
    }

    fn finalize(&self, env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {
        // Collect and combine all functions' dynamic field info
        let combined_info = DynamicFieldInfo::iter_union(
            targets
                .specs()
                .copied()
                .chain(targets.get_funs().filter(|fun_id| {
                    targets.is_pure_fun(fun_id) || targets.is_abort_check_fun(fun_id)
                }))
                .filter_map(|fun_id| {
                    targets
                        .get_data(&fun_id, &FunctionVariant::Baseline)
                        .and_then(|data| {
                            data.annotations
                                .get::<DynamicFieldInfo>()
                                .map(|info| info.clone())
                        })
                }),
        );

        // Detect well-foundedness cycles: a dynamic field value type that
        // transitively contains the parent struct creates a Boogie datatype
        // cycle (e.g. UID → Table<K,V> where Table has a UID field).
        // Report the error at each function that introduces the cyclic usage.
        let translated_funs: Vec<_> = targets.get_funs().collect();
        for fun_id in &translated_funs {
            let Some(data) = targets.get_data(fun_id, &FunctionVariant::Baseline) else {
                continue;
            };
            let Some(info) = data.annotations.get::<DynamicFieldInfo>() else {
                continue;
            };
            for (ty, name_value_set) in &info.dynamic_field_mappings {
                let Some((struct_qid, _)) = ty.get_datatype() else {
                    continue;
                };
                for nv in name_value_set {
                    if let Some((_name, value)) = nv.as_name_value() {
                        if type_transitively_contains_struct(
                            env,
                            value,
                            &struct_qid,
                            &mut BTreeSet::new(),
                        ) {
                            let fun_env = env.get_function(*fun_id);
                            let struct_env = env.get_struct(struct_qid);
                            env.error(
                                &fun_env.get_loc(),
                                &format!(
                                    "function `{}` uses a dynamic field whose value type \
                                     contains `{}`, creating a well-foundedness cycle in \
                                     the Boogie datatype. This is not yet supported by the prover.",
                                    fun_env.get_full_name_str(),
                                    struct_env.get_full_name_str(),
                                ),
                            );
                        }
                    }
                }
            }
        }

        // Set the combined info in the environment
        env.set_extension(combined_info);
    }

    fn name(&self) -> String {
        "dynamic_field_analysis_processor".to_string()
    }
}
