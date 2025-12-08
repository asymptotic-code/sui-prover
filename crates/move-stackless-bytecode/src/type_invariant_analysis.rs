use std::collections::BTreeSet;

use codespan_reporting::diagnostic::Severity;
use move_model::{
    model::{FunctionEnv, GlobalEnv, Loc, StructOrEnumEnv},
    ty::Type,
};

use crate::{
    exp_generator::ExpGenerator,
    function_data_builder::FunctionDataBuilder,
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    stackless_bytecode::Bytecode,
};

pub struct TypeInvariantAnalysisProcessor();

impl TypeInvariantAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NestedPathEntry {
    field_ty: Type,
    field_offset: usize,
    enum_loc: Option<Loc>,
}

fn analyze_type_invariants(
    targets: &FunctionTargetsHolder,
    env: &GlobalEnv,
    ty: &Type,
) -> BTreeSet<Vec<NestedPathEntry>> {
    let mut results = BTreeSet::new();
    analyze_type_invariants_r(targets, env, vec![], ty, &mut results);

    for result in &results {
        if let Some(npe) = result.iter().find(|p| p.enum_loc.is_some()) {
            env.diag(
                Severity::Error,
                npe.enum_loc.as_ref().unwrap(),
                "Type invariants cannot be used through enum fields",
            );
        }
    }

    results
}

fn analyze_type_invariants_r(
    targets: &FunctionTargetsHolder,
    env: &GlobalEnv,
    nested: Vec<NestedPathEntry>,
    ty: &Type,
    results: &mut BTreeSet<Vec<NestedPathEntry>>,
) {
    match ty.skip_reference() {
        Type::TypeParameter(_) => {
            results.insert(vec![]);
        }
        Type::Datatype(mid, datatype_qid, type_params) => {
            let qid = mid.qualified(*datatype_qid);

            if targets.get_inv_by_datatype(&qid).is_some() {
                results.insert(nested);
            } else {
                let mut enum_loc = None;
                let fields: Vec<(Type, usize)> = match env.get_struct_or_enum_qid(qid) {
                    StructOrEnumEnv::Struct(struct_env) => struct_env
                        .get_fields()
                        .map(|f| (f.get_type(), f.get_offset()))
                        .collect(),
                    StructOrEnumEnv::Enum(enum_env) => {
                        enum_loc = Some(enum_env.get_loc());
                        enum_env
                            .get_all_fields()
                            .map(|f| (f.get_type(), f.get_offset()))
                            .collect()
                    }
                };

                fields.into_iter().for_each(|(field_ty, field_offset)| {
                    let field_ty = field_ty.instantiate(type_params);
                    let mut new_nested = nested.clone();
                    new_nested.push(NestedPathEntry {
                        field_ty: field_ty.clone(),
                        field_offset,
                        enum_loc: enum_loc.clone(),
                    });
                    analyze_type_invariants_r(targets, env, new_nested, &field_ty, results);
                });
            }
        }
        _ => {}
    }
}

fn process_type_inv<F>(
    builder: &mut FunctionDataBuilder,
    targets: &FunctionTargetsHolder,
    param: usize,
    emit: F,
) where
    F: Fn(&mut FunctionDataBuilder, usize),
{
    let nested_invs = analyze_type_invariants(
        targets,
        builder.global_env(),
        &builder.get_local_type(param),
    );
    for nested_path in nested_invs {
        let mut parameter = param;
        for (idx, path_el) in nested_path.iter().enumerate() {
            parameter = builder.emit_let_get_datatype_field(
                parameter,
                if idx == 0 {
                    builder.get_local_type(param)
                } else {
                    nested_path[idx - 1].field_ty.clone()
                },
                path_el.field_ty.clone(),
                path_el.field_offset,
            );
        }
        let type_inv_temp = builder.emit_type_inv(parameter);
        emit(builder, type_inv_temp);
    }
}

fn process_type_inv_with_requires(
    builder: &mut FunctionDataBuilder,
    targets: &FunctionTargetsHolder,
    param: usize,
) {
    process_type_inv(builder, targets, param, |b, temp| {
        b.emit_requires(temp);
    });
}

fn process_type_inv_with_ensures(
    builder: &mut FunctionDataBuilder,
    targets: &FunctionTargetsHolder,
    param: usize,
) {
    process_type_inv(builder, targets, param, |b, temp| {
        b.emit_ensures(temp);
    });
}

fn detect_recursion_cycles(targets: &FunctionTargetsHolder, env: &GlobalEnv, ty: &Type) -> bool {
    let mut cycles = BTreeSet::new();
    let mut visited = BTreeSet::new();
    let mut path = Vec::new();

    find_recursion_cycles_r(
        env,
        ty.skip_reference(),
        &mut visited,
        &mut path,
        &mut cycles,
    );

    for cycle_ty in &cycles {
        if let Type::Datatype(mid, datatype_id, _) = cycle_ty {
            let qid = mid.qualified(*datatype_id);
            if targets.get_inv_by_datatype(&qid).is_none() {
                continue;
            }

            let loc = match env.get_struct_or_enum_qid(qid) {
                StructOrEnumEnv::Struct(struct_env) => struct_env.get_loc(),
                StructOrEnumEnv::Enum(enum_env) => enum_env.get_loc(),
            };
            env.diag(
                Severity::Error,
                &loc,
                "Type invariant is not allowed for recursive types",
            );
            return true;
        }
    }

    false
}

fn find_recursion_cycles_r(
    env: &GlobalEnv,
    ty: &Type,
    visited: &mut BTreeSet<Type>,
    path: &mut Vec<Type>,
    cycles: &mut BTreeSet<Type>,
) {
    let ty = ty.skip_reference();

    match ty {
        Type::Datatype(mid, datatype_id, type_params) => {
            let base_ty = Type::Datatype(*mid, *datatype_id, vec![]);

            if let Some(cycle_start) = path.iter().position(|t| {
                if let Type::Datatype(m, d, _) = t {
                    *m == *mid && *d == *datatype_id
                } else {
                    false
                }
            }) {
                // Found a cycle - add all types in the cycle
                for cycle_ty in &path[cycle_start..] {
                    cycles.insert(cycle_ty.clone());
                }
                cycles.insert(ty.clone());
                return;
            }

            if visited.contains(&base_ty) {
                return;
            }

            path.push(ty.clone());

            let qid = mid.qualified(*datatype_id);
            let fields: Vec<Type> = match env.get_struct_or_enum_qid(qid) {
                StructOrEnumEnv::Struct(struct_env) => struct_env
                    .get_fields()
                    .map(|f| f.get_type().instantiate(type_params))
                    .collect(),
                StructOrEnumEnv::Enum(enum_env) => enum_env
                    .get_all_fields()
                    .map(|f| f.get_type().instantiate(type_params))
                    .collect(),
            };

            for field_ty in fields {
                find_recursion_cycles_r(env, &field_ty, visited, path, cycles);
            }

            path.pop();
            visited.insert(base_ty);
        }
        Type::Vector(inner_ty) => {
            find_recursion_cycles_r(env, inner_ty, visited, path, cycles);
        }
        _ => {}
    }
}

impl FunctionTargetProcessor for TypeInvariantAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        if !targets.is_spec(&func_env.get_qualified_id()) {
            // only need to do this for spec functions
            return data;
        }

        let mut builder = FunctionDataBuilder::new(func_env, data);
        let code = std::mem::take(&mut builder.data.code);

        builder.set_loc(builder.fun_env.get_loc().at_start());
        for param in 0..builder.fun_env.get_parameter_count() {
            if detect_recursion_cycles(
                &targets,
                builder.global_env(),
                &builder.get_local_type(param),
            ) {
                return builder.data;
            }

            process_type_inv_with_requires(&mut builder, targets, param);
        }

        for bc in code {
            match bc {
                Bytecode::Ret(_, ref rets) => {
                    builder.set_loc(builder.fun_env.get_loc().at_end());
                    for ret in rets {
                        process_type_inv_with_ensures(&mut builder, targets, *ret);
                    }
                    for param in 0..builder.fun_env.get_parameter_count() {
                        if builder.get_local_type(param).is_mutable_reference() {
                            process_type_inv_with_ensures(&mut builder, targets, param);
                        }
                    }
                }
                _ => {}
            }
            builder.emit(bc);
        }

        builder.data
    }

    fn name(&self) -> String {
        "type_invariant_analysis".to_string()
    }
}
