use codespan_reporting::diagnostic::Severity;
use move_model::{
    model::{FunctionEnv, FunctionVisibility, GlobalEnv, Loc, ModuleId, StructOrEnumEnv},
    ty::Type,
};

use crate::{
    exp_generator::ExpGenerator,
    function_data_builder::FunctionDataBuilder,
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    stackless_bytecode::{Bytecode, Operation},
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

/// Result of analyzing a type for invariants: the nested field path plus
/// the qualified ID and type instantiation of the invariant function to call.
#[derive(Clone, Debug)]
struct InvPathResult {
    nested_path: Vec<NestedPathEntry>,
    inv_fun: move_model::model::QualifiedId<move_model::model::FunId>,
    type_inst: Vec<Type>,
}

/// Analyze a type to find all nested paths that lead to an invariant type.
/// If `filter_module` is Some, only consider invariants from that module.
/// If `filter_module` is None, consider invariants from any module.
fn analyze_type_invariants(
    targets: &FunctionTargetsHolder,
    env: &GlobalEnv,
    ty: &Type,
    filter_module: Option<ModuleId>,
) -> Vec<InvPathResult> {
    let mut results = Vec::new();
    analyze_type_invariants_r(targets, env, vec![], ty, filter_module, &mut results);

    for result in &results {
        if let Some(npe) = result.nested_path.iter().find(|p| p.enum_loc.is_some()) {
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
    filter_module: Option<ModuleId>,
    results: &mut Vec<InvPathResult>,
) {
    match ty.skip_reference() {
        Type::Datatype(mid, datatype_qid, type_params) => {
            let qid = mid.qualified(*datatype_qid);

            // Check if this type has an invariant
            if let Some(inv_fun_qid) = targets.get_inv_by_datatype(&qid) {
                // If filtering by module, check that the invariant function
                // is in the specified module
                let matches_module = filter_module.map_or(true, |m| inv_fun_qid.module_id == m);
                if matches_module {
                    results.push(InvPathResult {
                        nested_path: nested.clone(),
                        inv_fun: *inv_fun_qid,
                        type_inst: type_params.clone(),
                    });
                }
            }

            // Recurse into fields
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
                analyze_type_invariants_r(
                    targets,
                    env,
                    new_nested,
                    &field_ty,
                    filter_module,
                    results,
                );
            });
        }
        _ => {
            // Skip type parameters and primitives
        }
    }
}

/// Emit a direct call to an invariant function for the value at `param`,
/// navigating nested field paths as needed. Returns the bool temp holding the result.
fn emit_direct_inv_call(
    builder: &mut FunctionDataBuilder,
    param: usize,
    inv_path: &InvPathResult,
) -> usize {
    let mut parameter = param;
    for (idx, path_el) in inv_path.nested_path.iter().enumerate() {
        parameter = builder.emit_let_get_datatype_field(
            parameter,
            if idx == 0 {
                builder.get_local_type(param)
            } else {
                inv_path.nested_path[idx - 1].field_ty.clone()
            },
            path_el.field_ty.clone(),
            path_el.field_offset,
        );
    }
    builder.emit_inv_fun_call(parameter, &inv_path.inv_fun, inv_path.type_inst.clone())
}

/// Process direct invariant calls for a parameter, emitting via the callback.
/// If `filter_module` is Some, only consider invariants from that module.
/// If `filter_module` is None, consider invariants from any module.
fn process_inv<F>(
    builder: &mut FunctionDataBuilder,
    targets: &FunctionTargetsHolder,
    param: usize,
    filter_module: Option<ModuleId>,
    emit: F,
) where
    F: Fn(&mut FunctionDataBuilder, usize),
{
    let inv_paths = analyze_type_invariants(
        targets,
        builder.global_env(),
        &builder.get_local_type(param),
        filter_module,
    );
    for inv_path in &inv_paths {
        let bool_temp = emit_direct_inv_call(builder, param, inv_path);
        emit(builder, bool_temp);
    }
}

/// Check if a module contains any invariant functions.
fn module_has_invariant_funs(targets: &FunctionTargetsHolder, module_id: ModuleId) -> bool {
    targets
        .get_datatype_invs()
        .iter()
        .any(|(_, inv_fun_qid)| inv_fun_qid.module_id == module_id)
}

impl FunctionTargetProcessor for TypeInvariantAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        let func_qid = func_env.get_qualified_id();
        let is_spec = targets.is_spec(&func_qid);
        let module_id = func_env.module_env.get_id();
        let has_module_inv_funs = module_has_invariant_funs(targets, module_id);
        let is_inv_fun = targets.get_datatype_by_inv(&func_qid).is_some();

        // Nothing to do if:
        // - not a spec function AND
        // - module has no invariants (so no public function or cross-module call handling needed)
        if !is_spec && !has_module_inv_funs {
            return data;
        }

        // Skip invariant functions themselves
        if is_inv_fun {
            return data;
        }

        let is_public_or_friend = matches!(
            func_env.visibility(),
            FunctionVisibility::Public | FunctionVisibility::Friend
        );

        let mut builder = FunctionDataBuilder::new(func_env, data);
        let code = std::mem::take(&mut builder.data.code);

        builder.set_loc(builder.fun_env.get_loc().at_start());

        // For spec functions: add requires using direct calls to ALL invariant functions
        if is_spec {
            for param in 0..builder.fun_env.get_parameter_count() {
                process_inv(&mut builder, targets, param, None, |b, temp| {
                    b.emit_requires(temp);
                });
            }
        }

        // For public/friend functions in the defining module: add requires
        // using direct calls to the invariant function (filtered to this module)
        if !is_spec && has_module_inv_funs && is_public_or_friend {
            for param in 0..builder.fun_env.get_parameter_count() {
                process_inv(&mut builder, targets, param, Some(module_id), |b, temp| {
                    b.emit_requires(temp);
                });
            }
        }

        for bc in code {
            // For non-spec functions in the defining module,
            // wrap cross-module calls with assert-before / assume-after
            if !is_spec && has_module_inv_funs {
                if let Bytecode::Call(
                    _attr_id,
                    ref dests,
                    Operation::Function(callee_mid, _callee_fid, ref _tys),
                    ref srcs,
                    _,
                ) = bc
                {
                    let callee_module_id = callee_mid;
                    if callee_module_id != module_id {
                        // Cross-module call: assert invariants on arguments before the call
                        let srcs_copy: Vec<usize> = srcs.clone();
                        let dests_copy: Vec<usize> = dests.clone();
                        for src in &srcs_copy {
                            process_inv(&mut builder, targets, *src, Some(module_id), |b, temp| {
                                b.emit_assert(temp);
                            });
                        }

                        // Emit the actual call
                        builder.emit(bc);

                        // After the call: assume invariants on return values
                        for dest in &dests_copy {
                            process_inv(
                                &mut builder,
                                targets,
                                *dest,
                                Some(module_id),
                                |b, temp| {
                                    b.emit_assume(temp);
                                },
                            );
                        }

                        // Also assume invariants on mut ref parameters
                        for src in &srcs_copy {
                            if builder.get_local_type(*src).is_mutable_reference() {
                                process_inv(
                                    &mut builder,
                                    targets,
                                    *src,
                                    Some(module_id),
                                    |b, temp| {
                                        b.emit_assume(temp);
                                    },
                                );
                            }
                        }

                        continue;
                    }
                }
            }

            match bc {
                Bytecode::Ret(_, ref rets) => {
                    // Spec functions: ensures using direct calls to ALL invariant functions
                    if is_spec {
                        builder.set_loc(builder.fun_env.get_loc().at_end());
                        for ret in rets {
                            process_inv(&mut builder, targets, *ret, None, |b, temp| {
                                b.emit_ensures(temp);
                            });
                        }
                        for param in 0..builder.fun_env.get_parameter_count() {
                            if builder.get_local_type(param).is_mutable_reference() {
                                process_inv(&mut builder, targets, param, None, |b, temp| {
                                    b.emit_ensures(temp);
                                });
                            }
                        }
                    }

                    // For public/friend functions, add ensures using direct calls
                    if !is_spec && has_module_inv_funs && is_public_or_friend {
                        builder.set_loc(builder.fun_env.get_loc().at_end());
                        for ret in rets {
                            process_inv(&mut builder, targets, *ret, Some(module_id), |b, temp| {
                                b.emit_ensures(temp);
                            });
                        }
                        for param in 0..builder.fun_env.get_parameter_count() {
                            if builder.get_local_type(param).is_mutable_reference() {
                                process_inv(
                                    &mut builder,
                                    targets,
                                    param,
                                    Some(module_id),
                                    |b, temp| {
                                        b.emit_ensures(temp);
                                    },
                                );
                            }
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
