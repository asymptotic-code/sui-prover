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

// NOTE: we don't care about type cycles here, as they are resticted by Move type system/compiler
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
