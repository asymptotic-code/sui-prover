use move_model::model::{FunctionEnv, GlobalEnv};
use std::fmt::{self, Formatter};

use crate::{
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant},
    stackless_bytecode::{Bytecode, Operation, PropKind},
    verification_analysis::VerificationInfo,
};

#[derive(Clone, Default, Debug)]
pub struct NoAbortInfo {
    pub does_not_abort: bool,
}

pub fn has_no_abort_spec(targets: &FunctionTargetsHolder, fun_env: &FunctionEnv) -> bool {
    targets
        .get_spec_by_fun(&fun_env.get_qualified_id())
        .is_some_and(|spec_qid| {
            let spec_data = targets
                .get_data(&spec_qid, &FunctionVariant::Baseline)
                .expect(&format!(
                    "missing spec data for spec={}, fun={}",
                    fun_env
                        .module_env
                        .env
                        .get_function(*spec_qid)
                        .get_full_name_str(),
                    fun_env.get_full_name_str()
                ));

            !targets.ignore_aborts().contains(&spec_qid)
                && !Bytecode::calls_function(&spec_data.code, &fun_env.module_env.env.asserts_qid())
        })
}

pub fn does_not_abort(
    targets: &FunctionTargetsHolder,
    callee_env: &FunctionEnv,
    caller_env: Option<&FunctionEnv>,
) -> bool {
    if callee_env.is_native() {
        return callee_env
            .module_env
            .env
            .func_not_aborts(callee_env.get_qualified_id())
            .unwrap();
    }
    if callee_env.is_intrinsic()
        && callee_env
            .module_env
            .env
            .func_not_aborts(callee_env.get_qualified_id())
            .unwrap()
    {
        return true;
    }

    if !targets.has_target(callee_env, &FunctionVariant::Baseline)
        && targets.data_bypass_allowed(
            &callee_env.get_qualified_id(),
            &caller_env.map(|fun_env| fun_env.get_qualified_id()),
        )
    {
        return true;
    }

    let no_abort_info = targets
        .get_annotation::<NoAbortInfo>(&callee_env.get_qualified_id(), &FunctionVariant::Baseline);
    let use_no_abort_spec = targets.get_spec_by_fun(&callee_env.get_qualified_id())
        != caller_env
            .map(|fun_env| fun_env.get_qualified_id())
            .as_ref()
        && has_no_abort_spec(targets, callee_env);
    no_abort_info.does_not_abort
        || use_no_abort_spec
        || targets.is_function_with_abort_check(&callee_env.get_qualified_id())
}

pub struct NoAbortAnalysisProcessor();

impl NoAbortAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }
}

impl FunctionTargetProcessor for NoAbortAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        fun_env: &FunctionEnv,
        mut data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        let verification_shadowed = data
            .annotations
            .get::<VerificationInfo>()
            .map(|info| info.shadowed)
            .unwrap_or(false);

        let info = data.annotations.get_or_default_mut::<NoAbortInfo>(true);

        let env = fun_env.module_env.env;
        let qualified_id = fun_env.get_qualified_id();

        if fun_env.is_native() {
            info.does_not_abort = env.func_not_aborts(qualified_id).unwrap();
            return data;
        }

        if verification_shadowed
            || (fun_env.is_intrinsic() && env.func_not_aborts(qualified_id).unwrap())
        {
            info.does_not_abort = true;
            return data;
        }

        for callee in fun_env.get_called_functions() {
            if !does_not_abort(
                targets,
                &fun_env.module_env.env.get_function(callee),
                Some(&fun_env),
            ) {
                info.does_not_abort = false;
                return data;
            }
        }

        for bytecode in data.code.iter() {
            let aborts = match bytecode {
                // callees covered upper
                Bytecode::Call(_, _, op, _, _) => {
                    op.can_abort() && !matches!(op, Operation::Function { .. })
                }
                Bytecode::Abort(_, _) => true,
                Bytecode::Prop(_, kind, _) => *kind == PropKind::Assert,
                Bytecode::Assign(_, _, _, _)
                | Bytecode::Branch(_, _, _, _)
                | Bytecode::Load(_, _, _)
                | Bytecode::Ret(_, _)
                | Bytecode::Jump(_, _)
                | Bytecode::VariantSwitch(_, _, _)
                | Bytecode::Label(_, _)
                | Bytecode::Nop(_)
                | Bytecode::SaveMem(_, _, _) => false,
            };

            if aborts {
                info.does_not_abort = false;
                return data;
            }
        }

        info.does_not_abort = true;
        data
    }

    fn name(&self) -> String {
        "no_abort_analysis".to_string()
    }

    fn dump_result(
        &self,
        f: &mut Formatter<'_>,
        env: &GlobalEnv,
        targets: &FunctionTargetsHolder,
    ) -> fmt::Result {
        writeln!(f, "\n********* Result of no-abort analysis *********\n")?;

        writeln!(f, "no-abort analysis: [")?;
        for fun_id in targets.get_funs() {
            let fenv = env.get_function(fun_id);
            for fun_variant in targets.get_target_variants(&fenv) {
                let target = targets.get_target(&fenv, &fun_variant);
                let result = target.get_annotations().get::<NoAbortInfo>().unwrap();
                write!(f, "  {}: ", fenv.get_full_name_str())?;
                if result.does_not_abort {
                    writeln!(f, "does not abort")?;
                } else {
                    writeln!(f, "can abort")?;
                }
            }
        }
        writeln!(f, "]")
    }
}

pub fn get_info(data: &FunctionData) -> &NoAbortInfo {
    data.annotations.get::<NoAbortInfo>().unwrap()
}
