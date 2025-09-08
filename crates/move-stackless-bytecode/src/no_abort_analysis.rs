use move_model::model::{FunctionEnv, GlobalEnv};
use std::fmt::{self, Formatter};

use crate::{
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant},
    stackless_bytecode::{Bytecode, Operation, PropKind},
};

#[derive(Clone, Default, Debug)]
pub struct NoAbortInfo {
    pub does_not_abort: bool,
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
        let info = data
            .annotations
            .get_or_default_mut::<NoAbortInfo>(true);

        let env = fun_env.module_env.env;
        let qualified_id = fun_env.get_qualified_id();
        let variant = FunctionVariant::Baseline;

        if fun_env.is_native() {
            info.does_not_abort = env.func_not_aborts(qualified_id).unwrap();
            return data;
        }

        for callee in fun_env.get_called_functions() {
            let callee_info = targets
                .get_data(&callee, &variant)
                .unwrap()
                .annotations
                .get::<NoAbortInfo>()
                .unwrap();

            if !callee_info.does_not_abort && !targets.is_abort_check_fun(&callee) {
                info.does_not_abort = false;
                return data;
            }
        }

        for bytecode in data.code.iter() {
            let aborts = match bytecode {
                // calles covered upper
                Bytecode::Call(_, _, op, _, _) =>  op.can_abort() && !matches!(op, Operation::Function { .. }),
                Bytecode::Abort(_, _) => true,
                Bytecode::Prop(_, kind, _) => *kind == PropKind::Assert,
                Bytecode::Assign(_, _, _, _) |
                Bytecode::Branch(_, _, _, _) |
                Bytecode::Load(_, _, _) |
                Bytecode::Ret(_, _) |
                Bytecode::Jump(_, _) |
                Bytecode::VariantSwitch(_, _, _) |
                Bytecode::Label(_, _) |
                Bytecode::Nop(_) |
                Bytecode::SaveMem(_, _, _) => false,
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
                let result = target
                    .get_annotations()
                    .get::<NoAbortInfo>()
                    .cloned()
                    .unwrap_or_default();
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
