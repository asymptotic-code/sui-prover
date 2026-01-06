use move_model::model::{FunctionEnv, GlobalEnv};
use std::fmt::{self, Formatter};

use crate::{
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant},
};

#[derive(Clone, Default, Debug)]
pub struct DeterministicInfo {
    pub is_deterministic: bool,
}

pub struct DeterministicAnalysisProcessor();

impl DeterministicAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }
}

impl FunctionTargetProcessor for DeterministicAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        fun_env: &FunctionEnv,
        mut data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        let info = data
            .annotations
            .get_or_default_mut::<DeterministicInfo>(true);

        let env = fun_env.module_env.env;
        let qualified_id = fun_env.get_qualified_id();
        let variant = FunctionVariant::Baseline;

        if fun_env.is_native() {
            // NOTE: if native function is marked as pure assume it deterministic
            info.is_deterministic =
                targets.is_pure_fun(&qualified_id) || env.is_deterministic(qualified_id).unwrap();
            return data;
        }

        info.is_deterministic = false; // in case of early return
        for callee_id in fun_env.get_called_functions() {
            let Some(callee_id_info) = targets.get_data(&callee_id, &variant) else {
                return data;
            }; // TODO: handle recursive functions properly
            let Some(callee_info) = callee_id_info.annotations.get::<DeterministicInfo>() else {
                return data;
            };
            if !callee_info.is_deterministic {
                return data;
            }
        }
        info.is_deterministic = true;
        data
    }

    fn name(&self) -> String {
        "deterministic_analysis".to_string()
    }

    fn dump_result(
        &self,
        f: &mut Formatter<'_>,
        env: &GlobalEnv,
        targets: &FunctionTargetsHolder,
    ) -> fmt::Result {
        writeln!(
            f,
            "\n********* Result of deterministic analysis *********\n"
        )?;

        writeln!(f, "deterministic analysis: [")?;
        for fun_id in targets.get_funs() {
            let fenv = env.get_function(fun_id);
            for fun_variant in targets.get_target_variants(&fenv) {
                let target = targets.get_target(&fenv, &fun_variant);
                let result = target
                    .get_annotations()
                    .get::<DeterministicInfo>()
                    .cloned()
                    .unwrap();
                write!(f, "  {}: ", fenv.get_full_name_str())?;
                if result.is_deterministic {
                    writeln!(f, "deterministic")?;
                } else {
                    writeln!(f, "non-deterministic")?;
                }
            }
        }
        writeln!(f, "]")
    }
}

pub fn get_info(data: &FunctionData) -> &DeterministicInfo {
    data.annotations.get::<DeterministicInfo>().unwrap()
}
