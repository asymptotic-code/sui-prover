use move_model::model::{FunctionEnv, GlobalEnv};
use std::fmt::{self, Formatter};

use crate::{
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant},
};

use move_model::sui_native_deterministic_functions::is_deterministic;

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

        info.is_deterministic = match is_deterministic(env, qualified_id) {
            Some(result) => result,
            None => {
                let mut all_deterministic = true;

                for callee_id in fun_env.get_called_functions() {
                    let info = targets
                        .get_data_mut(&callee_id, &variant)
                        .unwrap()
                        .annotations
                        .get_or_default_mut::<DeterministicInfo>(true);


                    if !info.is_deterministic {
                        all_deterministic = false;
                        break;
                    }
                }
                all_deterministic
            }
        };

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
        writeln!(f, "\n********* Result of deterministic analysis *********\n")?;

        writeln!(f, "deterministic analysis: [")?;
        for fun_id in targets.get_funs() {
            let fenv = env.get_function(fun_id);
            for fun_variant in targets.get_target_variants(&fenv) {
                let target = targets.get_target(&fenv, &fun_variant);
                let result = target
                    .get_annotations()
                    .get::<DeterministicInfo>()
                    .cloned()
                    .unwrap_or_default();
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
