use move_model::model::{FunctionEnv, GlobalEnv, QualifiedId, FunId};
use std::fmt::{self, Formatter};

use crate::{
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant},
};

use move_model::sui_native_deterministic_functions::is_deterministic;

#[derive(Clone, Default, Debug)]
pub struct DeterministicInfo {
    pub is_deterministic: bool,
    pub checked: bool,
}

pub struct DeterministicAnalysisProcessor();

impl DeterministicAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }

    fn analyze_function_determinism(
        fun_env: &FunctionEnv,
        targets: &mut FunctionTargetsHolder,
    ) -> bool {
        let env = fun_env.module_env.env;
        let fun_id = fun_env.get_qualified_id();        
        Self::compute_determinism_recursive(env, fun_id, targets)
    }

    fn compute_determinism_recursive(
        env: &GlobalEnv,
        fun_id: QualifiedId<FunId>,
        targets: &mut FunctionTargetsHolder,
    ) -> bool {
        let variant = FunctionVariant::Baseline;
        
        if let Some(data) = targets.get_data(&fun_id, &variant) {
            let info = data
                .annotations
                .get::<DeterministicInfo>()
                .cloned()
                .unwrap_or_default();
            
            if info.checked {
                return info.is_deterministic;
            }
        }

        match is_deterministic(env, fun_id) {
            Some(result) => {
                Self::save_determinism_result(fun_id, result, targets);
                return result;
            },
            None => {
                let fun_env = env.get_function(fun_id);
                
                for callee_id in fun_env.get_called_functions() {
                    if !Self::compute_determinism_recursive(env, callee_id, targets) {
                        Self::save_determinism_result(fun_id, false, targets);
                        return false;
                    }
                }
                
                Self::save_determinism_result(fun_id, true, targets);
                return true;
            }
        }
    }

    fn save_determinism_result(
        fun_id: QualifiedId<FunId>,
        is_deterministic: bool,
        targets: &mut FunctionTargetsHolder,
    ) {
        let variant = FunctionVariant::Baseline;
        
        if let Some(data) = targets.get_data_mut(&fun_id, &variant) {
            let info = data
                .annotations
                .get_or_default_mut::<DeterministicInfo>(true);
            
            if !info.checked {
                info.is_deterministic = is_deterministic;
                info.checked = true;
            }
        }
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

        if !info.checked {
            let env = fun_env.module_env.env;
            let qualified_id = fun_env.get_qualified_id();
            
            match is_deterministic(env, qualified_id) {
                Some(result) => {
                    info.is_deterministic = result;
                },
                None => {
                    info.is_deterministic = Self::analyze_function_determinism(fun_env, targets);
                }
            }
            info.checked = true;
        }

        println!(
            "Deterministic analysis for {}: {}",
            fun_env.get_full_name_str(),
            if info.is_deterministic {
                "deterministic"
            } else {
                "non-deterministic"
            }
        );
        
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
                if result.checked {
                    if result.is_deterministic {
                        writeln!(f, "deterministic")?;
                    } else {
                        writeln!(f, "non-deterministic")?;
                    }
                } else {
                    writeln!(f, "unknown (not analyzed)")?;
                }
            }
        }
        writeln!(f, "]")
    }
}
