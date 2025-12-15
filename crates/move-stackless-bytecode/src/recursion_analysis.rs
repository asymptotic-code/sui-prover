use crate::{
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
};
use codespan_reporting::diagnostic::Severity;
use move_model::model::FunctionEnv;

pub struct RecursionAnalysisProcessor();

impl RecursionAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }

    pub fn find_simple_recursion(&self, fun_env: &FunctionEnv) -> Vec<String> {
        for qid in fun_env.get_called_functions() {
            if qid == fun_env.get_qualified_id() {
                return vec![fun_env.get_full_name_str(), fun_env.get_full_name_str()];
            }
        }

        vec![]
    }
}

impl FunctionTargetProcessor for RecursionAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        fun_env: &FunctionEnv,
        data: FunctionData,
        scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        let trace = if let Some(scc) = scc_opt {
            scc.iter().map(|f| f.get_full_name_str()).collect()
        } else {
            // NOTE: also check for simple direct recursion (scc is not handling it)
            self.find_simple_recursion(fun_env)
        };

        if !trace.is_empty() {
            fun_env.module_env.env.diag(
                Severity::Error,
                &fun_env.get_loc(),
                &format!(
                    "Recursive functions are not supported for specifications.\nPath: {}",
                    trace.join(" -> ")
                ),
            );
        }

        data
    }

    fn name(&self) -> String {
        "recursion_analysis".to_string()
    }
}
