use crate::{
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    verification_analysis::VerificationInfo,
};
use codespan_reporting::diagnostic::Severity;
use move_model::model::{FunId, FunctionEnv, QualifiedId};

pub struct RecursionAnalysisProcessor();

impl RecursionAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }

    pub fn find_recursive_functions(
        &self,
        fun_env: &FunctionEnv,
        data: &FunctionData,
    ) -> Option<Vec<String>> {
        self.find_recursive_functions_r(fun_env, data, vec![fun_env.get_qualified_id()])
    }

    fn find_recursive_functions_r(
        &self,
        fun_env: &FunctionEnv,
        data: &FunctionData,
        trace: Vec<QualifiedId<FunId>>,
    ) -> Option<Vec<String>> {
        for qid in fun_env.get_called_functions() {
            let calle_env = fun_env.module_env.env.get_function(qid);
            let verification_info = data.annotations.get::<VerificationInfo>().unwrap();
            if !verification_info.inlined
                && !verification_info.verified
                && !verification_info.reachable
            {
                continue;
            }

            if trace.contains(&qid) {
                let mut result = vec![];
                for id in &trace {
                    result.push(fun_env.module_env.env.get_function(*id).get_full_name_str());
                }
                result.push(calle_env.get_full_name_str());
                return Some(result);
            } else {
                let mut new_trace = trace.clone();
                new_trace.push(qid);

                if let Some(trace) = self.find_recursive_functions_r(&calle_env, data, new_trace) {
                    return Some(trace);
                }
            }
        }
        None
    }
}

impl FunctionTargetProcessor for RecursionAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        fun_env: &FunctionEnv,
        data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        if !targets.is_spec(&fun_env.get_qualified_id())
            && !targets.is_function_with_abort_check(&fun_env.get_qualified_id())
        {
            // NOTE: build trace only from meaningful functions
            return data;
        }

        if let Some(trace) = self.find_recursive_functions(fun_env, &data) {
            fun_env.module_env.env.diag(
                Severity::Error,
                &fun_env.get_loc(),
                &format!(
                    "Recursive functions is not supported for specifications. {}",
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
