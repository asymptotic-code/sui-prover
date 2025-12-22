use codespan_reporting::diagnostic::Severity;
use move_model::{
    model::FunctionEnv,
    ty::{PrimitiveType, Type},
};

use crate::{
    deterministic_analysis,
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    pure_function_analysis::PureFunctionAnalysisProcessor,
};

pub struct AxiomFunctionAnalysisProcessor();

impl AxiomFunctionAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }

    fn check_parameters(&self, func_env: &FunctionEnv) -> bool {
        for param in func_env.get_parameters() {
            if param.1.is_mutable_reference() {
                func_env.module_env.env.diag(
                    Severity::Error,
                    &func_env.get_loc(),
                    &format!(
                        "Axiom functions cannot have mutable reference parameters: '{}'",
                        func_env.symbol_pool().string(param.0)
                    ),
                );
                return false;
            }
        }

        if func_env.get_return_count() != 1 {
            func_env.module_env.env.diag(
                Severity::Error,
                &func_env.get_loc(),
                "Axiom functions must have exactly one return value",
            );
            return false;
        }

        if !matches!(
            func_env.get_return_types()[0],
            Type::Primitive(PrimitiveType::Bool)
        ) {
            func_env.module_env.env.diag(
                Severity::Error,
                &func_env.get_loc(),
                "Axiom functions should return bool type",
            );
            return false;
        }

        if func_env.get_type_parameter_count() != 0 {
            func_env.module_env.env.diag(
                Severity::Error,
                &func_env.get_loc(),
                "Axiom functions cannot have type parameters",
            );
            return false;
        }

        true
    }
}

impl FunctionTargetProcessor for AxiomFunctionAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        fun_env: &FunctionEnv,
        data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        if !targets.is_axiom_fun(&fun_env.get_qualified_id()) {
            if fun_env
                .get_called_functions()
                .iter()
                .find(|f| targets.is_axiom_fun(f))
                .is_some()
            {
                fun_env.module_env.env.diag(
                    Severity::Error,
                    &fun_env.get_loc(),
                    "Axiom functions cannot be called from non-axiom functions",
                );
            }
            return data;
        }

        if !self.check_parameters(fun_env) {
            return data;
        }

        if !deterministic_analysis::get_info(&data).is_deterministic {
            fun_env.module_env.env.diag(
                Severity::Error,
                &fun_env.get_loc(),
                &format!(
                    "Axiom function '{}' must be deterministic",
                    fun_env.get_full_name_str()
                ),
            );
            return data;
        }

        if let Some((loc, reason)) =
            PureFunctionAnalysisProcessor::check_bytecode(fun_env, &data, targets)
        {
            fun_env
                .module_env
                .env
                .diag(Severity::Error, &loc, &reason.replace("Pure", "Axiom"));
            return data;
        }

        data
    }

    fn name(&self) -> String {
        "axiom_function_analysis".to_string()
    }
}
