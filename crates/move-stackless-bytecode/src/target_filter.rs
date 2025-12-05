use move_model::model::{FunctionEnv, GlobalEnv};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;

#[derive(clap::Args, Debug, Clone, Deserialize, Serialize, Default)]
#[clap(next_help_heading = "Filtering Options")]
pub struct TargetFilterOptions {
    /// Specify modules names to target
    #[clap(long = "modules", global = true)]
    pub modules: Option<Vec<String>>,

    /// Specify functions names to target
    #[clap(long = "functions", global = true)]
    pub functions: Option<Vec<String>>,
}

impl TargetFilterOptions {
    pub fn is_configured(&self) -> bool {
        self.modules.is_some() || self.functions.is_some()
    }

    pub fn is_targeted(&self, func_env: &FunctionEnv) -> bool {
        if let Some(modules) = &self.modules {
            let module_name = &func_env
                .module_env
                .get_name()
                .name()
                .display(func_env.module_env.env.symbol_pool())
                .to_string();
            if !modules.contains(&module_name) {
                return false;
            }
        }

        if let Some(functions) = &self.functions {
            functions.contains(&func_env.get_name_str())
        } else {
            true
        }
    }

    pub fn check_filter_correctness(&self, env: &GlobalEnv) -> Option<String> {
        if let Some(modules) = &self.modules {
            let mut seen = HashSet::new();
            for module in modules {
                if !seen.insert(module) {
                    return Some(format!("Duplicate module `{}` found", module));
                }
                if env
                    .find_module_by_name(env.symbol_pool().make(module))
                    .is_none()
                {
                    return Some(format!("Module `{}` does not exist", module));
                }
            }
        }

        if let Some(functions) = &self.functions {
            let mut seen = HashSet::new();

            let available_modules: Vec<_> = match &self.modules {
                Some(f_modules) => env
                    .get_modules()
                    .filter(|m| {
                        let name = m.get_name().name().display(env.symbol_pool()).to_string();
                        f_modules.contains(&name)
                    })
                    .collect(),
                None => env.get_modules().collect(),
            };

            for function in functions {
                if !seen.insert(function) {
                    return Some(format!("Duplicate function `{}` found", function));
                }

                let symbol = env.symbol_pool().make(function);
                let found = available_modules
                    .iter()
                    .any(|m| env.find_function_by_name(m.get_id(), symbol).is_some());

                if !found {
                    return Some(format!("Function `{}` does not exist", function));
                }
            }
        }

        None
    }
}
