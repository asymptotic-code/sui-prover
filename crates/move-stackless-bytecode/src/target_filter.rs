use move_model::model::{FunctionEnv, GlobalEnv};
use serde::{Deserialize, Serialize};

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
    pub fn is_targeted(&self, func_env: &FunctionEnv) -> bool {
        if let Some(modules) = &self.modules {
            let module_name = &func_env.module_env.get_name().name().display(func_env.module_env.env.symbol_pool()).to_string();
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
            for module in modules {
                if !env.find_module_by_name(env.symbol_pool().make(module)).is_some() {
                    return Some(format!("Module `{}` does not exist", module));
                }
            }
        }

        if let Some(functions) = &self.functions {
            let modules = if let Some(f_modules) = &self.modules {
                env.get_modules()
                    .filter(|m| f_modules.contains(&m.get_name().name().display(env.symbol_pool()).to_string()))
                    .collect::<Vec<_>>()
            } else {
                env.get_modules().collect::<Vec<_>>()
            };

            for function in functions {
                let mut found = false;
                for module in &modules {
                    if env.find_function_by_name(module.get_id(), env.symbol_pool().make(function)).is_some() {
                        found = true;
                        break;
                    }
                }
                if !found {
                    return Some(format!("Function `{}` does not exist", function));
                }
            }
        }

        None
    }
}
