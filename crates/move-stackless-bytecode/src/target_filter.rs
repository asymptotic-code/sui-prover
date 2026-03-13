use move_model::model::{FunctionEnv, GlobalEnv};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;

#[derive(clap::Args, Debug, Clone, Deserialize, Serialize, Default)]
#[clap(next_help_heading = "Filtering Options")]
pub struct TargetFilterOptions {
    /// Specify modules names to target (supports <module> or <package>::<module>)
    #[clap(long = "modules", global = true)]
    pub modules: Option<Vec<String>>,

    /// Specify functions names to target (supports <function>, <module>::<function>, or <package>::<module>::<function>)
    #[clap(long = "functions", global = true)]
    pub functions: Option<Vec<String>>,
}

/// Returns true if the given filter string matches the function environment.
/// Supports three forms:
///   - `<function>` — matches by simple function name
///   - `<module>::<function>` — matches by module name and function name
///   - `<package>::<module>::<function>` — matches by fully qualified name
fn function_matches(func_env: &FunctionEnv, name: &str) -> bool {
    // Match simple function name
    if func_env.get_name_str() == name {
        return true;
    }
    // Match module::function (uses simple module name)
    if func_env.get_full_name_str() == name {
        return true;
    }
    // Match package::module::function
    format!(
        "{}::{}",
        func_env.module_env.get_full_name_str(),
        func_env.get_name_str()
    ) == name
}

impl TargetFilterOptions {
    pub fn is_configured(&self) -> bool {
        self.modules.is_some() || self.functions.is_some()
    }

    pub fn is_targeted(&self, func_env: &FunctionEnv) -> bool {
        if let Some(modules) = &self.modules {
            if !modules.iter().any(|m| func_env.module_env.matches_name(m)) {
                return false;
            }
        }

        if let Some(functions) = &self.functions {
            functions.iter().any(|f| function_matches(func_env, f))
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
                if !env.get_modules().any(|m| m.matches_name(module)) {
                    return Some(format!("Module `{}` does not exist", module));
                }
            }
        }

        if let Some(functions) = &self.functions {
            let mut seen = HashSet::new();

            let available_modules: Vec<_> = match &self.modules {
                Some(f_modules) => env
                    .get_modules()
                    .filter(|m| f_modules.iter().any(|name| m.matches_name(name)))
                    .collect(),
                None => env.get_modules().collect(),
            };

            for function in functions {
                if !seen.insert(function) {
                    return Some(format!("Duplicate function `{}` found", function));
                }

                let found = available_modules
                    .iter()
                    .flat_map(|m| m.get_functions())
                    .any(|f| function_matches(&f, function));

                if !found {
                    return Some(format!("Function `{}` does not exist", function));
                }
            }
        }

        None
    }
}
