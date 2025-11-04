use crate::function_target_pipeline::FunctionTargetsHolder;
use move_model::model::{FunId, FunctionEnv, GlobalEnv, QualifiedId};
use num::BigUint;
use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

pub fn display_spec_hierarchy(env: &GlobalEnv, targets: &FunctionTargetsHolder, output_dir: &Path) {
    let excluded_addresses = [
        0u16.into(),
        1u16.into(),
        2u16.into(),
        3u16.into(),
        0xdee9u16.into(),
    ];

    for spec_id in targets.specs() {
        if let Some(fun_id) = targets.get_fun_by_spec(spec_id) {
            let func_env = env.get_function(*fun_id);
            let spec_env = env.get_function(*spec_id);

            let spec_name = spec_env.get_name_str();
            let log_file_path = output_dir.join(format!("{}.log.txt", spec_name));

            let mut content = String::new();
            let mut displayed = BTreeSet::new();

            content.push_str(&format!(
                "{}::{}_spec\n",
                func_env.module_env.get_name().display(env.symbol_pool()),
                func_env.get_name_str()
            ));

            build_implementation_tree(
                env,
                targets,
                &func_env,
                "",
                &excluded_addresses,
                &mut displayed,
                &mut content,
            );

            if let Err(e) = fs::write(&log_file_path, content) {
                eprintln!("Failed to write log file {:?}: {}", log_file_path, e);
            }
        }
    }
}

fn is_system_function(func_env: &FunctionEnv, excluded_addresses: &[BigUint]) -> bool {
    let module_addr = func_env.module_env.get_name().addr();
    let module_name = func_env
        .module_env
        .get_name()
        .name()
        .display(func_env.module_env.env.symbol_pool())
        .to_string();

    excluded_addresses.contains(module_addr)
        || GlobalEnv::SPECS_MODULES_NAMES.contains(&module_name.as_str())
}

fn build_implementation_tree(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    func_env: &FunctionEnv,
    prefix: &str,
    excluded_addresses: &[BigUint],
    displayed: &mut BTreeSet<QualifiedId<FunId>>,
    content: &mut String,
) {
    let called_functions = func_env.get_called_functions();

    let filtered_calls: Vec<_> = called_functions
        .into_iter()
        .filter(|called_id| {
            let called_env = env.get_function(*called_id);
            !is_system_function(&called_env, excluded_addresses)
        })
        .collect();

    for (i, called_id) in filtered_calls.iter().enumerate() {
        let is_last = i == filtered_calls.len() - 1;
        let (current_branch, next_prefix) = if is_last {
            ("└──", format!("{}   ", prefix))
        } else {
            ("├──", format!("{}│  ", prefix))
        };

        let called_env = env.get_function(*called_id);

        let (display_name, has_spec, spec_id_opt) =
            if let Some(spec_id) = targets.get_spec_by_fun(called_id) {
                let spec_env = env.get_function(*spec_id);
                (spec_env.get_name_str(), true, Some(*spec_id))
            } else {
                (called_env.get_name_str(), false, None)
            };

        let mut properties = Vec::new();

        if has_spec {
            if let Some(spec_id) = spec_id_opt {
                if targets.is_verified_spec(&spec_id) {
                    properties.push("prove");
                }
                if targets.omits_opaque(&spec_id) {
                    properties.push("no_opaque");
                }
            }
        }

        let props_str = if properties.is_empty() {
            String::new()
        } else {
            format!(" ({})", properties.join(", "))
        };

        content.push_str(&format!(
            "{}{} {}{}\n",
            prefix, current_branch, display_name, props_str
        ));

        if !displayed.contains(called_id) {
            displayed.insert(*called_id);
            build_implementation_tree(
                env,
                targets,
                &called_env,
                &next_prefix,
                excluded_addresses,
                displayed,
                content,
            );
        }
    }
}
