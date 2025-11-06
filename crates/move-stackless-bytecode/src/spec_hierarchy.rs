use crate::function_target_pipeline::FunctionTargetsHolder;
use move_model::model::{FunId, FunctionEnv, GlobalEnv, QualifiedId};
use num::BigUint;
use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

struct CallInfo {
    display_name: String,
    spec_id: Option<QualifiedId<FunId>>,
}

pub fn display_spec_hierarchy(env: &GlobalEnv, targets: &FunctionTargetsHolder, output_dir: &Path) {
    let excluded_addresses = get_excluded_addresses();

    for spec_id in targets.specs() {
        let spec_env = env.get_function(*spec_id);
        let spec_name = spec_env.get_name_str();
        
        if let Some(fun_id) = targets.get_fun_by_spec(spec_id) {
            let func_env = env.get_function(*fun_id);
            let header = func_env.get_full_name_str();
            write_spec_log_file(env, targets, &func_env, spec_name, &header, output_dir, &excluded_addresses);
        } else if targets.is_scenario_spec(spec_id) {
            let header = format!("{} [scenario]", spec_env.get_full_name_str());
            write_spec_log_file(env, targets, &spec_env, spec_name, &header, output_dir, &excluded_addresses);
        }
    }
}

fn get_excluded_addresses() -> [BigUint; 5] {
    [
        0u16.into(),      // System address (core framework)
        1u16.into(),      // Tests address
        2u16.into(),      // Event address
        3u16.into(),      // Stdlib address
        0xdee9u16.into(), // DeepBook address
    ]
}

fn write_spec_log_file(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    func_env: &FunctionEnv,
    spec_name: String,
    header: &str,
    output_dir: &Path,
    excluded_addresses: &[BigUint],
) {
    let log_file_path = output_dir.join(format!("{}.log.txt", spec_name));

    let mut content = String::new();
    let mut displayed = BTreeSet::new();
    
    content.push_str(&format!("{}\n", header));
    
    build_implementation_tree(env, targets, func_env, "", excluded_addresses, &mut displayed, &mut content);
    
    if let Err(e) = fs::write(&log_file_path, content) {
        eprintln!("Failed to write log file {:?}: {}", log_file_path, e);
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

fn get_call_display_info(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    called_id: &QualifiedId<FunId>,
) -> CallInfo {
    if let Some(spec_id) = targets.get_spec_by_fun(called_id) {
        let spec_env = env.get_function(*spec_id);
        CallInfo {
            display_name: spec_env.get_full_name_str(),
            spec_id: Some(*spec_id),
        }
    } else {
        let called_env = env.get_function(*called_id);
        CallInfo {
            display_name: called_env.get_full_name_str(),
            spec_id: None,
        }
    }
}

fn format_spec_properties(targets: &FunctionTargetsHolder, spec_id: &QualifiedId<FunId>) -> String {
    let mut properties = Vec::new();

    if targets.is_verified_spec(spec_id) {
        properties.push("prove");
    }
    if targets.omits_opaque(spec_id) {
        properties.push("no_opaque");
    }

    if properties.is_empty() {
        String::new()
    } else {
        format!(" ({})", properties.join(", "))
    }
}

fn get_tree_branch(is_last: bool, prefix: &str) -> (String, String) {
    if is_last {
        (format!("{}└──", prefix), format!("{}   ", prefix))
    } else {
        (format!("{}├──", prefix), format!("{}│  ", prefix))
    }
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
        let (branch, next_prefix) = get_tree_branch(is_last, prefix);

        let call_info = get_call_display_info(env, targets, called_id);

        let props_str = call_info
            .spec_id
            .map(|spec_id| format_spec_properties(targets, &spec_id))
            .unwrap_or_default();

        content.push_str(&format!(
            "{} {}{}\n",
            branch, call_info.display_name, props_str
        ));

        if !displayed.contains(called_id) {
            displayed.insert(*called_id);
            let called_env = env.get_function(*called_id);
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
