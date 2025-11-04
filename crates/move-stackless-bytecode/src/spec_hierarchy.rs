use crate::function_target_pipeline::FunctionTargetsHolder;
use move_model::model::{FunctionEnv, GlobalEnv, QualifiedId, FunId};
use std::collections::{BTreeSet, BTreeMap};

pub fn display_spec_hierarchy(env: &GlobalEnv, targets: &FunctionTargetsHolder) {
    println!("\n📋 Spec Function Hierarchy\n");

    let mut processed = BTreeSet::new();
    let mut spec_tree: BTreeMap<QualifiedId<FunId>, Vec<QualifiedId<FunId>>> = BTreeMap::new();

    for spec_id in targets.specs() {
        if processed.contains(spec_id) {
            continue;
        }

        let spec_env = env.get_function(*spec_id);
        let called_specs = get_called_specs(&spec_env, targets);
        
        spec_tree.insert(*spec_id, called_specs);
        processed.insert(*spec_id);
    }

    for (spec_id, called_specs) in spec_tree {
        display_spec_node(env, targets, &spec_id, &called_specs, 0);
    }
}

fn get_called_specs(
    func_env: &FunctionEnv,
    targets: &FunctionTargetsHolder,
) -> Vec<QualifiedId<FunId>> {
    let called_functions = func_env.get_called_functions();
    
    called_functions
        .into_iter()
        .filter(|called_id| targets.is_spec(called_id))
        .collect()
}

fn display_spec_node(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    spec_id: &QualifiedId<FunId>,
    called_specs: &[QualifiedId<FunId>],
    depth: usize,
) {
    let spec_env = env.get_function(*spec_id);
    let spec_name = spec_env.get_full_name_str();
    
    let indent = "  ".repeat(depth);
    let status_icon = if targets.is_verified_spec(spec_id) {
        "✅"
    } else {
        "⚠️ "
    };

    if depth == 0 {
        println!("{}{} {}", indent, status_icon, spec_name);
    } else {
        println!("{}{} {}", indent, status_icon, spec_name);
    }

    for (i, called_spec_id) in called_specs.iter().enumerate() {
        let is_last = i == called_specs.len() - 1;
        let branch = if is_last { " └ " } else { " ├ " };
        let next_indent = format!("{}{}", indent, branch);
        
        let called_spec_env = env.get_function(*called_spec_id);
        let called_spec_name = called_spec_env.get_name_str();
        
        let mut properties = Vec::new();
        
        if targets.is_verified_spec(called_spec_id) {
            properties.push("prove");
        }
        
        if targets.omits_opaque(called_spec_id) {
            properties.push("opaque");
        }
        
        let props_str = if properties.is_empty() {
            String::new()
        } else {
            format!(" ({})", properties.join(", "))
        };
        
        println!("{}{}{}", next_indent, called_spec_name, props_str);
    }
    
    if !called_specs.is_empty() {
        println!();
    }
}

