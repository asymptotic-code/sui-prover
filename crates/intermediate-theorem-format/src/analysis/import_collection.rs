// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Import collection pass

use crate::data::{Dependable, ModuleID, Program};
use crate::{Function, FunctionID};
use std::collections::HashSet;

pub fn collect_imports(program: &mut Program) {
    let module_imports: Vec<_> = program
        .modules
        .iter_ids()
        .map(|id| (id, collect_module_imports(program, id)))
        .collect();

    for (module_id, imports) in module_imports {
        program.modules.get_mut(module_id).required_imports = imports;
    }
}

fn collect_module_imports(program: &Program, module_id: ModuleID) -> Vec<ModuleID> {
    let module = program.modules.get(module_id);

    let struct_deps = collect_struct_imports(program, module_id);
    let function_deps = collect_function_imports(program, module_id);

    let combined: HashSet<ModuleID> = struct_deps
        .into_iter()
        .chain(function_deps)
        .filter(|m| *m != module_id)
        .collect();

    let result: Vec<ModuleID> = combined.into_iter().collect();

    result
}

fn collect_struct_imports(program: &Program, module_id: ModuleID) -> HashSet<ModuleID> {
    program
        .structs
        .values()
        .filter(|s| s.module_id == module_id)
        .flat_map(|s| s.dependencies())
        .map(|sid| program.structs.get(sid).module_id)
        .collect()
}

fn collect_function_imports(program: &Program, module_id: ModuleID) -> HashSet<ModuleID> {
    // Only collect imports from base (Runtime) functions, not spec variants.
    // Spec variants (.requires, .ensures, etc.) are rendered in SpecDefs/Specs directories,
    // not in Impls. Including them here creates circular dependencies because spec functions
    // call back to the implementation they're specifying.
    program
        .functions
        .base_values()
        .filter(|f| f.module_id == module_id)
        .flat_map(|f| collect_from_function(program, f))
        .collect()
}

fn collect_from_function<'a>(
    program: &'a Program,
    function: &'a Function,
) -> impl Iterator<Item = ModuleID> + 'a {
    let sig_deps = function
        .signature
        .parameters
        .iter()
        .map(|p| &p.param_type)
        .chain(std::iter::once(&function.signature.return_type))
        .flat_map(|t| t.struct_ids())
        .map(|sid| program.structs.get(sid).module_id);

    // Get base IDs from function calls and look up their module
    // IMPORTANT: We use fid (the actual FunctionID being called) instead of just fid.base
    // to properly handle calls to spec-target functions with _impl variants
    let call_deps = function.body.calls().into_iter().map(move |fid| {
        let called_func = program.functions.get(&fid);
        called_func.module_id
    });

    let struct_deps = function
        .body
        .iter_struct_references()
        .chain(function.body.iter_type_struct_ids())
        .map(|sid| program.structs.get(sid).module_id);

    sig_deps.chain(call_deps).chain(struct_deps)
}
