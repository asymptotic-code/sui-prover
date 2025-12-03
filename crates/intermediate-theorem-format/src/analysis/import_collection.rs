// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Import collection pass

use crate::data::{Dependable, TheoremModuleID, TheoremProgram};
use crate::TheoremFunction;
use std::collections::HashSet;

pub fn collect_imports(program: &mut TheoremProgram) {
    let module_imports: Vec<_> = program
        .modules
        .iter_ids()
        .map(|id| (id, collect_module_imports(program, id)))
        .collect();

    for (module_id, imports) in module_imports {
        program.modules.get_mut(module_id).required_imports = imports;
    }
}

fn collect_module_imports(program: &TheoremProgram, module_id: TheoremModuleID) -> Vec<TheoremModuleID> {
    let struct_deps = collect_struct_imports(program, module_id);
    let function_deps = collect_function_imports(program, module_id);

    struct_deps
        .into_iter()
        .chain(function_deps)
        .filter(|m| *m != module_id)
        .collect()
}

fn collect_struct_imports(program: &TheoremProgram, module_id: TheoremModuleID) -> HashSet<TheoremModuleID> {
    program
        .structs
        .values()
        .filter(|s| s.module_id == module_id)
        .flat_map(|s| s.dependencies())
        .map(|sid| program.structs.get(sid).module_id)
        .collect()
}

fn collect_function_imports(program: &TheoremProgram, module_id: TheoremModuleID) -> HashSet<TheoremModuleID> {
    program
        .functions
        .values()
        .filter(|f| f.module_id == module_id)
        .flat_map(|f| collect_from_function(program, f))
        .collect()
}

fn collect_from_function<'a>(
    program: &'a TheoremProgram,
    function: &'a TheoremFunction,
) -> impl Iterator<Item = TheoremModuleID> + 'a {
    let sig_deps = function
        .signature
        .parameters
        .iter()
        .map(|p| &p.param_type)
        .chain(std::iter::once(&function.signature.return_type))
        .flat_map(|t| t.struct_ids())
        .map(|sid| program.structs.get(sid).module_id);

    let body_deps = function.dependencies()
        .map(|fid| program.functions.get(fid).module_id)
        .chain(
            function
                .body
                .iter_struct_references()
                .chain(function.body.iter_type_struct_ids())
                .map(|sid| program.structs.get(sid).module_id),
        );

    sig_deps.chain(body_deps)
}
