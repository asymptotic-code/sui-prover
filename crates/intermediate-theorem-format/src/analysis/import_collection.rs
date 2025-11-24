// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Import collection pass

use crate::data::{Dependable, TheoremModuleID, TheoremProgram};
use crate::TheoremFunction;
use std::collections::HashSet;

pub struct ImportCollectionPass;

impl ImportCollectionPass {
    pub fn run(program: &mut TheoremProgram) {
        // Collect imports for each module first (immutable borrow)
        let mut module_imports = Vec::new();
        for module in program.modules() {
            let imports = Self::collect_module_imports(program, module.id);
            module_imports.push((module.id, imports));
        }

        // Then update modules (mutable borrow)
        for (module_id, imports) in module_imports {
            program.get_module_mut(module_id).required_imports = imports;
        }
    }

    fn collect_module_imports(
        program: &TheoremProgram,
        module_id: TheoremModuleID,
    ) -> Vec<TheoremModuleID> {
        let struct_deps = Self::collect_struct_imports(program, module_id);
        let function_deps = Self::collect_function_imports(program, module_id);

        struct_deps
            .into_iter()
            .chain(function_deps)
            .filter(|m| *m != module_id)
            .collect()
    }

    fn collect_struct_imports(
        program: &TheoremProgram,
        module_id: TheoremModuleID,
    ) -> HashSet<TheoremModuleID> {
        program
            .structs()
            .filter(|s| s.module_id == module_id)
            .flat_map(|s| s.dependencies())
            .map(|sid| program.get_struct_module(sid))
            .collect()
    }

    fn collect_function_imports(
        program: &TheoremProgram,
        module_id: TheoremModuleID,
    ) -> HashSet<TheoremModuleID> {
        program
            .functions()
            .filter(|f| f.module_id == module_id)
            .flat_map(|f| Self::collect_from_function(program, f))
            .collect()
    }

    fn collect_from_function<'a>(
        program: &'a TheoremProgram,
        function: &'a TheoremFunction,
    ) -> impl Iterator<Item = TheoremModuleID> + 'a {
        let sig_deps = Self::collect_from_signature(program, function);
        let body_deps = Self::collect_from_body(program, function);
        sig_deps.chain(body_deps)
    }

    fn collect_from_signature<'a>(
        program: &'a TheoremProgram,
        function: &'a TheoremFunction,
    ) -> impl Iterator<Item = TheoremModuleID> + 'a {
        function
            .signature
            .parameters
            .iter()
            .map(|p| &p.param_type)
            .chain(function.signature.return_types.iter())
            .flat_map(|t| t.collect_struct_ids())
            .map(|sid| program.get_struct_module(sid))
    }

    fn collect_from_body<'a>(
        program: &'a TheoremProgram,
        function: &'a crate::data::functions::TheoremFunction,
    ) -> impl Iterator<Item = TheoremModuleID> + 'a {
        let fn_calls = function
            .body
            .collect_function_calls()
            .into_iter()
            .map(|fid| program.get_function_module(fid));

        let struct_refs = function
            .body
            .collect_struct_references()
            .into_iter()
            .map(|sid| program.get_struct_module(sid));

        let type_refs = function
            .body
            .collect_type_struct_ids()
            .into_iter()
            .map(|sid| program.get_struct_module(sid));

        fn_calls.chain(struct_refs).chain(type_refs)
    }
}
