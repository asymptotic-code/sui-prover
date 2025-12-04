// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Monadicity analysis pass
//!
//! All functions start as monadic (return type wrapped in Except).
//! This pass identifies pure functions and unwraps their return types.
//!
//! Prerequisites: DependencyOrderPass must have run first.

use crate::data::Program;
use crate::FunctionID;
use std::collections::BTreeSet;

pub fn analyze_monadicity(program: &mut Program) {
    let func_ids: Vec<_> = program.functions.iter_ids().collect();
    let mut monadic_funcs: BTreeSet<FunctionID> = BTreeSet::new();

    // First pass: identify which functions are intrinsically monadic
    // - Functions that abort
    // - Native functions (we assume they may abort since we don't know their implementation)
    for func_id in &func_ids {
        let func = program.functions.get(*func_id);
        if func.body.aborts() || func.is_native {
            monadic_funcs.insert(*func_id);
        }
    }

    // Iterate until fixed point to propagate monadicity through call chains
    // This handles cross-module calls where topological order may not be perfect
    loop {
        let mut changed = false;
        for func_id in &func_ids {
            if monadic_funcs.contains(func_id) {
                continue;
            }
            let func = program.functions.get(*func_id);
            let calls_monadic = func.body.calls().any(|id| monadic_funcs.contains(&id));
            if calls_monadic {
                monadic_funcs.insert(*func_id);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Second pass: unwrap return types for non-monadic functions
    // Native functions stay monadic since we don't know their behavior
    for func_id in &func_ids {
        let func = program.functions.get(*func_id);
        if !monadic_funcs.contains(func_id) && !func.is_native {
            if let Some(inner) = func.signature.return_type.unwrap_monad().cloned() {
                program.functions.get_mut(*func_id).signature.return_type = inner;
            }
        }
    }
}
