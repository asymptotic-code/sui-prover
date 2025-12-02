// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Monadicity analysis pass
//!
//! All functions start as monadic (return type wrapped in Except).
//! This pass identifies pure functions, unwraps their return types,
//! and updates Call nodes accordingly.
//!
//! Prerequisites: DependencyOrderPass must have run first.

use crate::data::TheoremProgram;
use crate::{IRNode, TheoremFunctionID};
use std::collections::BTreeSet;

pub fn analyze_monadicity(program: &mut TheoremProgram) {
    let func_ids: Vec<_> = program.functions.iter_ids().collect();
    let mut monadic_funcs: BTreeSet<TheoremFunctionID> = BTreeSet::new();

    for func_id in &func_ids {
        let func = program.functions.get(*func_id);
        let has_intrinsic = func.body.aborts();
        let calls_monadic = func.body.calls().any(|id| monadic_funcs.contains(&id));

        if has_intrinsic || calls_monadic {
            monadic_funcs.insert(*func_id);
        } else if let Some(inner) = func.signature.return_type.unwrap_monad().cloned() {
            program.functions.get_mut(*func_id).signature.return_type = inner;
        }
    }

    for func_id in &func_ids {
        let func = program.functions.get_mut(*func_id);
        func.body = update_call_monadicity(func.body.clone(), &monadic_funcs);
    }
}

fn update_call_monadicity(ir: IRNode, monadic_funcs: &BTreeSet<TheoremFunctionID>) -> IRNode {
    ir.transform(&mut |node| match node {
        IRNode::Call { function, args, type_args, .. } => IRNode::Call {
            monadic: monadic_funcs.contains(&function),
            function,
            args,
            type_args,
        },
        other => other,
    })
}
