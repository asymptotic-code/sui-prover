// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Guard clause extraction pass for TheoremIR
//!
//! Transforms if-else with abort in one branch into guard clauses:
//!
//! Before: `if cond then body else abort`
//! After:  `if !cond then abort; body`

use crate::IRNode;

pub fn extract_guard_clauses(ir: IRNode) -> IRNode {
    ir.transform(&mut |node| {
        let IRNode::If {
            cond,
            then_branch,
            else_branch,
        } = node
        else {
            return node;
        };

        let make_if = |guard, then_branch, continue_branch| IRNode::Block {
            children: vec![
                IRNode::If {
                    cond: Box::new(guard),
                    then_branch,
                    else_branch: Box::new(IRNode::unit()),
                },
                continue_branch,
            ],
        };

        // Determine which branch aborts
        if else_branch.get_abort_code().is_some() {
            make_if(cond.negate(), else_branch, *then_branch)
        } else if then_branch.get_abort_code().is_some() {
            make_if(*cond, then_branch, *else_branch)
        } else {
            IRNode::If {
                cond,
                then_branch,
                else_branch,
            }
        }
    })
}
