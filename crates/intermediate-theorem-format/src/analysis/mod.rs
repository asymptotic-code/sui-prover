// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Analysis and optimization passes for TheoremIR

mod cleanup;
mod dead_code_removal;
mod dependency_order;
mod import_collection;
mod monadicity;
mod runtime_variants;
mod spec_generation;
mod temp_inlining;

pub use dependency_order::order_by_dependencies;
pub use import_collection::collect_imports;
pub use monadicity::analyze_monadicity;
pub use runtime_variants::generate_runtime_variants;
pub use spec_generation::generate_spec_functions;

use crate::{IRNode, VariableRegistry};

const MAX_FIXPOINT_ITERATIONS: usize = 100;

pub fn optimize(mut node: IRNode, registry: &VariableRegistry) -> IRNode {
    for _ in 0..MAX_FIXPOINT_ITERATIONS {
        let next = optimize_single_pass(node.clone(), registry);
        if next == node {
            break;
        }
        node = next;
    }
    node
}

fn optimize_single_pass(node: IRNode, registry: &VariableRegistry) -> IRNode {
    let node = temp_inlining::inline_temps(node, registry);
    let node = dead_code_removal::remove_dead_code(node);
    cleanup::cleanup(node)
}
