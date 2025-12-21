// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Analysis and optimization passes for TheoremIR

mod abort_elimination;
mod cleanup;
mod constant_folding;
mod dead_code_removal;
mod dependency_order;
mod import_collection;
mod logical_simplification;
mod monadicity;
mod runtime_variants;
mod spec_generation;
mod temp_inlining;

pub use abort_elimination::eliminate_impossible_aborts;
pub use constant_folding::{fold_constants, FunctionBodies};
pub use dependency_order::order_by_dependencies;
pub use import_collection::collect_imports;
pub use logical_simplification::simplify as logical_simplify;
pub use monadicity::analyze_monadicity;
pub use runtime_variants::{generate_runtime_variants, convert_to_pure};
pub use spec_generation::generate_spec_functions;

use crate::data::variables::TypeContext;
use crate::IRNode;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

const MAX_FIXPOINT_ITERATIONS: usize = 100;

/// Compute a hash of an IR node for change detection.
/// This is much cheaper than cloning or comparing the entire tree.
fn compute_ir_hash(node: &IRNode) -> u64 {
    let mut hasher = DefaultHasher::new();
    // Use format debug representation as a quick hash
    // This is not perfect but good enough for detecting changes
    format!("{:?}", node).hash(&mut hasher);
    hasher.finish()
}

pub fn optimize(mut node: IRNode, ctx: &TypeContext) -> IRNode {
    for _ in 0..MAX_FIXPOINT_ITERATIONS {
        let prev_hash = compute_ir_hash(&node);
        node = optimize_single_pass(node, ctx);
        let new_hash = compute_ir_hash(&node);
        if new_hash == prev_hash {
            break;
        }
    }
    node
}

fn optimize_single_pass(node: IRNode, ctx: &TypeContext) -> IRNode {
    let node = temp_inlining::inline_temps(node, ctx.vars);
    let node = dead_code_removal::remove_dead_code(node);
    let node = logical_simplification::simplify(node);
    cleanup::cleanup(node, ctx)
}
