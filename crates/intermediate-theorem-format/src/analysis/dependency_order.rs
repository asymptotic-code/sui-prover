// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Topological sorting of functions and structs by dependency order
//!
//! This pass analyzes both function call dependencies and struct field dependencies,
//! reordering them globally so that each item is defined before it's used by other items.

use crate::data::{Dependable, TheoremProgram};
use indexmap::IndexMap;
use petgraph::algo::{condensation, toposort};
use petgraph::graphmap::DiGraphMap;
use std::collections::hash_map::RandomState;

pub struct DependencyOrderPass;

impl DependencyOrderPass {
    pub fn new() -> Self {
        Self
    }

    /// Run dependency ordering on the entire program (both structs and functions)
    /// Performs global topological sort - items from all modules are sorted together
    pub fn run(program: &mut TheoremProgram) {
        Self::topological_sort(&mut program.structs);
        Self::topological_sort(&mut program.functions);
    }

    /// Unified topological sort for any Dependable item type with mutual recursion detection
    /// Reorders items in-place according to topological dependency order
    /// Detects and marks mutually recursive groups using strongly connected components
    fn topological_sort<T: Dependable>(items: &mut IndexMap<T::Id, T>) {
        // Build dependency graph (dep -> id means id depends on dep)
        let mut base_graph_builder = DiGraphMap::<T::Id, (), RandomState>::new();

        // Add all nodes first
        for id in items.keys() {
            base_graph_builder.add_node(*id);
        }

        // Add dependency edges (dep -> id)
        for (id, item) in items.iter() {
            for dep in item.dependencies() {
                base_graph_builder.add_edge(dep, *id, ());
            }
        }

        let base_graph = base_graph_builder.into_graph::<u32>();

        // Condense to SCCs (strongly connected components)
        let mut graph = condensation(base_graph, false);

        // Perform topological sort on the condensation graph
        let sorted = match toposort(&graph, None) {
            Ok(sorted) => sorted,
            Err(cycle) => {
                // If there's still a cycle after condensation, something went wrong
                panic!(
                    "BUG: Cycle detected in condensation graph at node {:?}. Graph has {} nodes.",
                    cycle.node_id(),
                    graph.node_count()
                );
            }
        };

        // Now reorder items according to the topological sort and mark mutual groups
        *items = sorted
            .into_iter()
            .map(|id| graph.remove_node(id).unwrap())
            .enumerate()
            .flat_map(|(group_id, group)| {
                group
                    .into_iter()
                    .map(|id| {
                        (
                            id,
                            items
                                .swap_remove(&id)
                                .unwrap()
                                .with_mutual_group_id(group_id),
                        )
                    })
                    .collect::<Vec<_>>()
            })
            .collect();
    }
}
