// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Topological sorting of functions and structs by dependency order

use crate::data::{Dependable, Program};
use indexmap::IndexMap;
use petgraph::algo::{condensation, toposort};
use petgraph::graphmap::DiGraphMap;
use std::collections::hash_map::RandomState;

pub fn order_by_dependencies(program: &mut Program) {
    topological_sort(&mut program.structs.items);
    topological_sort(&mut program.functions.items);
}

fn topological_sort<T: Dependable>(items: &mut IndexMap<T::Id, T>) {
    // Build graph including ALL nodes, even those with no edges
    let mut graph = DiGraphMap::<T::Id, (), RandomState>::with_capacity(items.len(), 0);

    // Add all nodes first
    for id in items.keys() {
        graph.add_node(*id);
    }

    // Then add edges (only where both endpoints exist)
    for (id, item) in items.iter() {
        for dep in item.dependencies() {
            if items.contains_key(&dep) {
                graph.add_edge(dep, *id, ());
            }
        }
    }

    let mut condensed = condensation(graph.into_graph::<u32>(), false);

    let sorted_groups: Vec<_> = toposort(&condensed, None)
        .unwrap()
        .into_iter()
        .map(|node| condensed.remove_node(node).unwrap())
        .enumerate()
        .collect();

    *items = sorted_groups
        .into_iter()
        .flat_map(|(group_id, group)| group.into_iter().map(move |id| (id, group_id)))
        .map(|(id, group_id)| {
            (
                id,
                items
                    .swap_remove(&id)
                    .unwrap()
                    .with_mutual_group_id(group_id),
            )
        })
        .collect();
}
