// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Topological sorting of functions and structs by dependency order

use crate::data::{Dependable, Program};
use indexmap::IndexMap;
use petgraph::algo::{condensation, toposort};
use petgraph::graphmap::DiGraphMap;
use std::collections::hash_map::RandomState;
use std::collections::HashMap;

pub fn order_by_dependencies(program: &mut Program) {
    topological_sort(&mut program.structs.items);
    topological_sort_functions(program);
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

/// Topological sort for functions, accounting for spec function dependencies.
/// When a spec function targets a function, the target function's rendered body
/// comes from the spec, so the target needs the spec's dependencies.
fn topological_sort_functions(program: &mut Program) {
    let items = program.functions.base_functions_mut();

    let mut graph = DiGraphMap::<usize, (), RandomState>::with_capacity(items.len(), 0);

    // Add all nodes first
    for id in items.keys() {
        graph.add_node(*id);
    }

    // Build target_id -> spec_ids mapping
    // (a target can have multiple spec functions, but we need their dependencies)
    let mut target_to_specs: HashMap<usize, Vec<usize>> = HashMap::new();
    for (id, func) in items.iter() {
        if let Some(target_id) = func.spec_target {
            target_to_specs.entry(target_id).or_default().push(*id);
        }
    }

    // Add edges for normal dependencies
    for (id, func) in items.iter() {
        for dep in func.dependencies() {
            if items.contains_key(&dep) {
                graph.add_edge(dep, *id, ());
            }
        }
    }

    // Add edges for spec function dependencies -> target function
    // The target function's rendered body uses the spec's body, so the target
    // needs all dependencies that the spec body has.
    for (target_id, spec_ids) in &target_to_specs {
        if !items.contains_key(target_id) {
            continue;
        }
        for spec_id in spec_ids {
            if let Some(spec_func) = items.get(spec_id) {
                for dep in spec_func.dependencies() {
                    // Add edge: dep must come before target (not spec)
                    // because when rendering target, we use spec's body
                    if items.contains_key(&dep) && dep != *target_id {
                        graph.add_edge(dep, *target_id, ());
                    }
                }
            }
        }
    }

    // Add edges for original_body dependencies -> function with original_body
    // When a function has original_body (is a spec-target), the _impl version
    // is rendered using original_body. If original_body calls other spec-target
    // functions, those must be defined first (because calls render as the spec name).
    for (id, func) in items.iter() {
        if let Some(ref original_body) = func.original_body {
            for dep in original_body.calls().map(|call_id| call_id.base) {
                if items.contains_key(&dep) && dep != *id {
                    graph.add_edge(dep, *id, ());
                }
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
