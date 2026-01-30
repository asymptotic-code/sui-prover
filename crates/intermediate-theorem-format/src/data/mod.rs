// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

use indexmap::IndexMap;
use move_model::model::{DatatypeId, FunId, ModuleId, QualifiedId};
use std::borrow::Borrow;
use std::collections::BTreeMap;

use crate::analysis::{
    analyze_abortability, collect_imports, fold_constants, order_by_dependencies, FunctionBodies,
};
use crate::data::functions::{FunctionFlags, FunctionVariant};
use crate::data::variables::TypeContext;
use crate::{FunctionSignature, IRNode, Type};

pub use functions::FunctionID;
pub use structure::StructID;

pub mod conversion;
pub mod functions;
pub mod ir;
pub mod structure;
pub mod types;
pub mod variables;

pub type ModuleID = usize;

/// Trait for items that can have dependencies on other items of the same type
pub trait Dependable {
    type Id: Copy + Eq + std::hash::Hash + Ord + std::fmt::Debug;
    type MoveKey: Copy + Eq + std::hash::Hash + Ord + std::fmt::Debug;

    fn dependencies(&self) -> impl Iterator<Item = Self::Id>;
    fn with_mutual_group_id(self, group_id: usize) -> Self;
}

// ============================================================================
// Program Item Storage
// ============================================================================

/// Storage for program items with ID allocation
#[derive(Debug, Clone)]
pub struct ItemStore<MoveKey: Ord, Item> {
    ids: BTreeMap<MoveKey, usize>,
    pub items: IndexMap<usize, Item>,
}

impl<MoveKey: Ord, Item> Default for ItemStore<MoveKey, Item> {
    fn default() -> Self {
        Self {
            ids: BTreeMap::new(),
            items: IndexMap::new(),
        }
    }
}

impl<MoveKey: Ord + Copy, Item> ItemStore<MoveKey, Item> {
    /// Look up the ID for a key, creating one if it doesn't exist
    pub fn id_for_key(&mut self, key: MoveKey) -> usize {
        let next_id = self.ids.len();
        *self.ids.entry(key).or_insert(next_id)
    }

    pub fn has(&self, id: usize) -> bool {
        self.items.contains_key(&id)
    }
    pub fn create(&mut self, key: MoveKey, item: Item) {
        let id = self.id_for_key(key);
        self.items.insert(id, item);
    }
    pub fn get(&self, id: impl Borrow<usize>) -> &Item {
        let id = id.borrow();
        self.items.get(id).unwrap_or_else(|| {
            panic!(
                "Item {} should exist, but only have IDs: {:?}",
                id,
                self.items.keys().collect::<Vec<_>>()
            )
        })
    }
    pub fn get_mut(&mut self, id: impl Borrow<usize>) -> &mut Item {
        self.items.get_mut(id.borrow()).expect("Item should exist")
    }
    pub fn iter(&self) -> impl Iterator<Item = (&usize, &Item)> {
        self.items.iter()
    }
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Item> {
        self.items.values_mut()
    }
    pub fn iter_ids(&self) -> impl Iterator<Item = usize> + '_ {
        self.items.keys().copied()
    }
    pub fn values(&self) -> impl Iterator<Item = &Item> {
        self.items.values()
    }
    pub fn len(&self) -> usize {
        self.items.len()
    }
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

impl<'a, MoveKey: Ord, Item> IntoIterator for &'a ItemStore<MoveKey, Item> {
    type Item = (&'a usize, &'a Item);
    type IntoIter = indexmap::map::Iter<'a, usize, Item>;
    fn into_iter(self) -> Self::IntoIter {
        self.items.iter()
    }
}

// ============================================================================
// Function Storage - stores base functions and variants
// ============================================================================

/// Storage for functions with variant support
#[derive(Debug, Clone, Default)]
pub struct FunctionStore {
    /// Maps Move qualified IDs to base function IDs
    ids: BTreeMap<QualifiedId<FunId>, usize>,
    /// Base functions (Runtime variant)
    base_functions: IndexMap<usize, functions::Function>,
    /// Variant functions keyed by (base_id, variant)
    variants: BTreeMap<FunctionID, functions::Function>,
}

impl FunctionStore {
    /// Look up the base ID for a Move key, creating one if it doesn't exist
    pub fn id_for_key(&mut self, key: QualifiedId<FunId>) -> usize {
        let next_id = self.ids.len();
        *self.ids.entry(key).or_insert(next_id)
    }

    /// Check if a base function exists
    pub fn has(&self, base_id: usize) -> bool {
        self.base_functions.contains_key(&base_id)
    }

    /// Look up the base ID for a Move key without creating one
    pub fn get_id_for_move_key(&self, key: &QualifiedId<FunId>) -> Option<usize> {
        self.ids.get(key).copied()
    }

    /// Create a base (Runtime) function
    pub fn create(&mut self, key: QualifiedId<FunId>, func: functions::Function) {
        let id = self.id_for_key(key);
        self.base_functions.insert(id, func);
    }

    /// Get a function by ID (checks base functions then variants)
    pub fn get(&self, id: &FunctionID) -> &functions::Function {
        if id.variant == FunctionVariant::Runtime {
            self.base_functions.get(&id.base).unwrap_or_else(|| {
                panic!(
                    "Base function {} should exist, but only have IDs: {:?}",
                    id.base,
                    self.base_functions.keys().collect::<Vec<_>>()
                )
            })
        } else {
            self.variants
                .get(id)
                .unwrap_or_else(|| panic!("Variant function {:?} should exist", id))
        }
    }

    /// Try to get a function by ID, returning None if it doesn't exist
    pub fn try_get(&self, id: &FunctionID) -> Option<&functions::Function> {
        if id.variant == FunctionVariant::Runtime {
            self.base_functions.get(&id.base)
        } else {
            self.variants.get(id)
        }
    }

    /// Get a mutable reference to a function by ID
    pub fn get_mut(&mut self, id: FunctionID) -> &mut functions::Function {
        if id.variant == FunctionVariant::Runtime {
            self.base_functions
                .get_mut(&id.base)
                .expect("Base function should exist")
        } else {
            self.variants
                .get_mut(&id)
                .expect("Variant function should exist")
        }
    }

    /// Insert a variant function
    pub fn insert_variant(&mut self, id: FunctionID, func: functions::Function) {
        debug_assert!(
            id.variant != FunctionVariant::Runtime,
            "Use create() for base functions"
        );
        self.variants.insert(id, func);
    }

    /// Iterate over base function IDs
    pub fn iter_base_ids(&self) -> impl Iterator<Item = usize> + '_ {
        self.base_functions.keys().copied()
    }

    /// Iterate over all function IDs (base + variants)
    pub fn iter_ids(&self) -> impl Iterator<Item = FunctionID> + '_ {
        let base_ids = self
            .base_functions
            .keys()
            .map(|&base| FunctionID::new(base));
        let variant_ids = self.variants.keys().copied();
        base_ids.chain(variant_ids)
    }

    /// Iterate over all functions with their IDs
    pub fn iter(&self) -> impl Iterator<Item = (FunctionID, &functions::Function)> {
        let base_iter = self
            .base_functions
            .iter()
            .map(|(&base, f)| (FunctionID::new(base), f));
        let variant_iter = self.variants.iter().map(|(&id, f)| (id, f));
        base_iter.chain(variant_iter)
    }

    /// Iterate mutably over all functions
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (FunctionID, &mut functions::Function)> {
        let base_iter = self
            .base_functions
            .iter_mut()
            .map(|(&base, f)| (FunctionID::new(base), f));
        let variant_iter = self.variants.iter_mut().map(|(&id, f)| (id, f));
        base_iter.chain(variant_iter)
    }

    /// Number of base functions
    pub fn len(&self) -> usize {
        self.base_functions.len()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.base_functions.is_empty()
    }

    /// Get all variants for a base function ID
    pub fn variants_for(
        &self,
        base_id: usize,
    ) -> impl Iterator<Item = (FunctionID, &functions::Function)> {
        self.variants
            .iter()
            .filter(move |(id, _)| id.base == base_id)
            .map(|(&id, f)| (id, f))
    }

    /// Get mutable access to base functions (for dependency sorting)
    pub fn base_functions_mut(&mut self) -> &mut IndexMap<usize, functions::Function> {
        &mut self.base_functions
    }

    /// Iterate over base functions only
    pub fn iter_base(&self) -> impl Iterator<Item = (usize, &functions::Function)> {
        self.base_functions.iter().map(|(&id, f)| (id, f))
    }

    /// Iterate over base function values only (no variants)
    pub fn base_values(&self) -> impl Iterator<Item = &functions::Function> {
        self.base_functions.values()
    }

    /// Iterate over all function values (base + variants)
    pub fn values(&self) -> impl Iterator<Item = &functions::Function> {
        self.base_functions.values().chain(self.variants.values())
    }

    /// Delete a base function and all its variants
    pub fn delete_function(&mut self, base_id: usize) {
        // Remove the base function
        self.base_functions.swap_remove(&base_id);

        // Remove all variants for this function
        self.variants.retain(|id, _| id.base != base_id);
    }

    /// Insert a synthetic function directly with a given ID (for compiler-generated functions)
    /// Returns the ID that was used
    pub fn insert_synthetic(&mut self, id: usize, func: functions::Function) -> usize {
        self.base_functions.insert(id, func);
        id
    }

    /// Get the maximum base function ID (for generating fresh IDs)
    pub fn max_base_id(&self) -> Option<usize> {
        self.base_functions.keys().max().copied()
    }
}

// ============================================================================
// Complete Program IR
// ============================================================================

#[derive(Debug, Clone, Default)]
pub struct Program {
    pub modules: ItemStore<ModuleId, Module>,
    pub structs: ItemStore<QualifiedId<DatatypeId>, structure::Struct>,
    pub functions: FunctionStore,
    /// Generic spec metadata computed by the spec_genericize analysis pass
    pub generic_specs: std::collections::HashMap<FunctionID, crate::analysis::GenericSpec>,
    /// Conversion functions between spec and implementation types
    pub conversions: conversion::ConversionRegistry,
}

impl Program {
    pub fn finalize(&mut self) {
        // ============================================================
        // Phase 1: All function creation/transformation passes
        // ============================================================

        // Dependency ordering (needed for mutual recursion detection)
        order_by_dependencies(self);

        // Analyze abortability before generating variants
        analyze_abortability(self);

        // Generate runtime variants (.pure, .aborts) for aborting functions
        crate::analysis::generate_runtime_variants(self);

        // Generate spec functions (.requires, .ensures)
        // Specs now stay separate - no call rewriting to Pure variants
        crate::analysis::generate_spec_functions(self);

        // Analyze spec functions to infer generic typeclass constraints
        crate::analysis::genericize_specs(self);

        // Generate spec type conversion functions (e.g., i32_to_int, int_to_i32)
        // This should run early so the functions are available for use
        crate::analysis::generate_spec_type_conversions(self);

        // Generate goal functions (.goal) for functions that have specs targeting them
        // Goals use conversion functions to bridge type differences (I32 vs Int)
        crate::analysis::generate_goal_functions(self);

        // Collect imports for each module
        collect_imports(self);

        // ============================================================
        // Phase 2: Optimization (runs on ALL functions created above)
        // ============================================================
        self.optimize_all();
    }

    /// Optimize all functions
    fn optimize_all(&mut self) {
        let function_sigs: BTreeMap<usize, functions::FunctionSignature> = self
            .functions
            .base_functions
            .iter()
            .map(|(&id, f)| (id, f.signature.clone()))
            .collect();
        let struct_defs: BTreeMap<StructID, structure::Struct> = self
            .structs
            .iter()
            .map(|(id, s)| (*id, s.clone()))
            .collect();

        for (_, func) in self.functions.iter_mut() {
            if !func.is_native() {
                let vars = func.variables.clone();
                let ctx = TypeContext::new(&vars, &function_sigs, &struct_defs);
                func.optimize(&ctx);
            }
        }

        // Constant folding pass: inline function calls with constant arguments
        self.fold_constant_calls();
    }

    /// Fold function calls with constant arguments by inlining and evaluating.
    /// Runs multiple passes until no more changes occur.
    fn fold_constant_calls(&mut self) {
        const MAX_ITERATIONS: usize = 10;

        for _ in 0..MAX_ITERATIONS {
            // Collect current function bodies for inlining
            let function_bodies: FunctionBodies = self
                .functions
                .iter()
                .map(|(id, f)| {
                    let params: Vec<String> = f
                        .signature
                        .parameters
                        .iter()
                        .map(|p| p.name.clone())
                        .collect();
                    (id, (params, f.body.clone(), f.is_native()))
                })
                .collect();

            // Track if any changes occurred
            let mut changed = false;

            // Fold constants and simplify in all functions
            for (_, func) in self.functions.iter_mut() {
                let old_body = func.body.clone();
                func.body = fold_constants(func.body.clone(), &function_bodies);
                func.body = crate::analysis::logical_simplify(func.body.clone());
                if func.body != old_body {
                    changed = true;
                }
            }

            // Stop if no changes occurred
            if !changed {
                break;
            }
        }
    }

    // ========================================================================
    // Function Variant Creation
    // ========================================================================

    /// Create a function variant from a source function.
    /// The variant ID uses the same base as the source.
    pub fn create_variant<F>(
        &mut self,
        source_id: FunctionID,
        variant: FunctionVariant,
        return_type: Type,
        transform_body: F,
    ) -> FunctionID
    where
        F: FnOnce(&IRNode) -> IRNode,
    {
        let source = self.functions.get(&source_id);
        let body = transform_body(&source.body);

        // For spec function variants (.requires, .ensures), use the target's name if one exists
        let name = if variant.is_spec_variant() {
            if let Some(target_base_id) = source.spec_target {
                self.functions
                    .get(&FunctionID::new(target_base_id))
                    .name
                    .clone()
            } else {
                source.name.clone()
            }
        } else {
            source.name.clone()
        };

        // Propagate spec_target for spec variants so they can be rendered with the target's namespace
        let propagated_spec_target = if variant.is_spec_variant() {
            source.spec_target
        } else {
            None
        };

        let new_func = functions::Function {
            module_id: source.module_id,
            name,
            signature: FunctionSignature {
                type_params: source.signature.type_params.clone(),
                parameters: source.signature.parameters.clone(),
                return_type,
            },
            body,
            variables: source.variables.clone(),
            mutual_group_id: None,
            flags: FunctionFlags::new(),
            spec_target: propagated_spec_target,
        };

        let new_id = FunctionID::with_variant(source_id.base, variant);
        self.functions.insert_variant(new_id, new_func);
        new_id
    }

    /// Set spec_target for spec functions based on the spec-to-target mapping.
    /// `spec_targets` maps spec function base IDs to their target function base IDs.
    pub fn set_spec_targets(&mut self, spec_targets: &std::collections::HashMap<usize, usize>) {
        for (spec_base_id, target_base_id) in spec_targets {
            let func_id = FunctionID::new(*spec_base_id);
            if self.functions.has(*spec_base_id) {
                let func = self.functions.get_mut(func_id);
                func.spec_target = Some(*target_base_id);
            }
        }
    }

    /// Get all spec functions that target a specific function.
    /// Returns the spec function base IDs.
    pub fn get_specs_for(&self, target_base_id: usize) -> Vec<usize> {
        self.functions
            .iter_base()
            .filter_map(|(base_id, func)| {
                if func.spec_target == Some(target_base_id) {
                    Some(base_id)
                } else {
                    None
                }
            })
            .collect()
    }

    /// Build a mapping from target function base IDs to their spec function base IDs.
    /// This is the reverse of spec_target: target_id -> spec_id.
    /// Used to replace calls to target functions with calls to spec functions.
    pub fn build_target_to_spec_mapping(&self) -> std::collections::HashMap<usize, usize> {
        let mut result = std::collections::HashMap::new();
        for (base_id, func) in self.functions.iter_base() {
            if let Some(target_id) = func.spec_target {
                result.insert(target_id, base_id);
            }
        }
        result
    }
}

#[derive(Debug, Clone)]
pub struct Module {
    pub name: String,
    pub package_name: String,
    pub required_imports: Vec<ModuleID>,
}
