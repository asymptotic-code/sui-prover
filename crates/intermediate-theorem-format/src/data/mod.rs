// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

use indexmap::IndexMap;
use move_model::model::{DatatypeId, FunId, ModuleId, QualifiedId};
use std::borrow::Borrow;
use std::collections::BTreeMap;

use crate::analysis::{analyze_monadicity, collect_imports, convert_to_pure, fold_constants, order_by_dependencies, FunctionBodies};
use crate::data::functions::{FunctionFlags, FunctionVariant};
use crate::data::variables::TypeContext;
use crate::{FunctionSignature, IRNode, Type};

/// Extract the computation from a spec function body.
/// Strips requires/ensures nodes and extracts the return value.
fn extract_spec_computation(body: &IRNode) -> IRNode {
    // Clone and filter out requires/ensures
    let filtered = body.clone().filter(|n| {
        !matches!(n, IRNode::Requires(_) | IRNode::Ensures(_))
    });

    // The spec function body typically ends with Return([expr]).
    // We want to keep the let bindings and replace Return with the inner expression.
    transform_return_to_expr(filtered)
}

/// Transform Return nodes into their inner expression.
/// Block([..stmts, Return([expr])]) becomes Block([..stmts, expr])
fn transform_return_to_expr(node: IRNode) -> IRNode {
    node.map(&mut |n| match n {
        IRNode::Block { mut children } => {
            // Check if last child is Return
            if let Some(last) = children.last_mut() {
                if let IRNode::Return(values) = last {
                    if values.len() == 1 {
                        *last = values.pop().unwrap();
                    } else if values.is_empty() {
                        *last = IRNode::unit();
                    } else {
                        *last = IRNode::Tuple(std::mem::take(values));
                    }
                }
            }
            IRNode::Block { children }
        }
        IRNode::Return(mut values) => {
            // Top-level Return
            if values.len() == 1 {
                values.pop().unwrap()
            } else if values.is_empty() {
                IRNode::unit()
            } else {
                IRNode::Tuple(values)
            }
        }
        other => other,
    })
}
pub use functions::FunctionID;
pub use structure::StructID;

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
            self.variants.get(id).unwrap_or_else(|| {
                panic!("Variant function {:?} should exist", id)
            })
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
            self.base_functions.get_mut(&id.base).expect("Base function should exist")
        } else {
            self.variants.get_mut(&id).expect("Variant function should exist")
        }
    }

    /// Insert a variant function
    pub fn insert_variant(&mut self, id: FunctionID, func: functions::Function) {
        debug_assert!(id.variant != FunctionVariant::Runtime, "Use create() for base functions");
        self.variants.insert(id, func);
    }

    /// Iterate over base function IDs
    pub fn iter_base_ids(&self) -> impl Iterator<Item = usize> + '_ {
        self.base_functions.keys().copied()
    }

    /// Iterate over all function IDs (base + variants)
    pub fn iter_ids(&self) -> impl Iterator<Item = FunctionID> + '_ {
        let base_ids = self.base_functions.keys().map(|&base| FunctionID::new(base));
        let variant_ids = self.variants.keys().copied();
        base_ids.chain(variant_ids)
    }

    /// Iterate over all functions with their IDs
    pub fn iter(&self) -> impl Iterator<Item = (FunctionID, &functions::Function)> {
        let base_iter = self.base_functions.iter().map(|(&base, f)| (FunctionID::new(base), f));
        let variant_iter = self.variants.iter().map(|(&id, f)| (id, f));
        base_iter.chain(variant_iter)
    }

    /// Iterate mutably over all functions
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (FunctionID, &mut functions::Function)> {
        let base_iter = self.base_functions.iter_mut().map(|(&base, f)| (FunctionID::new(base), f));
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
    pub fn variants_for(&self, base_id: usize) -> impl Iterator<Item = (FunctionID, &functions::Function)> {
        self.variants.iter()
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

    /// Iterate over all function values
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
}

// ============================================================================
// Complete Program IR
// ============================================================================

#[derive(Debug, Clone, Default)]
pub struct Program {
    pub modules: ItemStore<ModuleId, Module>,
    pub structs: ItemStore<QualifiedId<DatatypeId>, structure::Struct>,
    pub functions: FunctionStore,
}

impl Program {
    pub fn finalize(&mut self) {
        // Replace target function bodies with spec function bodies.
        // This must happen BEFORE runtime variants are generated so the
        // Pure/Aborts variants get the simplified spec body.
        self.apply_spec_body_replacements();

        // First pass: dependency ordering and optimization
        order_by_dependencies(self);
        self.optimize_all();

        // Analyze monadicity before generating variants
        analyze_monadicity(self);

        // Generate runtime variants (.pure, .aborts) for monadic functions
        crate::analysis::generate_runtime_variants(self);

        // Generate spec functions (.requires, .ensures) AFTER runtime variants exist
        // so calls can be properly rewritten to .pure variants
        crate::analysis::generate_spec_functions(self);

        // Final passes
        collect_imports(self);
        self.optimize_all();
    }

    /// Replace target function bodies with their spec function bodies.
    /// For each spec function that targets another function AND provides an alternative
    /// implementation (i.e., does NOT call the target), copy the spec's body into the target.
    /// After replacement, delete the original spec function.
    fn apply_spec_body_replacements(&mut self) {
        // Build target -> spec mapping
        let target_to_spec = self.build_target_to_spec_mapping();

        log::debug!("=== Spec Body Replacement ===");
        log::debug!("  Found {} spec->target mappings", target_to_spec.len());

        let mut spec_ids_to_delete: Vec<usize> = Vec::new();

        // For each target function, check if spec provides an alternative implementation
        for (target_id, spec_id) in target_to_spec {
            let spec_name = self.functions.get(&FunctionID::new(spec_id)).name.clone();
            let target_name = self.functions.get(&FunctionID::new(target_id)).name.clone();

            // Check if the spec function calls the target function
            // If it does, it's a verification spec (not an implementation spec)
            let calls_target = {
                let spec_func = self.functions.get(&FunctionID::new(spec_id));
                spec_func.body.calls().any(|call_id| call_id.base == target_id)
            };

            log::debug!("  {} -> {} (calls_target={})", spec_name, target_name, calls_target);

            // Only replace if spec does NOT call target (i.e., it's an alternative implementation)
            if !calls_target {
                let spec_body = {
                    let spec_func = self.functions.get(&FunctionID::new(spec_id));
                    extract_spec_computation(&spec_func.body)
                };

                log::debug!("    REPLACING body of {}", target_name);

                // Save the original body before replacing
                let original_body = {
                    let target_func = self.functions.get(&FunctionID::new(target_id));
                    target_func.body.clone()
                };

                // If original body has aborts, create a Pure variant from it
                // This is needed because after replacement, monadicity analysis will see
                // the clean spec body and won't generate a Pure variant
                if original_body.aborts() {
                    log::debug!("    Creating Pure variant from original body (has aborts)");
                    let pure_body = convert_to_pure(&original_body);
                    let target_func = self.functions.get(&FunctionID::new(target_id));
                    let return_type = target_func.signature.return_type.base_type();
                    let mut pure_func = target_func.clone();
                    pure_func.body = pure_body;
                    pure_func.signature.return_type = return_type;

                    let pure_id = FunctionID {
                        base: target_id,
                        variant: FunctionVariant::Pure,
                    };
                    self.functions.insert_variant(pure_id, pure_func);
                }

                // Now replace the body with spec body and store original
                let target_func = self.functions.get_mut(FunctionID::new(target_id));
                target_func.original_body = Some(original_body);
                target_func.body = spec_body;

                // If the original return type was wrapped in Except (monadic) but the
                // spec body is pure, unwrap the return type to match the spec's semantics
                if !target_func.body.aborts() {
                    if let crate::Type::Except(inner) = &target_func.signature.return_type {
                        let inner_type = (**inner).clone();
                        log::debug!("    Unwrapping return type from {:?} to {:?}", target_func.signature.return_type, inner_type);
                        target_func.signature.return_type = inner_type;
                    }
                }

                // Don't delete spec functions - they're needed in Specs/ directory
            }
        }

        log::debug!("=============================");
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
                    let params: Vec<String> = f.signature.parameters.iter().map(|p| p.name.clone()).collect();
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
                self.functions.get(&FunctionID::new(target_base_id)).name.clone()
            } else {
                source.name.clone()
            }
        } else {
            source.name.clone()
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
            spec_target: None,
            original_body: None,
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

