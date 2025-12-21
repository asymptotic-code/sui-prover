// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Builds complete TheoremProgram from Move GlobalEnv
//!
//! Uses lazy ID generation - IDs are created on first reference.
//! Single pass creates all definitions and translates function bodies.

use crate::package_utils::extract_package_name;
use crate::translation::function_translator::translate_function;
use intermediate_theorem_format::{Field, FunctionID, Module, Program, Struct, StructID, Type};
use move_model::model::{DatatypeId, FunId, GlobalEnv, ModuleEnv, QualifiedId, TypeParameter};
use move_model::symbol::Symbol;
use move_model::ty::Type as MoveType;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::function_target_pipeline::{FunctionTargetsHolder, FunctionVariant};
use move_stackless_bytecode::package_targets::PackageTargets;
use move_stackless_bytecode::stackless_bytecode::Bytecode;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

pub struct ProgramBuilder<'env> {
    env: &'env GlobalEnv,
    pub program: Program,
    /// Cached FunctionID for prover::prover::invariant_begin (if available)
    pub invariant_begin_id: Option<FunctionID>,
    /// Cached FunctionID for prover::prover::invariant_end (if available)
    pub invariant_end_id: Option<FunctionID>,
}

impl<'env> ProgramBuilder<'env> {
    pub fn new(env: &'env GlobalEnv) -> Self {
        Self {
            env,
            program: Program::default(),
            invariant_begin_id: None,
            invariant_end_id: None,
        }
    }

    /// Cache the invariant function IDs after initial function ID creation
    pub fn cache_invariant_ids(&mut self) {
        // Look up invariant_begin
        if let Some(qid) = self.try_get_prover_function_qid("invariant_begin") {
            self.invariant_begin_id = Some(self.function_id(qid));
        }
        // Look up invariant_end
        if let Some(qid) = self.try_get_prover_function_qid("invariant_end") {
            self.invariant_end_id = Some(self.function_id(qid));
        }
    }

    /// Try to get a QualifiedId for a function in the prover module
    fn try_get_prover_function_qid(&self, func_name: &str) -> Option<QualifiedId<FunId>> {
        // Look for the prover module
        for module_env in self.env.get_modules() {
            let module_name = self.symbol_str(module_env.get_name().name());
            if module_name.as_str() == "prover" {
                // Found the prover module, look for the function
                for func_env in module_env.get_functions() {
                    let name = self.symbol_str(func_env.get_name());
                    if name.as_str() == func_name {
                        return Some(func_env.get_qualified_id());
                    }
                }
            }
        }
        None
    }

    pub fn env(&self) -> &GlobalEnv {
        self.env
    }

    pub fn struct_id(&mut self, id: QualifiedId<DatatypeId>) -> StructID {
        let struct_id = self.program.structs.id_for_key(id);
        // Ensure struct data exists - create it if not yet processed
        if !self.program.structs.has(struct_id) {
            self.create_struct(id);
        }
        struct_id
    }

    pub fn function_id(&mut self, id: QualifiedId<FunId>) -> FunctionID {
        FunctionID::new(self.program.functions.id_for_key(id))
    }

    pub fn build(mut self, targets: &'env FunctionTargetsHolder, package_targets: &PackageTargets) -> Program {
        // Compute reachable functions from spec functions
        let reachable = self.compute_reachable_functions(targets, package_targets);

        // First pass: create modules and register function IDs for reachable functions only
        for module_env in self.env.get_modules() {
            self.create_module(&module_env);

            // Register function IDs only for reachable functions
            for func_env in module_env.get_functions() {
                let qid = func_env.get_qualified_id();
                if reachable.contains(&qid) {
                    if targets.get_target_opt(&func_env, &FunctionVariant::Baseline).is_some() {
                        let _ = self.function_id(qid);
                    }
                }
            }
        }

        // Cache invariant function IDs now that all functions are registered
        self.cache_invariant_ids();

        // Second pass: translate function bodies for reachable functions only
        for module_env in self.env.get_modules() {
            for func_env in module_env.get_functions() {
                let qid = func_env.get_qualified_id();
                if reachable.contains(&qid) {
                    if let Some(target) = targets.get_target_opt(&func_env, &FunctionVariant::Baseline)
                    {
                        self.create_function(target);
                    }
                }
            }
        }

        // Build spec_target mapping and set it BEFORE finalize() so dependency ordering
        // can account for spec function body dependencies
        let spec_targets = self.build_spec_target_mapping(package_targets);
        self.program.set_spec_targets(&spec_targets);

        self.program.finalize();
        self.program
    }

    /// Compute the set of functions reachable from spec functions.
    /// This includes:
    /// - All spec functions (target_specs)
    /// - All functions called transitively by spec functions (full transitive closure)
    fn compute_reachable_functions(
        &self,
        targets: &FunctionTargetsHolder,
        package_targets: &PackageTargets,
    ) -> HashSet<QualifiedId<FunId>> {
        let mut reachable = HashSet::new();
        let mut worklist: Vec<QualifiedId<FunId>> = Vec::new();

        // Start with all spec functions
        eprintln!("[REACHABLE] Starting with {} target_specs", package_targets.target_specs().len());
        for spec_id in package_targets.target_specs() {
            let func_name = self.env.get_function(*spec_id).get_name_str();
            if func_name.contains("tick") || func_name.contains("sqrt") {
                eprintln!("[REACHABLE]   Adding spec: {}", func_name);
            }
            worklist.push(*spec_id);
        }

        // BFS to find all reachable functions
        while let Some(func_id) = worklist.pop() {
            if reachable.contains(&func_id) {
                continue;
            }
            reachable.insert(func_id);

            // Get the function's bytecode and find all called functions
            let func_env = self.env.get_function(func_id);
            let func_name = func_env.get_name_str();
            if let Some(target) = targets.get_target_opt(&func_env, &FunctionVariant::Baseline) {
                for called_id in Bytecode::get_called_functions(target.get_bytecode()) {
                    if !reachable.contains(&called_id) {
                        worklist.push(called_id);
                    }
                }
            } else {
                if func_name.contains("_math") {
                    // Debug: check if the function exists in targets at all
                    let has_target = targets.has_target(&func_env, &FunctionVariant::Baseline);
                    let variants = targets.get_target_variants(&func_env);
                    eprintln!("[REACHABLE]   {} has NO bytecode target! has_target={} variants={:?} qid={:?}",
                        func_name, has_target, variants, func_id);
                }
            }
        }

        eprintln!("[REACHABLE] Final reachable set has {} functions", reachable.len());
        reachable
    }

    /// Build mapping from spec function base IDs to their target function base IDs.
    fn build_spec_target_mapping(&self, package_targets: &PackageTargets) -> HashMap<usize, usize> {
        let mut result = HashMap::new();

        eprintln!("[BUILD_SPEC_TARGET] Building spec->target mapping");
        // Iterate through all spec->target mappings from PackageTargets
        // all_specs maps target_id -> set of spec_ids
        // We need the reverse: spec_id -> target_id
        for (target_move_id, spec_move_ids) in package_targets.iter_all_specs() {
            // Look up the target function's IR base ID
            let target_func_name = self.env.get_function(*target_move_id).get_name_str();
            let target_ir_id = match self.program.functions.get_id_for_move_key(target_move_id) {
                Some(id) => id,
                None => {
                    if target_func_name.contains("tick") || target_func_name.contains("sqrt") {
                        eprintln!("[BUILD_SPEC_TARGET]   Target {} NOT in IR (skipping)", target_func_name);
                    }
                    continue; // Target function not in IR
                }
            };

            // For each spec function targeting this function
            for spec_move_id in spec_move_ids {
                let spec_func_name = self.env.get_function(*spec_move_id).get_name_str();
                // Look up the spec function's IR base ID
                if let Some(spec_ir_id) = self.program.functions.get_id_for_move_key(spec_move_id) {
                    if spec_func_name.contains("tick") || spec_func_name.contains("sqrt") {
                        eprintln!("[BUILD_SPEC_TARGET]   Mapping spec {} (IR {}) -> target {} (IR {})",
                            spec_func_name, spec_ir_id, target_func_name, target_ir_id);
                    }
                    result.insert(spec_ir_id, target_ir_id);
                } else {
                    if spec_func_name.contains("tick") || spec_func_name.contains("sqrt") {
                        eprintln!("[BUILD_SPEC_TARGET]   Spec {} NOT in IR (skipping)", spec_func_name);
                    }
                }
            }
        }

        eprintln!("[BUILD_SPEC_TARGET] Final mapping has {} entries", result.len());
        result
    }

    fn create_module(&mut self, module_env: &ModuleEnv) {
        self.program.modules.create(
            module_env.get_id(),
            Module {
                name: Self::sanitize_name(&self.symbol_str(module_env.get_name().name())),
                package_name: extract_package_name(self.env, module_env),
                required_imports: Vec::new(),
            },
        );
    }

    fn create_struct(&mut self, qualified_id: QualifiedId<DatatypeId>) {
        let module_env = self.env.get_module(qualified_id.module_id);

        // DatatypeId can refer to either a struct or an enum
        // Try to find as struct first, then as enum
        let struct_symbol = qualified_id.id.symbol();
        let Some(move_struct) = module_env.find_struct(struct_symbol) else {
            // Check if it's an enum instead - enums are not yet supported
            if module_env.find_enum(struct_symbol).is_some() {
                let name = self.env.symbol_pool().string(struct_symbol);
                let module_name = module_env.get_full_name_str();
                panic!("Enums are not yet supported: {}::{}", module_name, name);
            }
            // Struct not found in module - this shouldn't happen in normal operation
            panic!("Struct not found: {:?}", qualified_id);
        };

        // Ensure module exists
        let module_id = self.program.modules.id_for_key(qualified_id.module_id);
        if !self.program.modules.has(module_id) {
            self.create_module(&module_env);
        }

        let fields = move_struct
            .get_fields()
            .map(|f| Field {
                name: Self::sanitize_name(&self.symbol_str(f.get_name())),
                field_type: self.convert_type(&f.get_type()),
            })
            .collect();

        let struct_name = Self::sanitize_name(&self.symbol_str(move_struct.get_name()));
        self.program.structs.create(
            qualified_id,
            Struct {
                module_id,
                name: struct_name,
                qualified_name: move_struct.get_full_name_str(),
                type_params: self.sanitize_type_params(&move_struct.get_type_parameters()),
                fields,
                mutual_group_id: None,
            },
        );
    }

    fn create_function(&mut self, target: FunctionTarget<'_>) {
        let qualified_id = target.func_env.get_qualified_id();
        let func = translate_function(self, target);
        self.program.functions.create(qualified_id, func);
    }

    pub fn convert_types(&mut self, types: &[MoveType]) -> Vec<Type> {
        types.iter().map(|types| self.convert_type(types)).collect()
    }
    
    pub fn convert_type(&mut self, ty: &MoveType) -> Type {
        use move_model::ty::PrimitiveType;
        match ty {
            MoveType::Primitive(PrimitiveType::Bool) => Type::Bool,
            MoveType::Primitive(PrimitiveType::U8) => Type::UInt(8),
            MoveType::Primitive(PrimitiveType::U16) => Type::UInt(16),
            MoveType::Primitive(PrimitiveType::U32) => Type::UInt(32),
            MoveType::Primitive(PrimitiveType::U64) => Type::UInt(64),
            MoveType::Primitive(PrimitiveType::U128) => Type::UInt(128),
            MoveType::Primitive(PrimitiveType::U256) => Type::UInt(256),
            MoveType::Primitive(PrimitiveType::Address | PrimitiveType::Signer) => Type::Address,
            MoveType::Datatype(mid, sid, args) => {
                let qualified_id = mid.qualified(*sid);
                self.convert_datatype(qualified_id, args)
            }
            MoveType::Vector(t) => Type::Vector(Box::new(self.convert_type(t))),
            MoveType::Reference(_, t) => Type::Reference(Box::new(self.convert_type(t))),
            MoveType::TypeParameter(idx) => Type::TypeParameter(*idx),
            MoveType::Tuple(ts) => Type::Tuple(ts.iter().map(|t| self.convert_type(t)).collect()),
            _ => unreachable!("Unsupported type: {:?}", ty),
        }
    }

    /// Convert a datatype (struct or enum) to TheoremType
    /// Panics if the datatype is an enum (unsupported)
    fn convert_datatype(
        &mut self,
        qualified_id: QualifiedId<DatatypeId>,
        args: &[MoveType],
    ) -> Type {
        let module_env = self.env.get_module(qualified_id.module_id);
        let symbol = qualified_id.id.symbol();

        // Check if this is an enum - enums are not yet supported
        if module_env.find_enum(symbol).is_some() {
            let name = self.env.symbol_pool().string(symbol);
            let module_name = module_env.get_full_name_str();
            panic!("Enums are not yet supported: {}::{}", module_name, name);
        }

        Type::Struct {
            struct_id: self.struct_id(qualified_id),
            type_args: args.iter().map(|a| self.convert_type(a)).collect(),
        }
    }

    pub fn sanitize_name(name: &str) -> String {
        name.replace("::", "_")
            .replace("<", "")
            .replace(">", "")
            .replace("$", "_")
            .replace("%", "_")
            .replace("#", "_")
            .replace("@", "_")
            .chars()
            .filter(|c| c.is_alphanumeric() || *c == '_')
            .collect()
    }

    pub(crate) fn sanitize_type_params(&self, params: &[TypeParameter]) -> Vec<String> {
        params
            .iter()
            .map(|p| Self::sanitize_name(self.symbol_str(p.0).trim_start_matches('$')))
            .collect()
    }

    pub(crate) fn symbol_str(&self, sym: Symbol) -> Rc<String> {
        self.env.symbol_pool().string(sym)
    }
}
