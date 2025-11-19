// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Builds TheoremProgram from Move GlobalEnv
//!
//! Single responsibility: Collect modules, structs, and function signatures.
//! Does NOT translate function bodies - that's FunctionTranslator's job.

use crate::data::functions::{FunctionSignature, Parameter, TheoremFunction};
use crate::data::statements::Statement;
use crate::data::structure::{TheoremField, TheoremStruct};
use crate::data::types::TheoremType;
use crate::data::variables::VariableRegistry;
use crate::data::{
    StructNames, TheoremFunctionID, TheoremModule, TheoremModuleID, TheoremProgram,
    TheoremStructID,
};
use move_model::model::{
    DatatypeId, FunId, FunctionEnv, GlobalEnv, ModuleEnv, ModuleId, QualifiedId,
};
use std::collections::BTreeMap;

/// Builds the complete program IR structure
pub struct ProgramBuilder<'env> {
    env: &'env GlobalEnv,
    next_module_id: TheoremModuleID,
    next_struct_id: TheoremStructID,
    next_function_id: TheoremFunctionID,

    /// Maps Move function QualifiedId to TheoremFunctionID
    function_id_map: BTreeMap<QualifiedId<FunId>, TheoremFunctionID>,

    /// Maps Move struct QualifiedId to TheoremStructID
    struct_id_map: BTreeMap<QualifiedId<DatatypeId>, TheoremStructID>,

    /// Maps Move ModuleId to TheoremModuleID
    module_id_map: BTreeMap<ModuleId, TheoremModuleID>,
}

impl<'env> ProgramBuilder<'env> {
    pub fn new(env: &'env GlobalEnv) -> Self {
        Self {
            env,
            next_module_id: 0,
            next_struct_id: 0,
            next_function_id: 0,
            function_id_map: BTreeMap::new(),
            struct_id_map: BTreeMap::new(),
            module_id_map: BTreeMap::new(),
        }
    }

    /// Build complete program structure
    /// Returns (program, function_id_map, struct_id_map, module_id_map) for use by FunctionTranslator
    pub fn build(
        mut self,
    ) -> (
        TheoremProgram,
        BTreeMap<QualifiedId<FunId>, TheoremFunctionID>,
        BTreeMap<QualifiedId<DatatypeId>, TheoremStructID>,
        BTreeMap<ModuleId, TheoremModuleID>,
    ) {
        let mut program = TheoremProgram::new();

        // Multi-pass approach to handle cross-module dependencies:
        // Pass 1: Collect all modules and register ALL struct IDs across all modules
        for module_env in self.env.get_modules() {
            let _module_id = self.collect_module(&mut program, &module_env);

            // Register ALL datatypes (structs AND enums) - use get_structs_and_enums if available
            // or fall back to iterating all DatatypeId values in the module
            for struct_env in module_env.get_structs() {
                let struct_id = self.next_struct_id;
                self.next_struct_id += 1;

                let qualified_struct_id = QualifiedId {
                    module_id: module_env.get_id(),
                    id: struct_env.get_id(),
                };

                self.struct_id_map.insert(qualified_struct_id, struct_id);
            }

            // Also register enums if they exist
            for enum_env in module_env.get_enums() {
                let struct_id = self.next_struct_id;
                self.next_struct_id += 1;

                let qualified_struct_id = QualifiedId {
                    module_id: module_env.get_id(),
                    id: enum_env.get_id(),
                };

                self.struct_id_map.insert(qualified_struct_id, struct_id);
            }
        }

        // Pass 2: Build all struct definitions (now that all struct IDs are registered)
        for module_env in self.env.get_modules() {
            let module_id = *self.module_id_map.get(&module_env.get_id()).unwrap();
            self.build_structs(&mut program, module_id, &module_env);
        }

        // Pass 3: Build all function signatures (now that all structs are defined)
        for module_env in self.env.get_modules() {
            let module_id = *self.module_id_map.get(&module_env.get_id()).unwrap();
            self.collect_function_signatures(&mut program, module_id, &module_env);
        }

        (
            program,
            self.function_id_map,
            self.struct_id_map,
            self.module_id_map,
        )
    }

    /// Collect a single module
    fn collect_module(
        &mut self,
        program: &mut TheoremProgram,
        module_env: &ModuleEnv,
    ) -> TheoremModuleID {
        let module_id = self.next_module_id;
        self.next_module_id += 1;

        // Extract package name from Move.toml by parsing module location
        let package_name = self
            .extract_package_name_from_module(module_env)
            .unwrap_or_else(|| {
                panic!(
                    "Failed to find Move.toml for module: {}",
                    module_env.get_full_name_str()
                )
            });

        let simple_name = module_env
            .get_name()
            .display(self.env.symbol_pool())
            .to_string();
        let qualified_name = module_env.get_full_name_str();

        let module = TheoremModule {
            id: module_id,
            name: qualified_name.clone(),
            simple_name: simple_name.clone(),
            package_name,
        };

        program.modules.insert(module_id, module);

        // Register in module_id_map for efficient lookup
        self.module_id_map.insert(module_env.get_id(), module_id);

        module_id
    }

    /// Extract package name from module by parsing its source location and finding Move.toml
    fn extract_package_name_from_module(&self, module_env: &ModuleEnv) -> Option<String> {
        let loc = module_env.get_loc();
        let path_str = format!("{}", loc.display(self.env));

        // Location format: "at path:line:column"
        let without_prefix = if path_str.starts_with("at ") {
            &path_str[3..]
        } else {
            &path_str
        };

        // Find the last occurrence of ".move:" to identify the file path boundary
        let file_path = if let Some(move_pos) = without_prefix.find(".move:") {
            &without_prefix[..move_pos + 5] // Include ".move" but not the ":"
        } else {
            without_prefix
        };

        // Walk up directory tree to find Move.toml
        self.find_package_name_from_path(std::path::Path::new(file_path))
    }

    /// Find the Move.toml file by walking up from the given path and extract the package name
    fn find_package_name_from_path(&self, start_path: &std::path::Path) -> Option<String> {
        let mut current_dir = start_path.parent()?;

        // Walk up the directory tree looking for Move.toml
        loop {
            let move_toml_path = current_dir.join("Move.toml");

            if move_toml_path.exists() {
                // Found Move.toml, try to parse it
                if let Some(package_name) = self.parse_package_name_from_toml(&move_toml_path) {
                    return Some(package_name);
                }
            }

            // Move up one directory
            current_dir = current_dir.parent()?;
        }
    }

    /// Parse the package name from a Move.toml file
    fn parse_package_name_from_toml(&self, toml_path: &std::path::Path) -> Option<String> {
        use std::fs;

        // Read the file
        let content = fs::read_to_string(toml_path).ok()?;

        // Simple parsing - look for [package] section and name = "..."
        let mut in_package_section = false;

        for line in content.lines() {
            let line = line.trim();

            // Check if we're entering the [package] section
            if line == "[package]" {
                in_package_section = true;
                continue;
            }

            // Check if we're leaving the [package] section
            if line.starts_with('[') && line != "[package]" {
                in_package_section = false;
                continue;
            }

            // If we're in the [package] section, look for name = "..."
            if in_package_section && line.starts_with("name") {
                // Parse: name = "package_name"
                if let Some(eq_pos) = line.find('=') {
                    let value = line[eq_pos + 1..].trim();
                    // Remove quotes
                    let value = value.trim_matches('"').trim_matches('\'');
                    return Some(value.to_string());
                }
            }
        }

        None
    }

    /// Build all struct and enum definitions in a module
    /// IMPORTANT: Assumes struct IDs are already registered in struct_id_map
    fn build_structs(
        &mut self,
        program: &mut TheoremProgram,
        module_id: TheoremModuleID,
        module_env: &ModuleEnv,
    ) {
        // Build structs with field types (struct IDs already registered)
        for struct_env in module_env.get_structs() {
            let qualified_struct_id = QualifiedId {
                module_id: module_env.get_id(),
                id: struct_env.get_id(),
            };
            let struct_id = *self.struct_id_map.get(&qualified_struct_id).unwrap();

            let struct_name = struct_env
                .get_name()
                .display(self.env.symbol_pool())
                .to_string();
            let qualified_name = struct_env.get_full_name_str();

            // Build fields with type resolution
            let fields = struct_env
                .get_fields()
                .map(|field| {
                    let field_type = TheoremType::from_move_type(
                        &field.get_type(),
                        self.env,
                        &self.struct_id_map,
                    );
                    TheoremField {
                        name: field.get_name().display(self.env.symbol_pool()).to_string(),
                        field_type,
                    }
                })
                .collect();

            let theorem_struct = TheoremStruct {
                id: struct_id,
                module_id,
                name: struct_name.clone(),
                qualified_name: qualified_name.clone(),
                type_params: struct_env
                    .get_type_parameters()
                    .iter()
                    .map(|tp| {
                        let name = tp.0.display(self.env.symbol_pool()).to_string();
                        // Sanitize: Remove $ prefix from type parameter names (Lean doesn't allow $)
                        name.trim_start_matches('$').to_string()
                    })
                    .collect(),
                fields,
                mutual_group_id: None, // Will be set by dependency analysis
            };

            program.structs.insert(struct_id, theorem_struct);

            // Register struct names in NameManager
            let type_name = TheoremType::sanitize_name(&struct_name);
            let module_name = TheoremType::sanitize_name(
                &module_env
                    .get_name()
                    .display(self.env.symbol_pool())
                    .to_string(),
            );

            program.name_manager.register_struct(
                struct_id,
                StructNames {
                    type_name,
                    module_name,
                },
            );
        }

        // Build enums similarly to structs
        for enum_env in module_env.get_enums() {
            let qualified_enum_id = QualifiedId {
                module_id: module_env.get_id(),
                id: enum_env.get_id(),
            };
            let enum_id = *self.struct_id_map.get(&qualified_enum_id).unwrap();

            let enum_name = enum_env
                .get_name()
                .display(self.env.symbol_pool())
                .to_string();
            let qualified_name = enum_env.get_full_name_str();

            // Enums are treated as structs with variant fields
            // Empty struct representation for enums
            let theorem_struct = TheoremStruct {
                id: enum_id,
                module_id,
                name: enum_name.clone(),
                qualified_name: qualified_name.clone(),
                type_params: enum_env
                    .get_type_parameters()
                    .iter()
                    .map(|tp| {
                        let name = tp.0.display(self.env.symbol_pool()).to_string();
                        name.trim_start_matches('$').to_string()
                    })
                    .collect(),
                fields: vec![],        // Enums don't have simple fields like structs
                mutual_group_id: None, // Will be set by dependency analysis
            };

            program.structs.insert(enum_id, theorem_struct);

            let type_name = TheoremType::sanitize_name(&enum_name);
            let module_name = TheoremType::sanitize_name(
                &module_env
                    .get_name()
                    .display(self.env.symbol_pool())
                    .to_string(),
            );

            program.name_manager.register_struct(
                enum_id,
                StructNames {
                    type_name,
                    module_name,
                },
            );
        }
    }

    /// Collect function signatures (bodies will be translated later)
    /// Collects ALL functions for signature resolution, but marks which are verification targets
    fn collect_function_signatures(
        &mut self,
        program: &mut TheoremProgram,
        module_id: TheoremModuleID,
        module_env: &ModuleEnv,
    ) {
        for func_env in module_env.get_functions() {
            let func_id = self.next_function_id;
            self.next_function_id += 1;

            // Record mapping for later function body translation
            let qualified_id = func_env.get_qualified_id();
            self.function_id_map.insert(qualified_id.clone(), func_id);

            // Build signature
            let signature = self.build_signature(&func_env);

            // Create function with empty body (will be filled by FunctionTranslator)
            let theorem_func = TheoremFunction {
                id: func_id,
                module_id,
                name: func_env
                    .get_name()
                    .display(self.env.symbol_pool())
                    .to_string(),
                signature,
                body: Statement::Sequence(vec![]), // Placeholder
                ssa_registry: VariableRegistry::new(),
                mutual_group_id: None, // Will be set by dependency analysis
            };

            program.functions.insert(func_id, theorem_func);
        }
    }

    /// Build function signature from FunctionEnv
    fn build_signature(&self, func_env: &FunctionEnv) -> FunctionSignature {
        let type_params = func_env
            .get_type_parameters()
            .iter()
            .map(|tp| {
                let name = tp.0.display(self.env.symbol_pool()).to_string();
                // Sanitize: Remove $ prefix from type parameter names (Lean doesn't allow $)
                name.trim_start_matches('$').to_string()
            })
            .collect();

        let parameters = func_env
            .get_parameters()
            .iter()
            .enumerate()
            .map(|(idx, param)| {
                let param_type =
                    TheoremType::from_move_type(&param.1, self.env, &self.struct_id_map);
                let param_name = param.0.display(self.env.symbol_pool()).to_string();
                // Sanitize parameter names: replace _ with a valid name
                let sanitized_name = if param_name == "_" {
                    format!("param{}", idx)
                } else {
                    param_name
                };
                Parameter {
                    name: sanitized_name,
                    param_type,
                    ssa_value: idx as u32, // Initial SSA value is parameter index
                }
            })
            .collect();

        // Build return types wrapped in ProgramState monad for abort handling
        let return_types: Vec<TheoremType> = func_env
            .get_return_types()
            .iter()
            .map(|ty| TheoremType::from_move_type(ty, self.env, &self.struct_id_map))
            .collect();

        // Wrap return type in ProgramState monad
        // - Empty return (Unit) -> ProgramState Unit
        // - Single return -> ProgramState T
        // - Multiple returns -> ProgramState (T1 × T2 × ...)
        let wrapped_return_types = if return_types.is_empty() {
            // Empty tuple is Unit
            vec![TheoremType::Tuple(vec![]).wrap_in_monad()]
        } else if return_types.len() == 1 {
            vec![return_types[0].clone().wrap_in_monad()]
        } else {
            vec![TheoremType::Tuple(return_types.clone()).wrap_in_monad()]
        };

        FunctionSignature {
            type_params,
            parameters,
            return_types: wrapped_return_types,
        }
    }
}
