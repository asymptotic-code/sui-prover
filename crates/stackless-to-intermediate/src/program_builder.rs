// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Builds complete TheoremProgram from Move GlobalEnv
//!
//! Uses the builder infrastructure from intermediate_theorem_format

use crate::{package_utils, translation::function_translator};
use intermediate_theorem_format::{
    FunctionConstruction, FunctionSignature, LazyIdBuilder, ModuleConstruction, Parameter,
    StructConstruction, StructNames, TheoremField, TheoremFunctionID, TheoremModuleID,
    TheoremStructID, TheoremType, VariableRegistry,
};
use move_model::model::{
    DatatypeId, FunId, FunctionEnv, GlobalEnv, ModuleEnv, QualifiedId,
};
use move_stackless_bytecode::function_target_pipeline::{FunctionTargetsHolder, FunctionVariant};

/// Builds the complete program IR structure
pub struct ProgramBuilder<'env> {
    env: &'env GlobalEnv,
    builder: LazyIdBuilder,
}

impl<'env> ProgramBuilder<'env> {
    pub fn new(env: &'env GlobalEnv) -> Self {
        Self {
            env,
            builder: LazyIdBuilder::new(),
        }
    }

    pub fn env(&self) -> &GlobalEnv {
        self.env
    }

    /// Check if a function is native (has no bytecode implementation)
    pub fn is_function_native(&self, module_id: move_model::model::ModuleId, fun_id: FunId) -> bool {
        let module_env = self.env.get_module(module_id);
        let fun_env = module_env.get_function(fun_id);
        fun_env.is_native()
    }

    /// Get or create a module ID, adding the module if it doesn't exist
    fn get_or_create_module_id(&mut self, module_env: &ModuleEnv) -> TheoremModuleID {
        let module_key = module_env.get_id();
        let id = self.builder.get_or_create_module_id(module_key);

        // Add construction data if not already added
        if !self.builder.modules.contains_key(&id) {
            let package_name = package_utils::extract_package_name(self.env, module_env);
            let name = module_env
                .get_name()
                .display(self.env.symbol_pool())
                .to_string();

            let construction = ModuleConstruction {
                name,
                package_name,
            };

            self.builder.add_module(id, construction);
        }

        id
    }

    /// Get or reserve a struct ID for type conversion
    /// This allocates an ID early for forward references
    pub fn get_or_reserve_struct_id(
        &mut self,
        qualified_id: QualifiedId<DatatypeId>,
    ) -> TheoremStructID {
        self.builder.get_or_create_struct_id(qualified_id)
    }

    /// Get or reserve a function ID for forward references
    pub fn get_or_reserve_function_id(&mut self, qualified_id: QualifiedId<FunId>) -> TheoremFunctionID {
        self.builder.get_or_create_function_id(qualified_id)
    }

    /// Build complete program with all function bodies translated
    pub fn build(mut self, targets: &'env FunctionTargetsHolder) -> LazyIdBuilder {
        let modules: Vec<_> = self.env.get_modules().collect();
        for module_env in modules {
            self.build_module(&module_env, targets);
        }

        self.builder
    }

    /// Build a complete module including its structs and functions
    fn build_module<'m>(&mut self, module_env: &'m ModuleEnv<'m>, targets: &'env FunctionTargetsHolder) {
        let _module_id = self.get_or_create_module_id(module_env);

        // Build structs and enums
        self.build_structs(module_env);

        // Build functions
        self.build_functions(module_env, targets);
    }

    /// Build all struct and enum definitions in a module
    fn build_structs(&mut self, module_env: &ModuleEnv) {
        let module_id = self.get_or_create_module_id(module_env);

        for struct_env in module_env.get_structs() {
            let fields = struct_env
                .get_fields()
                .map(|field| TheoremField {
                    name: field.get_name().display(self.env.symbol_pool()).to_string(),
                    field_type: self.convert_type(&field.get_type()),
                })
                .collect();

            self.build_datatype(
                module_id,
                module_env,
                struct_env.get_id(),
                struct_env.get_name(),
                struct_env.get_full_name_str(),
                &struct_env.get_type_parameters(),
                fields,
            );
        }

        for enum_env in module_env.get_enums() {
            self.build_datatype(
                module_id,
                module_env,
                enum_env.get_id(),
                enum_env.get_name(),
                enum_env.get_full_name_str(),
                &enum_env.get_type_parameters(),
                vec![],
            );
        }
    }

    /// Build a single datatype (struct or enum) and register it
    fn build_datatype(
        &mut self,
        module_id: TheoremModuleID,
        module_env: &ModuleEnv,
        datatype_id: DatatypeId,
        name_symbol: move_model::symbol::Symbol,
        qualified_name: String,
        type_parameters: &[move_model::model::TypeParameter],
        fields: Vec<TheoremField>,
    ) {
        let qualified_id = QualifiedId {
            module_id: module_env.get_id(),
            id: datatype_id,
        };

        let struct_id = self.builder.get_or_create_struct_id(qualified_id);

        // Skip if already added
        if self.builder.structs.contains_key(&struct_id) {
            return;
        }

        let name = name_symbol.display(self.env.symbol_pool()).to_string();
        let type_params = self.sanitize_type_params(type_parameters);

        let construction = StructConstruction {
            name: name.clone(),
            qualified_name,
            type_params,
            fields,
        };

        self.builder.add_struct(struct_id, module_id, construction);
        self.register_struct_name(module_env, struct_id, &name);
    }

    /// Build all function definitions in a module
    fn build_functions<'m>(&mut self, module_env: &'m ModuleEnv<'m>, targets: &'env FunctionTargetsHolder) {
        let module_id = self.get_or_create_module_id(module_env);

        for func_env in module_env.get_functions() {
            if !targets.has_target(&func_env, &FunctionVariant::Baseline) {
                continue;
            }

            let qualified_id = func_env.get_qualified_id();
            let function_id = self.builder.get_or_create_function_id(qualified_id);

            // Skip if already added
            if self.builder.functions.contains_key(&function_id) {
                continue;
            }

            let target = targets.get_target(&func_env, &FunctionVariant::Baseline);
            let signature = self.build_signature(&func_env);
            let parameters = signature.parameters.clone();
            let name = func_env
                .get_name()
                .display(self.env.symbol_pool())
                .to_string();

            eprintln!("PROGRAM_BUILDER: Translating function '{}'...", func_env.get_name().display(self.env.symbol_pool()));
            let mut registry = VariableRegistry::new();
            let body = function_translator::translate_function(self, &target, &mut registry, &parameters);

            // A function is considered "native" (requiring external implementation) if:
            // 1. It's declared as native in Move, OR
            // 2. It has no bytecode (e.g., stdlib functions without available bytecode)
            let has_no_bytecode = target.get_bytecode().is_empty();
            let is_native = func_env.is_native() || has_no_bytecode;

            let construction = FunctionConstruction {
                name,
                signature,
                body,
                ssa_registry: registry,
                is_native,
            };

            self.builder.add_function(function_id, module_id, construction);
        }
    }

    /// Convert a Move type to TheoremType
    pub fn convert_type(&mut self, ty: &move_model::ty::Type) -> TheoremType {
        use move_model::ty::{Type, PrimitiveType};

        match ty {
            Type::Primitive(PrimitiveType::Bool) => TheoremType::Bool,
            Type::Primitive(PrimitiveType::U8) => TheoremType::UInt(8),
            Type::Primitive(PrimitiveType::U16) => TheoremType::UInt(16),
            Type::Primitive(PrimitiveType::U32) => TheoremType::UInt(32),
            Type::Primitive(PrimitiveType::U64) => TheoremType::UInt(64),
            Type::Primitive(PrimitiveType::U128) => TheoremType::UInt(128),
            Type::Primitive(PrimitiveType::U256) => TheoremType::UInt(256),
            Type::Primitive(PrimitiveType::Address) => TheoremType::Address,
            Type::Primitive(PrimitiveType::Signer) => TheoremType::Address,
            Type::Datatype(module_id, struct_id, type_args) => {
                let qualified_id = module_id.qualified(*struct_id);
                let theorem_struct_id = self.get_or_reserve_struct_id(qualified_id);
                let resolved_type_args: Vec<TheoremType> = type_args.iter()
                    .map(|arg| self.convert_type(arg))
                    .collect();

                TheoremType::Struct {
                    struct_id: theorem_struct_id,
                    type_args: resolved_type_args,
                }
            }
            Type::Vector(elem_ty) => {
                TheoremType::Vector(Box::new(self.convert_type(elem_ty)))
            }
            Type::Reference(_, ty) => {
                TheoremType::Reference(Box::new(self.convert_type(ty)))
            }
            Type::TypeParameter(idx) => TheoremType::TypeParameter(*idx),
            Type::Tuple(tys) => {
                TheoremType::Tuple(tys.iter().map(|t| self.convert_type(t)).collect())
            }
            _ => unreachable!("Unsupported type in convert_type: {:?}", ty),
        }
    }

    /// Build function signature from FunctionEnv
    fn build_signature(&mut self, func_env: &FunctionEnv) -> FunctionSignature {
        let type_params = self.sanitize_type_params(&func_env.get_type_parameters());
        let parameters = self.build_parameters(func_env);
        let return_types = self.build_return_types(func_env);

        FunctionSignature {
            type_params,
            parameters,
            return_types,
        }
    }

    /// Sanitize type parameters (remove $ prefix for Lean compatibility)
    fn sanitize_type_params(&self, type_params: &[move_model::model::TypeParameter]) -> Vec<String> {
        type_params
            .iter()
            .map(|tp| {
                let name = tp.0.display(self.env.symbol_pool()).to_string();
                name.trim_start_matches('$').to_string()
            })
            .collect()
    }

    /// Build function parameters with SSA values
    fn build_parameters(&mut self, func_env: &FunctionEnv) -> Vec<Parameter> {
        func_env
            .get_parameters()
            .iter()
            .enumerate()
            .map(|(idx, param)| {
                let param_type = self.convert_type(&param.1);
                let param_name = param.0.display(self.env.symbol_pool()).to_string();
                let sanitized_name = if param_name == "_" {
                    format!("param{}", idx)
                } else {
                    param_name
                };
                Parameter {
                    name: sanitized_name,
                    param_type,
                    ssa_value: idx as u32,
                }
            })
            .collect()
    }

    /// Build return types wrapped in Except monad
    fn build_return_types(&mut self, func_env: &FunctionEnv) -> Vec<TheoremType> {
        let return_types: Vec<TheoremType> = func_env
            .get_return_types()
            .iter()
            .map(|ty| self.convert_type(ty))
            .collect();

        let return_type = match return_types.len() {
            0 => TheoremType::Tuple(vec![]),
            1 => return_types[0].clone(),
            _ => TheoremType::Tuple(return_types),
        };

        vec![return_type.wrap_in_monad()]
    }

    /// Register struct name in name manager
    fn register_struct_name(&mut self, module_env: &ModuleEnv, struct_id: TheoremStructID, name: &str) {
        let module_name = TheoremType::sanitize_name(
            &module_env
                .get_name()
                .display(self.env.symbol_pool())
                .to_string(),
        );
        self.builder.name_manager_mut().register_struct(
            struct_id,
            StructNames {
                type_name: TheoremType::sanitize_name(name),
                module_name,
            },
        );
    }
}
