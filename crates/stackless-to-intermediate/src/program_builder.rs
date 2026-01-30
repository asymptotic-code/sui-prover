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
use std::rc::Rc;

pub struct ProgramBuilder<'env> {
    env: &'env GlobalEnv,
    pub program: Program,
}

impl<'env> ProgramBuilder<'env> {
    pub fn new(env: &'env GlobalEnv) -> Self {
        Self {
            env,
            program: Program::default(),
        }
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

    pub fn build(mut self, targets: &'env FunctionTargetsHolder) -> Program {
        // Only create modules and functions - structs are created on-demand
        // when referenced by function signatures or bodies via struct_id()
        for module_env in self.env.get_modules() {
            self.create_module(&module_env);

            for func_env in module_env.get_functions() {
                if let Some(target) = targets.get_target_opt(&func_env, &FunctionVariant::Baseline)
                {
                    self.create_function(target);
                }
            }
        }

        self.program.finalize();
        self.program
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
