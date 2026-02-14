// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

//! This module translates the bytecode of a module to Boogie code.

use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    iter,
    str::FromStr,
};

use bimap::btree::BiBTreeMap;
use codespan::LineIndex;
use itertools::Itertools;
#[allow(unused_imports)]
use log::{debug, info, log, warn, Level};

use move_compiler::interface_generator::NATIVE_INTERFACE;
use move_core_types::language_storage::StructTag;
use move_model::{
    ast::Attribute,
    code_writer::CodeWriter,
    emit, emitln,
    model::{
        DatatypeId, EnclosingEnv, EnumEnv, FieldId, FunId, FunctionEnv, GlobalEnv, Loc, ModuleId,
        NodeId, QualifiedId, QualifiedInstId, RefType, StructEnv, StructOrEnumEnv, VariantEnv,
    },
    pragmas::ADDITION_OVERFLOW_UNCHECKED_PRAGMA,
    ty::{PrimitiveType, Type, TypeDisplayContext, BOOL_TYPE},
};
use move_stackless_bytecode::{
    ast::{TempIndex, TraceKind},
    control_flow_reconstruction::{self, StructuredBlock},
    deterministic_analysis, dynamic_field_analysis,
    function_data_builder::FunctionDataBuilder,
    function_target::FunctionTarget,
    function_target_pipeline::{
        FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant, VerificationFlavor,
    },
    livevar_analysis::LiveVarAnalysisProcessor,
    mono_analysis::{self, MonoInfo},
    no_abort_analysis,
    number_operation::{
        FuncOperationMap, GlobalNumberOperationState,
        NumOperation::{self, Bitwise, Bottom},
    },
    pure_function_analysis::PureFunctionAnalysisProcessor,
    reaching_def_analysis::ReachingDefProcessor,
    spec_global_variable_analysis::{self},
    stackless_bytecode::{
        AbortAction, BorrowEdge, BorrowNode, Bytecode, Constant, HavocKind, IndexEdgeKind,
        Operation, PropKind, QuantifierHelperType, QuantifierType,
    },
    verification_analysis,
};

use crate::boogie_backend::{
    boogie_helpers::{
        boogie_address_blob, boogie_bv_type, boogie_byte_blob, boogie_constant_blob,
        boogie_debug_track_abort, boogie_debug_track_local, boogie_debug_track_return,
        boogie_declare_global, boogie_dynamic_field_sel, boogie_dynamic_field_update,
        boogie_enum_field_name, boogie_enum_field_update, boogie_enum_name,
        boogie_enum_variant_ctor_name, boogie_equality_for_type, boogie_field_sel,
        boogie_field_update, boogie_function_bv_name, boogie_function_name, boogie_inst_suffix,
        boogie_make_vec_from_strings, boogie_modifies_memory_name, boogie_num_literal,
        boogie_num_type_base, boogie_num_type_string_capital, boogie_resource_memory_name,
        boogie_spec_global_var_name, boogie_struct_name, boogie_temp, boogie_temp_from_suffix,
        boogie_type, boogie_type_param, boogie_type_suffix, boogie_type_suffix_bv,
        boogie_type_suffix_for_struct, boogie_well_formed_check, boogie_well_formed_expr_bv,
        FunctionTranslationStyle, TypeIdentToken,
    },
    options::BoogieOptions,
    spec_translator::SpecTranslator,
};

use super::boogie_helpers::boogie_enum_field_sel;

pub struct BoogieTranslator<'env> {
    env: &'env GlobalEnv,
    options: &'env BoogieOptions,
    writer: &'env CodeWriter,
    spec_translator: SpecTranslator<'env>,
    targets: &'env FunctionTargetsHolder,
    types: &'env RefCell<BiBTreeMap<Type, String>>,
    asserts_mode: AssertsMode,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AssertsMode {
    Check,
    Assume,
    SpecNoAbortCheck,
}

pub struct FunctionTranslator<'env> {
    parent: &'env BoogieTranslator<'env>,
    fun_target: &'env FunctionTarget<'env>,
    type_inst: &'env [Type],
    style: FunctionTranslationStyle,
}

pub struct StructTranslator<'env> {
    parent: &'env BoogieTranslator<'env>,
    struct_env: &'env StructEnv<'env>,
    type_inst: &'env [Type],
    is_opaque: bool,
}

pub struct EnumTranslator<'env> {
    parent: &'env BoogieTranslator<'env>,
    enum_env: &'env EnumEnv<'env>,
    type_inst: &'env [Type],
    is_opaque: bool,
}

impl<'env> BoogieTranslator<'env> {
    pub fn new(
        env: &'env GlobalEnv,
        options: &'env BoogieOptions,
        targets: &'env FunctionTargetsHolder,
        writer: &'env CodeWriter,
        types: &'env RefCell<BiBTreeMap<Type, String>>,
        asserts_mode: AssertsMode,
    ) -> Self {
        Self {
            env,
            options,
            targets,
            writer,
            types,
            spec_translator: SpecTranslator::new(writer, env, options),
            asserts_mode,
        }
    }

    pub fn get_quantifier_helper_name(
        &self,
        qt: QuantifierHelperType,
        function_name: &str,
    ) -> String {
        match qt {
            QuantifierHelperType::Map => format!("$MapQuantifierHelper_{}", function_name),
            QuantifierHelperType::RangeMap => {
                format!("$RangeMapQuantifierHelper_{}", function_name)
            }

            QuantifierHelperType::FindIndex => {
                format!("$FindIndexQuantifierHelper_{}", function_name)
            }

            QuantifierHelperType::FindIndices => {
                format!("$FindIndicesQuantifierHelper_{}", function_name)
            }

            QuantifierHelperType::Filter => format!("$FilterQuantifierHelper_{}", function_name),
        }
    }

    fn generate_axiom_function(&mut self, func_env: &FunctionEnv) {
        let func_name = boogie_function_name(func_env, &[], FunctionTranslationStyle::Pure);

        let params = func_env
            .get_parameter_types()
            .iter()
            .enumerate()
            .map(|(idx, ty)| {
                format!(
                    "$t{}: {}",
                    idx.to_string(),
                    boogie_type(self.env, ty.skip_reference())
                )
            })
            .join(", ");

        let args = (0..func_env.get_parameter_count())
            .map(|val| format!("$t{}", val.to_string()))
            .join(", ");

        emitln!(
            self.writer,
            "// axiom function for {} {}",
            func_env.get_full_name_str(),
            func_env.get_loc().display(self.env)
        );

        let conditions = func_env
            .get_parameter_types()
            .iter()
            .enumerate()
            .map(|(idx, ty)| {
                format!(
                    "$IsValid'{}'($t{})",
                    boogie_type_suffix(self.env, ty.skip_reference()),
                    idx.to_string(),
                )
            })
            .join(" && ");

        emitln!(
            self.writer,
            "axiom (forall {} :: {} ==> {}({}));",
            params,
            conditions,
            func_name,
            args
        );
        emitln!(self.writer);
    }

    /// Emit a bodyless `function $name$pure(params) returns (rets);` for a native
    /// uninterpreted function that has no FunctionTarget data.
    fn emit_uninterpreted_native_pure(&self, fun_env: &FunctionEnv) {
        let func_name = boogie_function_name(fun_env, &[], FunctionTranslationStyle::Pure);

        let params = fun_env
            .get_parameter_types()
            .iter()
            .enumerate()
            .map(|(idx, ty)| format!("$t{}: {}", idx, boogie_type(self.env, ty.skip_reference())))
            .join(", ");

        let rets = fun_env
            .get_return_types()
            .iter()
            .enumerate()
            .map(|(idx, ty)| {
                format!(
                    "$ret{}: {}",
                    idx,
                    boogie_type(self.env, ty.skip_reference())
                )
            })
            .join(", ");

        emitln!(
            self.writer,
            "function {}({}) returns ({});",
            func_name,
            params,
            rets,
        );
        emitln!(self.writer);
    }

    // Generate object::borrow_uid function
    fn translate_object_borrow_uid(&self, suffix: &str, obj_name: &str) {
        emitln!(
            self.writer,
            "function {{:inline}} $2_object_borrow_uid'{}'(obj: {}): $2_object_UID {{",
            suffix,
            obj_name,
        );
        self.writer.indent();
        emitln!(self.writer, "obj->$id");
        self.writer.unindent();
        emitln!(self.writer, "}");
    }

    pub fn translate(&mut self) {
        let writer = self.writer;
        let env = self.env;

        let mono_info = mono_analysis::get_info(self.env);
        let empty = &BTreeSet::new();

        emitln!(
            writer,
            "\n\n//==================================\n// Begin Translation\n"
        );

        // Add type reflection axioms
        if !mono_info.type_params.is_empty() {
            emitln!(writer, "function $TypeName(t: $TypeParamInfo): Vec int;");

            // type name <-> type info: primitives
            for name in [
                "Bool", "U8", "U16", "U32", "U64", "U128", "U256", "Address", "Signer",
            ]
            .into_iter()
            {
                emitln!(
                    writer,
                    "axiom (forall t: $TypeParamInfo :: {{$TypeName(t)}} \
                            t is $TypeParam{} ==> $IsEqual'vec'u8''($TypeName(t), {}));",
                    name,
                    TypeIdentToken::convert_to_bytes(TypeIdentToken::make(&name.to_lowercase()))
                );
                emitln!(
                    writer,
                    "axiom (forall t: $TypeParamInfo :: {{$TypeName(t)}} \
                            $IsEqual'vec'u8''($TypeName(t), {}) ==> t is $TypeParam{});",
                    TypeIdentToken::convert_to_bytes(TypeIdentToken::make(&name.to_lowercase())),
                    name,
                );
            }

            // type name <-> type info: vector
            let mut tokens = TypeIdentToken::make("vector<");
            tokens.push(TypeIdentToken::Variable("$TypeName(t->e)".to_string()));
            tokens.extend(TypeIdentToken::make(">"));
            emitln!(
                writer,
                "axiom (forall t: $TypeParamInfo :: {{$TypeName(t)}} \
                            t is $TypeParamVector ==> $IsEqual'vec'u8''($TypeName(t), {}));",
                TypeIdentToken::convert_to_bytes(tokens)
            );
            // TODO(mengxu): this will parse it to an uninterpreted vector element type
            emitln!(
                writer,
                "axiom (forall t: $TypeParamInfo :: {{$TypeName(t)}} \
                            ($IsPrefix'vec'u8''($TypeName(t), {}) && $IsSuffix'vec'u8''($TypeName(t), {})) ==> t is $TypeParamVector);",
                TypeIdentToken::convert_to_bytes(TypeIdentToken::make("vector<")),
                TypeIdentToken::convert_to_bytes(TypeIdentToken::make(">")),
            );

            // type name <-> type info: struct
            let mut tokens = TypeIdentToken::make("0x");
            // TODO(mengxu): this is not a correct radix16 encoding of an integer
            tokens.push(TypeIdentToken::Variable("MakeVec1(t->a)".to_string()));
            tokens.extend(TypeIdentToken::make("::"));
            tokens.push(TypeIdentToken::Variable("t->m".to_string()));
            tokens.extend(TypeIdentToken::make("::"));
            tokens.push(TypeIdentToken::Variable("t->s".to_string()));
            emitln!(
                writer,
                "axiom (forall t: $TypeParamInfo :: {{$TypeName(t)}} \
                            t is $TypeParamStruct ==> $IsEqual'vec'u8''($TypeName(t), {}));",
                TypeIdentToken::convert_to_bytes(tokens)
            );
            // TODO(mengxu): this will parse it to an uninterpreted struct
            emitln!(
                writer,
                "axiom (forall t: $TypeParamInfo :: {{$TypeName(t)}} \
                            $IsPrefix'vec'u8''($TypeName(t), {}) ==> t is $TypeParamVector);",
                TypeIdentToken::convert_to_bytes(TypeIdentToken::make("0x")),
            );
        }

        // Add given type declarations for type parameters.
        emitln!(writer, "\n\n// Given Types for Type Parameters\n");
        for idx in &mono_info.type_params {
            let param_type = boogie_type_param(env, *idx);
            let suffix = boogie_type_suffix(env, &Type::TypeParameter(*idx));
            let is_uid = self
                .env
                .find_datatype_by_tag(&StructTag::from_str("0x2::object::UID").unwrap())
                .and_then(|uid_qid| mono_info.structs.get(&uid_qid))
                .is_some();
            if is_uid {
                // Sui-specific to allow "using" unresolved type params as Sui objects in Boogie
                // (otherwise Boogie compilation errors may occur)
                emitln!(writer, "datatype {} {{", param_type);
                emitln!(writer, "    {}($id: $2_object_UID)", param_type);
                emitln!(writer, "}");

                self.translate_object_borrow_uid(&suffix, &param_type);
            } else {
                emitln!(writer, "type {};", param_type);
            }
            emitln!(
                writer,
                "function {{:inline}} $IsEqual'{}'(x1: {}, x2: {}): bool {{ x1 == x2 }}",
                suffix,
                param_type,
                param_type
            );
            emitln!(
                writer,
                "function {{:inline}} $IsValid'{}'(x: {}): bool {{ true }}",
                suffix,
                param_type,
            );
            emitln!(
                writer,
                "procedure {{:inline 1}} $0_prover_type_inv'{}'(x: {}) returns (res: bool) {{ res := true; }}",
                suffix,
                param_type,
            );

            // declare free variables to represent the type info for this type
            emitln!(writer, "var {}_info: $TypeParamInfo;", param_type);
        }
        emitln!(writer);

        self.translate_ghost_global(&mono_info);

        let intrinsic_fun_ids = self.env.intrinsic_fun_ids();

        let mut translated_types = BTreeSet::new();
        let mut verified_functions_count = 0;
        info!(
            "generating verification conditions for {:?} module(s)",
            self.env.get_module_count()
        );
        for module_env in self.env.get_modules() {
            self.writer.set_location(&module_env.env.internal_loc());

            for ref struct_env in module_env.get_structs() {
                if struct_env.is_native() {
                    continue;
                }
                for type_inst in mono_info
                    .structs
                    .get(&struct_env.get_qualified_id())
                    .unwrap_or(empty)
                {
                    let struct_name = boogie_struct_name(struct_env, type_inst);
                    if !translated_types.insert(struct_name) {
                        continue;
                    }
                    StructTranslator {
                        parent: self,
                        struct_env,
                        type_inst: type_inst.as_slice(),
                        is_opaque: !mono_info.is_used_datatype(
                            self.env,
                            self.targets,
                            &struct_env.get_qualified_id(),
                        ),
                    }
                    .translate();
                }
            }

            for ref enum_env in module_env.get_enums() {
                for type_inst in mono_info
                    .structs
                    .get(&enum_env.get_qualified_id())
                    .unwrap_or(empty)
                {
                    let enum_name = boogie_enum_name(enum_env, type_inst);
                    if !translated_types.insert(enum_name) {
                        continue;
                    }
                    EnumTranslator {
                        parent: self,
                        enum_env,
                        type_inst: type_inst.as_slice(),
                        is_opaque: !mono_info.is_used_datatype(
                            self.env,
                            self.targets,
                            &enum_env.get_qualified_id(),
                        ),
                    }
                    .translate();
                }
            }

            for ref fun_env in module_env.get_functions() {
                if fun_env.is_native() || intrinsic_fun_ids.contains(&fun_env.get_qualified_id()) {
                    if self.targets.is_uninterpreted(&fun_env.get_qualified_id()) {
                        self.emit_uninterpreted_native_pure(fun_env);
                    }
                    continue;
                }

                self.translate_function_style(fun_env, FunctionTranslationStyle::Pure);

                if self.targets.is_axiom_fun(&fun_env.get_qualified_id()) {
                    self.generate_axiom_function(fun_env);
                    continue;
                }

                if self.options.func_abort_check_only
                    && self
                        .targets
                        .should_generate_abort_check(&fun_env.get_qualified_id())
                {
                    self.translate_function_no_abort(fun_env);
                    self.translate_function_style(fun_env, FunctionTranslationStyle::Opaque);
                    continue;
                }

                if self.options.func_abort_check_only
                    && self.targets.is_spec(&fun_env.get_qualified_id())
                {
                    self.translate_function_style(fun_env, FunctionTranslationStyle::Opaque);
                    continue;
                }

                if !self.options.func_abort_check_only
                    && self.targets.is_spec(&fun_env.get_qualified_id())
                {
                    self.translate_spec(&fun_env);
                    verified_functions_count += 1;
                    continue;
                }

                // Skip functions that were removed by verification analysis
                let fun_target = match self
                    .targets
                    .get_target_opt(fun_env, &FunctionVariant::Baseline)
                {
                    Some(target) => target,
                    None => continue, // Function was filtered out
                };

                if !verification_analysis::get_info(&fun_target).inlined {
                    continue;
                }

                match self.targets.get_spec_by_fun(&fun_env.get_qualified_id()) {
                    Some(spec_qid) if !self.targets.omits_opaque(spec_qid) => {
                        if self.targets.is_verified_spec(spec_qid) {
                            FunctionTranslator::new(
                                self,
                                &fun_target,
                                &[],
                                FunctionTranslationStyle::Default,
                            )
                            .translate();
                        }
                    }
                    _ => {
                        // This variant is inlined, so translate for all type instantiations.
                        for type_inst in mono_info
                            .funs
                            .get(&(
                                fun_target.func_env.get_qualified_id(),
                                FunctionVariant::Baseline,
                            ))
                            .unwrap_or(&BTreeSet::new())
                        {
                            FunctionTranslator::new(
                                self,
                                &fun_target,
                                type_inst,
                                FunctionTranslationStyle::Default,
                            )
                            .translate();
                        }
                    }
                }
            }

            for ref struct_env in module_env.get_structs() {
                if struct_env.is_native() {
                    continue;
                }
                if let Some(inv_fun_id) = self
                    .targets
                    .get_inv_by_datatype(&struct_env.get_qualified_id())
                {
                    let inv_fun_env = self.env.get_function(*inv_fun_id);
                    let inv_fun_target = self
                        .targets
                        .get_target_opt(&inv_fun_env, &FunctionVariant::Baseline)
                        .expect("Invariant function was filtered out: could not find baseline target for invariant function");
                    let struct_type_instances = mono_info
                        .structs
                        .get(&struct_env.get_qualified_id())
                        .unwrap_or(empty);
                    let inv_fun_type_instances = mono_info
                        .funs
                        .get(&(inv_fun_env.get_qualified_id(), FunctionVariant::Baseline))
                        .unwrap_or(empty);
                    for type_inst in struct_type_instances.difference(inv_fun_type_instances) {
                        FunctionTranslator::new(
                            self,
                            &inv_fun_target,
                            type_inst,
                            FunctionTranslationStyle::Default,
                        )
                        .translate();
                    }
                }
            }
        }
        // Emit any finalization items required by spec translation.
        self.spec_translator.finalize();
        info!("{} verification conditions", verified_functions_count);
    }

    fn translate_spec(&self, fun_env: &FunctionEnv<'env>) {
        if self.options.spec_no_abort_check_only {
            if !self.targets.is_scenario_spec(&fun_env.get_qualified_id()) {
                self.translate_function_style(fun_env, FunctionTranslationStyle::Opaque);
                self.translate_function_style(fun_env, FunctionTranslationStyle::Aborts);
            }
            if !self.targets.is_verified_spec(&fun_env.get_qualified_id()) {
                self.translate_function_style(fun_env, FunctionTranslationStyle::SpecNoAbortCheck);
            }
            return;
        }

        if self
            .targets
            .scenario_specs()
            .contains(&fun_env.get_qualified_id())
        {
            if self.targets.is_verified_spec(&fun_env.get_qualified_id())
                && self.targets.has_target(
                    fun_env,
                    &FunctionVariant::Verification(VerificationFlavor::Regular),
                )
            {
                let fun_target = self.targets.get_target(
                    fun_env,
                    &FunctionVariant::Verification(VerificationFlavor::Regular),
                );
                let do_verify = match self.asserts_mode {
                    AssertsMode::Check | AssertsMode::SpecNoAbortCheck => !self
                        .targets
                        .ignore_aborts()
                        .contains(&fun_env.get_qualified_id()),
                    AssertsMode::Assume => self
                        .targets
                        .ignore_aborts()
                        .contains(&fun_env.get_qualified_id()),
                };
                if do_verify {
                    FunctionTranslator::new(
                        self,
                        &fun_target,
                        &[],
                        FunctionTranslationStyle::Default,
                    )
                    .translate();
                }
                self.translate_function_style(fun_env, FunctionTranslationStyle::Asserts);
                self.translate_function_style(fun_env, FunctionTranslationStyle::Aborts);
            }
            return;
        }

        self.translate_function_style(fun_env, FunctionTranslationStyle::Aborts);
        self.translate_function_style(fun_env, FunctionTranslationStyle::Opaque);

        if self.targets.is_verified_spec(&fun_env.get_qualified_id()) {
            self.translate_function_style(fun_env, FunctionTranslationStyle::Default);
            self.translate_function_style(fun_env, FunctionTranslationStyle::Asserts);
            self.translate_function_style(fun_env, FunctionTranslationStyle::SpecNoAbortCheck);
        }
    }

    fn translate_function_style(&self, fun_env: &FunctionEnv, style: FunctionTranslationStyle) {
        use Bytecode::*;

        match self.asserts_mode {
            AssertsMode::Check => {
                if style == FunctionTranslationStyle::SpecNoAbortCheck {
                    return;
                }
                if style.is_asserts_style() {
                    return;
                }
                if FunctionTranslationStyle::Default == style
                    && self.targets.is_verified_spec(&fun_env.get_qualified_id())
                    && self
                        .targets
                        .ignore_aborts()
                        .contains(&fun_env.get_qualified_id())
                {
                    return;
                }
            }
            AssertsMode::Assume => {
                if style == FunctionTranslationStyle::SpecNoAbortCheck {
                    return;
                }
                if FunctionTranslationStyle::Default == style
                    && self.targets.is_verified_spec(&fun_env.get_qualified_id())
                    && !self
                        .targets
                        .ignore_aborts()
                        .contains(&fun_env.get_qualified_id())
                    && !fun_env
                        .get_called_functions()
                        .iter()
                        .any(|f| *f == self.env.asserts_qid())
                {
                    return;
                }
                if style.is_asserts_style()
                    && !fun_env
                        .get_called_functions()
                        .iter()
                        .any(|f| *f == self.env.asserts_qid())
                {
                    return;
                }
            }
            AssertsMode::SpecNoAbortCheck => {
                if FunctionTranslationStyle::Default == style
                    && self.targets.is_verified_spec(&fun_env.get_qualified_id())
                {
                    return;
                }
                if style.is_asserts_style() {
                    return;
                }
            }
        }

        if style == FunctionTranslationStyle::Default
            && (self
                .get_verification_target_fun_env(&fun_env.get_qualified_id())
                .unwrap()
                .is_native()
                || self
                    .targets
                    .no_verify_specs()
                    .contains(&fun_env.get_qualified_id()))
        {
            return;
        }

        let requires_function =
            Operation::apply_fun_qid(&fun_env.module_env.env.requires_qid(), vec![]);
        let ensures_function =
            Operation::apply_fun_qid(&fun_env.module_env.env.ensures_qid(), vec![]);
        let asserts_function =
            Operation::apply_fun_qid(&fun_env.module_env.env.asserts_qid(), vec![]);
        let ensures_requires_swap_subst = BTreeMap::from_iter(vec![
            (requires_function.clone(), ensures_function.clone()),
            (ensures_function.clone(), requires_function.clone()),
        ]);
        let asserts_to_requires_subst =
            BTreeMap::from_iter(vec![(asserts_function.clone(), requires_function.clone())]);
        let asserts_to_ensures_subst =
            BTreeMap::from_iter(vec![(asserts_function.clone(), ensures_function.clone())]);
        let ensures_asserts_to_requires_subst = BTreeMap::from_iter(vec![
            (ensures_function.clone(), requires_function.clone()),
            (asserts_function.clone(), requires_function.clone()),
        ]);

        let variant = match style {
            FunctionTranslationStyle::Default | FunctionTranslationStyle::SpecNoAbortCheck => {
                FunctionVariant::Verification(VerificationFlavor::Regular)
            }
            FunctionTranslationStyle::Asserts
            | FunctionTranslationStyle::Aborts
            | FunctionTranslationStyle::Opaque
            | FunctionTranslationStyle::Pure => FunctionVariant::Baseline,
        };
        if !self.targets.has_target(fun_env, &variant) {
            return;
        }
        let spec_fun_target = self.targets.get_target(fun_env, &variant);

        if !variant.is_verified() && !verification_analysis::get_info(&spec_fun_target).inlined {
            return;
        }

        let mut builder =
            FunctionDataBuilder::new(spec_fun_target.func_env, spec_fun_target.data.clone());
        let code = std::mem::take(&mut builder.data.code);

        let da = deterministic_analysis::get_info(&builder.data);
        let skip_havok = da.is_deterministic && style == FunctionTranslationStyle::Opaque;

        for bc in code.into_iter() {
            match style {
                FunctionTranslationStyle::Default => match bc {
                    Call(_, _, ref op, _, _) if *op == asserts_function => {
                        if self.asserts_mode == AssertsMode::Check {
                            builder.emit(
                                bc.substitute_operations(&asserts_to_requires_subst)
                                    .update_abort_action(|_| None),
                            )
                        }
                    }
                    // skip ensures checks in assume mode if the function does not ignore aborts
                    Call(_, _, ref op, _, _) if *op == ensures_function => {
                        if self.asserts_mode == AssertsMode::Assume
                            && !self
                                .targets
                                .ignore_aborts()
                                .contains(&spec_fun_target.func_env.get_qualified_id())
                        {
                        } else {
                            builder.emit(bc.update_abort_action(|_| None));
                        }
                    }
                    Call(_, _, Operation::Function(module_id, fun_id, ref inst), _, _)
                        if self
                            .targets
                            .get_fun_by_spec(&spec_fun_target.func_env.get_qualified_id())
                            == Some(&QualifiedId {
                                module_id,
                                id: fun_id,
                            }) =>
                    {
                        // Check if this call will use $pure
                        if self.targets.is_pure_fun(&module_id.qualified(fun_id)) {
                            // No abort checking needed - $pure functions have abort-freedom proven separately
                            builder.emit(bc.update_abort_action(|_| None))
                        } else {
                            // Keep abort action for $impl calls
                            builder.emit(bc)
                        }
                    }
                    _ => builder.emit(bc.update_abort_action(|_| None)),
                },
                FunctionTranslationStyle::Asserts | FunctionTranslationStyle::Aborts => match bc {
                    Call(_, _, op, _, _) if op == requires_function || op == ensures_function => {}
                    Call(_, _, ref op, _, _) if *op == asserts_function => {
                        if style == FunctionTranslationStyle::Asserts {
                            builder.emit(
                                bc.substitute_operations(&asserts_to_ensures_subst)
                                    .update_abort_action(|_| None),
                            )
                        } else {
                            builder.emit(
                                bc.substitute_operations(&asserts_to_requires_subst)
                                    .update_abort_action(|_| None),
                            )
                        }
                    }
                    Call(_, _, op, _, _)
                        if matches!(
                            op,
                            Operation::TraceLocal { .. }
                                | Operation::TraceReturn { .. }
                                | Operation::TraceMessage { .. }
                                | Operation::TraceGhost { .. }
                        ) => {}
                    Call(_, _, Operation::Function(module_id, fun_id, _), _, _)
                        if self
                            .targets
                            .get_fun_by_spec(&spec_fun_target.func_env.get_qualified_id())
                            == Some(&QualifiedId {
                                module_id,
                                id: fun_id,
                            }) => {}
                    Ret(..) => {}
                    _ => builder.emit(bc.update_abort_action(|_| None)),
                },
                FunctionTranslationStyle::SpecNoAbortCheck => match bc {
                    Call(_, ref dests, Operation::Function(module_id, fun_id, _), ref srcs, _)
                        if self
                            .targets
                            .get_fun_by_spec(&spec_fun_target.func_env.get_qualified_id())
                            == Some(&QualifiedId {
                                module_id,
                                id: fun_id,
                            }) =>
                    {
                        let dests_clone = dests.clone();
                        let srcs_clone = srcs.clone();
                        builder.emit(
                            if self
                                .targets
                                .omits_opaque(&spec_fun_target.func_env.get_qualified_id())
                            {
                                bc
                            } else {
                                bc.update_abort_action(|_| None)
                            },
                        );
                        if !self
                            .targets
                            .omits_opaque(&spec_fun_target.func_env.get_qualified_id())
                        {
                            let callee_fun_env = self.env.get_function(module_id.qualified(fun_id));
                            for (ret_idx, temp_idx) in dests_clone.iter().enumerate() {
                                let havoc_kind = if callee_fun_env
                                    .get_return_type(ret_idx)
                                    .is_mutable_reference()
                                {
                                    HavocKind::MutationAll
                                } else {
                                    HavocKind::Value
                                };
                                builder.emit_havoc(*temp_idx, havoc_kind);
                            }
                            for (param_idx, temp_idx) in srcs_clone.iter().enumerate() {
                                if callee_fun_env
                                    .get_local_type(param_idx)
                                    .is_mutable_reference()
                                {
                                    builder.emit_havoc(*temp_idx, HavocKind::MutationValue);
                                };
                            }
                        }
                    }
                    _ => builder.emit(
                        bc.substitute_operations(&ensures_asserts_to_requires_subst)
                            .update_abort_action(|aa| match aa {
                                Some(AbortAction::Check) => Some(AbortAction::Check),
                                None => None,
                            }),
                    ),
                },
                FunctionTranslationStyle::Opaque => match bc {
                    Call(_, _, ref op, _, _) if *op == asserts_function => {
                        if self.asserts_mode == AssertsMode::Check {
                            builder.emit(
                                bc.substitute_operations(&asserts_to_ensures_subst)
                                    .update_abort_action(|_| None),
                            )
                        }
                    }
                    Call(_, ref dests, Operation::Function(module_id, fun_id, _), ref srcs, _)
                        if self
                            .targets
                            .get_fun_by_spec(&spec_fun_target.func_env.get_qualified_id())
                            == Some(&QualifiedId {
                                module_id,
                                id: fun_id,
                            }) =>
                    {
                        let dests_clone = dests.clone();
                        let srcs_clone = srcs.clone();

                        builder.emit(
                            if self
                                .targets
                                .omits_opaque(&spec_fun_target.func_env.get_qualified_id())
                                || !no_abort_analysis::does_not_abort(
                                    self.targets,
                                    &self.env.get_function(module_id.qualified(fun_id)),
                                    None,
                                )
                            {
                                bc
                            } else {
                                bc.update_abort_action(|_| None)
                            },
                        );
                        if !self
                            .targets
                            .omits_opaque(&spec_fun_target.func_env.get_qualified_id())
                        {
                            let callee_fun_env = self.env.get_function(module_id.qualified(fun_id));
                            for (ret_idx, temp_idx) in dests_clone.iter().enumerate() {
                                let havoc_kind = if callee_fun_env
                                    .get_return_type(ret_idx)
                                    .is_mutable_reference()
                                {
                                    HavocKind::MutationValue
                                } else {
                                    HavocKind::Value
                                };
                                if skip_havok {
                                    builder.emit_well_formed(*temp_idx);
                                } else {
                                    builder.emit_havoc(*temp_idx, havoc_kind);
                                }
                            }
                            for (param_idx, temp_idx) in srcs_clone.iter().enumerate() {
                                if callee_fun_env
                                    .get_local_type(param_idx)
                                    .is_mutable_reference()
                                {
                                    if skip_havok {
                                        builder.emit_well_formed(*temp_idx);
                                    } else {
                                        builder.emit_havoc(*temp_idx, HavocKind::MutationValue);
                                    }
                                };
                            }
                        }
                    }
                    _ => builder.emit(
                        bc.substitute_operations(&ensures_requires_swap_subst)
                            .update_abort_action(|_| None),
                    ),
                },
                FunctionTranslationStyle::Pure => {
                    // workaround: for pure functions, we just remove all casts via replacing with assigns (only in non-bitvector mode)
                    let mut bc = bc.update_abort_action(|_| None);
                    if self.targets.prover_options().bv_int_encoding {
                        // only in non-bitvector mode
                        bc = bc.replace_cast_with_assign();
                    }
                    builder.emit(bc);
                }
            }
        }

        builder = FunctionDataBuilder::new(builder.fun_env, builder.data);
        for bc in std::mem::take(&mut builder.data.code) {
            match bc {
                Call(_, _, Operation::Function(module_id, fun_id, _), _, _)
                    if !self
                        .env
                        .get_function(module_id.qualified(fun_id))
                        .is_native()
                        && !self
                            .env
                            .get_function(module_id.qualified(fun_id))
                            .is_intrinsic()
                        || self
                            .targets
                            .get_spec_by_fun(&module_id.qualified(fun_id))
                            .is_some()
                        || no_abort_analysis::get_info(&builder.data).does_not_abort =>
                {
                    builder.emit(bc.update_abort_action(|_| None));
                }
                _ => builder.emit(bc),
            }
        }

        let mut data = builder.data;
        let mut dummy_targets = self.targets.new_dummy();
        if data.code.len() > 0 {
            let reach_def = ReachingDefProcessor::new();
            data = reach_def.process(&mut dummy_targets, builder.fun_env, data, None);
        }
        if data.code.len() > 0 {
            let live_vars = LiveVarAnalysisProcessor::new_with_options(false, false);
            data = live_vars.process(&mut dummy_targets, builder.fun_env, data, None);
        }

        let fun_target = FunctionTarget::new(builder.fun_env, &data);
        if matches!(style, FunctionTranslationStyle::Pure) {
            if !self
                .targets
                .is_pure_fun(&fun_target.func_env.get_qualified_id())
                && !self
                    .targets
                    .is_axiom_fun(&fun_target.func_env.get_qualified_id())
            {
                return; // Only emit if #[ext(pure)] is present
            }
        }
        match style {
            FunctionTranslationStyle::Default
            | FunctionTranslationStyle::Asserts
            | FunctionTranslationStyle::SpecNoAbortCheck => {
                FunctionTranslator::new(self, &fun_target, &[], style).translate();
            }
            FunctionTranslationStyle::Opaque | FunctionTranslationStyle::Aborts => {
                if self
                    .targets
                    .scenario_specs()
                    .contains(&fun_target.func_env.get_qualified_id())
                {
                    return;
                }

                if self.options.func_abort_check_only
                    && self
                        .targets
                        .should_generate_abort_check(&fun_env.get_qualified_id())
                    && style == FunctionTranslationStyle::Opaque
                {
                    mono_analysis::get_info(self.env)
                        .funs
                        .get(&(
                            fun_target.func_env.get_qualified_id(),
                            FunctionVariant::Baseline,
                        ))
                        .unwrap_or(&BTreeSet::new())
                        .iter()
                        .for_each(|type_inst| {
                            FunctionTranslator::new(self, &fun_target, type_inst, style)
                                .translate();
                        });
                    return;
                }

                let mut type_insts = mono_analysis::get_info(self.env)
                    .funs
                    .get(&(
                        *self
                            .targets
                            .get_fun_by_spec(&fun_target.func_env.get_qualified_id())
                            .unwrap(),
                        FunctionVariant::Baseline,
                    ))
                    .unwrap_or(&BTreeSet::new())
                    .clone();
                if self.options.spec_no_abort_check_only
                    && !self
                        .targets
                        .is_verified_spec(&fun_target.func_env.get_qualified_id())
                {
                    // add the identity type instance, if it's not already in the set
                    type_insts.insert(
                        (0..fun_target.func_env.get_type_parameter_count())
                            .map(|i| Type::TypeParameter(i as u16))
                            .collect(),
                    );
                }
                for type_inst in type_insts {
                    FunctionTranslator::new(self, &fun_target, &type_inst, style).translate();
                }
            }
            FunctionTranslationStyle::Pure => {
                for type_inst in mono_analysis::get_info(self.env)
                    .funs
                    .get(&(
                        fun_target.func_env.get_qualified_id(),
                        FunctionVariant::Baseline,
                    ))
                    .unwrap_or(&BTreeSet::new())
                {
                    FunctionTranslator::new(self, &fun_target, type_inst, style).translate();
                }
            }
        }
    }

    fn translate_function_no_abort(&self, fun_env: &FunctionEnv) {
        let style = FunctionTranslationStyle::SpecNoAbortCheck;
        let variant = FunctionVariant::Verification(VerificationFlavor::Regular);

        let target = self.targets.get_target(fun_env, &variant);

        let mut builder = FunctionDataBuilder::new(target.func_env, target.data.clone());
        let code = std::mem::take(&mut builder.data.code);

        for bc in code.into_iter() {
            match bc {
                _ => builder.emit(bc.update_abort_action(|aa| match aa {
                    Some(AbortAction::Check) => Some(AbortAction::Check),
                    None => None,
                })),
            }
        }

        let mut data = builder.data;
        let reach_def = ReachingDefProcessor::new();
        let live_vars = LiveVarAnalysisProcessor::new_with_options(false, false);
        let mut dummy_targets = self.targets.new_dummy();
        data = reach_def.process(&mut dummy_targets, builder.fun_env, data, None);
        data = live_vars.process(&mut dummy_targets, builder.fun_env, data, None);

        let fun_target = FunctionTarget::new(builder.fun_env, &data);

        FunctionTranslator::new(self, &fun_target, &[], style).translate();
    }

    fn translate_ghost_global(&mut self, mono_info: &std::rc::Rc<MonoInfo>) {
        let ghost_declare_global_type_instances = self
            .targets
            .specs()
            .filter_map(|id| {
                self.targets
                    .get_data(id, &FunctionVariant::Baseline)
                    .map(|data| spec_global_variable_analysis::get_info(data).all_vars())
            })
            .flatten()
            .collect::<BTreeSet<_>>();
        let ghost_declare_global_mut_type_instances = self
            .targets
            .specs()
            .filter_map(|id| {
                self.targets
                    .get_data(id, &FunctionVariant::Baseline)
                    .map(|data| spec_global_variable_analysis::get_info(data).mut_vars())
            })
            .flatten()
            .collect::<BTreeSet<_>>();

        if ghost_declare_global_type_instances.is_empty() {
            return;
        }

        let ghost_global_fun_env = self.env.get_function(self.env.global_qid());
        let ghost_global_fun_target = self
            .targets
            .get_target_opt(&ghost_global_fun_env, &FunctionVariant::Baseline)
            .expect("ghost global function target should exist");

        let ghost_havoc_global_fun_env = self.env.get_function(self.env.havoc_global_qid());
        let ghost_havoc_global_fun_target = self
            .targets
            .get_target_opt(&ghost_havoc_global_fun_env, &FunctionVariant::Baseline)
            .expect("ghost havoc global function target should exist");

        let empty_set = &BTreeSet::new();
        let ghost_global_type_instances = mono_info
            .funs
            .get(&(
                ghost_global_fun_env.get_qualified_id(),
                FunctionVariant::Baseline,
            ))
            .unwrap_or(empty_set);

        assert!(
            ghost_global_type_instances.is_subset(
                &ghost_declare_global_type_instances
                    .iter()
                    .map(|x| (*x).clone())
                    .collect()
            ),
            "missing type instances for function {}",
            ghost_global_fun_env.get_full_name_str(),
        );

        for type_inst in ghost_declare_global_type_instances {
            self.generate_ghost_global_var_declaration(type_inst);
        }

        for type_inst in ghost_global_type_instances {
            FunctionTranslator::new(
                self,
                &ghost_global_fun_target,
                type_inst,
                FunctionTranslationStyle::Default,
            )
            .translate();
        }

        for type_inst in &ghost_declare_global_mut_type_instances {
            FunctionTranslator::new(
                self,
                &ghost_havoc_global_fun_target,
                type_inst,
                FunctionTranslationStyle::Default,
            )
            .translate();
        }
    }

    fn generate_ghost_global_var_declaration(&self, type_inst: &[Type]) {
        emitln!(
            self.writer,
            "{}",
            boogie_declare_global(
                self.env,
                &boogie_spec_global_var_name(self.env, type_inst),
                &type_inst[1],
            ),
        );
    }

    fn add_type(&self, ty: &Type) {
        let val_ty = ty.skip_reference();
        let overwritten = self
            .types
            .borrow_mut()
            .insert(val_ty.clone(), boogie_type_suffix(self.env, val_ty));
        match overwritten {
            bimap::Overwritten::Neither | bimap::Overwritten::Pair { .. } => {}
            _ => panic!("type already exists"),
        }
    }

    fn get_verification_target_fun_env(
        &self,
        spec_fun_qid: &QualifiedId<FunId>,
    ) -> Option<FunctionEnv> {
        self.targets
            .get_fun_by_spec(spec_fun_qid)
            .map(|qid| self.env.get_function(*qid))
    }
}

// =================================================================================================
// Struct Translation

impl<'env> StructTranslator<'env> {
    fn inst(&self, ty: &Type) -> Type {
        ty.instantiate(self.type_inst)
    }

    /// Return whether a field involves bitwise operations
    pub fn field_bv_flag(&self, field_id: &FieldId) -> bool {
        let global_state = &self
            .parent
            .env
            .get_extension::<GlobalNumberOperationState>()
            .expect("global number operation state");
        let operation_map = &global_state.struct_operation_map;
        let mid = self.struct_env.module_env.get_id();
        let sid = self.struct_env.get_id();
        let field_oper = operation_map.get(&(mid, sid)).unwrap().get(field_id);
        matches!(field_oper, Some(&Bitwise))
    }

    /// Return boogie type for a struct
    pub fn boogie_type_for_struct_field(
        &self,
        field_id: &FieldId,
        env: &GlobalEnv,
        ty: &Type,
    ) -> String {
        let bv_flag = self.field_bv_flag(field_id);
        if bv_flag {
            boogie_bv_type(env, ty)
        } else {
            boogie_type(env, ty)
        }
    }

    /// Translates the given struct.
    fn translate(&self) {
        let writer = self.parent.writer;
        let struct_env = self.struct_env;
        let env = struct_env.module_env.env;

        if struct_env.is_native() || (struct_env.is_intrinsic() && !self.is_opaque) {
            return;
        }

        let qid = struct_env
            .get_qualified_id()
            .instantiate(self.type_inst.to_owned());
        emitln!(
            writer,
            "// struct {} {}",
            env.display(&qid),
            struct_env.get_loc().display(env)
        );

        // Set the location to internal as default.
        writer.set_location(&env.internal_loc());

        if self.is_opaque {
            self.translate_opaque();
            return;
        }

        let struct_type = Type::Datatype(
            struct_env.module_env.get_id(),
            struct_env.get_id(),
            self.type_inst.to_owned(),
        );
        let dynamic_field_info = dynamic_field_analysis::get_env_info(self.parent.env);
        let dynamic_field_names_values = dynamic_field_info
            .dynamic_field_names_values(&struct_type)
            .collect_vec();

        // Emit data type
        let struct_name = boogie_struct_name(struct_env, self.type_inst);
        emitln!(writer, "datatype {} {{", struct_name);

        // Emit constructor
        let fields = struct_env.get_fields().map(|field| {
            format!(
                "${}: {}",
                field.get_name().display(env.symbol_pool()),
                self.boogie_type_for_struct_field(
                    &field.get_id(),
                    env,
                    &self.inst(&field.get_type())
                )
            )
        });
        let dynamic_fields = dynamic_field_names_values.iter().map(|(name, value)| {
            format!(
                "{}: (Table int {})",
                boogie_dynamic_field_sel(self.parent.env, name, value),
                boogie_type(env, value),
            )
        });
        let all_fields = fields.chain(dynamic_fields).join(", ");
        emitln!(writer, "    {}({})", struct_name, all_fields);
        emitln!(writer, "}");

        let suffix = boogie_type_suffix_for_struct(struct_env, self.type_inst, false);

        // Emit $UpdateField functions.
        let fields = struct_env.get_fields().collect_vec();
        for (pos, field_env) in fields.iter().enumerate() {
            let field_name = field_env.get_name().display(env.symbol_pool()).to_string();
            self.emit_function(
                &format!(
                    "$Update'{}'_{}(s: {}, x: {}): {}",
                    suffix,
                    field_name,
                    struct_name,
                    self.boogie_type_for_struct_field(
                        &field_env.get_id(),
                        env,
                        &self.inst(&field_env.get_type())
                    ),
                    struct_name
                ),
                || {
                    let args = fields.iter().enumerate().map(|(p, f)| {
                        if p == pos {
                            "x".to_string()
                        } else {
                            format!("s->{}", boogie_field_sel(f, self.type_inst))
                        }
                    });
                    let dynamic_field_args =
                        dynamic_field_names_values.iter().map(|(name, value)| {
                            format!(
                                "s->{}",
                                boogie_dynamic_field_sel(self.parent.env, name, value)
                            )
                        });
                    let all_args = args.chain(dynamic_field_args).join(", ");
                    emitln!(writer, "{}({})", struct_name, all_args);
                },
            );
        }
        for (pos, (name, value)) in dynamic_field_names_values.iter().enumerate() {
            self.emit_function(
                &format!(
                    "{}(s: {}, x: (Table int {})): {}",
                    boogie_dynamic_field_update(struct_env, self.type_inst, name, value),
                    struct_name,
                    boogie_type(env, value),
                    struct_name
                ),
                || {
                    let args = fields
                        .iter()
                        .map(|f| format!("s->{}", boogie_field_sel(f, self.type_inst)));
                    let dynamic_field_args =
                        dynamic_field_names_values
                            .iter()
                            .enumerate()
                            .map(|(p, (n, v))| {
                                if p == pos {
                                    "x".to_string()
                                } else {
                                    format!(
                                        "s->{}",
                                        boogie_dynamic_field_sel(self.parent.env, n, v)
                                    )
                                }
                            });
                    let all_args = args.chain(dynamic_field_args).join(", ");
                    emitln!(writer, "{}({})", struct_name, all_args);
                },
            );
        }

        // Skip for table_vec and option as it's handled by native templates
        let skip_is_valid = self.parent.env.table_vec_qid().unwrap()
            == struct_env.get_qualified_id()
            || self.parent.env.option_qid().unwrap() == struct_env.get_qualified_id();

        // Emit $IsValid function.
        if !skip_is_valid {
            self.emit_function_with_attr(
                "", // not inlined!
                &format!("$IsValid'{}'(s: {}): bool", suffix, struct_name),
                || {
                    if struct_env.is_native() {
                        emitln!(writer, "true")
                    } else {
                        let mut sep = "";
                        for field in struct_env.get_fields() {
                            let sel = format!("s->{}", boogie_field_sel(&field, self.type_inst));
                            let ty = &field.get_type().instantiate(self.type_inst);
                            let bv_flag = self.field_bv_flag(&field.get_id());
                            emitln!(
                                writer,
                                "{}{}",
                                sep,
                                boogie_well_formed_expr_bv(env, &sel, ty, bv_flag)
                            );
                            sep = "  && ";
                        }
                        if let Some(vec_set_qid) = self.parent.env.vec_set_qid() {
                            if struct_env.get_qualified_id() == vec_set_qid {
                                emitln!(
                                    writer,
                                    "{}$DisjointVecSet{}(s->$contents)",
                                    sep,
                                    boogie_inst_suffix(self.parent.env, self.type_inst)
                                );
                            }
                        }
                        if let Some(vec_map_qid) = self.parent.env.vec_map_qid() {
                            if struct_env.get_qualified_id() == vec_map_qid {
                                emitln!(
                                    writer,
                                    "{}$DisjointVecMap{}(s->$contents)",
                                    sep,
                                    boogie_inst_suffix(self.parent.env, self.type_inst)
                                );
                            }
                        }
                    }
                },
            );
        }

        // Emit equality
        self.emit_function(
            &format!(
                "$IsEqual'{}'(s1: {}, s2: {}): bool",
                suffix, struct_name, struct_name
            ),
            || {
                if struct_has_native_equality(struct_env, self.type_inst, self.parent.options) {
                    emitln!(writer, "s1 == s2")
                } else {
                    let mut sep = "";
                    for field in &fields {
                        let sel_fun = boogie_field_sel(field, self.type_inst);
                        let bv_flag = self.field_bv_flag(&field.get_id());
                        let field_suffix =
                            boogie_type_suffix_bv(env, &self.inst(&field.get_type()), bv_flag);
                        emit!(
                            writer,
                            "{}$IsEqual'{}'(s1->{}, s2->{})",
                            sep,
                            field_suffix,
                            sel_fun,
                            sel_fun,
                        );
                        sep = "\n&& ";
                    }
                }
            },
        );

        // emit object::borrow_uid function
        self.translate_object_borrow_uid();

        if struct_env.has_memory() {
            // Emit memory variable.
            let memory_name = boogie_resource_memory_name(
                env,
                &struct_env
                    .get_qualified_id()
                    .instantiate(self.type_inst.to_owned()),
                &None,
            );
            emitln!(writer, "var {}: $Memory {};", memory_name, struct_name);
        }

        emitln!(
            writer,
            "procedure {{:inline 1}} $0_prover_type_inv'{}'(s: {}) returns (res: bool) {{",
            suffix,
            struct_name
        );
        writer.indent();
        if let Some(inv_fun_id) = self
            .parent
            .targets
            .get_inv_by_datatype(&self.struct_env.get_qualified_id())
        {
            emitln!(
                writer,
                "call res := {}(s);",
                boogie_function_name(
                    &self.parent.env.get_function(*inv_fun_id),
                    self.type_inst,
                    FunctionTranslationStyle::Default
                )
            );
        } else {
            emitln!(writer, "res := true;");
        }
        emitln!(writer, "return;");
        writer.unindent();
        emitln!(writer, "}");
        emitln!(writer);
    }

    // Generate object::borrow_uid function for structs with key ability
    fn translate_object_borrow_uid(&self) {
        if !self.struct_env.get_abilities().has_key() {
            return;
        }

        self.parent.translate_object_borrow_uid(
            &boogie_type_suffix(
                self.parent.env,
                &Type::Datatype(
                    self.struct_env.module_env.get_id(),
                    self.struct_env.get_id(),
                    self.type_inst.to_vec(),
                ),
            ),
            &boogie_struct_name(self.struct_env, self.type_inst),
        );
    }

    fn translate_opaque(&self) {
        let struct_name = boogie_struct_name(self.struct_env, self.type_inst);
        let suffix = boogie_type_suffix_for_struct(self.struct_env, self.type_inst, false);

        // Emit data type
        emitln!(self.parent.writer, "datatype {} {{", struct_name);
        self.parent.writer.indent();
        let content = if self.struct_env.get_abilities().has_key() {
            "$id: $2_object_UID"
        } else {
            "$content: int"
        };
        emitln!(self.parent.writer, "{}({})", struct_name, content);
        self.parent.writer.unindent();
        emitln!(self.parent.writer, "}");

        // emit IsValid function
        self.emit_function(
            &format!("$IsValid'{}'(s: {}): bool", suffix, struct_name),
            || {
                if self.struct_env.get_abilities().has_key() {
                    emitln!(self.parent.writer, "$IsValid'$2_object_UID'(s->$id)")
                } else {
                    emitln!(self.parent.writer, "true")
                }
            },
        );

        // emit IsEqual function
        self.emit_function(
            &format!(
                "$IsEqual'{}'(s1: {}, s2: {}): bool",
                suffix, struct_name, struct_name
            ),
            || emitln!(self.parent.writer, "s1 == s2"),
        );

        // emit object::borrow_uid function
        self.translate_object_borrow_uid();

        emitln!(
            self.parent.writer,
            "procedure {{:inline 1}} $0_prover_type_inv'{}'(s: {}) returns (res: bool) {{",
            suffix,
            struct_name
        );
        self.parent.writer.indent();
        emitln!(self.parent.writer, "res := true;");
        emitln!(self.parent.writer, "return;");
        self.parent.writer.unindent();
        emitln!(self.parent.writer, "}");
        emitln!(self.parent.writer);
    }

    fn emit_function(&self, signature: &str, body_fn: impl Fn()) {
        self.emit_function_with_attr("{:inline} ", signature, body_fn)
    }

    fn emit_function_with_attr(&self, attr: &str, signature: &str, body_fn: impl Fn()) {
        let writer = self.parent.writer;
        emitln!(writer, "function {}{} {{", attr, signature);
        writer.indent();
        body_fn();
        writer.unindent();
        emitln!(writer, "}");
    }
}

// =================================================================================================
// Enum Translation

impl<'env> EnumTranslator<'env> {
    fn inst(&self, ty: &Type) -> Type {
        ty.instantiate(self.type_inst)
    }

    /// Return whether a field involves bitwise operations
    pub fn field_bv_flag(&self, field_id: &FieldId) -> bool {
        let global_state = &self
            .parent
            .env
            .get_extension::<GlobalNumberOperationState>()
            .expect("global number operation state");
        let operation_map = &global_state.struct_operation_map;
        let mid = self.enum_env.module_env.get_id();
        let eid = self.enum_env.get_id();
        // let field_oper = operation_map.get(&(mid, eid)).unwrap_or_default().get(field_id);
        // matches!(field_oper, Some(&Bitwise))
        false
    }

    /// Return boogie type for a enum
    pub fn boogie_type_for_enum_field(
        &self,
        field_id: &FieldId,
        env: &GlobalEnv,
        ty: &Type,
    ) -> String {
        let bv_flag = self.field_bv_flag(field_id);
        if bv_flag {
            boogie_bv_type(env, ty)
        } else {
            boogie_type(env, ty)
        }
    }

    /// Translates the given enum.
    fn translate(&self) {
        let writer = self.parent.writer;
        let enum_env = self.enum_env;
        let env = enum_env.module_env.env;

        let qid = enum_env
            .get_qualified_id()
            .instantiate(self.type_inst.to_owned());
        emitln!(
            writer,
            "// enum {} {}",
            env.display(&qid),
            enum_env.get_loc().display(env)
        );

        // Set the location to internal as default.
        writer.set_location(&env.internal_loc());

        if self.is_opaque {
            self.translate_opaque();
            return;
        }

        // Emit data type
        let enum_name = boogie_enum_name(enum_env, self.type_inst);
        emitln!(writer, "datatype {} {{", enum_name);

        // Emit enum as struct
        let fields = enum_env
            .get_variants()
            .flat_map(|variant| {
                variant
                    .get_fields()
                    .map(|field| {
                        format!(
                            "{}: {}",
                            boogie_enum_field_name(&field),
                            self.boogie_type_for_enum_field(
                                &field.get_id(),
                                env,
                                &self.inst(&field.get_type())
                            )
                        )
                    })
                    .collect_vec()
            })
            .chain(vec!["$variant_id: int".to_string()])
            .join(", ");
        emitln!(writer, "    {}({})", enum_name, fields);
        emitln!(writer, "}");

        // Emit constructors
        for variant in enum_env.get_variants() {
            emitln!(
                writer,
                "procedure {{:inline 1}} {}({}) returns (res: {}) {{",
                boogie_enum_variant_ctor_name(&variant, self.type_inst),
                variant
                    .get_fields()
                    .map(|field| {
                        format!(
                            "{}: {}",
                            boogie_enum_field_name(&field),
                            self.boogie_type_for_enum_field(
                                &field.get_id(),
                                env,
                                &self.inst(&field.get_type())
                            )
                        )
                    })
                    .join(", "),
                enum_name
            );
            writer.indent();

            emitln!(writer, "res->$variant_id := {};", variant.get_tag());

            for field in variant.get_fields() {
                let field_name = boogie_enum_field_name(&field);
                emitln!(writer, "res->{} := {};", field_name, field_name);
            }

            emitln!(writer, "return;");
            writer.unindent();
            emitln!(writer, "}");
            emitln!(writer);
        }

        let suffix = boogie_enum_name(enum_env, self.type_inst);

        for (pos, field_env) in enum_env.get_all_fields().enumerate() {
            let field_name = field_env.get_name().display(env.symbol_pool()).to_string();
            let EnclosingEnv::Variant(variant_env) = &field_env.parent_env else {
                unreachable!();
            };
            let variant_name = variant_env
                .get_name()
                .display(env.symbol_pool())
                .to_string();

            // Emit function signature
            self.emit_function(
                &format!(
                    "$Update'{}'_{}_{}(s: {}, x: {}): {}",
                    suffix,
                    variant_name,
                    field_name,
                    enum_name,
                    self.boogie_type_for_enum_field(
                        &field_env.get_id(),
                        env,
                        &self.inst(&field_env.get_type())
                    ),
                    enum_name
                ),
                || {
                    let args = enum_env
                        .get_all_fields()
                        .enumerate()
                        .map(|(p, f)| {
                            if f.get_name() == field_env.get_name()
                                && f.get_id() == field_env.get_id()
                                && pos == p
                            {
                                "x".to_string()
                            } else {
                                format!("s->{}", boogie_enum_field_name(&f))
                            }
                        })
                        .chain(std::iter::once("s->$variant_id".to_string()))
                        .join(", ");

                    emitln!(writer, "{}({})", enum_name, args);
                },
            );
        }

        // Emit $IsValid function.
        self.emit_function_with_attr(
            "", // not inlined!
            &format!("$IsValid'{}'(e: {}): bool", suffix, enum_name),
            || {
                let well_formed_checks = enum_env
                    .get_variants()
                    .flat_map(|variant| {
                        variant
                            .get_fields()
                            .map(|field| {
                                let sel = format!("e->{}", boogie_enum_field_name(&field));
                                let ty = &field.get_type().instantiate(self.type_inst);
                                let bv_flag = self.field_bv_flag(&field.get_id());
                                boogie_well_formed_expr_bv(env, &sel, ty, bv_flag)
                            })
                            .collect_vec()
                    })
                    .chain(vec![format!(
                        "0 <= e->$variant_id && e->$variant_id < {}",
                        enum_env.get_variants().count()
                    )])
                    .join("\n  && ");
                emitln!(writer, "{}", well_formed_checks);
            },
        );

        // Emit equality
        self.emit_function(
            &format!(
                "$IsEqual'{}'(e1: {}, e2: {}): bool",
                suffix, enum_name, enum_name
            ),
            || {
                let equality_checks = iter::once("e1->$variant_id == e2->$variant_id".to_string())
                    .chain(enum_env.get_variants().map(|variant| {
                        let variant_equality_checks = if variant.get_field_count() == 0 {
                            "true".to_string()
                        } else {
                            variant
                                .get_fields()
                                .map(|field| {
                                    let sel_fun = boogie_enum_field_name(&field);
                                    let bv_flag = self.field_bv_flag(&field.get_id());
                                    let field_suffix = boogie_type_suffix_bv(
                                        env,
                                        &self.inst(&field.get_type()),
                                        bv_flag,
                                    );
                                    format!(
                                        "$IsEqual'{}'(e1->{}, e2->{})",
                                        field_suffix, sel_fun, sel_fun,
                                    )
                                })
                                .join("\n    && ")
                        };
                        format!(
                            "(e1->$variant_id == {} ==> {})",
                            variant.get_tag(),
                            variant_equality_checks,
                        )
                    }))
                    .join("\n  && ");
                emit!(writer, "{}", equality_checks);
            },
        );

        emitln!(
            writer,
            "procedure {{:inline 1}} $0_prover_type_inv'{}'(s: {}) returns (res: bool) {{",
            suffix,
            enum_name
        );
        writer.indent();
        if let Some(inv_fun_id) = self
            .parent
            .targets
            .get_inv_by_datatype(&self.enum_env.get_qualified_id())
        {
            emitln!(
                writer,
                "call res := {}(s);",
                boogie_function_name(
                    &self.parent.env.get_function(*inv_fun_id),
                    self.type_inst,
                    FunctionTranslationStyle::Default
                )
            );
        } else {
            emitln!(writer, "res := true;");
        }
        emitln!(writer, "return;");
        writer.unindent();
        emitln!(writer, "}");

        emitln!(writer);
    }

    fn translate_opaque(&self) {
        let enum_name = boogie_enum_name(self.enum_env, self.type_inst);
        let suffix = boogie_enum_name(self.enum_env, self.type_inst);

        // Emit data type
        emitln!(self.parent.writer, "datatype {} {{", enum_name);
        self.parent.writer.indent();
        emitln!(self.parent.writer, "{}({})", enum_name, "$content: int");
        self.parent.writer.unindent();
        emitln!(self.parent.writer, "}");

        // emit IsValid function
        self.emit_function(
            &format!("$IsValid'{}'(s: {}): bool", suffix, enum_name),
            || emitln!(self.parent.writer, "true"),
        );

        // emit IsEqual function
        self.emit_function(
            &format!(
                "$IsEqual'{}'(s1: {}, s2: {}): bool",
                suffix, enum_name, enum_name
            ),
            || emitln!(self.parent.writer, "s1 == s2"),
        );

        emitln!(
            self.parent.writer,
            "procedure {{:inline 1}} $0_prover_type_inv'{}'(s: {}) returns (res: bool) {{",
            suffix,
            enum_name
        );
        self.parent.writer.indent();
        emitln!(self.parent.writer, "res := true;");
        emitln!(self.parent.writer, "return;");
        self.parent.writer.unindent();
        emitln!(self.parent.writer, "}");
        emitln!(self.parent.writer);
    }

    fn emit_function(&self, signature: &str, body_fn: impl Fn()) {
        self.emit_function_with_attr("{:inline} ", signature, body_fn)
    }

    fn emit_function_with_attr(&self, attr: &str, signature: &str, body_fn: impl Fn()) {
        let writer = self.parent.writer;
        emitln!(writer, "function {}{} {{", attr, signature);
        writer.indent();
        body_fn();
        writer.unindent();
        emitln!(writer, "}");
    }
}

// =================================================================================================
// Function Translation

impl<'env> FunctionTranslator<'env> {
    /// Return whether a specific TempIndex involves in bitwise operations
    pub fn bv_flag_from_map(&self, i: &usize, operation_map: &FuncOperationMap) -> bool {
        let mid = self.fun_target.module_env().get_id();
        let sid = self.fun_target.func_env.get_id();
        let param_oper = operation_map.get(&(mid, sid)).unwrap().get(i);
        matches!(param_oper, Some(&Bitwise))
    }

    pub fn new(
        parent: &'env BoogieTranslator<'env>,
        fun_target: &'env FunctionTarget<'env>,
        type_inst: &'env [Type],
        style: FunctionTranslationStyle,
    ) -> Self {
        Self {
            parent,
            fun_target,
            type_inst,
            style,
        }
    }

    fn ghost_var_name(&self, type_inst: &[Type]) -> String {
        let var_name = boogie_spec_global_var_name(self.parent.env, type_inst);
        format!("$ghost_{}", var_name)
    }

    /// Return whether a specific TempIndex involves in bitwise operations
    pub fn bv_flag(&self, num_oper: &NumOperation) -> bool {
        *num_oper == Bitwise
    }

    /// Return whether a return value at position i involves in bitwise operation
    pub fn ret_bv_flag(&self, i: &usize) -> bool {
        let global_state = &self
            .fun_target
            .global_env()
            .get_extension::<GlobalNumberOperationState>()
            .expect("global number operation state");
        let operation_map = &global_state.get_ret_map();
        self.bv_flag_from_map(i, operation_map)
    }

    /// Return boogie type for a local with given signature token.
    pub fn boogie_type_for_fun(
        &self,
        env: &GlobalEnv,
        ty: &Type,
        num_oper: &NumOperation,
    ) -> String {
        let bv_flag = self.bv_flag(num_oper);
        if bv_flag {
            boogie_bv_type(env, ty)
        } else {
            boogie_type(env, ty)
        }
    }

    fn inst(&self, ty: &Type) -> Type {
        ty.instantiate(self.type_inst)
    }

    fn inst_slice(&self, tys: &[Type]) -> Vec<Type> {
        tys.iter().map(|ty| self.inst(ty)).collect()
    }

    fn get_local_type(&self, idx: TempIndex) -> Type {
        self.fun_target
            .get_local_type(idx)
            .instantiate(self.type_inst)
    }

    /// Translates the given function.
    fn translate(mut self) {
        let writer = self.parent.writer;
        let fun_target = self.fun_target;
        let env = fun_target.global_env();
        let qid = fun_target
            .func_env
            .get_qualified_id()
            .instantiate(self.type_inst.to_owned());
        emitln!(
            writer,
            "// fun {} [{}] {}",
            env.display(&qid),
            fun_target.data.variant,
            fun_target.get_loc().display(env)
        );
        self.generate_function_sig();

        if self.fun_target.func_env.get_qualified_id() == self.parent.env.global_qid() {
            self.generate_ghost_global_body();
        } else if self.fun_target.func_env.get_qualified_id() == self.parent.env.havoc_global_qid()
        {
            self.generate_ghost_havoc_global_body();
        } else {
            self.generate_function_body();
        }
        emitln!(self.parent.writer);
    }

    fn generate_ghost_global_body(&self) {
        assert!(
            self.fun_target.func_env.is_native()
                && self.fun_target.get_type_parameter_count() == 2
                && self.fun_target.get_parameter_count() == 0
                && self.fun_target.get_return_count() == 1
        );
        emitln!(self.writer(), "{");
        self.writer().indent();
        emitln!(
            self.writer(),
            "$ret0 := {};",
            boogie_spec_global_var_name(self.parent.env, self.type_inst),
        );
        self.writer().unindent();
        emitln!(self.writer(), "}");
    }

    fn generate_ghost_havoc_global_body(&self) {
        assert!(
            self.fun_target.func_env.is_native()
                && self.fun_target.get_type_parameter_count() == 2
                && self.fun_target.get_parameter_count() == 0
                && self.fun_target.get_return_count() == 0
        );
        emitln!(self.writer(), "{");
        self.writer().indent();
        emitln!(
            self.writer(),
            "havoc {};",
            boogie_spec_global_var_name(self.parent.env, self.type_inst),
        );
        self.writer().unindent();
        emitln!(self.writer(), "}");
    }

    fn function_variant_name(&self, style: FunctionTranslationStyle) -> String {
        let variant = match style {
            FunctionTranslationStyle::Default => &self.fun_target.data.variant,
            FunctionTranslationStyle::Asserts
            | FunctionTranslationStyle::Aborts
            | FunctionTranslationStyle::Opaque
            | FunctionTranslationStyle::Pure => &FunctionVariant::Baseline,
            FunctionTranslationStyle::SpecNoAbortCheck => {
                &FunctionVariant::Verification(VerificationFlavor::Regular)
            }
        };
        let suffix = match variant {
            FunctionVariant::Baseline => "".to_string(),
            FunctionVariant::Verification(flavor) => match flavor {
                VerificationFlavor::Regular => "$verify".to_string(),
                VerificationFlavor::Instantiated(_) => {
                    format!("$verify_{}", flavor)
                }
                VerificationFlavor::Inconsistency(_) => {
                    format!("$verify_{}", flavor)
                }
            },
        };
        if self
            .parent
            .targets
            .get_spec_by_fun(&self.fun_target.func_env.get_qualified_id())
            .is_some()
            && style == FunctionTranslationStyle::Default
        {
            return format!(
                "{}$impl",
                boogie_function_name(self.fun_target.func_env, self.type_inst, style)
            );
        }
        let fun_name = self
            .parent
            .targets
            .get_fun_by_spec(&self.fun_target.func_env.get_qualified_id())
            .map_or(
                boogie_function_name(self.fun_target.func_env, self.type_inst, style),
                |fun_id| {
                    boogie_function_name(
                        &self.parent.env.get_function(*fun_id),
                        self.type_inst,
                        style,
                    )
                },
            );
        let result = format!("{}{}", fun_name, suffix);

        if self.parent.options.func_abort_check_only
            && style == FunctionTranslationStyle::SpecNoAbortCheck
        {
            result.replace("$spec_no_abort_check", "$no_abort_check")
        } else {
            result
        }
    }

    /// Return a string for a boogie procedure header. Use inline attribute and name
    /// suffix as indicated by `entry_point`.
    fn generate_function_sig(&self) {
        let writer = self.parent.writer;
        let options = self.parent.options;
        let fun_target = self.fun_target;
        let (args, prerets) = self.generate_function_args_and_returns(false);

        let emit_pure_in_place = self.style == FunctionTranslationStyle::Pure;

        let attribs = match &fun_target.data.variant {
            FunctionVariant::Baseline => {
                if emit_pure_in_place
                    && self
                        .parent
                        .targets
                        .is_uninterpreted(&self.fun_target.func_env.get_qualified_id())
                {
                    // Uninterpreted functions have no body, so no inline attribute
                    "".to_string()
                } else if emit_pure_in_place {
                    "{:inline} ".to_string()
                } else {
                    "{:inline 1} ".to_string()
                }
            }
            FunctionVariant::Verification(flavor) => {
                let mut attribs = vec![format!(
                    "{{:timeLimit {}}} ",
                    self.parent
                        .targets
                        .get_spec_timeout(&self.fun_target.func_env.get_qualified_id())
                        .unwrap_or(&(options.vc_timeout as u64)),
                )];
                match flavor {
                    VerificationFlavor::Regular => "".to_string(),
                    VerificationFlavor::Instantiated(_) => "".to_string(),
                    VerificationFlavor::Inconsistency(_) => {
                        attribs.push(format!(
                            "{{:msg_if_verifies \"inconsistency_detected{}\"}} ",
                            self.loc_str(&fun_target.get_loc())
                        ));
                        "".to_string()
                    }
                };
                attribs.join("")
            }
        };

        let rets = match self.style {
            FunctionTranslationStyle::Default
            | FunctionTranslationStyle::Opaque
            | FunctionTranslationStyle::SpecNoAbortCheck
            | FunctionTranslationStyle::Pure => prerets,
            FunctionTranslationStyle::Asserts | FunctionTranslationStyle::Aborts => "".to_string(),
        };

        writer.set_location(&fun_target.get_loc());
        if self.style == FunctionTranslationStyle::Opaque {
            let (args, orets) =
                self.generate_function_args_and_returns(self.should_use_temp_datatypes());
            let prefix = if self.should_use_opaque_as_function(true) {
                "function"
            } else {
                "procedure"
            };
            emitln!(
                writer,
                "{} {}$opaque({}) returns ({});",
                prefix,
                self.function_variant_name(FunctionTranslationStyle::Opaque),
                args,
                orets,
            );
            emitln!(writer, "");
        }

        // For SpecNoAbortCheck style in func_abort_check_only mode, we may need to declare the
        // opaque return datatype if the function returns multiple values (or has mutable references).
        if self.style == FunctionTranslationStyle::SpecNoAbortCheck
            && self.should_use_temp_datatypes()
            && options.func_abort_check_only
        {
            // Trigger datatype declaration by calling generate_function_args_and_returns with true
            let _ = self.generate_function_args_and_returns(true);
        }

        let prefix = if emit_pure_in_place {
            "function"
        } else {
            "procedure"
        };
        emitln!(
            writer,
            "{} {}{}({}) returns ({})",
            prefix,
            attribs,
            self.function_variant_name(self.style),
            args,
            rets,
        )
    }

    fn wrap_return_datatype_name(&self) -> String {
        format!(
            "{}_opaque_return_type",
            self.function_variant_name(FunctionTranslationStyle::Opaque)
        )
    }

    fn wrap_return_arg_in_tuple_datatype(&self, args: String) -> String {
        let writer = self.parent.writer;
        let name = self.wrap_return_datatype_name();
        emitln!(writer, "datatype {} {{", name);
        emitln!(writer, "    {}({})", name, args);
        emitln!(writer, "}\n");
        name
    }

    /// Generate boogie representation of function args and return args.
    fn generate_function_args_and_returns(
        &self,
        generate_custom_datatype: bool,
    ) -> (String, String) {
        let fun_target = self.fun_target;
        let env = fun_target.global_env();
        let baseline_flag = self.fun_target.data.variant == FunctionVariant::Baseline;
        let global_state = &self
            .fun_target
            .global_env()
            .get_extension::<GlobalNumberOperationState>()
            .expect("global number operation state");
        let mid = fun_target.func_env.module_env.get_id();
        let fid = fun_target.func_env.get_id();
        let regular_args = (0..fun_target.get_parameter_count())
            .map(|i| {
                let ty = self.get_local_type(i);
                // Boogie does not allow to assign to parameters, so we need to proxy them.
                let prefix = if self.parameter_needs_to_be_mutable(fun_target, i) {
                    "_$"
                } else {
                    "$"
                };
                let num_oper = global_state
                    .get_temp_index_oper(mid, fid, i, baseline_flag)
                    .unwrap_or(&Bottom);
                format!(
                    "{}t{}: {}",
                    prefix,
                    i,
                    self.boogie_type_for_fun(env, &ty, num_oper)
                )
            })
            .collect::<Vec<_>>();

        let ghost_args = if self.style.is_asserts_style() {
            let ghost_vars = self.get_ghost_vars();
            if !ghost_vars.is_empty() {
                ghost_vars
                    .into_iter()
                    .map(|type_inst| {
                        format!(
                            "{}: {}",
                            self.ghost_var_name(&type_inst),
                            boogie_type(env, &type_inst[1])
                        )
                    })
                    .collect::<Vec<_>>()
            } else {
                Vec::new()
            }
        } else {
            Vec::new()
        };

        let all_args = regular_args
            .into_iter()
            .chain(ghost_args)
            .collect::<Vec<_>>();
        let args = all_args.join(", ");

        let mut_ref_inputs = (0..fun_target.get_parameter_count())
            .enumerate()
            .filter_map(|(i, idx)| {
                let ty = self.get_local_type(idx);
                if ty.is_mutable_reference() {
                    Some((i, ty))
                } else {
                    None
                }
            })
            .collect_vec();
        let rets = fun_target
            .get_return_types()
            .iter()
            .enumerate()
            .map(|(i, s)| {
                let s = self.inst(s);
                let operation_map = global_state.get_ret_map();
                let num_oper = operation_map.get(&(mid, fid)).unwrap().get(&i).unwrap();
                format!("$ret{}: {}", i, self.boogie_type_for_fun(env, &s, num_oper))
            })
            // Add implicit return parameters for &mut
            .chain(mut_ref_inputs.into_iter().enumerate().map(|(i, (_, ty))| {
                let num_oper = &global_state
                    .get_temp_index_oper(mid, fid, i, baseline_flag)
                    .unwrap();
                format!(
                    "$ret{}: {}",
                    usize::saturating_add(fun_target.get_return_count(), i),
                    self.boogie_type_for_fun(env, &ty, num_oper)
                )
            }))
            .join(", ");

        if !generate_custom_datatype {
            return (args, rets);
        }

        let tdt_name = self.wrap_return_arg_in_tuple_datatype(rets);
        let rets = format!("$ret: {}", tdt_name);
        (args, rets)
    }

    /// Generates boogie implementation body.
    fn generate_function_body(&mut self) {
        let writer = self.parent.writer;
        let fun_target = self.fun_target;
        let variant = &fun_target.data.variant;
        let instantiation = &fun_target.data.type_args;
        let env = fun_target.global_env();
        let baseline_flag = self.fun_target.data.variant == FunctionVariant::Baseline;
        let global_state = &self
            .fun_target
            .global_env()
            .get_extension::<GlobalNumberOperationState>()
            .expect("global number operation state");

        let emit_pure_in_place = self.style == FunctionTranslationStyle::Pure;

        // Be sure to set back location to the whole function definition as a default.
        writer.set_location(&fun_target.get_loc().at_start());

        // For pure functions marked as uninterpreted, emit uninterpreted (no body)
        if emit_pure_in_place {
            if self
                .parent
                .targets
                .is_uninterpreted(&self.fun_target.func_env.get_qualified_id())
            {
                emitln!(writer, ";");
                return;
            }
        }

        emitln!(writer, "{");
        writer.indent();

        // Print instantiation information
        if !instantiation.is_empty() {
            let display_ctxt = TypeDisplayContext::WithEnv {
                env,
                type_param_names: None,
            };
            emitln!(
                writer,
                "// function instantiation <{}>",
                instantiation
                    .iter()
                    .map(|ty| ty.display(&display_ctxt))
                    .join(", ")
            );
            emitln!(writer, "");
        }

        // Skip variable declarations and imperative setup for Boogie functions
        if !emit_pure_in_place {
            // Generate local variable declarations. They need to appear first in boogie.
            emitln!(writer, "// declare local variables");
            let num_args = fun_target.get_parameter_count();
            let mid = fun_target.func_env.module_env.get_id();
            let fid = fun_target.func_env.get_id();
            for i in num_args..fun_target.get_local_count() {
                let num_oper = global_state
                    .get_temp_index_oper(mid, fid, i, baseline_flag)
                    .unwrap_or_else(|| {
                        panic!(
                            "missing number operation info for function={}, temp {}",
                            self.fun_target.func_env.get_full_name_str(),
                            i
                        )
                    });
                let local_type = &self.get_local_type(i);
                emitln!(
                    writer,
                    "var $t{}: {};",
                    i,
                    self.boogie_type_for_fun(env, local_type, num_oper)
                );
            }
            // Generate declarations for renamed parameters.
            let proxied_parameters = self.get_mutable_parameters();
            for (idx, ty) in &proxied_parameters {
                let num_oper = &global_state
                    .get_temp_index_oper(mid, fid, *idx, baseline_flag)
                    .unwrap();
                emitln!(
                    writer,
                    "var $t{}: {};",
                    idx,
                    self.boogie_type_for_fun(env, &ty.instantiate(self.type_inst), num_oper)
                );
            }

            // Add global ghost variables that can be used in this function
            if self.style == FunctionTranslationStyle::Default
                || self.style == FunctionTranslationStyle::Opaque
            {
                let ghost_vars = self.get_ghost_vars();
                for type_inst in ghost_vars {
                    emitln!(
                        writer,
                        "var {}: {};",
                        self.ghost_var_name(&type_inst),
                        boogie_type(env, &type_inst[1])
                    );
                }
            }

            if self.should_use_temp_datatypes() {
                emitln!(
                    writer,
                    "var $temp_opaque_res_var: {};",
                    self.wrap_return_datatype_name(),
                );
            }

            self.create_quantifiers_temp_vars();

            // Generate declarations for modifies condition.
            let mut mem_inst_seen = BTreeSet::new();
            for qid in fun_target.get_modify_ids() {
                let memory = qid.instantiate(self.type_inst);
                if !mem_inst_seen.contains(&memory) {
                    emitln!(
                        writer,
                        "var {}: {}",
                        boogie_modifies_memory_name(fun_target.global_env(), &memory),
                        "[int]bool;"
                    );
                    mem_inst_seen.insert(memory);
                }
            }
            let mut dup: Vec<String> = vec![];
            // Declare temporaries for debug tracing and other purposes.
            for (_, (ty, ref bv_flag, cnt)) in self.compute_needed_temps() {
                for i in 0..cnt {
                    let bv_type = if *bv_flag {
                        boogie_bv_type
                    } else {
                        boogie_type
                    };
                    let temp_name =
                        boogie_temp_from_suffix(env, &boogie_type_suffix_bv(env, &ty, *bv_flag), i);
                    if !dup.contains(&temp_name) {
                        emitln!(writer, "var {}: {};", temp_name.clone(), bv_type(env, &ty));
                        dup.push(temp_name);
                    }
                }
            }

            emitln!(writer, "var $abort_if_cond: bool;");

            // Generate memory snapshot variable declarations.
            let labels = fun_target
                .get_bytecode()
                .iter()
                .filter_map(|bc| {
                    use Bytecode::*;
                    match bc {
                        SaveMem(_, lab, mem) => Some((lab, mem)),
                        _ => None,
                    }
                })
                .collect::<BTreeSet<_>>();
            for (lab, mem) in labels {
                let mem = &mem.to_owned().instantiate(self.type_inst);
                let name = boogie_resource_memory_name(env, mem, &Some(*lab));
                emitln!(
                    writer,
                    "var {}: $Memory {};",
                    name,
                    boogie_struct_name(&env.get_struct_qid(mem.to_qualified_id()), &mem.inst)
                );
            }

            // Initialize renamed parameters.
            for (idx, _) in proxied_parameters {
                emitln!(writer, "$t{} := _$t{};", idx, idx);
            }

            // Initialize ghost variables
            if self.style == FunctionTranslationStyle::Default
                || self.style == FunctionTranslationStyle::Opaque
            {
                let ghost_vars = self.get_ghost_vars();
                for type_inst in ghost_vars {
                    emitln!(
                        writer,
                        "{} := {};",
                        self.ghost_var_name(&type_inst),
                        boogie_spec_global_var_name(self.parent.env, &type_inst)
                    );
                }
            }

            // Initial assumptions
            if variant.is_verified() {
                self.translate_verify_entry_assumptions(fun_target);
            }
        } // end of if !self.should_emit_as_function() block

        // Generate bytecode
        if !emit_pure_in_place {
            emitln!(writer, "\n// bytecode translation starts here");
        }
        let mut last_tracked_loc = None;
        let code = fun_target.get_bytecode();

        if emit_pure_in_place {
            self.generate_pure_expression(code);
        } else {
            if code.len() > 0 {
                // Use CFG recovery to generate structured if-then-else statements
                match control_flow_reconstruction::reconstruct_control_flow(code) {
                    Some(block) => self.translate_structured_block(&mut last_tracked_loc, &block),
                    None => {
                        for bytecode in code {
                            self.translate_bytecode(&mut last_tracked_loc, bytecode);
                        }
                    }
                }
            }
        }

        writer.unindent();
        emitln!(writer, "}");
    }

    fn get_mutable_parameters(&self) -> Vec<(TempIndex, Type)> {
        let fun_target = self.fun_target;
        (0..fun_target.get_parameter_count())
            .filter_map(|i| {
                if self.parameter_needs_to_be_mutable(fun_target, i) {
                    Some((i, fun_target.get_local_type(i).clone()))
                } else {
                    None
                }
            })
            .collect_vec()
    }

    /// Determines whether the parameter of a function needs to be mutable.
    /// Boogie does not allow to assign to procedure parameters. In some cases
    /// (e.g. for memory instrumentation, but also as a result of copy propagation),
    /// we may need to assign to parameters.
    fn parameter_needs_to_be_mutable(
        &self,
        _fun_target: &FunctionTarget<'_>,
        _idx: TempIndex,
    ) -> bool {
        // For now, we just always say true. This could be optimized because the actual (known
        // so far) sources for mutability are parameters which are used in WriteBack(LocalRoot(p))
        // position.
        true
    }

    fn translate_verify_entry_assumptions(&self, fun_target: &FunctionTarget<'_>) {
        let writer = self.parent.writer;
        emitln!(writer, "\n// verification entrypoint assumptions");

        // Prelude initialization
        emitln!(writer, "call $InitVerification();");

        // Assume reference parameters to be based on the Param(i) Location, ensuring
        // they are disjoint from all other references. This prevents aliasing and is justified as
        // follows:
        // - for mutual references, by their exclusive access in Move.
        // - for immutable references because we have eliminated them
        for i in 0..fun_target.get_parameter_count() {
            let ty = fun_target.get_local_type(i);
            if ty.is_reference() {
                emitln!(writer, "assume $t{}->l == $Param({});", i, i);
            }
        }
    }

    fn get_ghost_vars(&self) -> BTreeSet<Vec<Type>> {
        let spec_id = &self.fun_target.func_env.get_qualified_id();
        let spec_info = spec_global_variable_analysis::get_info(
            self.parent
                .targets
                .get_data(spec_id, &FunctionVariant::Baseline)
                .expect(&format!(
                    "spec `{}` was filtered out",
                    self.fun_target.func_env.get_full_name_str()
                )),
        );
        spec_info
            .all_vars()
            .map(|type_inst| {
                // Instantiate each type in the type_inst with the concrete types
                type_inst.iter().map(|ty| self.inst(ty)).collect()
            })
            .collect()
    }
}

// =================================================================================================
// Bytecode Translation

impl<'env> FunctionTranslator<'env> {
    fn writer(&self) -> &CodeWriter {
        self.parent.writer
    }

    fn create_quantifiers_temp_vars(&self) {
        let mut has_find = false;
        let mut has_quantifier_temp_vec = false;
        for bc in self.fun_target.get_bytecode() {
            if let Bytecode::Call(_, _, Operation::Quantifier(qt, _, _, _), _, _) = bc {
                if qt.is_find_or_find_index() {
                    has_find = true;
                }
                if qt.requires_sum() || qt.requires_filter_indices() {
                    has_quantifier_temp_vec = true;
                }
            }
        }
        if has_find {
            emitln!(self.parent.writer, "var $find_i: int;");
            emitln!(self.parent.writer, "var $find_exists: bool;");
        }
        if has_quantifier_temp_vec {
            emitln!(self.parent.writer, "var $quantifier_temp_vec: Vec int;");
        }
    }

    fn should_use_temp_datatypes(&self) -> bool {
        if self
            .parent
            .targets
            .is_scenario_spec(&self.fun_target.func_env.get_qualified_id())
        {
            return false;
        }
        let mut_ref_inputs_count = (0..self.fun_target.get_parameter_count())
            .filter(|&idx| self.get_local_type(idx).is_mutable_reference())
            .count();

        let returns_count = self.fun_target.func_env.get_return_count() + mut_ref_inputs_count;

        returns_count != 1 && self.should_use_opaque_as_function(false)
    }

    fn should_use_opaque_as_function(&self, write: bool) -> bool {
        let dinfo: &deterministic_analysis::DeterministicInfo =
            deterministic_analysis::get_info(self.fun_target.data);
        let correct_style = self.style == FunctionTranslationStyle::Opaque
            || (if write {
                false
            } else {
                self.style == FunctionTranslationStyle::SpecNoAbortCheck
            });

        dinfo.is_deterministic && correct_style
    }

    fn can_callee_be_function(&self, mid: &ModuleId, fid: &FunId) -> bool {
        self.parent.targets.is_pure_fun(&mid.qualified(*fid))
    }

    fn format_constant(&self, constant: &Constant) -> String {
        match constant {
            Constant::Bool(true) => "true".to_string(),
            Constant::Bool(false) => "false".to_string(),
            Constant::U8(num) => num.to_string(),
            Constant::U16(num) => num.to_string(),
            Constant::U32(num) => num.to_string(),
            Constant::U64(num) => num.to_string(),
            Constant::U128(num) => num.to_string(),
            Constant::U256(num) => num.to_string(),
            Constant::Address(val) => val.to_string(),
            Constant::ByteArray(val) => boogie_byte_blob(self.parent.options, val, false),
            Constant::AddressArray(val) => boogie_address_blob(self.parent.options, val),
            Constant::Vector(val) => boogie_constant_blob(self.parent.options, val),
        }
    }

    /// Generate Boogie pure function body using let/var expression nesting
    fn generate_pure_expression(&mut self, code: &[Bytecode]) {
        use Bytecode::*;
        use Operation::*;

        let writer = self.writer();
        let fun_target = self.fun_target;

        // Helper to format a temp reference
        let fmt_temp = |idx: usize| -> String {
            if idx < fun_target.get_parameter_count() {
                format!("_$t{}", idx)
            } else {
                format!("$t{}", idx)
            }
        };

        // Collect straightline assignments and operations
        let mut bindings = Vec::new();
        let mut final_return_temp = None;

        // Small helper for infix mapping (arity-checked)
        let op_symbol = |op: &Operation| -> Option<(&'static str, usize)> {
            match op {
                Add => Some(("+", 2)),
                Sub => Some(("-", 2)),
                Mul => Some(("*", 2)),
                Div => Some(("div", 2)),
                Mod => Some(("mod", 2)),
                Lt => Some(("<", 2)),
                Le => Some(("<=", 2)),
                Gt => Some((">", 2)),
                Ge => Some((">=", 2)),
                // Eq and Neq are handled separately to use $IsEqual functions
                And => Some(("&&", 2)),
                Or => Some(("||", 2)),
                Not => Some(("!", 1)),
                BitAnd => Some(("$andInt", 2)),
                BitOr => Some(("$orInt", 2)),
                Shl => Some(("$shl", 2)),
                Shr => Some(("$shr", 2)),
                _ => None,
            }
        };

        for bytecode in code.iter() {
            match bytecode {
                Assign(_, dest, src, _) => {
                    bindings.push((*dest, fmt_temp(*src)));
                }
                Load(_, dest, constant) => {
                    bindings.push((*dest, self.format_constant(constant)));
                }
                Call(_, dests, op, srcs, _) => {
                    if let [dest] = dests.as_slice() {
                        let expr = if let IfThenElse = op {
                            if let [cond, then_val, else_val] = srcs.as_slice() {
                                format!(
                                    "(if {} then {} else {})",
                                    fmt_temp(*cond),
                                    fmt_temp(*then_val),
                                    fmt_temp(*else_val)
                                )
                            } else {
                                panic!("unreachable: expected values for IfThenElse expressions")
                            }
                        } else if let Function(mid, fid, inst) = op {
                            let callee_env = self.parent.env.get_function(mid.qualified(*fid));
                            let native_fn =
                                self.parent.env.should_be_used_as_func(&mid.qualified(*fid));
                            // Handle function calls for functions that can be emitted as Boogie functions
                            if self.can_callee_be_function(mid, fid)
                                || PureFunctionAnalysisProcessor::native_pure_variants(
                                    self.parent.env,
                                )
                                .contains(&mid.qualified(*fid))
                                || native_fn
                            {
                                let inst = &self.inst_slice(inst);
                                let fun_name = boogie_function_name(
                                    &callee_env,
                                    inst,
                                    if native_fn
                                        && !self
                                            .parent
                                            .targets
                                            .is_uninterpreted(&mid.qualified(*fid))
                                    {
                                        FunctionTranslationStyle::Default
                                    } else {
                                        FunctionTranslationStyle::Pure
                                    },
                                );
                                let args = srcs.iter().map(|s| fmt_temp(*s)).join(", ");
                                format!("{}({})", fun_name, args)
                            } else {
                                unreachable!(
                                    "Cannot emit function call to {:?} as pure function",
                                    callee_env.get_full_name_str()
                                );
                            }
                        } else if let Operation::GetField(mid, sid, inst, field_offset) = op {
                            // Handle field access
                            if let [src] = srcs.as_slice() {
                                let inst = &self.inst_slice(inst);
                                let mut src_str = fmt_temp(*src);
                                let struct_env =
                                    fun_target.global_env().get_module(*mid).into_struct(*sid);
                                let field_env = &struct_env.get_field_by_offset(*field_offset);
                                let sel_fun = boogie_field_sel(field_env, inst);
                                if fun_target.get_local_type(*src).is_reference() {
                                    src_str = format!("$Dereference({})", src_str);
                                }
                                format!("{}->{}", src_str, sel_fun)
                            } else {
                                unreachable!("expected one source for GetField expression");
                            }
                        } else if let Quantifier(qt, qid, inst, li) = op {
                            let qfun_env = fun_target.global_env().get_function(*qid);
                            let inst = &self.inst_slice(inst);
                            self.generate_pure_quantifier_expr(
                                qt, &qfun_env, inst, srcs, dests, *li, &fmt_temp,
                            )
                        } else if let Operation::Pack(mid, sid, inst) = op {
                            let inst = &self.inst_slice(inst);
                            let struct_env =
                                fun_target.global_env().get_module(*mid).into_struct(*sid);

                            // Get regular field arguments
                            let regular_args = srcs.iter().cloned().map(fmt_temp).collect_vec();

                            // Get dynamic field arguments
                            let struct_type = Type::Datatype(*mid, *sid, inst.to_owned());
                            let dynamic_field_info =
                                dynamic_field_analysis::get_env_info(fun_target.global_env());
                            let dynamic_field_names_values = dynamic_field_info
                                .dynamic_field_names_values(&struct_type)
                                .collect_vec();

                            // Create EmptyTable() arguments for each dynamic field
                            let dynamic_args = dynamic_field_names_values
                                .iter()
                                .map(|_| "EmptyTable()".to_string())
                                .collect_vec();

                            // Combine all arguments
                            let all_args = regular_args.into_iter().chain(dynamic_args).join(", ");

                            format!("{}({})", boogie_struct_name(&struct_env, inst), all_args)
                        } else if matches!(op, Operation::Eq | Operation::Neq) {
                            // Handle equality/inequality using $IsEqual functions to support
                            // non-extensional types like vectors and tables
                            if let [op1, op2] = srcs.as_slice() {
                                let global_state = &self
                                    .fun_target
                                    .global_env()
                                    .get_extension::<GlobalNumberOperationState>()
                                    .expect("global number operation state");
                                let num_oper = global_state
                                    .get_temp_index_oper(
                                        fun_target.func_env.module_env.get_id(),
                                        fun_target.func_env.get_id(),
                                        *op1,
                                        fun_target.data.variant == FunctionVariant::Baseline,
                                    )
                                    .unwrap();
                                let bv_flag = self.bv_flag(num_oper);
                                let local_ty = self.get_local_type(*op1);
                                let ty = local_ty.skip_reference();
                                let eq_fun = boogie_equality_for_type(
                                    fun_target.global_env(),
                                    matches!(op, Operation::Eq),
                                    ty,
                                    bv_flag,
                                );
                                format!("{}({}, {})", eq_fun, fmt_temp(*op1), fmt_temp(*op2))
                            } else {
                                unreachable!(
                                    "unexpected {} sources for operation {:?} in function {}",
                                    srcs.len(),
                                    op,
                                    fun_target.func_env.get_full_name_str()
                                );
                            }
                        } else if let Some((sym, arity)) = op_symbol(op) {
                            if srcs.len() == arity {
                                // Bitwise operations and shifts are functions, not operators
                                let is_func_op = matches!(
                                    op,
                                    Operation::BitAnd
                                        | Operation::BitOr
                                        | Operation::Shl
                                        | Operation::Shr
                                );
                                if is_func_op {
                                    format!(
                                        "{}({})",
                                        sym,
                                        srcs.iter().map(|s| fmt_temp(*s)).join(", ")
                                    )
                                } else if arity == 1 {
                                    format!("({}{})", sym, fmt_temp(srcs[0]))
                                } else {
                                    format!("({} {} {})", fmt_temp(srcs[0]), sym, fmt_temp(srcs[1]))
                                }
                            } else {
                                unreachable!(
                                    "unexpected {} sources for operation {:?} in function {}",
                                    srcs.len(),
                                    op,
                                    fun_target.func_env.get_full_name_str()
                                );
                            }
                        } else {
                            panic!(
                                "unexpected operation {:?} in function {}",
                                op,
                                fun_target.func_env.get_full_name_str()
                            );
                        };
                        bindings.push((*dest, expr));
                    } else {
                        panic!(
                            "unexpected {} destinations for operation {:?} in function {}",
                            dests.len(),
                            op,
                            fun_target.func_env.get_full_name_str()
                        );
                    }
                }
                Ret(_, srcs) => {
                    if let [src] = srcs.as_slice() {
                        final_return_temp = Some(*src);
                    }
                }
                Branch(..) | Jump(..) | Label(..) | Nop(..) => {} // Skip control flow bytecodes that are summarized by if_then_else(...)
                VariantSwitch(..) | Abort(..) | SaveMem(..) | Prop(..) => {
                    panic!(
                        "Unsupported bytecode for #[ext(pure)] target: {:?}",
                        bytecode
                    )
                }
            }
        }

        // Emit using Boogie's var syntax: (var x := expr; body)
        if bindings.is_empty() {
            // No bindings, just return the value
            if let Some(return_temp) = final_return_temp {
                emitln!(writer, "{}", fmt_temp(return_temp));
            } else {
                panic!("expected Some return value");
            }
        } else {
            // Emit nested var bindings: (var x := e; (var y := f; body))
            for (dest, expr) in &bindings {
                emitln!(writer, "(var $t{} := {};", dest, expr);
            }

            // Emit return value
            if let Some(return_temp) = final_return_temp {
                emit!(writer, "{}", fmt_temp(return_temp));
            } else if let Some((last_dest, _)) = bindings.last() {
                emit!(writer, "$t{}", last_dest);
            } else {
                panic!("expected Some return value");
            }

            // Close all the nested parens
            for _ in 0..bindings.len() {
                emit!(writer, ")");
            }
            emitln!(writer, "");
        }
    }

    fn generate_pure_quantifier_expr<F>(
        &self,
        qt: &QuantifierType,
        fun_env: &FunctionEnv,
        inst: &[Type],
        srcs: &[TempIndex],
        dests: &[TempIndex],
        li: usize,
        fmt_temp: &F,
    ) -> String
    where
        F: Fn(usize) -> String,
    {
        let env = self.fun_target.global_env();
        let fun_name = &boogie_function_name(&fun_env, inst, FunctionTranslationStyle::Pure);

        let cr_args = |local_name: &str| -> String {
            if !qt.vector_based() {
                srcs.iter()
                    .enumerate()
                    .map(|(index, vidx)| {
                        if index == li {
                            local_name.to_string()
                        } else {
                            fmt_temp(*vidx)
                        }
                    })
                    .join(", ")
            } else {
                srcs.iter()
                    .skip(if qt.range_based() { 3 } else { 1 })
                    .enumerate()
                    .map(|(index, vidx)| {
                        if index == li {
                            format!("ReadVec({}, {})", fmt_temp(srcs[0]), local_name)
                        } else {
                            fmt_temp(*vidx)
                        }
                    })
                    .join(", ")
            }
        };

        let extra_args = if fun_env.get_parameter_count() > 1 {
            format!(
                ", {}",
                srcs.iter()
                    .skip(if qt.range_based() {
                        if qt.vector_based() {
                            3
                        } else {
                            2
                        }
                    } else {
                        1
                    })
                    .enumerate()
                    .filter(|(i, _)| *i != li)
                    .map(|(_, val)| fmt_temp(*val))
                    .join(", ")
            )
        } else {
            String::new()
        };

        match qt {
            QuantifierType::Forall => {
                let loc_type = fun_env.get_parameter_types()[0]
                    .skip_reference()
                    .instantiate(inst);
                let b_type = boogie_type(env, &loc_type);
                let suffix = boogie_type_suffix(env, &loc_type);
                format!(
                    "(forall x: {} :: $IsValid'{}'(x) ==> {}({}))",
                    b_type,
                    suffix,
                    fun_name,
                    cr_args("x")
                )
            }
            QuantifierType::Exists => {
                let loc_type = fun_env.get_parameter_types()[0]
                    .skip_reference()
                    .instantiate(inst);
                let b_type = boogie_type(env, &loc_type);
                let suffix = boogie_type_suffix(env, &loc_type);
                format!(
                    "(exists x: {} :: $IsValid'{}'(x) && {}({}))",
                    b_type,
                    suffix,
                    fun_name,
                    cr_args("x")
                )
            }
            QuantifierType::Any => {
                format!(
                    "(exists i:int :: 0 <= i && i < LenVec({}) && {}({}))",
                    fmt_temp(srcs[0]),
                    fun_name,
                    cr_args("i")
                )
            }
            QuantifierType::AnyRange => {
                format!(
                    "(exists i:int :: {} <= i && i < {} && {}({}))",
                    fmt_temp(srcs[1]),
                    fmt_temp(srcs[2]),
                    fun_name,
                    cr_args("i")
                )
            }
            QuantifierType::All => {
                format!(
                    "(forall i:int :: 0 <= i && i < LenVec({}) ==> {}({}))",
                    fmt_temp(srcs[0]),
                    fun_name,
                    cr_args("i")
                )
            }
            QuantifierType::AllRange => {
                format!(
                    "(forall i:int :: {} <= i && i < {} ==> {}({}))",
                    fmt_temp(srcs[1]),
                    fmt_temp(srcs[2]),
                    fun_name,
                    cr_args("i")
                )
            }
            QuantifierType::Map => {
                let res_elem_boogie_type =
                    if let Type::Vector(inner) = self.get_local_type(dests[0]) {
                        boogie_type(env, inner.as_ref())
                    } else {
                        panic!("Expected vector type for Map quantifier")
                    };

                let map_quant_name = self
                    .parent
                    .get_quantifier_helper_name(QuantifierHelperType::Map, fun_name);
                format!(
                    "{0}({1}, 0, LenVec({1}){2})",
                    map_quant_name,
                    fmt_temp(srcs[0]),
                    extra_args,
                )
            }
            QuantifierType::MapRange => {
                let map_quant_name = self
                    .parent
                    .get_quantifier_helper_name(QuantifierHelperType::Map, fun_name);
                format!(
                    "{}({}, {}, {}{})",
                    map_quant_name,
                    fmt_temp(srcs[0]),
                    fmt_temp(srcs[1]),
                    fmt_temp(srcs[2]),
                    extra_args,
                )
            }
            QuantifierType::RangeMap => {
                let map_quant_name = self
                    .parent
                    .get_quantifier_helper_name(QuantifierHelperType::RangeMap, fun_name);
                format!(
                    "{}({}, {}{})",
                    map_quant_name,
                    fmt_temp(srcs[0]),
                    fmt_temp(srcs[1]),
                    extra_args,
                )
            }
            QuantifierType::Count => {
                let find_indices_quant_name = self
                    .parent
                    .get_quantifier_helper_name(QuantifierHelperType::FindIndices, fun_name);
                format!(
                    "LenVec({}({}, 0, LenVec({}){}))",
                    find_indices_quant_name,
                    fmt_temp(srcs[0]),
                    fmt_temp(srcs[0]),
                    extra_args,
                )
            }
            QuantifierType::CountRange => {
                let find_indices_quant_name = self
                    .parent
                    .get_quantifier_helper_name(QuantifierHelperType::FindIndices, fun_name);
                format!(
                    "LenVec({}({}, {}, {}{}))",
                    find_indices_quant_name,
                    fmt_temp(srcs[0]),
                    fmt_temp(srcs[1]),
                    fmt_temp(srcs[2]),
                    extra_args,
                )
            }
            QuantifierType::SumMap => {
                let map_quant_name = self
                    .parent
                    .get_quantifier_helper_name(QuantifierHelperType::Map, fun_name);
                format!(
                    "$0_vec_$sum'u64'({0}({1}, 0, LenVec({1}){2}), 0, LenVec({1}))",
                    map_quant_name,
                    fmt_temp(srcs[0]),
                    extra_args,
                )
            }
            QuantifierType::SumMapRange => {
                let map_quant_name = self
                    .parent
                    .get_quantifier_helper_name(QuantifierHelperType::Map, fun_name);
                format!("(var $temp_map := {}({}, {}, {}{}); $0_vec_$sum'u64'($temp_map, 0, LenVec($temp_map)))",
                    map_quant_name,
                    fmt_temp(srcs[0]),
                    fmt_temp(srcs[1]),
                    fmt_temp(srcs[2]),
                    extra_args,
                )
            }
            QuantifierType::FindIndex => {
                let find_quant_name = self
                    .parent
                    .get_quantifier_helper_name(QuantifierHelperType::FindIndex, fun_name);
                format!(
                    "(var $find_res := {}({}, 0, LenVec({}){}); if $find_res >= 0 then $1_option_Option'u64'(MakeVec1($find_res)) else $1_option_Option'u64'(EmptyVec()))",
                    find_quant_name,
                    fmt_temp(srcs[0]),
                    fmt_temp(srcs[0]),
                    extra_args,
                )
            }
            QuantifierType::FindIndexRange => {
                let find_quant_name = self
                    .parent
                    .get_quantifier_helper_name(QuantifierHelperType::FindIndex, fun_name);
                format!(
                    "(var $find_res := {}({}, {}, {}{}); if $find_res >= 0 then $1_option_Option'u64'(MakeVec1($find_res)) else $1_option_Option'u64'(EmptyVec()))",
                    find_quant_name,
                    fmt_temp(srcs[0]),
                    fmt_temp(srcs[1]),
                    fmt_temp(srcs[2]),
                    extra_args,
                )
            }
            QuantifierType::Find => {
                let src_type = self
                    .fun_target
                    .get_local_type(srcs[0])
                    .vector_element_type();
                let src_elem_suffix = boogie_type_suffix(env, src_type);
                let find_quant_name = self
                    .parent
                    .get_quantifier_helper_name(QuantifierHelperType::FindIndex, fun_name);
                format!(
                    "(var $find_res := {0}({1}, 0, LenVec({1}){3}); if $find_res >= 0 then $1_option_Option'{2}'(MakeVec1(ReadVec({1}, $find_res))) else $1_option_Option'{2}'(EmptyVec()))",
                    find_quant_name, fmt_temp(srcs[0]), src_elem_suffix, extra_args,
                )
            }
            QuantifierType::FindRange => {
                let src_type = self
                    .fun_target
                    .get_local_type(srcs[0])
                    .vector_element_type();
                let src_elem_suffix = boogie_type_suffix(env, src_type);
                let find_quant_name = self
                    .parent
                    .get_quantifier_helper_name(QuantifierHelperType::FindIndex, fun_name);
                format!(
                    "(var $find_res := {0}({1}, {2}, {3}{5}); if $find_res >= 0 then $1_option_Option'{4}'(MakeVec1(ReadVec({1}, $find_res))) else $1_option_Option'{4}'(EmptyVec()))",
                    find_quant_name, fmt_temp(srcs[0]), fmt_temp(srcs[1]), fmt_temp(srcs[2]), src_elem_suffix, extra_args,
                )
            }
            QuantifierType::FindIndices => {
                let find_indices_quant_name = self
                    .parent
                    .get_quantifier_helper_name(QuantifierHelperType::FindIndices, fun_name);
                format!(
                    "{}({}, 0, LenVec({}){})",
                    find_indices_quant_name,
                    fmt_temp(srcs[0]),
                    fmt_temp(srcs[0]),
                    extra_args,
                )
            }
            QuantifierType::FindIndicesRange => {
                let find_indices_quant_name = self
                    .parent
                    .get_quantifier_helper_name(QuantifierHelperType::FindIndices, fun_name);
                format!(
                    "{}({}, {}, {}{})",
                    find_indices_quant_name,
                    fmt_temp(srcs[0]),
                    fmt_temp(srcs[1]),
                    fmt_temp(srcs[2]),
                    extra_args,
                )
            }
            QuantifierType::Filter => {
                let filter_quant_name = self
                    .parent
                    .get_quantifier_helper_name(QuantifierHelperType::Filter, fun_name);
                format!(
                    "{}({}, 0, LenVec({}){})",
                    filter_quant_name,
                    fmt_temp(srcs[0]),
                    fmt_temp(srcs[0]),
                    extra_args,
                )
            }
            QuantifierType::FilterRange => {
                let filter_quant_name = self
                    .parent
                    .get_quantifier_helper_name(QuantifierHelperType::Filter, fun_name);
                format!(
                    "{}({}, {}, {}{})",
                    filter_quant_name,
                    fmt_temp(srcs[0]),
                    fmt_temp(srcs[1]),
                    fmt_temp(srcs[2]),
                    extra_args,
                )
            }
        }
    }

    /// Translates a structured block.
    fn translate_structured_block(
        &mut self,
        last_tracked_loc: &mut Option<(Loc, LineIndex)>,
        block: &StructuredBlock,
    ) {
        let code = self.fun_target.get_bytecode();

        match block {
            StructuredBlock::Basic { lower, upper } => {
                for pc in *lower..=*upper {
                    let bytecode = &code[pc as usize];
                    // skip control flow bytecodes that are now handled structurally
                    if matches!(
                        bytecode,
                        Bytecode::Jump(..) | Bytecode::Branch(..) | Bytecode::Label(..)
                    ) {
                        continue;
                    }
                    self.translate_bytecode(last_tracked_loc, bytecode);
                }
            }
            StructuredBlock::Seq(blocks) => {
                for inner_block in blocks {
                    self.translate_structured_block(last_tracked_loc, inner_block);
                }
            }
            StructuredBlock::IfThenElse {
                cond_at,
                then_branch,
                else_branch,
            } => {
                self.translate_if_chain(
                    last_tracked_loc,
                    &[(*cond_at, then_branch.as_ref())],
                    else_branch.as_deref(),
                );
            }
            StructuredBlock::IfElseChain {
                branches,
                else_branch,
            } => {
                self.translate_if_chain(
                    last_tracked_loc,
                    &branches.iter().map(|(c, b)| (*c, b.as_ref())).collect_vec(),
                    else_branch.as_deref(),
                );
            }
        }
    }

    fn translate_if_chain(
        &mut self,
        last_tracked_loc: &mut Option<(Loc, LineIndex)>,
        branches: &[(u16, &StructuredBlock)],
        else_branch: Option<&StructuredBlock>,
    ) {
        let code = self.fun_target.get_bytecode();

        for (i, (cond_at, body)) in branches.iter().enumerate() {
            let branch_bc = &code[*cond_at as usize];
            let Bytecode::Branch(attr_id, _, _, cond_idx) = branch_bc else {
                panic!(
                    "expected branch at cond_at={}, actual bytecode: {} at {}",
                    cond_at,
                    branch_bc.display(self.fun_target, &BTreeMap::default()),
                    self.fun_target
                        .get_bytecode_loc(branch_bc.get_attr_id())
                        .display(self.fun_target.global_env())
                );
            };

            let loc = self.fun_target.get_bytecode_loc(*attr_id);
            self.writer().set_location(&loc);
            self.track_loc(last_tracked_loc, &loc);

            if i == 0 {
                emitln!(
                    self.writer(),
                    "// {} {}",
                    branch_bc.display(self.fun_target, &BTreeMap::default()),
                    loc.display(self.fun_target.global_env())
                );
                emitln!(self.writer(), "if ($t{}) {{", cond_idx);
            } else {
                emitln!(self.writer(), "}} else if ($t{}) {{", cond_idx);
            }

            self.writer().indent();
            self.translate_structured_block(last_tracked_loc, body);
            self.writer().unindent();
        }

        if let Some(else_block) = else_branch {
            emitln!(self.writer(), "} else {");
            self.writer().indent();
            self.translate_structured_block(last_tracked_loc, else_block);
            self.writer().unindent();
        }

        emitln!(self.writer(), "}");
        emitln!(self.writer());
    }

    /// Translates one bytecode instruction.
    fn translate_bytecode(
        &mut self,
        last_tracked_loc: &mut Option<(Loc, LineIndex)>,
        bytecode: &Bytecode,
    ) {
        use Bytecode::*;

        let spec_translator = &self.parent.spec_translator;
        let options = self.parent.options;
        let fun_target = self.fun_target;
        let env = fun_target.global_env();

        // Set location of this code in the CodeWriter.
        let attr_id = bytecode.get_attr_id();
        let loc = fun_target.get_bytecode_loc(attr_id);
        self.writer().set_location(&loc);

        // Print location.
        emitln!(
            self.writer(),
            "// {} {}",
            bytecode.display(fun_target, &BTreeMap::default()),
            loc.display(env)
        );

        // Print debug comments.
        if let Some(comment) = fun_target.get_debug_comment(attr_id) {
            if comment.starts_with("info: ") {
                // if the comment is annotated with "info: ", it should be displayed to the user
                emitln!(
                    self.writer(),
                    "assume {{:print \"${}(){}\"}} true;",
                    &comment[..4],
                    &comment[4..]
                );
            } else {
                emitln!(self.writer(), "// {}", comment);
            }
        }

        // Track location for execution traces.
        if matches!(bytecode, Call(_, _, Operation::TraceAbort, ..)) {
            // Ensure that aborts always has the precise location instead of the
            // line-approximated one
            *last_tracked_loc = None;
        }
        self.track_loc(last_tracked_loc, &loc);
        if matches!(bytecode, Label(_, _)) {
            // For labels, retrack the location after the label itself, so
            // the information will not be missing if we jump to this label
            *last_tracked_loc = None;
        }

        // Helper function to get a a string for a local
        let str_local = |idx: usize| format!("$t{}", idx);
        let baseline_flag = self.fun_target.data.variant == FunctionVariant::Baseline;
        let global_state = &self
            .fun_target
            .global_env()
            .get_extension::<GlobalNumberOperationState>()
            .expect("global number operation state");
        let mid = self.fun_target.func_env.module_env.get_id();
        let fid = self.fun_target.func_env.get_id();

        // Translate the bytecode instruction.
        match bytecode {
            SaveMem(_, label, mem) => {
                let mem = &mem.to_owned().instantiate(self.type_inst);
                let snapshot = boogie_resource_memory_name(env, mem, &Some(*label));
                let current = boogie_resource_memory_name(env, mem, &None);
                emitln!(self.writer(), "{} := {};", snapshot, current);
            }
            Prop(id, kind, exp) => match kind {
                PropKind::Assert => {
                    emit!(self.writer(), "assert ");
                    let info = fun_target
                        .get_vc_info(*id)
                        .map(|s| s.as_str())
                        .unwrap_or("unknown assertion failed");
                    emit!(
                        self.writer(),
                        "{{:msg \"assert_failed{}: {}\"}}\n  ",
                        self.loc_str(&loc),
                        info
                    );
                    spec_translator.translate(exp, &fun_target, self.type_inst);
                    emitln!(self.writer(), ";");
                }
                PropKind::Assume => {
                    emit!(self.writer(), "assume ");
                    spec_translator.translate(exp, &fun_target, self.type_inst);
                    emitln!(self.writer(), ";");
                }
                PropKind::Modifies => {
                    let ty = &self.inst(&env.get_node_type(exp.node_id()));
                    let bv_flag = global_state.get_node_num_oper(exp.node_id()) == Bitwise;
                    let (mid, sid, inst) = ty.require_datatype();
                    let memory = boogie_resource_memory_name(
                        env,
                        &mid.qualified_inst(sid, inst.to_owned()),
                        &None,
                    );
                    let exists_str = boogie_temp(env, &BOOL_TYPE, 0, false);
                    emitln!(self.writer(), "havoc {};", exists_str);
                    emitln!(self.writer(), "if ({}) {{", exists_str);
                    self.writer().with_indent(|| {
                        let val_str = boogie_temp(env, ty, 0, bv_flag);
                        emitln!(self.writer(), "havoc {};", val_str);
                        emit!(self.writer(), "{} := $ResourceUpdate({}, ", memory, memory);
                        spec_translator.translate(&exp.call_args()[0], &fun_target, self.type_inst);
                        emitln!(self.writer(), ", {});", val_str);
                    });
                    emitln!(self.writer(), "} else {");
                    self.writer().with_indent(|| {
                        emit!(self.writer(), "{} := $ResourceRemove({}, ", memory, memory);
                        spec_translator.translate(&exp.call_args()[0], &fun_target, self.type_inst);
                        emitln!(self.writer(), ");");
                    });
                    emitln!(self.writer(), "}");
                }
            },
            Label(_, label) => {
                self.writer().unindent();
                emitln!(self.writer(), "L{}:", label.as_usize());
                self.writer().indent();
            }
            Jump(_, target) => emitln!(self.writer(), "goto L{};", target.as_usize()),
            Branch(_, then_target, else_target, idx) => emitln!(
                self.writer(),
                "if ({}) {{ goto L{}; }} else {{ goto L{}; }}",
                str_local(*idx),
                then_target.as_usize(),
                else_target.as_usize(),
            ),
            VariantSwitch(_, idx, labels) => {
                // emit if then else for each variant
                for (i, target) in labels.iter().enumerate() {
                    emitln!(
                        self.writer(),
                        "if ({}->$variant_id == {}) {{ goto L{}; }}",
                        str_local(*idx),
                        i,
                        target.as_usize()
                    );
                }
            }
            Assign(_, dest, src, _) => {
                emitln!(
                    self.writer(),
                    "{} := {};",
                    str_local(*dest),
                    str_local(*src)
                );
            }
            Ret(_, rets) => {
                match self.parent.asserts_mode {
                    AssertsMode::Check | AssertsMode::SpecNoAbortCheck => {
                        if FunctionTranslationStyle::Opaque == self.style
                            && !self
                                .parent
                                .targets
                                .omits_opaque(&self.fun_target.func_env.get_qualified_id())
                            && self
                                .parent
                                .targets
                                .ignore_aborts()
                                .contains(&self.fun_target.func_env.get_qualified_id())
                        {
                            emitln!(
                                self.writer(),
                                "assert {{:msg \"assert_failed{}: {} ignore_aborts\"}} false;",
                                self.loc_str(&self.fun_target.get_loc()),
                                self.fun_target.func_env.get_full_name_str()
                            );
                        }
                    }
                    AssertsMode::Assume => {
                        if !self
                            .parent
                            .targets
                            .ignore_aborts()
                            .contains(&self.fun_target.func_env.get_qualified_id())
                            && self
                                .fun_target
                                .func_env
                                .get_called_functions()
                                .iter()
                                .any(|f| *f == self.parent.env.asserts_qid())
                        {
                            let args_string = (0..fun_target.get_parameter_count())
                                .map(|i| {
                                    let prefix =
                                        if self.parameter_needs_to_be_mutable(fun_target, i) {
                                            "_$"
                                        } else {
                                            "$"
                                        };
                                    format!("{}t{}", prefix, i)
                                })
                                .chain(
                                    self.get_ghost_vars()
                                        .into_iter()
                                        .map(|type_inst| self.ghost_var_name(&type_inst)),
                                )
                                .join(", ");
                            if FunctionTranslationStyle::Default == self.style
                                && self.fun_target.data.variant
                                    == FunctionVariant::Verification(VerificationFlavor::Regular)
                            {
                                emitln!(
                                    self.writer(),
                                    "call {}({});",
                                    self.function_variant_name(FunctionTranslationStyle::Asserts),
                                    args_string,
                                );
                            } else if FunctionTranslationStyle::Opaque == self.style
                                && !self
                                    .parent
                                    .targets
                                    .omits_opaque(&self.fun_target.func_env.get_qualified_id())
                            {
                                emitln!(
                                    self.writer(),
                                    "call {}({});",
                                    self.function_variant_name(FunctionTranslationStyle::Aborts),
                                    args_string,
                                );
                            }
                        }
                    }
                }

                for (i, r) in rets.iter().enumerate() {
                    emitln!(self.writer(), "$ret{} := {};", i, str_local(*r));
                }
                // Also assign input to output $mut parameters
                let mut ret_idx = rets.len();
                for i in 0..fun_target.get_parameter_count() {
                    if self.get_local_type(i).is_mutable_reference() {
                        emitln!(self.writer(), "$ret{} := {};", ret_idx, str_local(i));
                        ret_idx = usize::saturating_add(ret_idx, 1);
                    }
                }
                emitln!(self.writer(), "return;");
            }
            Load(_, dest, c) => {
                let num_oper = global_state
                    .get_temp_index_oper(mid, fid, *dest, baseline_flag)
                    .unwrap();
                let bv_flag = self.bv_flag(num_oper);
                let value = match c {
                    Constant::Bool(true) => "true".to_string(),
                    Constant::Bool(false) => "false".to_string(),
                    Constant::U8(num) => boogie_num_literal(&num.to_string(), 8, bv_flag),
                    Constant::U64(num) => boogie_num_literal(&num.to_string(), 64, bv_flag),
                    Constant::U128(num) => boogie_num_literal(&num.to_string(), 128, bv_flag),
                    Constant::U256(num) => boogie_num_literal(&num.to_string(), 256, bv_flag),
                    Constant::Address(val) => val.to_string(),
                    Constant::ByteArray(val) => boogie_byte_blob(options, val, bv_flag),
                    Constant::AddressArray(val) => boogie_address_blob(options, val),
                    Constant::Vector(val) => boogie_constant_blob(options, val),
                    Constant::U16(num) => boogie_num_literal(&num.to_string(), 16, bv_flag),
                    Constant::U32(num) => boogie_num_literal(&num.to_string(), 32, bv_flag),
                };
                let dest_str = str_local(*dest);
                emitln!(self.writer(), "{} := {};", dest_str, value);
                // Insert a WellFormed assumption so the new value gets tagged as u8, ...
                let ty = &self.get_local_type(*dest);
                let check = boogie_well_formed_check(env, &dest_str, ty, bv_flag);
                if !check.is_empty() {
                    emitln!(self.writer(), &check);
                }
            }
            Call(_, dests, oper, srcs, aa) => {
                use Operation::*;
                match oper {
                    FreezeRef => unreachable!(),
                    UnpackRef | UnpackRefDeep | PackRef | PackRefDeep => {
                        // No effect
                    }
                    OpaqueCallBegin(_, _, _) | OpaqueCallEnd(_, _, _) => {
                        // These are just markers.  There is no generated code.
                    }
                    WriteBack(node, edge) => {
                        self.translate_write_back(node, edge, srcs[0]);
                    }
                    IsParent(node, edge) => {
                        if let BorrowNode::Reference(parent) = node {
                            let src_str = str_local(srcs[0]);
                            let edge_pattern = edge
                                .flatten()
                                .into_iter()
                                .filter_map(|e| match e {
                                    BorrowEdge::Field(_, offset) => Some(format!("{}", offset)),
                                    BorrowEdge::EnumField(dt_id, offset, vid) => Some(format!(
                                        "{}",
                                        variant_field_offset(
                                            &self
                                                .parent
                                                .env
                                                .get_enum_qid(dt_id.to_qualified_id())
                                                .get_variant(*vid),
                                            *offset,
                                        )
                                    )),
                                    BorrowEdge::Index(_) => Some("-1".to_owned()),
                                    BorrowEdge::DynamicField(..) => Some("-1".to_owned()),
                                    BorrowEdge::Direct => None,
                                    BorrowEdge::Hyper(_) => unreachable!(),
                                })
                                .collect_vec();
                            if edge_pattern.is_empty() {
                                emitln!(
                                    self.writer(),
                                    "{} := $IsSameMutation({}, {});",
                                    str_local(dests[0]),
                                    str_local(*parent),
                                    src_str
                                );
                            } else if edge_pattern.len() == 1 {
                                emitln!(
                                    self.writer(),
                                    "{} := $IsParentMutation({}, {}, {});",
                                    str_local(dests[0]),
                                    str_local(*parent),
                                    edge_pattern[0],
                                    src_str
                                );
                            } else {
                                emitln!(
                                    self.writer(),
                                    "{} := $IsParentMutationHyper({}, {}, {});",
                                    str_local(dests[0]),
                                    str_local(*parent),
                                    boogie_make_vec_from_strings(
                                        self.parent.options.vector_theory,
                                        &edge_pattern
                                    ),
                                    src_str
                                );
                            }
                        } else {
                            panic!("inconsistent IsParent instruction: expected a reference node")
                        }
                    }
                    BorrowLoc => {
                        let src = srcs[0];
                        let dest = dests[0];
                        emitln!(
                            self.writer(),
                            "{} := $Mutation($Local({}), EmptyVec(), {});",
                            str_local(dest),
                            src,
                            str_local(src)
                        );
                    }
                    ReadRef => {
                        let src = srcs[0];
                        let dest = dests[0];
                        emitln!(
                            self.writer(),
                            "{} := $Dereference({});",
                            str_local(dest),
                            str_local(src)
                        );
                    }
                    WriteRef => {
                        let reference = srcs[0];
                        let value = srcs[1];
                        let field = str_local(reference);
                        emitln!(
                            self.writer(),
                            "{} := $UpdateMutation({}, {});",
                            field,
                            field,
                            str_local(value),
                        );
                    }
                    Function(mid, fid, inst) => {
                        let inst = &self.inst_slice(inst);
                        let module_env = env.get_module(*mid);
                        let callee_env = module_env.get_function(*fid);

                        let id = &self.fun_target.func_env.get_qualified_id();
                        let use_impl = self.style == FunctionTranslationStyle::Opaque
                            && self.parent.targets.omits_opaque(&id);
                        let mut use_func = false;
                        let mut use_func_datatypes = false;

                        let is_spec_call = self.parent.targets.get_fun_by_spec(id)
                            == Some(&QualifiedId {
                                module_id: *mid,
                                id: *fid,
                            });

                        let mut args_str = srcs.iter().cloned().map(str_local).join(", ");

                        // Check if callee is marked as pure
                        let callee_is_pure = self.can_callee_be_function(mid, fid);

                        if is_spec_call && !use_impl && self.should_use_opaque_as_function(false) {
                            use_func = true;
                            use_func_datatypes = self.should_use_temp_datatypes();
                        }

                        if !use_func && env.should_be_used_as_func(&callee_env.get_qualified_id()) {
                            use_func = true;
                        }

                        // Check if callee is marked as pure - if so, use as Boogie function (not procedure)
                        if callee_is_pure {
                            use_func = true;
                        }

                        let dest_str = if use_func_datatypes {
                            "$temp_opaque_res_var".to_string()
                        } else {
                            dests
                                .iter()
                                .cloned()
                                .map(str_local)
                                // Add implict dest returns for &mut srcs:
                                //  f(x) --> x := f(x)  if type(x) = &mut_
                                .chain(
                                    srcs.iter()
                                        .filter(|idx| {
                                            self.get_local_type(**idx).is_mutable_reference()
                                        })
                                        .cloned()
                                        .map(str_local),
                                )
                                .join(",")
                        };

                        // special casing for type reflection
                        let mut processed = false;

                        if callee_env.get_qualified_id() == self.parent.env.global_borrow_mut_qid()
                        {
                            emitln!(
                                self.writer(),
                                "{} := $Mutation($SpecGlobal(\"{}\"), EmptyVec(), {});",
                                str_local(dests[0]),
                                boogie_inst_suffix(self.parent.env, inst),
                                boogie_spec_global_var_name(self.parent.env, inst),
                            );
                            processed = true;
                        }

                        if callee_env.get_qualified_id() == self.parent.env.global_qid()
                            && self.style.is_asserts_style()
                        {
                            let var_name = boogie_spec_global_var_name(self.parent.env, inst);

                            emitln!(self.writer(), "{} := $ghost_{};", dest_str, var_name);
                            processed = true;
                        }

                        if callee_env.get_qualified_id() == self.parent.env.ensures_qid() {
                            let secondary = if let Some((sec_loc, sec_msg)) =
                                fun_target.get_secondary_label(attr_id)
                            {
                                format!(" @{{{}:{}}}", self.loc_str(sec_loc), sec_msg)
                            } else {
                                String::new()
                            };
                            emitln!(
                                self.writer(),
                                "assert {{:msg \"assert_failed{}: prover::ensures does not hold{}\"}} {};",
                                self.loc_str(&self.writer().get_loc()),
                                secondary,
                                args_str,
                            );
                            processed = true;
                        }

                        if callee_env.get_qualified_id() == self.parent.env.type_inv_qid() {
                            if self.style.is_asserts_style() {
                                emitln!(self.writer(), "{} := true;", dest_str);
                            } else {
                                assert_eq!(inst.len(), 1);
                                if let Some((datatype_qid, datatype_inst)) = &inst[0].get_datatype()
                                {
                                    if let Some(inv_qid) =
                                        self.parent.targets.get_inv_by_datatype(datatype_qid)
                                    {
                                        emitln!(
                                            self.writer(),
                                            "call {} := {}({});",
                                            dest_str,
                                            boogie_function_name(
                                                &self.parent.env.get_function(*inv_qid),
                                                datatype_inst,
                                                FunctionTranslationStyle::Default,
                                            ),
                                            args_str,
                                        );
                                    } else {
                                        emitln!(self.writer(), "{} := true;", dest_str);
                                    }
                                } else {
                                    emitln!(self.writer(), "{} := true;", dest_str);
                                }
                            }
                            processed = true;
                        }

                        // regular path
                        if !processed {
                            let targeted = self.fun_target.module_env().is_target();
                            // If the callee has been generated from a native interface, return an error
                            if callee_env.is_native() && targeted {
                                for attr in callee_env.get_attributes() {
                                    if let Attribute::Apply(_, name, _) = attr {
                                        if self
                                            .fun_target
                                            .module_env()
                                            .symbol_pool()
                                            .string(*name)
                                            .as_str()
                                            == NATIVE_INTERFACE
                                        {
                                            let loc = self.fun_target.get_bytecode_loc(attr_id);
                                            self.parent
                                                .env
                                                .error(&loc, "Unknown native function is called");
                                        }
                                    }
                                }
                            }
                            let caller_mid = self.fun_target.module_env().get_id();
                            let caller_fid = self.fun_target.get_id();
                            let fun_verified =
                                !self.fun_target.func_env.is_explicitly_not_verified(
                                    &self.parent.targets.prover_options().verify_scope,
                                );
                            let mut fun_name = boogie_function_name(
                                &callee_env,
                                inst,
                                FunctionTranslationStyle::Default,
                            );

                            // Native functions from native_fn_ids() use their base Boogie function name
                            // (no $pure/$impl suffix) as they have hardcoded definitions in prelude
                            let is_native_fn =
                                env.should_be_used_as_func(&callee_env.get_qualified_id());

                            if is_spec_call {
                                if self.style == FunctionTranslationStyle::Default
                                    && self.fun_target.data.variant
                                        == FunctionVariant::Verification(
                                            VerificationFlavor::Regular,
                                        )
                                {
                                    // Check if callee has $pure variant available
                                    if is_native_fn {
                                        // Native functions use base name (no suffix)
                                    } else if self.parent.targets.is_pure_fun(&QualifiedId {
                                        module_id: *mid,
                                        id: *fid,
                                    }) {
                                        fun_name = format!("{}{}", fun_name, "$pure");
                                    } else {
                                        // Fallback to $impl if no $pure available
                                        fun_name = format!("{}{}", fun_name, "$impl");
                                    }
                                } else if self.style == FunctionTranslationStyle::SpecNoAbortCheck {
                                    fun_name = format!("{}{}", fun_name, "$opaque");
                                } else if self.style == FunctionTranslationStyle::Opaque {
                                    if !is_native_fn {
                                        let suffix = if use_impl {
                                            if self.parent.targets.is_pure_fun(&QualifiedId {
                                                module_id: *mid,
                                                id: *fid,
                                            }) {
                                                "$pure"
                                            } else {
                                                "$impl"
                                            }
                                        } else {
                                            "$opaque"
                                        };
                                        fun_name = format!("{}{}", fun_name, suffix);
                                    }
                                }
                            } else if !is_spec_call && use_func && callee_is_pure && !is_native_fn {
                                // For non-spec calls using function syntax to pure functions,
                                // add $pure suffix (regardless of current style)
                                // But not for native functions which use their base name
                                fun_name = format!("{}{}", fun_name, "$pure");
                            } else if is_native_fn
                                && self
                                    .parent
                                    .targets
                                    .is_uninterpreted(&callee_env.get_qualified_id())
                            {
                                // Uninterpreted native functions use $pure suffix
                                fun_name = format!("{}{}", fun_name, "$pure");
                            };

                            // Helper function to check whether the idx corresponds to a bitwise operation
                            let compute_flag = |idx: TempIndex| {
                                targeted
                                    && fun_verified
                                    && *global_state
                                        .get_temp_index_oper(
                                            caller_mid,
                                            caller_fid,
                                            idx,
                                            baseline_flag,
                                        )
                                        .unwrap()
                                        == Bitwise
                            };
                            let instrument_bv2int =
                                |idx: TempIndex, args_str_vec: &mut Vec<String>| {
                                    let local_ty_srcs_1 = self.get_local_type(idx);
                                    let srcs_1_bv_flag = compute_flag(idx);
                                    let mut args_src_1_str = str_local(idx);
                                    if srcs_1_bv_flag {
                                        args_src_1_str = format!(
                                            "$bv2int.{}({})",
                                            boogie_num_type_base(&local_ty_srcs_1),
                                            args_src_1_str
                                        );
                                    }
                                    args_str_vec.push(args_src_1_str);
                                };
                            let callee_name = callee_env.get_name_str();
                            if dest_str.is_empty() {
                                let bv_flag = !srcs.is_empty() && compute_flag(srcs[0]);
                                if module_env.is_std_vector() {
                                    // Check the target vector contains bv values
                                    if callee_name.contains("insert") {
                                        let mut args_str_vec =
                                            vec![str_local(srcs[0]), str_local(srcs[1])];
                                        assert!(srcs.len() > 2);
                                        instrument_bv2int(srcs[2], &mut args_str_vec);
                                        args_str = args_str_vec.iter().cloned().join(", ");
                                    }
                                    fun_name =
                                        boogie_function_bv_name(&callee_env, inst, &[bv_flag]);
                                } else if module_env.is_table() {
                                    fun_name = boogie_function_bv_name(
                                        &callee_env,
                                        inst,
                                        &[false, bv_flag],
                                    );
                                }

                                emitln!(self.writer(), "call {}({});", fun_name, args_str);
                            } else {
                                let dest_bv_flag = !dests.is_empty() && compute_flag(dests[0]);
                                let bv_flag = !srcs.is_empty() && compute_flag(srcs[0]);
                                // Handle the case where the return value of length is assigned to a bv int because
                                // length always returns a non-bv result
                                if module_env.is_std_vector() {
                                    fun_name = boogie_function_bv_name(
                                        &callee_env,
                                        inst,
                                        &[bv_flag || dest_bv_flag],
                                    );
                                    // Handle the case where the return value of length is assigned to a bv int because
                                    // length always returns a non-bv result
                                    if callee_name.contains("length") && dest_bv_flag {
                                        let local_ty = self.get_local_type(dests[0]);
                                        // Insert '$' for calling function instead of procedure
                                        // TODO(tengzhang): a hacky way to convert int to bv for return value
                                        fun_name.insert(10, '$');
                                        // first call len fun then convert its return value to a bv type
                                        emitln!(
                                            self.writer(),
                                            "call {} := $int2bv{}({}({}));",
                                            dest_str,
                                            boogie_num_type_base(&local_ty),
                                            fun_name,
                                            args_str
                                        );
                                    } else if callee_name.contains("borrow")
                                        || callee_name.contains("remove")
                                        || callee_name.contains("swap")
                                    {
                                        let mut args_str_vec = vec![str_local(srcs[0])];
                                        instrument_bv2int(srcs[1], &mut args_str_vec);
                                        // Handle swap with three parameters
                                        if srcs.len() > 2 {
                                            instrument_bv2int(srcs[2], &mut args_str_vec);
                                        }
                                        args_str = args_str_vec.iter().cloned().join(", ");
                                    }
                                } else if module_env.is_table() {
                                    fun_name = boogie_function_bv_name(
                                        &callee_env,
                                        inst,
                                        &[false, bv_flag || dest_bv_flag],
                                    );
                                    if dest_bv_flag && callee_name.contains("length") {
                                        // Handle the case where the return value of length is assigned to a bv int because
                                        // length always returns a non-bv result
                                        let local_ty = self.get_local_type(dests[0]);
                                        // Replace with "spec_len"
                                        let length_idx_start = callee_name.find("length").unwrap();
                                        let length_idx_end = length_idx_start + "length".len();
                                        fun_name = [
                                            callee_name[0..length_idx_start].to_string(),
                                            "spec_len".to_string(),
                                            callee_name[length_idx_end..].to_string(),
                                        ]
                                        .join("");
                                        // first call len fun then convert its return value to a bv type
                                        emitln!(
                                            self.writer(),
                                            "call {} := $int2bv{}({}({}));",
                                            dest_str,
                                            boogie_num_type_base(&local_ty),
                                            fun_name,
                                            args_str
                                        );
                                    }
                                }

                                let call_line = if use_func { "" } else { "call " };

                                emitln!(
                                    self.writer(),
                                    "{}{} := {}({});",
                                    call_line,
                                    dest_str,
                                    fun_name,
                                    args_str
                                );
                            }
                        }

                        if is_spec_call {
                            if self.style == FunctionTranslationStyle::SpecNoAbortCheck
                                || self.style == FunctionTranslationStyle::Opaque
                                    && !self.parent.targets.omits_opaque(id)
                            {
                                for type_inst in
                                    spec_global_variable_analysis::get_info(&self.fun_target.data)
                                        .mut_vars()
                                {
                                    emitln!(
                                        self.writer(),
                                        "havoc {};",
                                        boogie_spec_global_var_name(self.parent.env, type_inst),
                                    );
                                }
                            }
                        };

                        if use_func_datatypes {
                            dests.iter().enumerate().for_each(|(idx, val)| {
                                emitln!(
                                    self.writer(),
                                    "{} := $temp_opaque_res_var -> $ret{};",
                                    str_local(*val),
                                    idx
                                )
                            });
                            srcs.iter()
                                .filter(|idx| self.get_local_type(**idx).is_mutable_reference())
                                .enumerate()
                                .for_each(|(idx, val)| {
                                    emitln!(
                                        self.writer(),
                                        "{} := $temp_opaque_res_var -> $ret{};",
                                        str_local(*val),
                                        dests.len() + idx
                                    )
                                });
                        }

                        // Clear the last track location after function call, as the call inserted
                        // location tracks before it returns.
                        *last_tracked_loc = None;
                    }
                    Pack(mid, sid, inst) => {
                        let inst = &self.inst_slice(inst);
                        let struct_env = env.get_module(*mid).into_struct(*sid);

                        // Get regular field arguments
                        let regular_args = srcs.iter().cloned().map(str_local).collect_vec();

                        // Get dynamic field arguments
                        let struct_type = Type::Datatype(*mid, *sid, inst.to_owned());
                        let dynamic_field_info = dynamic_field_analysis::get_env_info(env);
                        let dynamic_field_names_values = dynamic_field_info
                            .dynamic_field_names_values(&struct_type)
                            .collect_vec();

                        // Create EmptyTable() arguments for each dynamic field
                        let dynamic_args = dynamic_field_names_values
                            .iter()
                            .map(|_| "EmptyTable()".to_string())
                            .collect_vec();

                        // Combine all arguments
                        let all_args = regular_args.into_iter().chain(dynamic_args).join(", ");

                        let dest_str = str_local(dests[0]);
                        emitln!(
                            self.writer(),
                            "{} := {}({});",
                            dest_str,
                            boogie_struct_name(&struct_env, inst),
                            all_args
                        );
                    }
                    Unpack(mid, sid, inst) => {
                        let inst = &self.inst_slice(inst);
                        let struct_env = env.get_module(*mid).into_struct(*sid);
                        for (i, ref field_env) in struct_env.get_fields().enumerate() {
                            let field_sel = format!(
                                "{}->{}",
                                str_local(srcs[0]),
                                boogie_field_sel(field_env, inst),
                            );
                            emitln!(self.writer(), "{} := {};", str_local(dests[i]), field_sel);
                        }
                    }
                    PackVariant(mid, eid, vid, inst) => {
                        let inst = &self.inst_slice(inst);
                        let enum_env = env.get_module(*mid).into_enum(*eid);
                        let args = srcs.iter().cloned().map(str_local).join(", ");
                        let dest_str = str_local(dests[0]);
                        emitln!(
                            self.writer(),
                            "call {} := {}({});",
                            dest_str,
                            boogie_enum_variant_ctor_name(&enum_env.get_variant(*vid), inst),
                            args
                        );
                    }
                    UnpackVariant(mid, eid, vid, _inst, ref_type) => {
                        let enum_env = env.get_module(*mid).into_enum(*eid);
                        let variant_env = enum_env.get_variant(*vid);

                        for (i, ref field_env) in variant_env.get_fields().enumerate() {
                            let dest_str = str_local(dests[i]);
                            let src_str = str_local(srcs[0]);
                            let field_name = boogie_enum_field_name(field_env);

                            if *ref_type == RefType::ByMutRef {
                                emitln!(
                                    self.writer(),
                                    "{} := $ChildMutation({}, {}, $Dereference({})->{});",
                                    dest_str,
                                    src_str,
                                    variant_field_offset(&variant_env, field_env.get_offset()),
                                    src_str,
                                    field_name
                                );
                            } else {
                                emitln!(
                                    self.writer(),
                                    "{} := {}->{};",
                                    dest_str,
                                    src_str,
                                    field_name
                                );
                            }
                        }
                    }
                    BorrowField(mid, sid, inst, field_offset) => {
                        let inst = &self.inst_slice(inst);
                        let src_str = str_local(srcs[0]);
                        let dest_str = str_local(dests[0]);
                        let struct_env = env.get_module(*mid).into_struct(*sid);
                        let field_env = &struct_env.get_field_by_offset(*field_offset);
                        let sel_fun = boogie_field_sel(field_env, inst);
                        emitln!(
                            self.writer(),
                            "{} := $ChildMutation({}, {}, $Dereference({})->{});",
                            dest_str,
                            src_str,
                            field_offset,
                            src_str,
                            sel_fun
                        );
                    }
                    GetField(mid, sid, inst, field_offset) => {
                        let inst = &self.inst_slice(inst);
                        let src = srcs[0];
                        let mut src_str = str_local(src);
                        let dest_str = str_local(dests[0]);
                        let struct_env = env.get_module(*mid).into_struct(*sid);
                        let field_env = &struct_env.get_field_by_offset(*field_offset);
                        let sel_fun = boogie_field_sel(field_env, inst);
                        if self.get_local_type(src).is_reference() {
                            src_str = format!("$Dereference({})", src_str);
                        };
                        emitln!(self.writer(), "{} := {}->{};", dest_str, src_str, sel_fun);
                    }
                    Exists(mid, sid, inst) => {
                        let inst = self.inst_slice(inst);
                        let addr_str = str_local(srcs[0]);
                        let dest_str = str_local(dests[0]);
                        let memory = boogie_resource_memory_name(
                            env,
                            &mid.qualified_inst(*sid, inst),
                            &None,
                        );
                        emitln!(
                            self.writer(),
                            "{} := $ResourceExists({}, {});",
                            dest_str,
                            memory,
                            addr_str
                        );
                    }
                    BorrowGlobal(mid, sid, inst) => {
                        let inst = self.inst_slice(inst);
                        let addr_str = str_local(srcs[0]);
                        let dest_str = str_local(dests[0]);
                        let memory = boogie_resource_memory_name(
                            env,
                            &mid.qualified_inst(*sid, inst),
                            &None,
                        );
                        emitln!(
                            self.writer(),
                            "if (!$ResourceExists({}, {})) {{",
                            memory,
                            addr_str
                        );
                        self.writer()
                            .with_indent(|| emitln!(self.writer(), "call $ExecFailureAbort();"));
                        emitln!(self.writer(), "} else {");
                        self.writer().with_indent(|| {
                            emitln!(
                                self.writer(),
                                "{} := $Mutation($Global({}), EmptyVec(), $ResourceValue({}, {}));",
                                dest_str,
                                addr_str,
                                memory,
                                addr_str
                            );
                        });
                        emitln!(self.writer(), "}");
                    }
                    GetGlobal(mid, sid, inst) => {
                        let inst = self.inst_slice(inst);
                        let memory = boogie_resource_memory_name(
                            env,
                            &mid.qualified_inst(*sid, inst),
                            &None,
                        );
                        let addr_str = str_local(srcs[0]);
                        let dest_str = str_local(dests[0]);
                        emitln!(
                            self.writer(),
                            "if (!$ResourceExists({}, {})) {{",
                            memory,
                            addr_str
                        );
                        self.writer()
                            .with_indent(|| emitln!(self.writer(), "call $ExecFailureAbort();"));
                        emitln!(self.writer(), "} else {");
                        self.writer().with_indent(|| {
                            emitln!(
                                self.writer(),
                                "{} := $ResourceValue({}, {});",
                                dest_str,
                                memory,
                                addr_str
                            );
                        });
                        emitln!(self.writer(), "}");
                    }
                    MoveTo(mid, sid, inst) => {
                        let inst = self.inst_slice(inst);
                        let memory = boogie_resource_memory_name(
                            env,
                            &mid.qualified_inst(*sid, inst),
                            &None,
                        );
                        let value_str = str_local(srcs[0]);
                        let signer_str = str_local(srcs[1]);
                        emitln!(
                            self.writer(),
                            "if ($ResourceExists({}, {}->$addr)) {{",
                            memory,
                            signer_str
                        );
                        self.writer()
                            .with_indent(|| emitln!(self.writer(), "call $ExecFailureAbort();"));
                        emitln!(self.writer(), "} else {");
                        self.writer().with_indent(|| {
                            emitln!(
                                self.writer(),
                                "{} := $ResourceUpdate({}, {}->$addr, {});",
                                memory,
                                memory,
                                signer_str,
                                value_str
                            );
                        });
                        emitln!(self.writer(), "}");
                    }
                    MoveFrom(mid, sid, inst) => {
                        let inst = &self.inst_slice(inst);
                        let memory = boogie_resource_memory_name(
                            env,
                            &mid.qualified_inst(*sid, inst.to_owned()),
                            &None,
                        );
                        let addr_str = str_local(srcs[0]);
                        let dest_str = str_local(dests[0]);
                        emitln!(
                            self.writer(),
                            "if (!$ResourceExists({}, {})) {{",
                            memory,
                            addr_str
                        );
                        self.writer()
                            .with_indent(|| emitln!(self.writer(), "call $ExecFailureAbort();"));
                        emitln!(self.writer(), "} else {");
                        self.writer().with_indent(|| {
                            emitln!(
                                self.writer(),
                                "{} := $ResourceValue({}, {});",
                                dest_str,
                                memory,
                                addr_str
                            );
                            emitln!(
                                self.writer(),
                                "{} := $ResourceRemove({}, {});",
                                memory,
                                memory,
                                addr_str
                            );
                        });
                        emitln!(self.writer(), "}");
                    }
                    Havoc(HavocKind::Value) | Havoc(HavocKind::MutationAll) => {
                        let var_str = str_local(dests[0]);
                        emitln!(self.writer(), "havoc {};", var_str);
                    }
                    Havoc(HavocKind::MutationValue) => {
                        let ty = &self.get_local_type(dests[0]);
                        let num_oper = global_state
                            .get_temp_index_oper(mid, fid, dests[0], baseline_flag)
                            .unwrap();
                        let bv_flag = self.bv_flag(num_oper);
                        let var_str = str_local(dests[0]);
                        let temp_str = boogie_temp(env, ty.skip_reference(), 0, bv_flag);
                        emitln!(self.writer(), "havoc {};", temp_str);
                        emitln!(
                            self.writer(),
                            "{} := $UpdateMutation({}, {});",
                            var_str,
                            var_str,
                            temp_str
                        );
                    }
                    Stop => {
                        // the two statements combined terminate any execution trace that reaches it
                        emitln!(self.writer(), "assume false;");
                        emitln!(self.writer(), "return;");
                    }
                    CastU8 | CastU16 | CastU32 | CastU64 | CastU128 | CastU256 => {
                        let src = srcs[0];
                        let dest = dests[0];
                        let make_cast = |target_base: usize, src: TempIndex, dest: TempIndex| {
                            let num_oper = global_state
                                .get_temp_index_oper(mid, fid, src, baseline_flag)
                                .unwrap();
                            let bv_flag = self.bv_flag(num_oper);
                            if bv_flag {
                                let src_type = self.get_local_type(src);
                                let base = boogie_num_type_base(&src_type);
                                emitln!(
                                    self.writer(),
                                    "call {} := $CastBv{}to{}({});",
                                    str_local(dest),
                                    base,
                                    target_base,
                                    str_local(src)
                                );
                            } else {
                                // skip casting to higher bit width
                                if target_base
                                    < self.fun_target.get_local_type(src).get_bit_width().unwrap()
                                {
                                    emitln!(
                                        self.writer(),
                                        "call {} := $CastU{}({});",
                                        str_local(dest),
                                        target_base,
                                        str_local(src)
                                    );
                                } else {
                                    emitln!(
                                        self.writer(),
                                        "{} := {};",
                                        str_local(dest),
                                        str_local(src),
                                    );
                                    emit!(
                                        self.writer(),
                                        "assume {} <= $MAX_U{};",
                                        str_local(dest),
                                        target_base,
                                    );
                                }
                            }
                        };
                        let target_base = match oper {
                            CastU8 => 8,
                            CastU16 => 16,
                            CastU32 => 32,
                            CastU64 => 64,
                            CastU128 => 128,
                            CastU256 => 256,
                            _ => unreachable!(),
                        };
                        make_cast(target_base, src, dest);
                    }
                    Not => {
                        let src = srcs[0];
                        let dest = dests[0];
                        emitln!(
                            self.writer(),
                            "call {} := $Not({});",
                            str_local(dest),
                            str_local(src)
                        );
                    }
                    Add => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        let unchecked = if fun_target
                            .is_pragma_true(ADDITION_OVERFLOW_UNCHECKED_PRAGMA, || false)
                        {
                            "_unchecked"
                        } else {
                            ""
                        };
                        let num_oper = global_state
                            .get_temp_index_oper(mid, fid, dest, baseline_flag)
                            .unwrap();
                        let bv_flag = self.bv_flag(num_oper);

                        let add_type = match &self.get_local_type(dest) {
                            Type::Primitive(PrimitiveType::U8) => {
                                boogie_num_type_string_capital("8", bv_flag)
                            }
                            Type::Primitive(PrimitiveType::U16) => format!(
                                "{}{}",
                                boogie_num_type_string_capital("16", bv_flag),
                                unchecked
                            ),
                            Type::Primitive(PrimitiveType::U32) => format!(
                                "{}{}",
                                boogie_num_type_string_capital("32", bv_flag),
                                unchecked
                            ),
                            Type::Primitive(PrimitiveType::U64) => format!(
                                "{}{}",
                                boogie_num_type_string_capital("64", bv_flag),
                                unchecked
                            ),
                            Type::Primitive(PrimitiveType::U128) => format!(
                                "{}{}",
                                boogie_num_type_string_capital("128", bv_flag),
                                unchecked
                            ),
                            Type::Primitive(PrimitiveType::U256) => format!(
                                "{}{}",
                                boogie_num_type_string_capital("256", bv_flag),
                                unchecked
                            ),
                            Type::Primitive(_)
                            | Type::Tuple(_)
                            | Type::Vector(_)
                            | Type::Datatype(_, _, _)
                            | Type::TypeParameter(_)
                            | Type::Reference(_, _)
                            | Type::Fun(_, _)
                            | Type::TypeDomain(_)
                            | Type::ResourceDomain(_, _, _)
                            | Type::Error
                            | Type::Var(_) => unreachable!(),
                        };
                        emitln!(
                            self.writer(),
                            "call {} := $Add{}({}, {});",
                            str_local(dest),
                            add_type,
                            str_local(op1),
                            str_local(op2)
                        );
                    }
                    Sub => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        let num_oper = global_state
                            .get_temp_index_oper(mid, fid, dest, baseline_flag)
                            .unwrap();
                        let bv_flag = self.bv_flag(num_oper);
                        if bv_flag {
                            let sub_type = match &self.get_local_type(dest) {
                                Type::Primitive(PrimitiveType::U8) => "Bv8".to_string(),
                                Type::Primitive(PrimitiveType::U16) => "Bv16".to_string(),
                                Type::Primitive(PrimitiveType::U32) => "Bv32".to_string(),
                                Type::Primitive(PrimitiveType::U64) => "Bv64".to_string(),
                                Type::Primitive(PrimitiveType::U128) => "Bv128".to_string(),
                                Type::Primitive(PrimitiveType::U256) => "Bv256".to_string(),
                                Type::Primitive(_)
                                | Type::Tuple(_)
                                | Type::Vector(_)
                                | Type::Datatype(_, _, _)
                                | Type::TypeParameter(_)
                                | Type::Reference(_, _)
                                | Type::Fun(_, _)
                                | Type::TypeDomain(_)
                                | Type::ResourceDomain(_, _, _)
                                | Type::Error
                                | Type::Var(_) => unreachable!(),
                            };
                            emitln!(
                                self.writer(),
                                "call {} := $Sub{}({}, {});",
                                str_local(dest),
                                sub_type,
                                str_local(op1),
                                str_local(op2)
                            );
                        } else {
                            emitln!(
                                self.writer(),
                                "call {} := $Sub({}, {});",
                                str_local(dest),
                                str_local(op1),
                                str_local(op2)
                            );
                        }
                    }
                    Mul => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        let num_oper = global_state
                            .get_temp_index_oper(mid, fid, dest, baseline_flag)
                            .unwrap();
                        let bv_flag = self.bv_flag(num_oper);
                        let mul_type = match &self.get_local_type(dest) {
                            Type::Primitive(PrimitiveType::U8) => {
                                boogie_num_type_string_capital("8", bv_flag)
                            }
                            Type::Primitive(PrimitiveType::U16) => {
                                boogie_num_type_string_capital("16", bv_flag)
                            }
                            Type::Primitive(PrimitiveType::U32) => {
                                boogie_num_type_string_capital("32", bv_flag)
                            }
                            Type::Primitive(PrimitiveType::U64) => {
                                boogie_num_type_string_capital("64", bv_flag)
                            }
                            Type::Primitive(PrimitiveType::U128) => {
                                boogie_num_type_string_capital("128", bv_flag)
                            }
                            Type::Primitive(PrimitiveType::U256) => {
                                boogie_num_type_string_capital("256", bv_flag)
                            }
                            Type::Primitive(_)
                            | Type::Tuple(_)
                            | Type::Vector(_)
                            | Type::Datatype(_, _, _)
                            | Type::TypeParameter(_)
                            | Type::Reference(_, _)
                            | Type::Fun(_, _)
                            | Type::TypeDomain(_)
                            | Type::ResourceDomain(_, _, _)
                            | Type::Error
                            | Type::Var(_) => unreachable!(),
                        };
                        emitln!(
                            self.writer(),
                            "call {} := $Mul{}({}, {});",
                            str_local(dest),
                            mul_type,
                            str_local(op1),
                            str_local(op2)
                        );
                    }
                    Div => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        let num_oper = global_state
                            .get_temp_index_oper(mid, fid, dest, baseline_flag)
                            .unwrap();
                        let bv_flag = self.bv_flag(num_oper);
                        let div_type = if bv_flag {
                            match &self.get_local_type(dest) {
                                Type::Primitive(PrimitiveType::U8) => "Bv8".to_string(),
                                Type::Primitive(PrimitiveType::U16) => "Bv16".to_string(),
                                Type::Primitive(PrimitiveType::U32) => "Bv32".to_string(),
                                Type::Primitive(PrimitiveType::U64) => "Bv64".to_string(),
                                Type::Primitive(PrimitiveType::U128) => "Bv128".to_string(),
                                Type::Primitive(PrimitiveType::U256) => "Bv256".to_string(),
                                Type::Primitive(_)
                                | Type::Tuple(_)
                                | Type::Vector(_)
                                | Type::Datatype(_, _, _)
                                | Type::TypeParameter(_)
                                | Type::Reference(_, _)
                                | Type::Fun(_, _)
                                | Type::TypeDomain(_)
                                | Type::ResourceDomain(_, _, _)
                                | Type::Error
                                | Type::Var(_) => unreachable!(),
                            }
                        } else {
                            "".to_string()
                        };
                        emitln!(
                            self.writer(),
                            "call {} := $Div{}({}, {});",
                            str_local(dest),
                            div_type,
                            str_local(op1),
                            str_local(op2)
                        );
                    }
                    Mod => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        let num_oper = global_state
                            .get_temp_index_oper(mid, fid, dest, baseline_flag)
                            .unwrap();
                        let bv_flag = self.bv_flag(num_oper);
                        let mod_type = if bv_flag {
                            match &self.get_local_type(dest) {
                                Type::Primitive(PrimitiveType::U8) => "Bv8".to_string(),
                                Type::Primitive(PrimitiveType::U16) => "Bv16".to_string(),
                                Type::Primitive(PrimitiveType::U32) => "Bv32".to_string(),
                                Type::Primitive(PrimitiveType::U64) => "Bv64".to_string(),
                                Type::Primitive(PrimitiveType::U128) => "Bv128".to_string(),
                                Type::Primitive(PrimitiveType::U256) => "Bv256".to_string(),
                                Type::Primitive(_)
                                | Type::Tuple(_)
                                | Type::Vector(_)
                                | Type::Datatype(_, _, _)
                                | Type::TypeParameter(_)
                                | Type::Reference(_, _)
                                | Type::Fun(_, _)
                                | Type::TypeDomain(_)
                                | Type::ResourceDomain(_, _, _)
                                | Type::Error
                                | Type::Var(_) => unreachable!(),
                            }
                        } else {
                            "".to_string()
                        };
                        emitln!(
                            self.writer(),
                            "call {} := $Mod{}({}, {});",
                            str_local(dest),
                            mod_type,
                            str_local(op1),
                            str_local(op2)
                        );
                    }
                    Shl | Shr => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        let sh_oper_str = if oper == &Shl { "Shl" } else { "Shr" };
                        let num_oper = global_state
                            .get_temp_index_oper(mid, fid, dest, baseline_flag)
                            .unwrap();
                        let bv_flag = self.bv_flag(num_oper);
                        if bv_flag {
                            let target_type = match &self.get_local_type(dest) {
                                Type::Primitive(PrimitiveType::U8) => "Bv8",
                                Type::Primitive(PrimitiveType::U16) => "Bv16",
                                Type::Primitive(PrimitiveType::U32) => "Bv32",
                                Type::Primitive(PrimitiveType::U64) => "Bv64",
                                Type::Primitive(PrimitiveType::U128) => "Bv128",
                                Type::Primitive(PrimitiveType::U256) => "Bv256",
                                Type::Primitive(_)
                                | Type::Tuple(_)
                                | Type::Vector(_)
                                | Type::Datatype(_, _, _)
                                | Type::TypeParameter(_)
                                | Type::Reference(_, _)
                                | Type::Fun(_, _)
                                | Type::TypeDomain(_)
                                | Type::ResourceDomain(_, _, _)
                                | Type::Error
                                | Type::Var(_) => unreachable!(),
                            };
                            let src_type = boogie_num_type_base(&self.get_local_type(op2));
                            emitln!(
                                self.writer(),
                                "call {} := ${}{}From{}({}, {});",
                                str_local(dest),
                                sh_oper_str,
                                target_type,
                                src_type,
                                str_local(op1),
                                str_local(op2)
                            );
                        } else {
                            let sh_type = match &self.get_local_type(dest) {
                                Type::Primitive(PrimitiveType::U8) => "U8",
                                Type::Primitive(PrimitiveType::U16) => "U16",
                                Type::Primitive(PrimitiveType::U32) => "U32",
                                Type::Primitive(PrimitiveType::U64) => "U64",
                                Type::Primitive(PrimitiveType::U128) => "U128",
                                Type::Primitive(PrimitiveType::U256) => "U256",
                                Type::Primitive(_)
                                | Type::Tuple(_)
                                | Type::Vector(_)
                                | Type::Datatype(_, _, _)
                                | Type::TypeParameter(_)
                                | Type::Reference(_, _)
                                | Type::Fun(_, _)
                                | Type::TypeDomain(_)
                                | Type::ResourceDomain(_, _, _)
                                | Type::Error
                                | Type::Var(_) => unreachable!(),
                            };
                            emitln!(
                                self.writer(),
                                "call {} := ${}{}({}, {});",
                                str_local(dest),
                                sh_oper_str,
                                sh_type,
                                str_local(op1),
                                str_local(op2)
                            );
                        }
                    }
                    Lt | Le | Gt | Ge => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        let make_comparison = |comp_oper: &str, op1, op2, dest| {
                            let num_oper = global_state
                                .get_temp_index_oper(mid, fid, op1, baseline_flag)
                                .unwrap();
                            let bv_flag = self.bv_flag(num_oper);
                            let lt_type = if bv_flag {
                                match &self.get_local_type(op1) {
                                    Type::Primitive(PrimitiveType::U8) => "Bv8".to_string(),
                                    Type::Primitive(PrimitiveType::U16) => "Bv16".to_string(),
                                    Type::Primitive(PrimitiveType::U32) => "Bv32".to_string(),
                                    Type::Primitive(PrimitiveType::U64) => "Bv64".to_string(),
                                    Type::Primitive(PrimitiveType::U128) => "Bv128".to_string(),
                                    Type::Primitive(PrimitiveType::U256) => "Bv256".to_string(),
                                    Type::Primitive(_)
                                    | Type::Tuple(_)
                                    | Type::Vector(_)
                                    | Type::Datatype(_, _, _)
                                    | Type::TypeParameter(_)
                                    | Type::Reference(_, _)
                                    | Type::Fun(_, _)
                                    | Type::TypeDomain(_)
                                    | Type::ResourceDomain(_, _, _)
                                    | Type::Error
                                    | Type::Var(_) => unreachable!(),
                                }
                            } else {
                                "".to_string()
                            };
                            emitln!(
                                self.writer(),
                                "call {} := {}{}({}, {});",
                                str_local(dest),
                                comp_oper,
                                lt_type,
                                str_local(op1),
                                str_local(op2)
                            );
                        };
                        let comp_oper = match oper {
                            Lt => "$Lt",
                            Le => "$Le",
                            Gt => "$Gt",
                            Ge => "$Ge",
                            _ => unreachable!(),
                        };
                        make_comparison(comp_oper, op1, op2, dest);
                    }
                    Or => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        emitln!(
                            self.writer(),
                            "call {} := $Or({}, {});",
                            str_local(dest),
                            str_local(op1),
                            str_local(op2)
                        );
                    }
                    And => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        emitln!(
                            self.writer(),
                            "call {} := $And({}, {});",
                            str_local(dest),
                            str_local(op1),
                            str_local(op2)
                        );
                    }
                    Eq | Neq => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        let num_oper = global_state
                            .get_temp_index_oper(mid, fid, op1, baseline_flag)
                            .unwrap();
                        let bv_flag = self.bv_flag(num_oper);
                        let oper = boogie_equality_for_type(
                            env,
                            oper == &Eq,
                            &self.get_local_type(op1),
                            bv_flag,
                        );
                        emitln!(
                            self.writer(),
                            "{} := {}({}, {});",
                            str_local(dest),
                            oper,
                            str_local(op1),
                            str_local(op2)
                        );
                    }
                    Xor | BitOr | BitAnd => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        let make_bitwise =
                            |bv_oper: &str, op1: TempIndex, op2: TempIndex, dest: TempIndex| {
                                let base = match &self.get_local_type(dest) {
                                    Type::Primitive(PrimitiveType::U8) => "Bv8".to_string(),
                                    Type::Primitive(PrimitiveType::U16) => "Bv16".to_string(),
                                    Type::Primitive(PrimitiveType::U32) => "Bv32".to_string(),
                                    Type::Primitive(PrimitiveType::U64) => "Bv64".to_string(),
                                    Type::Primitive(PrimitiveType::U128) => "Bv128".to_string(),
                                    Type::Primitive(PrimitiveType::U256) => "Bv256".to_string(),
                                    Type::Primitive(_)
                                    | Type::Tuple(_)
                                    | Type::Vector(_)
                                    | Type::Datatype(_, _, _)
                                    | Type::TypeParameter(_)
                                    | Type::Reference(_, _)
                                    | Type::Fun(_, _)
                                    | Type::TypeDomain(_)
                                    | Type::ResourceDomain(_, _, _)
                                    | Type::Error
                                    | Type::Var(_) => unreachable!(),
                                };
                                let op1_ty = &self.get_local_type(op1);
                                let op2_ty = &self.get_local_type(op2);
                                let num_oper_1 = global_state
                                    .get_temp_index_oper(mid, fid, op1, baseline_flag)
                                    .unwrap();
                                let op1_bv_flag = self.bv_flag(num_oper_1);
                                let num_oper_2 = global_state
                                    .get_temp_index_oper(mid, fid, op2, baseline_flag)
                                    .unwrap();
                                let op2_bv_flag = self.bv_flag(num_oper_2);
                                let op1_str = if !op1_bv_flag {
                                    format!(
                                        "$int2bv.{}({})",
                                        boogie_num_type_base(op1_ty),
                                        str_local(op1)
                                    )
                                } else {
                                    str_local(op1)
                                };
                                let op2_str = if !op2_bv_flag {
                                    format!(
                                        "$int2bv.{}({})",
                                        boogie_num_type_base(op2_ty),
                                        str_local(op2)
                                    )
                                } else {
                                    str_local(op2)
                                };
                                emitln!(
                                    self.writer(),
                                    "call {} := {}{}({}, {});",
                                    str_local(dest),
                                    bv_oper,
                                    base,
                                    op1_str,
                                    op2_str
                                );
                            };
                        let bv_oper_str = match oper {
                            Xor => "$Xor",
                            BitOr => "$Or",
                            BitAnd => "$And",
                            _ => unreachable!(),
                        };
                        if self.parent.targets.prover_options().bv_int_encoding {
                            emitln!(
                                self.writer(),
                                "call {} := {}Int'u{}'({}, {});",
                                str_local(dest),
                                bv_oper_str,
                                boogie_num_type_base(&self.get_local_type(dest)),
                                str_local(op1),
                                str_local(op2),
                            );
                        } else {
                            make_bitwise(bv_oper_str, op1, op2, dest);
                        }
                    }
                    Uninit => {
                        emitln!(
                            self.writer(),
                            "assume $t{}->l == $Uninitialized();",
                            srcs[0]
                        );
                    }
                    Destroy => {}
                    TraceLocal(idx) => {
                        let num_oper = global_state
                            .get_temp_index_oper(mid, fid, srcs[0], baseline_flag)
                            .unwrap();
                        let bv_flag = self.bv_flag(num_oper);
                        self.track_local(*idx, srcs[0], bv_flag);
                    }
                    TraceReturn(i) => {
                        let oper_map = global_state.get_ret_map();
                        let bv_flag = self.bv_flag_from_map(&srcs[0], oper_map);
                        self.track_return(*i, srcs[0], bv_flag);
                    }
                    TraceAbort => self.track_abort(&str_local(srcs[0])),
                    TraceExp(kind, node_id) => {
                        let bv_flag = *global_state
                            .get_temp_index_oper(mid, fid, srcs[0], baseline_flag)
                            .unwrap()
                            == Bitwise;
                        self.track_exp(*kind, *node_id, srcs[0], bv_flag)
                    }
                    TraceMessage(message) => emitln!(
                        self.writer(),
                        "assume {{:print \"$info():{}\"}} true;",
                        message,
                    ),
                    TraceGhost(ghost_type, value_type) => {
                        let instantiated_ghost_type = ghost_type.instantiate(self.type_inst);
                        let instantiated_value_type = value_type.instantiate(self.type_inst);
                        self.parent.add_type(&instantiated_ghost_type);
                        self.parent.add_type(&instantiated_value_type);
                        emitln!(
                            self.writer(),
                            "assume {{:print \"$track_ghost({},{}):\", {}}} true;",
                            boogie_type_suffix(self.parent.env, &instantiated_ghost_type),
                            boogie_type_suffix(self.parent.env, &instantiated_value_type),
                            boogie_spec_global_var_name(
                                self.parent.env,
                                &vec![instantiated_ghost_type, instantiated_value_type]
                            ),
                        )
                    }
                    EmitEvent => {
                        let msg = srcs[0];
                        let handle = srcs[1];
                        let suffix = boogie_type_suffix(env, &self.get_local_type(msg));
                        emit!(
                            self.writer(),
                            "$es := ${}ExtendEventStore'{}'($es, ",
                            if srcs.len() > 2 { "Cond" } else { "" },
                            suffix
                        );
                        emit!(self.writer(), "{}, {}", str_local(handle), str_local(msg));
                        if srcs.len() > 2 {
                            emit!(self.writer(), ", {}", str_local(srcs[2]));
                        }
                        emitln!(self.writer(), ");");
                    }
                    EventStoreDiverge => {
                        emitln!(self.writer(), "call $es := $EventStore__diverge($es);");
                    }
                    TraceGlobalMem(mem) => {
                        let mem = &mem.to_owned().instantiate(self.type_inst);
                        let node_id = env.new_node(env.unknown_loc(), mem.to_type());
                        self.track_global_mem(mem, node_id);
                    }
                    IfThenElse => {
                        let cond_str = str_local(srcs[0]);
                        let true_expr_str = str_local(srcs[1]);
                        let false_expr_str = str_local(srcs[2]);
                        let dest_str = str_local(dests[0]);
                        emitln!(
                            self.writer(),
                            "{} := (if {} then {} else {});",
                            dest_str,
                            cond_str,
                            true_expr_str,
                            false_expr_str
                        );
                    }
                    Quantifier(qt, qid, inst, li) => {
                        let fun_env = self.parent.env.get_function(*qid);
                        let inst = &self.inst_slice(inst);
                        let fun_name =
                            boogie_function_name(&fun_env, inst, FunctionTranslationStyle::Pure);

                        let loc_type =
                            if qt.vector_based() || matches!(qt, QuantifierType::RangeMap) {
                                self.get_local_type(dests[0]).instantiate(inst)
                            } else {
                                fun_env.get_parameter_types()[0]
                                    .skip_reference()
                                    .instantiate(inst)
                            };
                        let suffix = boogie_type_suffix(env, &loc_type);

                        let cr_args = |local_name: &str| {
                            if !qt.vector_based() {
                                srcs.iter()
                                    .skip(if qt.range_based() { 2 } else { 0 })
                                    .enumerate()
                                    .map(|(index, vidx)| {
                                        if index == *li {
                                            local_name.to_string()
                                        } else {
                                            format!("$t{}", vidx)
                                        }
                                    })
                                    .join(", ")
                            } else {
                                srcs.iter()
                                    .skip(if qt.range_based() { 3 } else { 1 })
                                    .enumerate()
                                    .map(|(index, vidx)| {
                                        if index == *li {
                                            format!("ReadVec($t{}, {})", srcs[0], local_name)
                                        } else {
                                            format!("$t{}", vidx)
                                        }
                                    })
                                    .join(", ")
                            }
                        };

                        // srcs[0] is the source vector for vector-based quantifiers
                        // srcs[1] and srcs[2] are the range bounds for range-based quantifiers [start, end)

                        match qt {
                            QuantifierType::Forall => {
                                let b_type = boogie_type(env, &loc_type);
                                emitln!(
                                    self.writer(),
                                    "$t{} := (forall x: {} :: $IsValid'{}'(x) ==> {}({}));",
                                    dests[0],
                                    b_type,
                                    suffix,
                                    fun_name,
                                    cr_args("x")
                                );
                            }
                            QuantifierType::Exists => {
                                let b_type = boogie_type(env, &loc_type);
                                emitln!(
                                    self.writer(),
                                    "$t{} := (exists x: {} :: $IsValid'{}'(x) && {}({}));",
                                    dests[0],
                                    b_type,
                                    suffix,
                                    fun_name,
                                    cr_args("x")
                                );
                            }
                            QuantifierType::Map => {
                                emitln!(self.writer(), "havoc $t{};", dests[0]);
                                emitln!(
                                    self.writer(),
                                    "assume LenVec($t{}) == LenVec($t{});",
                                    dests[0],
                                    srcs[0]
                                );
                                emitln!(self.writer(), "assume (forall i:int :: 0 <= i && i < LenVec($t{}) ==> ReadVec($t{}, i) == {}({}));", srcs[0], dests[0], fun_name, cr_args("i"));
                                emitln!(
                                    self.writer(),
                                    "assume $IsValid'{}'($t{});",
                                    suffix,
                                    dests[0]
                                );
                            }
                            QuantifierType::MapRange => {
                                emitln!(self.writer(), "havoc $t{};", dests[0]);
                                emitln!(
                                    self.writer(),
                                    "assume $t{} <= $t{} ==> LenVec($t{}) == ($t{} - $t{});",
                                    srcs[1],
                                    srcs[2],
                                    dests[0],
                                    srcs[2],
                                    srcs[1]
                                );
                                emitln!(self.writer(), "assume (forall i:int :: $t{} <= i && i < $t{} ==> ReadVec($t{}, i - $t{}) == {}({}));", srcs[1], srcs[2], dests[0], srcs[1], fun_name, cr_args("i"));
                                emitln!(
                                    self.writer(),
                                    "assume $IsValid'{}'($t{});",
                                    suffix,
                                    dests[0]
                                );
                            }
                            QuantifierType::RangeMap => {
                                emitln!(self.writer(), "havoc $t{};", dests[0]);
                                emitln!(
                                    self.writer(),
                                    "assume LenVec($t{}) == (if $t{} <= $t{} then $t{} - $t{} else 0);",
                                    dests[0],
                                    srcs[0],
                                    srcs[1],
                                    srcs[1],
                                    srcs[0]
                                );
                                emitln!(self.writer(), "assume (forall i: int :: InRangeVec($t{}, i) ==> ReadVec($t{}, i) == {}({}));", dests[0], dests[0], fun_name, cr_args(&format!("i + $t{}", srcs[0])));
                                emitln!(
                                    self.writer(),
                                    "assume $IsValid'{}'($t{});",
                                    suffix,
                                    dests[0]
                                );
                            }
                            QuantifierType::Any => {
                                emitln!(self.writer(), "$t{} := (exists i:int :: 0 <= i && i < LenVec($t{}) && {}({}));", dests[0], srcs[0], fun_name, cr_args("i"));
                            }
                            QuantifierType::AnyRange => {
                                emitln!(
                                    self.writer(),
                                    "$t{} := (exists i:int :: $t{} <= i && i < $t{} && {}({}));",
                                    dests[0],
                                    srcs[1],
                                    srcs[2],
                                    fun_name,
                                    cr_args("i")
                                );
                            }
                            QuantifierType::All => {
                                emitln!(self.writer(), "$t{} := (forall i:int :: 0 <= i && i < LenVec($t{}) ==> {}({}));", dests[0], srcs[0], fun_name, cr_args("i"));
                            }
                            QuantifierType::AllRange => {
                                emitln!(
                                    self.writer(),
                                    "$t{} := (forall i:int :: $t{} <= i && i < $t{} ==> {}({}));",
                                    dests[0],
                                    srcs[1],
                                    srcs[2],
                                    fun_name,
                                    cr_args("i")
                                );
                            }
                            QuantifierType::Find => {
                                emitln!(self.writer(), "havoc $find_exists;");
                                emitln!(self.writer(), "$find_exists := (exists i:int :: 0 <= i && i < LenVec($t{}) && {}({}));", srcs[0], fun_name, cr_args("i"));
                                emitln!(self.writer(), "if ($find_exists) {");
                                emitln!(self.writer(), "    havoc $find_i;");
                                emitln!(
                                    self.writer(),
                                    "    assume 0 <= $find_i && $find_i < LenVec($t{});",
                                    srcs[0]
                                );
                                emitln!(
                                    self.writer(),
                                    "    assume {}({});",
                                    fun_name,
                                    cr_args("$find_i")
                                );
                                emitln!(self.writer(), "    assume (forall j:int :: 0 <= j && j < $find_i ==> !{}({}));", fun_name, cr_args("j"));
                                emitln!(
                                    self.writer(),
                                    "    $t{} := {}(MakeVec1(ReadVec($t{}, $find_i)));",
                                    dests[0],
                                    suffix,
                                    srcs[0]
                                );
                                emitln!(self.writer(), "} else {");
                                emitln!(
                                    self.writer(),
                                    "    $t{} := {}(EmptyVec());",
                                    dests[0],
                                    suffix
                                );
                                emitln!(self.writer(), "}");
                            }
                            QuantifierType::FindRange => {
                                emitln!(self.writer(), "havoc $find_exists;");
                                emitln!(self.writer(), "$find_exists := (exists i:int :: $t{} <= i && i < $t{} && {}({}));", srcs[1], srcs[2], fun_name, cr_args("i"));
                                emitln!(self.writer(), "if ($find_exists) {");
                                emitln!(self.writer(), "    havoc $find_i;");
                                emitln!(
                                    self.writer(),
                                    "    assume $t{} <= $find_i && $find_i < $t{};",
                                    srcs[1],
                                    srcs[2]
                                );
                                emitln!(
                                    self.writer(),
                                    "    assume {}({});",
                                    fun_name,
                                    cr_args("$find_i")
                                );
                                emitln!(self.writer(), "    assume (forall j:int :: $t{} <= j && j < $find_i ==> !{}({}));", srcs[1], fun_name, cr_args("j"));
                                emitln!(
                                    self.writer(),
                                    "    $t{} := {}(MakeVec1(ReadVec($t{}, $find_i)));",
                                    dests[0],
                                    suffix,
                                    srcs[0]
                                );
                                emitln!(self.writer(), "} else {");
                                emitln!(
                                    self.writer(),
                                    "    $t{} := {}(EmptyVec());",
                                    dests[0],
                                    suffix
                                );
                                emitln!(self.writer(), "}");
                            }
                            QuantifierType::FindIndex => {
                                emitln!(self.writer(), "havoc $find_exists;");
                                emitln!(self.writer(), "$find_exists := (exists i:int :: 0 <= i && i < LenVec($t{}) && {}({}));", srcs[0], fun_name, cr_args("i"));
                                emitln!(self.writer(), "if ($find_exists) {");
                                emitln!(self.writer(), "    havoc $find_i;");
                                emitln!(
                                    self.writer(),
                                    "    assume 0 <= $find_i && $find_i < LenVec($t{});",
                                    srcs[0]
                                );
                                emitln!(
                                    self.writer(),
                                    "    assume {}({});",
                                    fun_name,
                                    cr_args("$find_i")
                                );
                                emitln!(self.writer(), "    assume (forall j:int :: 0 <= j && j < $find_i ==> !{}({}));", fun_name, cr_args("j"));
                                emitln!(
                                    self.writer(),
                                    "    $t{} := $1_option_Option'u64'(MakeVec1($find_i));",
                                    dests[0]
                                );
                                emitln!(self.writer(), "} else {");
                                emitln!(
                                    self.writer(),
                                    "    $t{} := $1_option_Option'u64'(EmptyVec());",
                                    dests[0]
                                );
                                emitln!(self.writer(), "}");
                            }
                            QuantifierType::FindIndexRange => {
                                emitln!(self.writer(), "havoc $find_exists;");
                                emitln!(self.writer(), "$find_exists := (exists i:int :: $t{} <= i && i < $t{} && {}({}));", srcs[1], srcs[2], fun_name, cr_args("i"));
                                emitln!(self.writer(), "if ($find_exists) {");
                                emitln!(self.writer(), "    havoc $find_i;");
                                emitln!(
                                    self.writer(),
                                    "    assume $t{} <= $find_i && $find_i < $t{};",
                                    srcs[1],
                                    srcs[2]
                                );
                                emitln!(
                                    self.writer(),
                                    "    assume {}({});",
                                    fun_name,
                                    cr_args("$find_i")
                                );
                                emitln!(self.writer(), "    assume (forall j:int :: $t{} <= j && j < $find_i ==> !{}({}));", srcs[1], fun_name, cr_args("j"));
                                emitln!(
                                    self.writer(),
                                    "    $t{} := $1_option_Option'u64'(MakeVec1($find_i));",
                                    dests[0]
                                );
                                emitln!(self.writer(), "} else {");
                                emitln!(
                                    self.writer(),
                                    "    $t{} := $1_option_Option'u64'(EmptyVec());",
                                    dests[0]
                                );
                                emitln!(self.writer(), "}");
                            }
                            QuantifierType::Count => {
                                emitln!(self.writer(), "havoc $quantifier_temp_vec;");
                                emitln!(
                                    self.writer(),
                                    "assume LenVec($quantifier_temp_vec) == LenVec($t{});",
                                    srcs[0]
                                );
                                emitln!(self.writer(), "assume (forall i:int :: 0 <= i && i < LenVec($quantifier_temp_vec) ==> ReadVec($quantifier_temp_vec, i) == (if {}({}) then 1 else 0));", fun_name, cr_args("i"));
                                emitln!(self.writer(), "$t{} := $0_vec_$sum'u64'($quantifier_temp_vec, 0, LenVec($quantifier_temp_vec));", dests[0]);
                            }
                            QuantifierType::CountRange => {
                                emitln!(self.writer(), "havoc $quantifier_temp_vec;");
                                emitln!(
                                    self.writer(),
                                    "assume LenVec($quantifier_temp_vec) == LenVec($t{});",
                                    srcs[0]
                                );
                                emitln!(self.writer(), "assume (forall i:int :: 0 <= i && i < LenVec($quantifier_temp_vec) ==> ReadVec($quantifier_temp_vec, i) == (if {}({}) then 1 else 0));", fun_name, cr_args("i"));
                                emitln!(
                                    self.writer(),
                                    "$t{} := $0_vec_$sum'u64'($quantifier_temp_vec, $t{}, $t{});",
                                    dests[0],
                                    srcs[1],
                                    srcs[2]
                                );
                            }
                            QuantifierType::SumMap => {
                                emitln!(self.writer(), "havoc $quantifier_temp_vec;");
                                emitln!(
                                    self.writer(),
                                    "assume LenVec($quantifier_temp_vec) == LenVec($t{});",
                                    srcs[0]
                                );
                                emitln!(self.writer(), "assume (forall i:int :: 0 <= i && i < LenVec($quantifier_temp_vec) ==> ReadVec($quantifier_temp_vec, i) == {}({}));", fun_name, cr_args("i"));
                                emitln!(self.writer(), "$t{} := $0_vec_$sum'u64'($quantifier_temp_vec, 0, LenVec($quantifier_temp_vec));", dests[0]);
                            }
                            QuantifierType::SumMapRange => {
                                emitln!(self.writer(), "havoc $quantifier_temp_vec;");
                                emitln!(self.writer(), "assume $t{} <= $t{} ==> LenVec($quantifier_temp_vec) == ($t{} - $t{});", srcs[1], srcs[2], srcs[2], srcs[1]);
                                emitln!(self.writer(), "assume (forall i:int :: $t{} <= i && i < $t{} ==> ReadVec($quantifier_temp_vec, i - $t{}) ==  {}({}));", srcs[1], srcs[2], srcs[1], fun_name, cr_args("i"));
                                emitln!(self.writer(), "$t{} := $0_vec_$sum'u64'($quantifier_temp_vec, 0, LenVec($quantifier_temp_vec));", dests[0]);
                            }
                            QuantifierType::Filter => {
                                emitln!(self.writer(), "havoc $t{};", dests[0]);
                                emitln!(self.writer(), "havoc $quantifier_temp_vec;");
                                emitln!(
                                    self.writer(),
                                    "assume LenVec($quantifier_temp_vec) == LenVec($t{});",
                                    dests[0]
                                );
                                emitln!(
                                    self.writer(),
                                    "assume LenVec($t{}) <= LenVec($t{});",
                                    dests[0],
                                    srcs[0]
                                );
                                emitln!(self.writer(), "assume (forall i:int, j:int :: 0 <= i && i < j && j < LenVec($quantifier_temp_vec) ==> ReadVec($quantifier_temp_vec, i) < ReadVec($quantifier_temp_vec, j));");
                                emitln!(self.writer(), "assume (forall i:int :: 0 <= i && i < LenVec($quantifier_temp_vec) ==> 0 <= ReadVec($quantifier_temp_vec, i) && ReadVec($quantifier_temp_vec, i) < LenVec($t{}));", srcs[0]);
                                emitln!(self.writer(), "assume (forall i:int :: 0 <= i && i < LenVec($t{}) ==> ReadVec($t{}, i) == ReadVec($t{}, ReadVec($quantifier_temp_vec, i)));", dests[0], dests[0], srcs[0]);
                                emitln!(self.writer(), "assume (forall j:int :: 0 <= j && j < LenVec($t{}) ==> ({}({}) <==> ContainsVec($quantifier_temp_vec, j)));", srcs[0], fun_name, cr_args("j"));
                                emitln!(
                                    self.writer(),
                                    "assume $IsValid'{}'($t{});",
                                    suffix,
                                    dests[0]
                                );
                            }
                            QuantifierType::FilterRange => {
                                emitln!(self.writer(), "havoc $t{};", dests[0]);
                                emitln!(self.writer(), "havoc $quantifier_temp_vec;");
                                emitln!(
                                    self.writer(),
                                    "assume LenVec($quantifier_temp_vec) == LenVec($t{});",
                                    dests[0]
                                );
                                emitln!(
                                    self.writer(),
                                    "assume $t{} <= $t{} ==> LenVec($t{}) <= ($t{} - $t{});",
                                    srcs[1],
                                    srcs[2],
                                    dests[0],
                                    srcs[2],
                                    srcs[1]
                                );
                                emitln!(
                                    self.writer(),
                                    "assume $t{} > $t{} ==> LenVec($t{}) == 0;",
                                    srcs[1],
                                    srcs[2],
                                    dests[0]
                                );
                                emitln!(self.writer(), "assume (forall i:int, j:int :: 0 <= i && i < j && j < LenVec($quantifier_temp_vec) ==> ReadVec($quantifier_temp_vec, i) < ReadVec($quantifier_temp_vec, j));");
                                emitln!(self.writer(), "assume (forall i:int :: 0 <= i && i < LenVec($quantifier_temp_vec) ==> $t{} <= ReadVec($quantifier_temp_vec, i) && ReadVec($quantifier_temp_vec, i) < $t{});", srcs[1], srcs[2]);
                                emitln!(self.writer(), "assume (forall i:int :: 0 <= i && i < LenVec($t{}) ==> ReadVec($t{}, i) == ReadVec($t{}, ReadVec($quantifier_temp_vec, i)));", dests[0], dests[0], srcs[0]);
                                emitln!(self.writer(), "assume (forall j:int :: $t{} <= j && j < $t{} ==> ({}({}) <==> ContainsVec($quantifier_temp_vec, j)));", srcs[1], srcs[2], fun_name, cr_args("j"));
                                emitln!(
                                    self.writer(),
                                    "assume $IsValid'{}'($t{});",
                                    suffix,
                                    dests[0]
                                );
                            }
                            QuantifierType::FindIndices => {
                                emitln!(self.writer(), "havoc $t{};", dests[0]);
                                emitln!(
                                    self.writer(),
                                    "assume LenVec($t{}) <= LenVec($t{});",
                                    dests[0],
                                    srcs[0]
                                );
                                emitln!(self.writer(), "assume (forall i:int, j:int :: 0 <= i && i < j && j < LenVec($t{}) ==> ReadVec($t{}, i) < ReadVec($t{}, j));", dests[0], dests[0], dests[0]);
                                emitln!(self.writer(), "assume (forall i:int :: 0 <= i && i < LenVec($t{}) ==> 0 <= ReadVec($t{}, i) && ReadVec($t{}, i) < LenVec($t{}));", dests[0], dests[0], dests[0], srcs[0]);
                                emitln!(self.writer(), "assume (forall i:int :: 0 <= i && i < LenVec($t{}) ==> {}({}));", dests[0], fun_name, cr_args(&format!("ReadVec($t{}, i)", dests[0])));
                                emitln!(self.writer(), "assume (forall i:int :: 0 <= i && i < LenVec($t{}) ==> ({}({}) <==> ContainsVec($t{}, i)));", srcs[0], fun_name, cr_args("i"), dests[0]);
                            }
                            QuantifierType::FindIndicesRange => {
                                emitln!(self.writer(), "havoc $t{};", dests[0]);
                                emitln!(
                                    self.writer(),
                                    "assume $t{} <= $t{} ==> LenVec($t{}) <= ($t{} - $t{});",
                                    srcs[1],
                                    srcs[2],
                                    dests[0],
                                    srcs[2],
                                    srcs[1]
                                );
                                emitln!(
                                    self.writer(),
                                    "assume $t{} > $t{} ==> LenVec($t{}) == 0;",
                                    srcs[1],
                                    srcs[2],
                                    dests[0]
                                );
                                emitln!(self.writer(), "assume (forall i:int, j:int :: 0 <= i && i < j && j < LenVec($t{}) ==> ReadVec($t{}, i) < ReadVec($t{}, j));", dests[0], dests[0], dests[0]);
                                emitln!(self.writer(), "assume (forall i:int :: 0 <= i && i < LenVec($t{}) ==> $t{} <= ReadVec($t{}, i) && ReadVec($t{}, i) < $t{});", dests[0], srcs[1], dests[0], dests[0], srcs[2]);
                                emitln!(self.writer(), "assume (forall i:int :: 0 <= i && i < LenVec($t{}) ==> {}({}));", dests[0], fun_name, cr_args(&format!("ReadVec($t{}, i)", dests[0])));
                                emitln!(self.writer(), "assume (forall i:int :: $t{} <= i && i < $t{} ==> ({}({}) <==> ContainsVec($t{}, i)));", srcs[1], srcs[2], fun_name, cr_args("i"), dests[0]);
                            }
                        }
                    }
                }
                match aa {
                    Some(AbortAction::Check) => match self.parent.asserts_mode {
                        AssertsMode::Check | AssertsMode::SpecNoAbortCheck => {
                            let message = if self.parent.options.func_abort_check_only {
                                "function code should not abort"
                            } else {
                                "code should not abort"
                            };
                            emitln!(
                                self.writer(),
                                "assert {{:msg \"assert_failed{}: {}\"}} !$abort_flag;",
                                self.loc_str(&self.writer().get_loc()),
                                message,
                            );
                        }
                        AssertsMode::Assume => {
                            emitln!(self.writer(), "assume !$abort_flag;");
                        }
                    },
                    None => {}
                }
            }
            Abort(_, src) => {
                match self.parent.asserts_mode {
                    AssertsMode::Check | AssertsMode::SpecNoAbortCheck => {
                        let message = if self.parent.options.func_abort_check_only {
                            "function code should not abort"
                        } else {
                            "code should not abort"
                        };
                        emitln!(
                            self.writer(),
                            "assert {{:msg \"assert_failed{}: {}\"}} false;",
                            self.loc_str(&self.writer().get_loc()),
                            message,
                        );
                    }
                    AssertsMode::Assume => {
                        emitln!(self.writer(), "assume false;");
                    }
                }
                let src_str = str_local(*src);
                let src_val = if self.parent.targets.prover_options().bv_int_encoding {
                    src_str
                } else {
                    format!("$bv2int.64({})", src_str)
                };
                emitln!(self.writer(), "$abort_code := {};", src_val);
                emitln!(self.writer(), "$abort_flag := true;");
                emitln!(self.writer(), "return;")
            }
            Nop(..) => {}
        }
        emitln!(self.writer());
    }

    fn translate_write_back(&self, dest: &BorrowNode, edge: &BorrowEdge, src: TempIndex) {
        use BorrowNode::*;
        let writer = self.parent.writer;
        let env = self.parent.env;
        let src_str = format!("$t{}", src);
        match dest {
            ReturnPlaceholder(_) => {
                unreachable!("unexpected transient borrow node")
            }
            GlobalRoot(memory) => {
                assert!(matches!(edge, BorrowEdge::Direct));
                let memory = &memory.to_owned().instantiate(self.type_inst);
                let memory_name = boogie_resource_memory_name(env, memory, &None);
                emitln!(
                    writer,
                    "{} := $ResourceUpdate({}, $GlobalLocationAddress({}),\n    \
                     $Dereference({}));",
                    memory_name,
                    memory_name,
                    src_str,
                    src_str
                );
            }
            SpecGlobalRoot(tys) => {
                assert!(matches!(edge, BorrowEdge::Direct));
                emitln!(
                    writer,
                    "{} := $Dereference({});",
                    boogie_spec_global_var_name(self.parent.env, tys),
                    src_str
                );
            }
            LocalRoot(idx) => {
                assert!(matches!(edge, BorrowEdge::Direct));
                emitln!(writer, "$t{} := $Dereference({});", idx, src_str);
            }
            Reference(idx) => {
                let dst_value = format!("$Dereference($t{})", idx);
                let src_value = format!("$Dereference({})", src_str);
                let get_path_index = |offset: usize| {
                    if offset == 0 {
                        format!("ReadVec({}->p, LenVec($t{}->p))", src_str, idx)
                    } else {
                        format!("ReadVec({}->p, LenVec($t{}->p) + {})", src_str, idx, offset)
                    }
                };

                let update = if let BorrowEdge::Hyper(edges) = edge {
                    self.translate_write_back_update(
                        &mut || dst_value.clone(),
                        &get_path_index,
                        src_value,
                        edges,
                        0,
                    )
                } else {
                    self.translate_write_back_update(
                        &mut || dst_value.clone(),
                        &get_path_index,
                        src_value,
                        &[edge.to_owned()],
                        0,
                    )
                };
                emitln!(
                    writer,
                    "$t{} := $UpdateMutation($t{}, {});",
                    idx,
                    idx,
                    update
                );
            }
        }
    }

    /// Returns read aggregate and write aggregate if fun_env matches one of the native functions
    /// implementing custom mutable borrow.
    fn get_borrow_native_aggregate_names(&self, fn_name: &String) -> Option<(String, String)> {
        for f in &self.parent.options.borrow_aggregates {
            if &f.name == fn_name {
                return Some((f.read_aggregate.clone(), f.write_aggregate.clone()));
            }
        }
        None
    }

    fn translate_write_back_update(
        &self,
        mk_dest: &mut dyn FnMut() -> String,
        get_path_index: &dyn Fn(usize) -> String,
        src: String,
        edges: &[BorrowEdge],
        at: usize,
    ) -> String {
        if at >= edges.len() {
            src
        } else {
            match &edges[at] {
                BorrowEdge::Direct => {
                    self.translate_write_back_update(mk_dest, get_path_index, src, edges, at + 1)
                }
                BorrowEdge::Field(memory, offset) => {
                    let memory = memory.to_owned().instantiate(self.type_inst);
                    let struct_env = &self.parent.env.get_struct_qid(memory.to_qualified_id());
                    let field_env = &struct_env.get_field_by_offset(*offset);
                    let sel_fun = boogie_field_sel(field_env, &memory.inst);
                    let new_dest = format!("{}->{}", (*mk_dest)(), sel_fun);
                    let mut new_dest_needed = false;
                    let new_src = self.translate_write_back_update(
                        &mut || {
                            new_dest_needed = true;
                            format!("$$sel{}", at)
                        },
                        get_path_index,
                        src,
                        edges,
                        at + 1,
                    );
                    let update_fun = boogie_field_update(field_env, &memory.inst);
                    if new_dest_needed {
                        format!(
                            "(var $$sel{} := {}; {}({}, {}))",
                            at,
                            new_dest,
                            update_fun,
                            (*mk_dest)(),
                            new_src
                        )
                    } else {
                        format!("{}({}, {})", update_fun, (*mk_dest)(), new_src)
                    }
                }
                BorrowEdge::EnumField(memory, offset, vid) => {
                    let memory = memory.to_owned().instantiate(self.type_inst);
                    let enum_env = &self.parent.env.get_enum_qid(memory.to_qualified_id());
                    let variant_env = &enum_env.get_variant(*vid);
                    let field_env = &variant_env.get_field_by_offset(*offset);

                    let update_fun = boogie_enum_field_update(field_env);
                    let sel_fun = boogie_enum_field_sel(field_env, &memory.inst);

                    let new_dest = format!("{}->{}", (*mk_dest)(), sel_fun);
                    let mut new_dest_needed = false;
                    let new_src = self.translate_write_back_update(
                        &mut || {
                            new_dest_needed = true;
                            format!("$$sel{}", at)
                        },
                        get_path_index,
                        src,
                        edges,
                        at + 1,
                    );
                    if new_dest_needed {
                        format!(
                            "(var $$sel{} := {}; {}({}, {}))",
                            at,
                            new_dest,
                            update_fun,
                            (*mk_dest)(),
                            new_src
                        )
                    } else {
                        format!("{}({}, {})", update_fun, (*mk_dest)(), new_src)
                    }
                }
                BorrowEdge::DynamicField(struct_qid, name_type, value_type) => {
                    let struct_env = &self.parent.env.get_struct_qid(struct_qid.to_qualified_id());
                    let instantiated_struct_qid = struct_qid.to_owned().instantiate(self.type_inst);
                    let instantiated_name_type = name_type.instantiate(self.type_inst);
                    let instantiated_value_type = value_type.instantiate(self.type_inst);
                    let sel_fun = boogie_dynamic_field_sel(
                        self.parent.env,
                        &instantiated_name_type,
                        &instantiated_value_type,
                    );
                    let update_fun = boogie_dynamic_field_update(
                        &struct_env,
                        &instantiated_struct_qid.inst,
                        &instantiated_name_type,
                        &instantiated_value_type,
                    );
                    let new_dest = format!("{}->{}", (*mk_dest)(), sel_fun);
                    let mut new_dest_needed = false;
                    let new_src = self.translate_write_back_update(
                        &mut || {
                            new_dest_needed = true;
                            format!("$$sel{}", at)
                        },
                        get_path_index,
                        src,
                        edges,
                        at + 1,
                    );
                    if new_dest_needed {
                        format!(
                            "(var $$sel{} := {}; {}({}, {}))",
                            at,
                            new_dest,
                            update_fun,
                            (*mk_dest)(),
                            new_src
                        )
                    } else {
                        format!("{}({}, {})", update_fun, (*mk_dest)(), new_src)
                    }
                }
                BorrowEdge::Index(index_edge_kind) => {
                    // Index edge is used for both vectors, tables, and custom native methods
                    // implementing similar functionality (mutable borrow). Determine which
                    // operations to use to read and update.
                    let (read_aggregate, update_aggregate) = match index_edge_kind {
                        IndexEdgeKind::Vector => ("ReadVec".to_string(), "UpdateVec".to_string()),
                        IndexEdgeKind::Table => ("GetTable".to_string(), "UpdateTable".to_string()),
                        IndexEdgeKind::Custom(name) => {
                            // panic here means that custom borrow natives options were not specified properly
                            self.get_borrow_native_aggregate_names(name).unwrap()
                        }
                    };

                    // Compute the offset into the path where to retrieve the index.
                    let offset = edges[0..at]
                        .iter()
                        .filter(|e| !matches!(e, BorrowEdge::Direct))
                        .count();
                    let index = (*get_path_index)(offset);
                    let new_dest = format!("{}({}, {})", read_aggregate, (*mk_dest)(), index);
                    let mut new_dest_needed = false;
                    // Recursively perform write backs for next edges
                    let new_src = self.translate_write_back_update(
                        &mut || {
                            new_dest_needed = true;
                            format!("$$sel{}", at)
                        },
                        get_path_index,
                        src,
                        edges,
                        at + 1,
                    );
                    if new_dest_needed {
                        format!(
                            "(var $$sel{} := {}; {}({}, {}, {}))",
                            at,
                            new_dest,
                            update_aggregate,
                            (*mk_dest)(),
                            index,
                            new_src
                        )
                    } else {
                        format!(
                            "{}({}, {}, {})",
                            update_aggregate,
                            (*mk_dest)(),
                            index,
                            new_src
                        )
                    }
                }
                BorrowEdge::Hyper(_) => unreachable!("unexpected borrow edge"),
            }
        }
    }

    /// Track location for execution trace, avoiding to track the same line multiple times.
    fn track_loc(&self, last_tracked_loc: &mut Option<(Loc, LineIndex)>, loc: &Loc) {
        let env = self.fun_target.global_env();
        if let Some(l) = env.get_location(loc) {
            if let Some((last_loc, last_line)) = last_tracked_loc {
                if *last_line == l.line {
                    // This line already tracked.
                    return;
                }
                *last_loc = loc.clone();
                *last_line = l.line;
            } else {
                *last_tracked_loc = Some((loc.clone(), l.line));
            }
            emitln!(
                self.writer(),
                "assume {{:print \"$at{}\"}} true;",
                self.loc_str(loc)
            );
        }
    }

    fn track_abort(&self, code_var: &str) {
        emitln!(
            self.writer(),
            &boogie_debug_track_abort(self.fun_target, code_var)
        );
    }

    /// Generates an update of the debug information about temporary.
    fn track_local(&self, origin_idx: TempIndex, idx: TempIndex, bv_flag: bool) {
        self.parent.add_type(&self.get_local_type(idx));
        emitln!(
            self.writer(),
            &boogie_debug_track_local(
                self.fun_target,
                origin_idx,
                idx,
                &self.get_local_type(idx),
                bv_flag
            )
        );
    }

    /// Generates an update of the debug information about the return value at given location.
    fn track_return(&self, return_idx: usize, idx: TempIndex, bv_flag: bool) {
        self.parent.add_type(&self.get_local_type(idx));
        emitln!(
            self.writer(),
            &boogie_debug_track_return(
                self.fun_target,
                return_idx,
                idx,
                &self.get_local_type(idx),
                bv_flag
            )
        );
    }

    /// Generates the bytecode to print out the value of mem.
    fn track_global_mem(&self, mem: &QualifiedInstId<DatatypeId>, node_id: NodeId) {
        let env = self.parent.env;
        let temp_str = boogie_resource_memory_name(env, mem, &None);
        emitln!(
            self.writer(),
            "assume {{:print \"$track_global_mem({}):\", {}}} true;",
            node_id.as_usize(),
            temp_str,
        );
    }

    fn track_exp(&self, kind: TraceKind, node_id: NodeId, temp: TempIndex, bv_flag: bool) {
        let env = self.parent.env;
        let ty = self.get_local_type(temp);
        let temp_str = if ty.is_reference() {
            let new_temp = boogie_temp(env, ty.skip_reference(), 0, bv_flag);
            emitln!(self.writer(), "{} := $Dereference($t{});", new_temp, temp);
            new_temp
        } else {
            format!("$t{}", temp)
        };
        let suffix = if kind == TraceKind::SubAuto {
            "_sub"
        } else {
            ""
        };
        emitln!(
            self.writer(),
            "assume {{:print \"$track_exp{}({}):\", {}}} true;",
            suffix,
            node_id.as_usize(),
            temp_str,
        );
    }

    fn loc_str(&self, loc: &Loc) -> String {
        let file_idx = self.fun_target.global_env().file_id_to_idx(loc.file_id());
        format!("({},{},{})", file_idx, loc.span().start(), loc.span().end())
    }

    fn compute_needed_temps(&self) -> BTreeMap<(String, bool), (Type, bool, usize)> {
        use Bytecode::*;
        use Operation::*;

        let fun_target = self.fun_target;
        let env = fun_target.global_env();

        let mut res: BTreeMap<(String, bool), (Type, bool, usize)> = BTreeMap::new();
        let mut need = |ty: &Type, bv_flag: bool, n: usize| {
            // Index by type suffix, which is more coarse grained then type.
            let ty = ty.skip_reference();
            let suffix = boogie_type_suffix(env, ty);
            let cnt = res
                .entry((suffix, bv_flag))
                .or_insert_with(|| (ty.to_owned(), bv_flag, 0));
            cnt.2 = cnt.2.max(n);
        };
        let baseline_flag = self.fun_target.data.variant == FunctionVariant::Baseline;
        let global_state = &self
            .fun_target
            .global_env()
            .get_extension::<GlobalNumberOperationState>()
            .expect("global number operation state");
        let ret_oper_map = &global_state.get_ret_map();
        let mid = fun_target.func_env.module_env.get_id();
        let fid = fun_target.func_env.get_id();

        for bc in &fun_target.data.code {
            match bc {
                Call(_, dests, oper, srcs, ..) => match oper {
                    TraceExp(_, id) => {
                        let ty = &self.inst(&env.get_node_type(*id));
                        let bv_flag = global_state.get_node_num_oper(*id) == Bitwise;
                        need(ty, bv_flag, 1)
                    }
                    TraceReturn(idx) => {
                        let ty = &self.inst(fun_target.get_return_type(*idx));
                        let bv_flag = self.bv_flag_from_map(idx, ret_oper_map);
                        need(ty, bv_flag, 1)
                    }
                    TraceLocal(_) => {
                        let ty = &self.get_local_type(srcs[0]);
                        let num_oper = &global_state
                            .get_temp_index_oper(mid, fid, srcs[0], baseline_flag)
                            .unwrap();
                        let bv_flag = self.bv_flag(num_oper);
                        need(ty, bv_flag, 1)
                    }
                    Havoc(HavocKind::MutationValue) => {
                        let ty = &self.get_local_type(dests[0]);
                        let num_oper = &global_state
                            .get_temp_index_oper(mid, fid, dests[0], baseline_flag)
                            .unwrap();
                        let bv_flag = self.bv_flag(num_oper);
                        need(ty, bv_flag, 1)
                    }
                    _ => {}
                },
                Prop(_, PropKind::Modifies, exp) => {
                    // global_state.exp_operation_map.get(exp.node_id()) == Bitwise;
                    //let bv_flag = env.get_node_num_oper(exp.node_id()) == Bitwise;
                    let bv_flag = global_state.get_node_num_oper(exp.node_id()) == Bitwise;
                    need(&BOOL_TYPE, false, 1);
                    need(&self.inst(&env.get_node_type(exp.node_id())), bv_flag, 1)
                }
                _ => {}
            }
        }
        res
    }
}

fn struct_has_native_equality(
    struct_env: &StructEnv<'_>,
    inst: &[Type],
    options: &BoogieOptions,
) -> bool {
    if options.native_equality {
        // Everything has native equality
        return true;
    }
    for field in struct_env.get_fields() {
        if !has_native_equality(
            struct_env.module_env.env,
            options,
            &field.get_type().instantiate(inst),
        ) {
            return false;
        }
    }
    true
}

fn enum_has_native_equality(
    enum_env: &EnumEnv<'_>,
    inst: &[Type],
    options: &BoogieOptions,
) -> bool {
    if options.native_equality {
        // Everything has native equality
        return true;
    }
    for variant in enum_env.get_variants() {
        for field in variant.get_fields() {
            if !has_native_equality(
                enum_env.module_env.env,
                options,
                &field.get_type().instantiate(inst),
            ) {
                return false;
            }
        }
    }
    true
}

pub fn has_native_equality(env: &GlobalEnv, options: &BoogieOptions, ty: &Type) -> bool {
    if options.native_equality {
        // Everything has native equality
        return true;
    }
    match ty {
        Type::Vector(..) => false,
        Type::Datatype(mid, did, inst) => match &env.get_struct_or_enum_qid(mid.qualified(*did)) {
            StructOrEnumEnv::Struct(struct_env) => {
                struct_has_native_equality(&struct_env, inst, options)
            }
            StructOrEnumEnv::Enum(enum_env) => enum_has_native_equality(&enum_env, inst, options),
        },
        Type::Primitive(_)
        | Type::Tuple(_)
        | Type::TypeParameter(_)
        | Type::Reference(_, _)
        | Type::Fun(_, _)
        | Type::TypeDomain(_)
        | Type::ResourceDomain(_, _, _)
        | Type::Error
        | Type::Var(_) => true,
    }
}

// Create a unique offset for the variant and field offset combination
fn variant_field_offset(variant_env: &VariantEnv<'_>, offset: usize) -> usize {
    (variant_env.get_tag() << 32) | offset
}
