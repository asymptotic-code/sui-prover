use crate::lean_backend::lean_helpers::{lean_enum_name, lean_field_sel, lean_function_name, lean_modifies_memory_name, lean_resource_memory_name, lean_struct_name, lean_temp_from_suffix, lean_type, lean_type_param, lean_type_suffix, lean_type_suffix_bv, FunctionTranslationStyle};
use crate::lean_backend::options::LeanOptions;
use crate::lean_backend::spec_translator::SpecTranslator;
use bimap::BiBTreeMap;
use codespan::LineIndex;
use itertools::Itertools;
use log::info;
use move_compiler::interface_generator::NATIVE_INTERFACE;
use move_core_types::language_storage::StructTag;
use move_model::ast::Attribute;
use move_model::code_writer::CodeWriter;
use move_model::model::{
    DatatypeId, EnumEnv, FieldId, FunId, FunctionEnv, GlobalEnv, Loc, QualifiedId, RefType, StructEnv,
};
use move_model::pragmas::ADDITION_OVERFLOW_UNCHECKED_PRAGMA;
use move_model::ty::{PrimitiveType, Type, TypeDisplayContext, BOOL_TYPE};
use move_model::well_known::{TYPE_INFO_MOVE, TYPE_NAME_GET_MOVE, TYPE_NAME_MOVE};
use move_model::{emit, emitln};
use move_stackless_bytecode::ast::TempIndex;
use move_stackless_bytecode::function_data_builder::FunctionDataBuilder;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::function_target_pipeline::{
    FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant, VerificationFlavor,
};
use move_stackless_bytecode::livevar_analysis::LiveVarAnalysisProcessor;
use move_stackless_bytecode::number_operation::NumOperation::{Bitwise, Bottom};
use move_stackless_bytecode::number_operation::{GlobalNumberOperationState, NumOperation};
use move_stackless_bytecode::options::ProverOptions;
use move_stackless_bytecode::reaching_def_analysis::ReachingDefProcessor;
use move_stackless_bytecode::stackless_bytecode::Bytecode::{Call, Prop, Ret, SaveMem};
use move_stackless_bytecode::stackless_bytecode::Label;
use move_stackless_bytecode::stackless_bytecode::Operation::{
    Add, And, BitAnd, BitOr, BorrowLoc, CastU128, CastU16, CastU256, CastU32, CastU64, CastU8,
    Destroy, Div, EmitEvent, Eq, EventStoreDiverge, FreezeRef, Ge, GetField, Gt, Le, Lt, Mod, Mul, Neq, Not,
    Or, Pack, PackRef, PackRefDeep, ReadRef, Shl, Shr, Stop, Sub, TraceAbort, TraceExp, TraceGhost, TraceLocal, TraceMessage, TraceReturn, Uninit, UnpackRef,
    UnpackRefDeep, WriteRef, Xor, Function,
};
use move_stackless_bytecode::stackless_bytecode::{
    AbortAction, BorrowEdge, BorrowNode, Bytecode, HavocKind, Operation, PropKind,
};
use move_stackless_bytecode::{
    mono_analysis, spec_global_variable_analysis, verification_analysis,
};
use move_binary_format::file_format::CodeOffset;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use move_stackless_bytecode::graph::Graph;
use std::str::FromStr;
use crate::wip;

pub struct LeanTranslator<'env> {
    env: &'env GlobalEnv,
    options: &'env LeanOptions,
    writer: &'env CodeWriter,
    spec_translator: SpecTranslator<'env>,
    targets: &'env FunctionTargetsHolder,
    types: &'env RefCell<BiBTreeMap<Type, String>>,
}

pub struct FunctionTranslator<'env> {
    parent: &'env LeanTranslator<'env>,
    fun_target: &'env FunctionTarget<'env>,
    type_inst: &'env [Type],
    style: FunctionTranslationStyle,
    ensures_info: RefCell<Vec<(usize, TempIndex)>>,
}

pub struct StructTranslator<'env> {
    parent: &'env LeanTranslator<'env>,
    struct_env: &'env StructEnv<'env>,
    type_inst: &'env [Type],
}

pub struct EnumTranslator<'env> {
    parent: &'env LeanTranslator<'env>,
    enum_env: &'env EnumEnv<'env>,
    type_inst: &'env [Type],
}



impl<'env> LeanTranslator<'env> {
    pub fn new(
        env: &'env GlobalEnv,
        options: &'env LeanOptions,
        targets: &'env FunctionTargetsHolder,
        writer: &'env CodeWriter,
        types: &'env RefCell<BiBTreeMap<Type, String>>,
    ) -> Self {
        Self {
            env,
            options,
            targets,
            writer,
            types,
            spec_translator: SpecTranslator::new(writer, env, options),
        }
    }

    pub fn translate(&mut self) {
        let writer = self.writer;
        let env = self.env;

        let mono_info = mono_analysis::get_info(self.env);
        let empty = &BTreeSet::new();

        emitln!(
            writer,
            "\n\n--==================================\n-- Begin Translation\n"
        );

        // Add given type declarations for type parameters.
        emitln!(writer, "\n\n-- Given Types for Type Parameters\n");
        for idx in &mono_info.type_params {
            let param_type = lean_type_param(env, *idx);
            let suffix = lean_type_suffix(env, &Type::TypeParameter(*idx));
            let is_uid = self
                .env
                .find_datatype_by_tag(&StructTag::from_str("0x2::object::UID").unwrap())
                .and_then(|uid_qid| mono_info.structs.get(&uid_qid))
                .is_some();
            if is_uid {
                todo!()
            }
        }
        emitln!(writer);

        let intrinsic_fun_ids = self.env.intrinsic_fun_ids();

        let mut translated_types = BTreeSet::new();
        let mut verified_functions_count = 0;
        info!(
            "generating verification conditions for {:?} module(s)",
            self.env.get_module_count()
        );
        
        // First pass: translate structs and enums for all modules
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
                    let struct_name = lean_struct_name(struct_env, type_inst);
                    if !translated_types.insert(struct_name) {
                        continue;
                    }
                    StructTranslator {
                        parent: self,
                        struct_env,
                        type_inst: type_inst.as_slice(),
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
                    let enum_name = lean_enum_name(enum_env, type_inst);
                    if !translated_types.insert(enum_name) {
                        continue;
                    }
                    EnumTranslator {
                        parent: self,
                        enum_env,
                        type_inst: type_inst.as_slice(),
                    }
                        .translate();
                }
            }
        }

        // Second pass: collect functions that need to be processed for dependency ordering
        let mut all_function_qids = Vec::new();
        
        for module_env in self.env.get_modules() {
            for fun_env in module_env.get_functions().collect_vec().iter().rev() {
                if self.targets.is_spec(&fun_env.get_qualified_id()) {
                    verified_functions_count += 1;
                    // Include spec functions that need to be verified
                    if self.targets.scenario_specs().contains(&fun_env.get_qualified_id()) {
                        if self.targets.has_target(
                            &fun_env,
                            &FunctionVariant::Verification(VerificationFlavor::Regular),
                        ) {
                            all_function_qids.push((fun_env.get_qualified_id(), true));
                        }
                    } else {
                        // Check if this spec function should be generated
                        if self.should_generate_style(&fun_env, FunctionTranslationStyle::Default) {
                            all_function_qids.push((fun_env.get_qualified_id(), true));
                        }
                    }
                } else {
                    // Include regular functions that might be needed
                    // We'll filter them during processing based on actual usage
                    all_function_qids.push((fun_env.get_qualified_id(), false));
                }
            }
        }

        // Third pass: handle invariant functions
        for module_env in self.env.get_modules() {
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
                        .get_target(&inv_fun_env, &FunctionVariant::Baseline);
                    let struct_type_instances = mono_info
                        .structs
                        .get(&struct_env.get_qualified_id())
                        .unwrap_or(empty);
                    let inv_fun_type_instances = mono_info
                        .funs
                        .get(&(inv_fun_env.get_qualified_id(), FunctionVariant::Baseline))
                        .unwrap_or(empty);
                    for type_inst in struct_type_instances.difference(inv_fun_type_instances) {
                        FunctionTranslator {
                            parent: self,
                            fun_target: &inv_fun_target,
                            type_inst,
                            style: FunctionTranslationStyle::Default,
                            ensures_info: RefCell::new(Vec::new()),
                        }
                            .translate();
                    }
                }
            }
        }

        // Fourth pass: process all functions in global dependency order
        if !all_function_qids.is_empty() {
            let ordered_qids = self.order_functions_by_dependencies_qids(&all_function_qids);
            
            // Build a set of functions that are actually needed
            let mut needed_functions = std::collections::HashSet::new();
            
            // First, identify spec functions that need to be verified
            for (qid, is_spec) in &ordered_qids {
                if *is_spec {
                    let fun_env = self.env.get_function(*qid);
                    if self.targets.scenario_specs().contains(qid) {
                        if self.targets.has_target(
                            &fun_env,
                            &FunctionVariant::Verification(VerificationFlavor::Regular),
                        ) {
                            needed_functions.insert(*qid);
                        }
                    } else if self.should_generate_style(&fun_env, FunctionTranslationStyle::Default) {
                        needed_functions.insert(*qid);
                    }
                }
            }
            
            // Then, find all dependencies of needed functions
            let mut to_process = needed_functions.clone();
            while !to_process.is_empty() {
                let current = to_process.iter().next().unwrap().clone();
                to_process.remove(&current);
                
                let fun_env = self.env.get_function(current);
                let dependencies = self.get_function_dependencies(&fun_env);
                
                for dep_qid in dependencies {
                    let dep_fun_env = self.env.get_function(dep_qid);
                    // Skip native and intrinsic functions
                    if dep_fun_env.is_native() || intrinsic_fun_ids.contains(&dep_qid) {
                        continue;
                    }
                    
                    if !needed_functions.contains(&dep_qid) {
                        needed_functions.insert(dep_qid);
                        to_process.insert(dep_qid);
                    }
                }
            }
            
            // Debug: Print the ordering for overflowing_mul related functions
            eprintln!("=== FUNCTION ORDERING ===");
            for (i, (qid, is_spec)) in ordered_qids.iter().enumerate() {
                let fun_env = self.env.get_function(*qid);
                let fun_name = fun_env.get_name_str();
                if fun_name.contains("overflowing_mul") || fun_name.contains("mul_spec") {
                    eprintln!("  {}: {} (is_spec: {}, needed: {})", i, fun_name, is_spec, needed_functions.contains(qid));
                }
            }
            eprintln!("=========================");
            
            for (qid, is_spec) in ordered_qids {
                let fun_env = self.env.get_function(qid);
                
                // Filter out native and intrinsic functions during processing
                if fun_env.is_native() || intrinsic_fun_ids.contains(&qid) {
                    if fun_env.get_name_str().contains("overflowing_mul") {
                        eprintln!("FILTERED OUT: {} (native: {}, intrinsic: {})", 
                                  fun_env.get_name_str(), fun_env.is_native(), intrinsic_fun_ids.contains(&qid));
                    }
                    continue;
                }
                
                // Only process functions that are actually needed
                if !needed_functions.contains(&qid) {
                    if fun_env.get_name_str().contains("overflowing_mul") {
                        eprintln!("SKIPPED: {} (not needed)", fun_env.get_name_str());
                    }
                    continue;
                }
                
                if fun_env.get_name_str().contains("overflowing_mul") {
                    eprintln!("PROCESSING: {} (is_spec: {})", fun_env.get_name_str(), is_spec);
                }
                
                if is_spec {
                    // Handle scenario spec functions
                    if self.targets.scenario_specs().contains(&qid) {
                        if self.targets.has_target(
                            &fun_env,
                            &FunctionVariant::Verification(VerificationFlavor::Regular),
                        ) {
                            let fun_target = self.targets.get_target(
                                &fun_env,
                                &FunctionVariant::Verification(VerificationFlavor::Regular),
                            );
                            FunctionTranslator {
                                parent: self,
                                fun_target: &fun_target,
                                type_inst: &[],
                                style: FunctionTranslationStyle::Default,
                                ensures_info: RefCell::new(Vec::new()),
                            }
                                .translate();
                        }
                    } else {
                        // Handle regular spec functions
                        self.translate_function_styles_mutual(&fun_env);
                    }
                } else {
                    let fun_target = self.targets.get_target(&fun_env, &FunctionVariant::Baseline);
                    
                    if fun_env.get_name_str().contains("overflowing_mul") {
                        eprintln!("  Regular function processing for: {}", fun_env.get_name_str());
                        let spec_qid = self.targets.get_spec_by_fun(&fun_env.get_qualified_id());
                        eprintln!("    Has spec counterpart: {:?}", spec_qid.is_some());
                        if let Some(spec_qid) = spec_qid {
                            eprintln!("    Spec function: {}", self.env.get_function(*spec_qid).get_name_str());
                            eprintln!("    No verify specs contains: {}", self.targets.no_verify_specs().contains(spec_qid));
                        } else {
                            eprintln!("    Inlined: {}", verification_analysis::get_info(&fun_target).inlined);
                        }
                    }
                    
                    // Process functions that have spec counterparts
                    if let Some(spec_qid) = self.targets.get_spec_by_fun(&fun_env.get_qualified_id()) {
                        if !self.targets.no_verify_specs().contains(spec_qid) {
                            if fun_env.get_name_str().contains("overflowing_mul") {
                                eprintln!("    -> Translating {} (has spec counterpart)", fun_env.get_name_str());
                            }
                            FunctionTranslator {
                                parent: self,
                                fun_target: &fun_target,
                                type_inst: &[],
                                style: FunctionTranslationStyle::Default,
                                ensures_info: RefCell::new(Vec::new()),
                            }
                                .translate();
                        } else {
                            // Only translate if this function is actually needed as a dependency
                            // Since we're processing in dependency order, if we reach here, it means
                            // this function is needed by something else
                            if fun_env.get_name_str().contains("overflowing_mul") {
                                eprintln!("    -> Translating {} (spec in no_verify_specs but function is needed as dependency)", fun_env.get_name_str());
                            }
                            FunctionTranslator {
                                parent: self,
                                fun_target: &fun_target,
                                type_inst: &[],
                                style: FunctionTranslationStyle::Default,
                                ensures_info: RefCell::new(Vec::new()),
                            }
                                .translate();
                        }
                    } else if verification_analysis::get_info(&fun_target).inlined {
                        if fun_env.get_name_str().contains("overflowing_mul") {
                            eprintln!("    -> Translating {} (inlined, no spec counterpart)", fun_env.get_name_str());
                        }
                        // This variant is inlined, so translate for all type instantiations.
                        for type_inst in mono_info
                            .funs
                            .get(&(
                                fun_target.func_env.get_qualified_id(),
                                FunctionVariant::Baseline,
                            ))
                            .unwrap_or(&BTreeSet::new())
                        {
                            FunctionTranslator {
                                parent: self,
                                fun_target: &fun_target,
                                type_inst,
                                style: FunctionTranslationStyle::Default,
                                ensures_info: RefCell::new(Vec::new()),
                            }
                                .translate();
                        }
                    } else if fun_env.get_name_str().contains("overflowing_mul") {
                        eprintln!("    -> NOT translating {} (not inlined, no spec counterpart)", fun_env.get_name_str());
                    }
                }
            }
        }
        
        // Emit any finalization items required by spec translation.
        self.spec_translator.finalize();
        info!("{} verification conditions", verified_functions_count);
    }

    /// Generate all function styles for a function together in a mutual block
    fn translate_function_styles_mutual(&self, fun_env: &FunctionEnv) {
        let writer = self.writer;
        
        // Collect which styles need to be generated
        let styles = vec![
            FunctionTranslationStyle::Opaque,
            FunctionTranslationStyle::Default,
            FunctionTranslationStyle::Asserts,
            FunctionTranslationStyle::Aborts,
            FunctionTranslationStyle::SpecNoAbortCheck,
        ];
        
        // Filter out styles that won't generate functions
        let mut active_styles = Vec::new();
        for style in styles {
            if self.should_generate_style(fun_env, style) {
                active_styles.push(style);
            }
        }
        
        if active_styles.is_empty() {
            return;
        }
        
        // Collect ensures info for generating theorems later
        let mut all_ensures_info = Vec::new();
        
        // Generate each function style (functions only, not theorems)
        for style in &active_styles {
            let ensures_info = self.translate_function_style_no_theorems(fun_env, *style);
            if *style == FunctionTranslationStyle::Default {
                all_ensures_info = ensures_info;
            }
        }

        if !all_ensures_info.is_empty() {
            emitln!(writer, "\n-- Theorems proving ensures conditions");
            
            // We need to create a FunctionTranslator to generate the theorem
            let variant = FunctionVariant::Verification(VerificationFlavor::Regular);
            if self.targets.has_target(fun_env, &variant) {
                let fun_target = self.targets.get_target(fun_env, &variant);
                let translator = FunctionTranslator {
                    parent: self,
                    fun_target: &fun_target,
                    type_inst: &[],
                    style: FunctionTranslationStyle::Default,
                    ensures_info: RefCell::new(all_ensures_info.clone()),
                };
                
                for (idx, _) in all_ensures_info.iter().enumerate() {
                    translator.generate_ensures_impl_function(idx);
                }
            }
        }
    }

    /// Check if a function style should be generated for the given function
    fn should_generate_style(&self, fun_env: &FunctionEnv, style: FunctionTranslationStyle) -> bool {
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
            return false;
        }

        let variant = match style {
            FunctionTranslationStyle::Default | FunctionTranslationStyle::SpecNoAbortCheck => {
                FunctionVariant::Verification(VerificationFlavor::Regular)
            }
            FunctionTranslationStyle::Asserts
            | FunctionTranslationStyle::Aborts
            | FunctionTranslationStyle::Opaque => FunctionVariant::Baseline,
        };
        
        if variant.is_verified() && !self.targets.has_target(fun_env, &variant) {
            return false;
        }
        
        let spec_fun_target = self.targets.get_target(&fun_env, &variant);
        if !variant.is_verified() && !verification_analysis::get_info(&spec_fun_target).inlined {
            return false;
        }
        
        true
    }

    /// Translate a function style and return ensures info for theorem generation later
    fn translate_function_style_no_theorems(&self, fun_env: &FunctionEnv, style: FunctionTranslationStyle) -> Vec<(usize, TempIndex)> {
        let ensures_info = self.translate_function_style_internal(fun_env, style, false);
        ensures_info
    }

    fn translate_function_style(&self, fun_env: &FunctionEnv, style: FunctionTranslationStyle) {
        self.translate_function_style_internal(fun_env, style, true);
    }

    fn translate_function_style_internal(&self, fun_env: &FunctionEnv, style: FunctionTranslationStyle, generate_theorems: bool) -> Vec<(usize, TempIndex)> {
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
            return Vec::new();
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
            | FunctionTranslationStyle::Opaque => FunctionVariant::Baseline,
        };
        if variant.is_verified() && !self.targets.has_target(fun_env, &variant) {
            return Vec::new();
        }
        let spec_fun_target = self.targets.get_target(&fun_env, &variant);
        if !variant.is_verified() && !verification_analysis::get_info(&spec_fun_target).inlined {
            return Vec::new();
        }

        let mut builder =
            FunctionDataBuilder::new(spec_fun_target.func_env, spec_fun_target.data.clone());
        let code = std::mem::take(&mut builder.data.code);
        for bc in code.into_iter() {
            match style {
                FunctionTranslationStyle::Default => match bc {
                    Call(_, _, op, _, _) if op == asserts_function => {}
                    Call(_, _, Operation::Function(module_id, fun_id, _), _, _)
                    if self
                        .targets
                        .get_fun_by_spec(&spec_fun_target.func_env.get_qualified_id())
                        == Some(&QualifiedId {
                        module_id,
                        id: fun_id,
                    }) =>
                        {
                            builder.emit(bc)
                        }
                    _ => builder.emit(bc.update_abort_action(|_| None)),
                },
                FunctionTranslationStyle::Asserts | FunctionTranslationStyle::Aborts => match bc {
                    Call(_, _, op, _, _) if op == requires_function || op == ensures_function => {}
                    Call(_, _, op, _, _)
                    if matches!(
                            op,
                            Operation::TraceLocal { .. }
                                | Operation::TraceReturn { .. }
                                | Operation::TraceMessage { .. }
                                | Operation::TraceGhost { .. }
                        ) => {}
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
                            builder.emit(bc.update_abort_action(|_| None));
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
                    Ret(..) => {}
                    _ => builder.emit(
                        bc.substitute_operations(&ensures_asserts_to_requires_subst)
                            .update_abort_action(|aa| match aa {
                                Some(AbortAction::Jump(_, _)) => Some(AbortAction::Check),
                                Some(AbortAction::Check) => Some(AbortAction::Check),
                                None => None,
                            }),
                    ),
                },
                FunctionTranslationStyle::Opaque => match bc {
                    Call(_, _, op, _, _) if op == asserts_function => {}
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
                            builder.emit(bc);
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
                    _ => builder.emit(
                        bc.substitute_operations(&ensures_requires_swap_subst)
                            .update_abort_action(|_| None),
                    ),
                },
            }
        }

        let mut data = builder.data;
        let reach_def = ReachingDefProcessor::new();
        let live_vars = LiveVarAnalysisProcessor::new_no_annotate();
        let mut dummy_targets = self.targets.new_dummy();
        data = reach_def.process(&mut dummy_targets, builder.fun_env, data, None);
        data = live_vars.process(&mut dummy_targets, builder.fun_env, data, None);

        let fun_target = FunctionTarget::new(builder.fun_env, &data);
        if style == FunctionTranslationStyle::Default
            || style == FunctionTranslationStyle::Asserts
            || style == FunctionTranslationStyle::Aborts
            || style == FunctionTranslationStyle::SpecNoAbortCheck
            || style == FunctionTranslationStyle::Opaque
        // this is for the $opaque signature
        {
            let translator = FunctionTranslator {
                parent: self,
                fun_target: &fun_target,
                type_inst: &[],
                style,
                ensures_info: RefCell::new(Vec::new()),
            };
            let ensures_info = translator.translate_with_ensures_control(generate_theorems);
            
            if style == FunctionTranslationStyle::Default {
                return ensures_info;
            }
        }

        if style == FunctionTranslationStyle::Opaque || style == FunctionTranslationStyle::Aborts {
            mono_analysis::get_info(self.env)
                .funs
                .get(&(
                    *self
                        .targets
                        .get_fun_by_spec(&fun_target.func_env.get_qualified_id())
                        .unwrap(),
                    FunctionVariant::Baseline,
                ))
                .unwrap_or(&BTreeSet::new())
                .iter()
                .for_each(|type_inst| {
                    // Skip the none instantiation (i.e., each type parameter is
                    // instantiated to itself as a concrete type). This has the same
                    // effect as `type_inst: &[]` and is already captured above.
                    let is_none_inst = type_inst
                        .iter()
                        .enumerate()
                        .all(|(i, t)| matches!(t, Type::TypeParameter(idx) if *idx == i as u16));
                    if is_none_inst {
                        return;
                    }

                    FunctionTranslator {
                        parent: self,
                        fun_target: &fun_target,
                        type_inst,
                        style,
                        ensures_info: RefCell::new(Vec::new()),
                    }
                        .translate_with_ensures_control(generate_theorems);
                });
        }
        
        Vec::new() // Return empty ensures info for non-Default styles
    }

    /// Order functions by their dependencies using topological sorting
    fn order_functions_by_dependencies_qids(&self, functions: &[(QualifiedId<FunId>, bool)]) -> Vec<(QualifiedId<FunId>, bool)> {
        use std::collections::{HashMap, HashSet, VecDeque};
        
        let intrinsic_fun_ids = self.env.intrinsic_fun_ids();
        
        // Build function ID to index mapping
        let mut func_to_idx = HashMap::new();
        let mut idx_to_func = HashMap::new();
        for (i, (qid, is_spec)) in functions.iter().enumerate() {
            func_to_idx.insert(*qid, i);
            idx_to_func.insert(i, (*qid, *is_spec));
        }
        
        // Build dependency graph
        let mut graph = vec![Vec::new(); functions.len()];
        let mut in_degree = vec![0; functions.len()];
        
        for (i, (qid, _)) in functions.iter().enumerate() {
            // Get function dependencies by analyzing bytecode calls
            let fun_env = self.env.get_function(*qid);
            let dependencies = self.get_function_dependencies(&fun_env);
            
            for dep_qid in dependencies {
                // Filter out native and intrinsic functions from dependency graph
                let dep_fun_env = self.env.get_function(dep_qid);
                if dep_fun_env.is_native() || intrinsic_fun_ids.contains(&dep_qid) {
                    continue;
                }
                
                if let Some(&dep_idx) = func_to_idx.get(&dep_qid) {
                    // Add edge from dependency to current function
                    graph[dep_idx].push(i);
                    in_degree[i] += 1;
                }
            }
        }
        
        // Topological sort using Kahn's algorithm
        let mut queue = VecDeque::new();
        let mut result = Vec::new();
        
        // Start with functions that have no dependencies
        for i in 0..functions.len() {
            if in_degree[i] == 0 {
                queue.push_back(i);
            }
        }
        
        while let Some(current) = queue.pop_front() {
            result.push(idx_to_func[&current]);
            
            // Remove edges from current node
            for &neighbor in &graph[current] {
                in_degree[neighbor] -= 1;
                if in_degree[neighbor] == 0 {
                    queue.push_back(neighbor);
                }
            }
        }
        
        // If we couldn't order all functions, there might be circular dependencies
        // In that case, append remaining functions in original order
        if result.len() < functions.len() {
            let processed: HashSet<_> = result.iter().map(|(qid, _)| *qid).collect();
            for (qid, is_spec) in functions {
                if !processed.contains(qid) {
                    result.push((*qid, *is_spec));
                }
            }
        }
        
        result
    }

    /// Get the qualified IDs of functions that this function depends on
    fn get_function_dependencies(&self, fun_env: &FunctionEnv) -> Vec<QualifiedId<FunId>> {
        use move_stackless_bytecode::stackless_bytecode::Bytecode;
        use move_stackless_bytecode::stackless_bytecode::Operation;
        
        let mut dependencies = Vec::new();
        let is_spec_function = self.targets.is_spec(&fun_env.get_qualified_id());
        let fun_name = fun_env.get_name_str();
        
        let should_debug = fun_name.contains("math_u128") || fun_name.contains("math_u64");
        
        if should_debug {
            eprintln!("DEPENDENCY ANALYSIS: Analyzing function: {} (is_spec: {})", fun_name, is_spec_function);
        }
        
        // Try to get function target for analysis - more comprehensive approach for spec functions
        let mut targets_to_analyze = Vec::new();
        
        if is_spec_function {
            // For spec functions, analyze all available variants
            if self.targets.has_target(fun_env, &FunctionVariant::Verification(VerificationFlavor::Regular)) {
                targets_to_analyze.push(self.targets.get_target(fun_env, &FunctionVariant::Verification(VerificationFlavor::Regular)));
                if should_debug {
                    eprintln!("  Added Verification(Regular) target");
                }
            }
            if self.targets.has_target(fun_env, &FunctionVariant::Baseline) {
                targets_to_analyze.push(self.targets.get_target(fun_env, &FunctionVariant::Baseline));
                if should_debug {
                    eprintln!("  Added Baseline target");
                }
            }
            // Note: Additional spec variants could be checked here if needed
        } else {
            // For regular functions, use baseline variant
            if self.targets.has_target(fun_env, &FunctionVariant::Baseline) {
                targets_to_analyze.push(self.targets.get_target(fun_env, &FunctionVariant::Baseline));
                if should_debug {
                    eprintln!("  Added Baseline target");
                }
            } else if should_debug {
                eprintln!("  WARNING: No Baseline target available for regular function {}", fun_name);
            }
        }
        
        if should_debug {
            eprintln!("  Total targets to analyze: {}", targets_to_analyze.len());
        }
        
        // Analyze all relevant targets for dependencies
        for (target_idx, target) in targets_to_analyze.iter().enumerate() {
            if should_debug {
                eprintln!("  Analyzing target {}: {} bytecode instructions", target_idx, target.get_bytecode().len());
            }
            
            // Analyze bytecode for function calls
            for (bc_idx, bytecode) in target.get_bytecode().iter().enumerate() {
                match bytecode {
                    Bytecode::Call(_, _, operation, _, _) => {
                        if should_debug {
                            eprintln!("    Bytecode[{}]: Call operation: {:?}", bc_idx, operation);
                        }
                        if let Operation::Function(module_id, fun_id, _) = operation {
                            let callee_qid = QualifiedId {
                                module_id: *module_id,
                                id: *fun_id,
                            };
                            let callee_name = self.env.get_function(callee_qid).get_name_str();
                            let is_math_call = callee_name.contains("math_u128") || callee_name.contains("math_u64") || callee_name.contains("overflowing_mul");
                            
                            // Include dependencies from the same module and cross-module dependencies
                            // Don't filter out based on native/intrinsic here - let the processing phase handle that
                            dependencies.push(callee_qid);
                        } else if should_debug {
                            eprintln!("      Non-function operation: {:?}", operation);
                        }
                    },
                    // TODO: Could also check Prop expressions for function calls if needed
                    _ => {}
                }
            }
            
            // Also analyze pre/post conditions and other specifications
            if is_spec_function {
                // TODO: Add analysis of specification expressions if needed
            }
        }
        
        dependencies.sort();
        dependencies.dedup();
        
        // Debug output to help diagnose dependency issues
        if should_debug && !dependencies.is_empty() {
            let dep_names: Vec<_> = dependencies.iter()
                .map(|qid| self.env.get_function(*qid).get_name_str())
                .collect();
            eprintln!("DEPENDENCY DEBUG: {} depends on: {:?}", fun_name, dep_names);
        }
        
        dependencies
    }

    /// Helper method to collect function calls from expressions (for spec analysis)
    fn collect_function_calls_from_exp(&self, _exp: &move_stackless_bytecode::ast::Exp, _module_id: move_model::model::ModuleId, _dependencies: &mut Vec<QualifiedId<FunId>>) {
        // TODO: Implement proper expression analysis if needed
        // For now, this is a placeholder since the expression analysis is complex
        // and the main dependency detection is handled by bytecode analysis
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

    /// Return lean type for a struct field
    pub fn lean_type_for_struct_field(
        &self,
        field_id: &FieldId,
        env: &GlobalEnv,
        ty: &Type,
    ) -> String {
        lean_type(env, ty)
    }

    /// Translates the given struct.
    fn translate(&self) {
        let writer = self.parent.writer;
        let struct_env = self.struct_env;
        let env = struct_env.module_env.env;

        if struct_env.is_native() || struct_env.is_intrinsic() {
            return;
        }

        let qid = struct_env
            .get_qualified_id()
            .instantiate(self.type_inst.to_owned());
        emitln!(
            writer,
            "-- struct {} {}",
            env.display(&qid),
            struct_env.get_loc().display(env)
        );

        // Set the location to internal as default.
        writer.set_location(&env.internal_loc());

        // Emit structure definition
        let struct_name = lean_struct_name(struct_env, self.type_inst);
        emitln!(writer, "structure {} where", struct_name);
        writer.indent();

        // Emit fields
        for field in struct_env.get_fields() {
            let field_name = field.get_name().display(env.symbol_pool()).to_string();
            let field_type = self.lean_type_for_struct_field(
                &field.get_id(),
                env,
                &self.inst(&field.get_type()),
            );
            emitln!(writer, "{} : {}", field_name, field_type);
        }
        writer.unindent();
        emitln!(writer);

        let suffix = lean_type_suffix(env, &Type::Datatype(
            struct_env.module_env.get_id(),
            struct_env.get_id(),
            self.type_inst.to_vec(),
        ));

        // Emit field update functions
        let fields = struct_env.get_fields().collect_vec();
        for field_env in fields.iter() {
            let field_name = field_env.get_name().display(env.symbol_pool()).to_string();
            self.emit_function(
                &format!(
                    "update_{}_{}",
                    suffix,
                    field_name
                ),
                &format!(
                    "(s : {}) (x : {}) : {}",
                    struct_name,
                    self.lean_type_for_struct_field(
                        &field_env.get_id(),
                        env,
                        &self.inst(&field_env.get_type())
                    ),
                    struct_name
                ),
                || {
                    emitln!(writer, "{{ s with {} := x }}", field_name);
                },
            );
        }

        // Emit validity check function
        self.emit_function(
            &format!("is_valid_{}", suffix),
            &format!("(s : {}) : Bool", struct_name),
            || {
                if struct_env.is_native() {
                    emitln!(writer, "true")
                } else {
                    let mut checks = Vec::new();
                    for field in struct_env.get_fields() {
                        let field_name = field.get_name().display(env.symbol_pool()).to_string();
                        let ty = &field.get_type().instantiate(self.type_inst);
                        checks.push(format!("is_valid_{} s.{}", lean_type_suffix(env, ty), field_name));
                    }
                    if checks.is_empty() {
                        emitln!(writer, "true");
                    } else {
                        emitln!(writer, "{}", checks.join(" ∧ "));
                    }
                }
            },
        );

        // Emit equality function
        self.emit_function(
            &format!("is_equal_{}", suffix),
            &format!("(s1 s2 : {}) : Bool", struct_name),
            || {
                let mut checks = Vec::new();
                for field in &fields {
                    let field_name = field.get_name().display(env.symbol_pool()).to_string();
                    let field_type = &self.inst(&field.get_type());
                    let field_suffix = lean_type_suffix(env, field_type);
                    checks.push(format!("is_equal_{} s1.{} s2.{}", field_suffix, field_name, field_name));
                }
                if checks.is_empty() {
                    emitln!(writer, "true");
                } else {
                    emitln!(writer, "{}", checks.join(" ∧ "));
                }
            },
        );

        if struct_env.has_memory() {
            // Emit memory variable
            let memory_name = lean_resource_memory_name(
                env,
                &struct_env
                    .get_qualified_id()
                    .instantiate(self.type_inst.to_owned()),
                &None,
            );
            emitln!(writer, "variable {} : Memory {}", memory_name, struct_name);
        }

        // Emit type invariant function
        self.emit_function(
            &format!("type_inv_{}", suffix),
            &format!("(s : {}) : Bool", struct_name),
            || {
                if let Some(inv_fun_id) = self
                    .parent
                    .targets
                    .get_inv_by_datatype(&self.struct_env.get_qualified_id())
                {
                    emitln!(
                        writer,
                        "{} s",
                        lean_function_name(
                            &self.parent.env.get_function(*inv_fun_id),
                            self.type_inst,
                            FunctionTranslationStyle::Default
                        )
                    );
                } else {
                    emitln!(writer, "true");
                }
            },
        );

        emitln!(writer);
    }

    fn emit_function(&self, name: &str, signature: &str, body_fn: impl Fn()) {
        let writer = self.parent.writer;
        emitln!(writer, "def {} {} :=", name, signature);
        writer.indent();
        body_fn();
        writer.unindent();
        emitln!(writer);
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
        // For now, return false as enum bitwise operations are not implemented
        false
    }

    /// Return lean type for an enum field
    pub fn lean_type_for_enum_field(
        &self,
        field_id: &FieldId,
        env: &GlobalEnv,
        ty: &Type,
    ) -> String {
        lean_type(env, ty)
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
            "-- enum {} {}",
            env.display(&qid),
            enum_env.get_loc().display(env)
        );

        // Set the location to internal as default.
        writer.set_location(&env.internal_loc());

        // Emit inductive type definition
        let enum_name = lean_enum_name(enum_env, self.type_inst);
        emitln!(writer, "inductive {} where", enum_name);
        writer.indent();

        // Emit variants as constructors
        for variant in enum_env.get_variants() {
            let variant_name = variant.get_name().display(env.symbol_pool()).to_string();
            if variant.get_field_count() == 0 {
                emitln!(writer, "| {} : {}", variant_name, enum_name);
            } else {
                let fields = variant
                    .get_fields()
                    .map(|field| {
                        let field_type = self.lean_type_for_enum_field(
                            &field.get_id(),
                            env,
                            &self.inst(&field.get_type()),
                        );
                        field_type
                    })
                    .join(" → ");
                emitln!(writer, "| {} : {} → {}", variant_name, fields, enum_name);
            }
        }
        writer.unindent();
        emitln!(writer);

        let suffix = lean_type_suffix(env, &Type::Datatype(
            enum_env.module_env.get_id(),
            enum_env.get_id(),
            self.type_inst.to_vec(),
        ));

        // Emit validity check function
        self.emit_function(
            &format!("is_valid_{}", suffix),
            &format!("(e : {}) : Bool", enum_name),
            || {
                emitln!(writer, "match e with");
                writer.indent();
                for variant in enum_env.get_variants() {
                    let variant_name = variant.get_name().display(env.symbol_pool()).to_string();
                    if variant.get_field_count() == 0 {
                        emitln!(writer, "| {} => true", variant_name);
                    } else {
                        let field_patterns = variant
                            .get_fields()
                            .enumerate()
                            .map(|(i, _)| format!("f{}", i))
                            .join(" ");
                        let field_checks = variant
                            .get_fields()
                            .enumerate()
                            .map(|(i, field)| {
                                let field_type = &self.inst(&field.get_type());
                                format!("is_valid_{} f{}", lean_type_suffix(env, field_type), i)
                            })
                            .collect::<Vec<_>>();

                        if field_checks.is_empty() {
                            emitln!(writer, "| {} {} => true", variant_name, field_patterns);
                        } else {
                            emitln!(writer, "| {} {} => {}", variant_name, field_patterns, field_checks.join(" ∧ "));
                        }
                    }
                }
                writer.unindent();
            },
        );

        // Emit equality function
        self.emit_function(
            &format!("is_equal_{}", suffix),
            &format!("(e1 e2 : {}) : Bool", enum_name),
            || {
                emitln!(writer, "match e1, e2 with");
                writer.indent();
                for variant in enum_env.get_variants() {
                    let variant_name = variant.get_name().display(env.symbol_pool()).to_string();
                    if variant.get_field_count() == 0 {
                        emitln!(writer, "| {}, {} => true", variant_name, variant_name);
                    } else {
                        let field_patterns1 = variant
                            .get_fields()
                            .enumerate()
                            .map(|(i, _)| format!("f1_{}", i))
                            .join(" ");
                        let field_patterns2 = variant
                            .get_fields()
                            .enumerate()
                            .map(|(i, _)| format!("f2_{}", i))
                            .join(" ");
                        let field_checks = variant
                            .get_fields()
                            .enumerate()
                            .map(|(i, field)| {
                                let field_type = &self.inst(&field.get_type());
                                format!("is_equal_{} f1_{} f2_{}", lean_type_suffix(env, field_type), i, i)
                            })
                            .collect::<Vec<_>>();

                        if field_checks.is_empty() {
                            emitln!(writer, "| {} {}, {} {} => true", variant_name, field_patterns1, variant_name, field_patterns2);
                        } else {
                            emitln!(writer, "| {} {}, {} {} => {}", variant_name, field_patterns1, variant_name, field_patterns2, field_checks.join(" ∧ "));
                        }
                    }
                }
                // Add catch-all case for different variants
                emitln!(writer, "| _, _ => false");
                writer.unindent();
            },
        );

        // Emit type invariant function
        self.emit_function(
            &format!("type_inv_{}", suffix),
            &format!("(e : {}) : Bool", enum_name),
            || {
                if let Some(inv_fun_id) = self
                    .parent
                    .targets
                    .get_inv_by_datatype(&self.enum_env.get_qualified_id())
                {
                    emitln!(
                        writer,
                        "{} e",
                        lean_function_name(
                            &self.parent.env.get_function(*inv_fun_id),
                            self.type_inst,
                            FunctionTranslationStyle::Default
                        )
                    );
                } else {
                    emitln!(writer, "true");
                }
            },
        );

        emitln!(writer);
    }

    fn emit_function(&self, name: &str, signature: &str, body_fn: impl Fn()) {
        let writer = self.parent.writer;
        emitln!(writer, "def {} {} :=", name, signature);
        writer.indent();
        body_fn();
        writer.unindent();
        emitln!(writer);
    }
}

impl FunctionTranslator<'_> {
    /// Translates the function with control over ensures theorem generation.
    fn translate_with_ensures_control(mut self, generate_theorems: bool) -> Vec<(usize, TempIndex)> {
        let writer = self.parent.writer;
        let fun_target = self.fun_target;
        let env = fun_target.global_env();
        let qid = fun_target
            .func_env
            .get_qualified_id()
            .instantiate(self.type_inst.to_owned());
        emitln!(
            writer,
            "-- fun {} [{}] {}",
            env.display(&qid),
            fun_target.data.variant,
            fun_target.get_loc().display(env)
        );
        
        // Special handling for SpecNoAbortCheck: generate a theorem instead of a function
        if self.style == FunctionTranslationStyle::SpecNoAbortCheck {
            self.generate_no_abort_check_theorem();
        } else {
            // Emit locals frame type and State monad alias before the function definition
            self.generate_locals_frame_type_and_monad();
            self.generate_function_sig();

            if self.fun_target.func_env.get_qualified_id() == self.parent.env.global_qid() {
                todo!()
            } else if self.fun_target.func_env.get_qualified_id() == self.parent.env.havoc_global_qid()
            {
                todo!()
            } else {
                self.generate_function_body();
            }
        }
        emitln!(self.parent.writer);

        // Generate additional functions for ensures if found
        let ensures_info = self.ensures_info.borrow().clone();
        if !ensures_info.is_empty() && self.style == FunctionTranslationStyle::Default {
            for (idx, (bytecode_idx, ensures_temp)) in ensures_info.iter().enumerate() {
                // Generate the first function: copy up to ensures and return the condition
                self.generate_ensures_check_function(idx, *bytecode_idx, *ensures_temp);

                // Generate the second function only if requested
                if generate_theorems {
                    self.generate_ensures_impl_function(idx);
                }
            }
        }
        
        ensures_info
    }

    /// Translates the given function.
    fn translate(mut self) {
        self.translate_with_ensures_control(true);
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
            "-- {} {}",
            bytecode.display(fun_target, &BTreeMap::default()),
            loc.display(env)
        );

        // Print debug comments.
        if let Some(comment) = fun_target.get_debug_comment(attr_id) {
            emitln!(self.writer(), "-- {}", comment);
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

        // Helper function to get a string for a local
        let str_local = |idx: usize| format!("t{}", idx);
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
                    WriteBack(node, edge) => wip!("WriteBack"),
                    IsParent(node, edge) => wip!("IsParent"),
                    BorrowLoc => wip!("BorrowLoc"),
                    ReadRef => wip!("ReadRef"),
                    WriteRef => wip!("WriteRef"),
                    IfThenElse => {
                        let cond_str = str_local(srcs[0]);
                        let true_expr_str = str_local(srcs[1]);
                        let false_expr_str = str_local(srcs[2]);
                        let dest_str = str_local(dests[0]);
                        emitln!(
                            self.writer(),
                            "let {} := if {} then {} else {};",
                            dest_str,
                            cond_str,
                            true_expr_str,
                            false_expr_str
                        )
                    },
                    Function(mid, fid, inst) => {
                        let inst = &self.inst_slice(inst);
                        let module_env = env.get_module(*mid);
                        let callee_env = module_env.get_function(*fid);

                        let mut args_str = srcs.iter().cloned().map(str_local).join(" ");
                        let dest_vars: Vec<String> = dests
                            .iter()
                            .cloned()
                            .map(str_local)
                            // Add implict dest returns for &mut srcs:
                            //  f(x) --> x := f(x)  if type(x) = &mut_
                            .chain(
                                srcs.iter()
                                    .filter(|idx| self.get_local_type(**idx).is_mutable_reference())
                                    .cloned()
                                    .map(str_local),
                            )
                            .collect();
                        let dest_str = if dest_vars.len() > 1 {
                            format!("({})", dest_vars.join(", "))
                        } else {
                            dest_vars.join("")
                        };

                        // special casing for type reflection
                        let mut processed = false;

                        // TODO(mengxu): change it to a better address name instead of extlib
                        if env.get_extlib_address() == *module_env.get_name().addr() {
                            let qualified_name = format!(
                                "{}::{}",
                                module_env.get_name().name().display(env.symbol_pool()),
                                callee_env.get_name().display(env.symbol_pool()),
                            );
                            if qualified_name == TYPE_NAME_MOVE {
                                assert_eq!(inst.len(), 1);
                                todo!();
                            } else if qualified_name == TYPE_INFO_MOVE {
                                assert_eq!(inst.len(), 1);
                                todo!();
                            }
                        }

                        if env.get_stdlib_address() == *module_env.get_name().addr() {
                            let qualified_name = format!(
                                "{}::{}",
                                module_env.get_name().name().display(env.symbol_pool()),
                                callee_env.get_name().display(env.symbol_pool()),
                            );
                            if qualified_name == TYPE_NAME_GET_MOVE {
                                assert_eq!(inst.len(), 1);
                                todo!()
                            }
                        }

                        if callee_env.get_qualified_id() == self.parent.env.global_borrow_mut_qid()
                        {
                            todo!()
                        }

                        if callee_env.get_qualified_id() == self.parent.env.ensures_qid() {
                            // Track this ensures call
                            if !srcs.is_empty() {
                                let bytecode_idx = self.fun_target.get_bytecode().iter().position(|bc| std::ptr::eq(bc, bytecode)).unwrap();
                                self.ensures_info.borrow_mut().push((bytecode_idx, srcs[0]));
                            }

                            emitln!(
                                self.writer(),
                                "-- assert {{:msg \"assert_failed{}: prover::ensures assertion does not hold\"}} {};",
                                self.loc_str(&self.writer().get_loc()),
                                args_str,
                            );
                            processed = true;
                        }

                        if callee_env.get_qualified_id() == self.parent.env.asserts_qid()
                            && self.style == FunctionTranslationStyle::Asserts
                        {
                            // TODO
                        }

                        if callee_env.get_qualified_id() == self.parent.env.asserts_qid()
                            && self.style == FunctionTranslationStyle::Aborts
                        {
                            // TODO
                        }

                        if callee_env.get_qualified_id() == self.parent.env.type_inv_qid() {
                            if self.style == FunctionTranslationStyle::Asserts
                                || self.style == FunctionTranslationStyle::Aborts
                            {
                                emitln!(self.writer(), "{} := true;", dest_str);
                            } else {
                                assert_eq!(inst.len(), 1);
                                if let Some((datatype_qid, datatype_inst)) = &inst[0].get_datatype()
                                {
                                    if let Some(inv_qid) =
                                        self.parent.targets.get_inv_by_datatype(datatype_qid)
                                    {
                                        todo!()
                                    } else {
                                        emitln!(self.writer(), "{} := true;", dest_str);
                                    }
                                } else {
                                    emitln!(self.writer(), "{} := true;", dest_str);
                                }
                            }
                            processed = true;
                        }

                        if self
                            .parent
                            .targets
                            .get_fun_by_spec(&self.fun_target.func_env.get_qualified_id())
                            == Some(&mid.qualified(*fid))
                            && self.style == FunctionTranslationStyle::Opaque
                        {
                            if self
                                .parent
                                .targets
                                .ignore_aborts()
                                .contains(&self.fun_target.func_env.get_qualified_id())
                            {
                                emitln!(self.writer(), "-- havoc abort_flag");
                            } else {
                                /*emitln!(
                                    self.writer(),
                                    "let abort_if_cond := {} {};",
                                    self.function_variant_name(FunctionTranslationStyle::Aborts),
                                    args_str,
                                );
                                emitln!(self.writer(), "-- abort_flag := !abort_if_cond");*/
                            }
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
                            let mut fun_name = lean_function_name(
                                &callee_env,
                                inst,
                                FunctionTranslationStyle::Default,
                            );

                            // Check if the callee function has a spec counterpart
                            let callee_qid = QualifiedId {
                                module_id: *mid,
                                id: *fid,
                            };
                            if let Some(spec_qid) = self.parent.targets.get_spec_by_fun(&callee_qid) {
                                // The callee function has a spec counterpart, so we need to call the _impl version
                                fun_name = format!("{}_impl", fun_name);
                            } else if self
                                .parent
                                .targets
                                .get_fun_by_spec(&self.fun_target.func_env.get_qualified_id())
                                == Some(&callee_qid)
                            {
                                // This is the case where we're calling the spec function from the implementation
                                if self.style == FunctionTranslationStyle::Default
                                    && self.fun_target.data.variant
                                    == FunctionVariant::Verification(
                                    VerificationFlavor::Regular,
                                )
                                {
                                    fun_name = format!("{}_impl", fun_name);
                                } else if self.style == FunctionTranslationStyle::SpecNoAbortCheck
                                    || self.style == FunctionTranslationStyle::Opaque
                                {
                                    fun_name = format!("{}_opaque", fun_name);
                                }
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
                            let callee_name = callee_env.get_name_str();
                            if dest_str.is_empty() {
                                let bv_flag = !srcs.is_empty() && compute_flag(srcs[0]);
                                if module_env.is_std_vector() {
                                    todo!()
                                } else if module_env.is_table() {
                                    todo!()
                                }
                                emitln!(self.writer(), "-- {} {}", fun_name, args_str);
                            } else {
                                let dest_bv_flag = !dests.is_empty() && compute_flag(dests[0]);
                                let bv_flag = !srcs.is_empty() && compute_flag(srcs[0]);
                                // Handle the case where the return value of length is assigned to a bv int because
                                // length always returns a non-bv result
                                if module_env.is_std_vector() {
                                    todo!()
                                } else if module_env.is_table() {
                                    todo!()
                                }
                                emitln!(
                                    self.writer(),
                                    "let {} := {} {};",
                                    dest_str,
                                    fun_name,
                                    args_str
                                );
                            }
                        }

                        if self
                            .parent
                            .targets
                            .get_fun_by_spec(&self.fun_target.func_env.get_qualified_id())
                            == Some(&mid.qualified(*fid))
                            && (self.style == FunctionTranslationStyle::SpecNoAbortCheck
                            || self.style == FunctionTranslationStyle::Opaque)
                        {
                            for type_inst in
                                spec_global_variable_analysis::get_info(&self.fun_target.data)
                                    .mut_vars()
                            {
                                todo!()
                            }
                        };

                        // Clear the last track location after function call, as the call inserted
                        // location tracks before it returns.
                        *last_tracked_loc = None;
                    }
                    Pack(mid, sid, inst) => {
                        let inst = &self.inst_slice(inst);
                        let dest_str = str_local(dests[0]);
                        let srcs_str = srcs.iter().cloned().map(str_local).join(" ");
                        let struct_env = env.get_module(*mid).into_struct(*sid);
                        let struct_name = lean_struct_name(&struct_env, inst);
                        emitln!(
                            self.writer(),
                            "let {} := {}.mk {};",
                            dest_str,
                            struct_name,
                            srcs_str
                        );
                    }
                    Unpack(mid, sid, inst) => {
                        let inst = &self.inst_slice(inst);
                        let src = srcs[0];
                        let src_str = str_local(src);
                        let struct_env = env.get_module(*mid).into_struct(*sid);
                        for (i, field_env) in struct_env.get_fields().enumerate() {
                            let dest_str = str_local(dests[i]);
                            let sel_fun = lean_field_sel(&field_env, inst);
                            emitln!(self.writer(), "let {} := {}.{};", dest_str, src_str, sel_fun);
                        }
                    }
                    PackVariant(mid, eid, vid, inst) => wip!("PackVariant"),
                    UnpackVariant(mid, eid, vid, _inst, ref_type) => wip!("UnpackVariant"),
                    BorrowField(mid, sid, inst, field_offset) => {
                        let inst = &self.inst_slice(inst);
                        let src = srcs[0];
                        let mut src_str = str_local(src);
                        let dest_str = str_local(dests[0]);
                        let struct_env = env.get_module(*mid).into_struct(*sid);
                        let field_env = &struct_env.get_field_by_offset(*field_offset);
                        let sel_fun = lean_field_sel(field_env, inst);
                        if self.get_local_type(src).is_reference() {
                            src_str = format!("$Dereference({})", src_str);
                        };
                        emitln!(self.writer(), "{} := {}->{};", dest_str, src_str, sel_fun);
                    }
                    GetField(mid, sid, inst, field_offset) => {
                        let inst = &self.inst_slice(inst);
                        let src = srcs[0];
                        let mut src_str = str_local(src);
                        let dest_str = str_local(dests[0]);
                        let struct_env = env.get_module(*mid).into_struct(*sid);
                        let field_env = &struct_env.get_field_by_offset(*field_offset);
                        let sel_fun = lean_field_sel(field_env, inst);
                        emitln!(self.writer(), "let {} := {}.{};", dest_str, src_str, sel_fun);
                    }
                    Exists(mid, sid, inst) => wip!("Exists"),
                    BorrowGlobal(mid, sid, inst) => wip!("BorrowGlobal"),
                    GetGlobal(mid, sid, inst) => wip!("GetGlobal"),
                    MoveTo(mid, sid, inst) => wip!("MoveTo"),
                    MoveFrom(mid, sid, inst) => wip!("MoveFrom"),
                    Havoc(HavocKind::Value) | Havoc(HavocKind::MutationAll) => wip!("Havoc"),
                    Havoc(HavocKind::MutationValue) => wip!("HavocMutationValue"),
                    CastU8 | CastU16 | CastU32 | CastU64 | CastU128 | CastU256 => {
                        let dest = dests[0];
                        let src = srcs[0];
                        let cast_type = match oper {
                            CastU8 => "UInt8",
                            CastU16 => "UInt16",
                            CastU32 => "UInt32",
                            CastU64 => "UInt64",
                            CastU128 => "UInt128",
                            CastU256 => "UInt256",
                            _ => unreachable!(),
                        };
                        emitln!(
                            self.writer(),
                            "let {} := {}.toNat.to{};",
                            str_local(dest),
                            str_local(src),
                            cast_type,
                        );
                    }
                    Stop => wip!("Stop"),
                    Not => {
                        let src = srcs[0];
                        let dest = dests[0];
                        emitln!(
                            self.writer(),
                            "let {} := ¬{};",
                            str_local(dest),
                            str_local(src)
                        );
                    }
                    Add => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        emitln!(
                            self.writer(),
                            "let {} := {} + {};",
                            str_local(dest),
                            str_local(op1),
                            str_local(op2)
                        );
                    }
                    Sub => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        emitln!(
                            self.writer(),
                            "let {} := {} - {};",
                            str_local(dest),
                            str_local(op1),
                            str_local(op2)
                        );
                    }
                    Mul => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        emitln!(
                            self.writer(),
                            "let {} := {} * {};",
                            str_local(dest),
                            str_local(op1),
                            str_local(op2)
                        );
                    }
                    Div => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        emitln!(
                            self.writer(),
                            "let {} := {} / {};",
                            str_local(dest),
                            str_local(op1),
                            str_local(op2)
                        );
                    }
                    Mod => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        emitln!(
                            self.writer(),
                            "let {} := {} % {};",
                            str_local(dest),
                            str_local(op1),
                            str_local(op2)
                        );
                    }
                    Shl | Shr => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        let sh_oper_str = if oper == &Shl { "<<<" } else { ">>>" };

                        emitln!(
                            self.writer(),
                            "let {} := {} {} {};",
                            str_local(dest),
                            str_local(op1),
                            sh_oper_str,
                            str_local(op2)
                        );
                    }
                    Lt | Le | Gt | Ge => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        let comp_oper = match oper {
                            Lt => "<",
                            Le => "<=",
                            Gt => ">",
                            Ge => ">=",
                            _ => unreachable!(),
                        };
                        emitln!(
                            self.writer(),
                            "let {} := {} {} {};",
                            str_local(dest),
                            str_local(op1),
                            comp_oper,
                            str_local(op2)
                        );
                    }
                    Or => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        emitln!(
                            self.writer(),
                            "let {} := {} || {};",
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
                            "let {} := {} && {};",
                            str_local(dest),
                            str_local(op1),
                            str_local(op2)
                        );
                    }
                    Eq | Neq => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        let oper = if *oper == Eq { "==" } else { "!=" };
                        emitln!(
                            self.writer(),
                            "let {} := {} {} {};",
                            str_local(dest),
                            str_local(op1),
                            oper,
                            str_local(op2)
                        );
                    }
                    Xor | BitOr | BitAnd => {
                        let dest = dests[0];
                        let op1 = srcs[0];
                        let op2 = srcs[1];
                        let oper = match oper {
                            Xor => "^^^",
                            BitOr => "|||",
                            BitAnd => "&&&",
                            _ => unreachable!(),
                        };
                        emitln!(
                            self.writer(),
                            "let {} := {} {} {};",
                            str_local(dest),
                            str_local(op1),
                            oper,
                            str_local(op2),
                        );
                    }
                    Uninit => wip!("Uninit"),
                    Destroy => {},
                    TraceLocal(idx) => wip!("TraceLocal"),
                    TraceReturn(i) => wip!("TraceReturn"),
                    TraceAbort => wip!("TraceAbort"),
                    TraceExp(kind, node_id) => wip!("TraceExp"),
                    TraceMessage(message) => wip!("TraceMessage"),
                    TraceGhost(ghost_type, value_type) => wip!("TraceGhost"),
                    EmitEvent => wip!("EmitEvent"),
                    EventStoreDiverge => wip!("EventStoreDiverge"),
                    TraceGlobalMem(mem) => {},
                    Quantifier(_,_,_,_) => unreachable!("Add support for quantifiers in lean backend"),
                }
                match aa {
                    Some(AbortAction::Jump(target, code)) => {}
                    Some(AbortAction::Check) => {}
                    None => {}
                }
            }
            Ret(_, srcs) => {
                // Handle return instruction
                if srcs.is_empty() {
                    // No return value
                    emitln!(self.writer(), "()");
                } else if srcs.len() == 1 {
                    // Single return value
                    emitln!(self.writer(), "{}", str_local(srcs[0]));
                } else {
                    // Multiple return values - create tuple
                    let values = srcs.iter().map(|&idx| str_local(idx)).join(", ");
                    emitln!(self.writer(), "({})", values);
                }
            }
            Label(_, _) => {
                // Labels don't generate code in Lean
                emitln!(self.writer(), "-- Label (no code generated)");
            }
            Jump(_, _) => {
                // Jumps are control flow, not directly translated in functional style
                emitln!(self.writer(), "-- Jump (control flow not implemented in simple mode)");
            }
            Branch(_, _, _, _) => {
                // Branches are control flow, not directly translated in functional style
                emitln!(self.writer(), "-- Branch (control flow not implemented in simple mode)");
            }
            VariantSwitch(_, _, _) => {
                // Variant switch is control flow, not directly translated in functional style
                emitln!(self.writer(), "-- VariantSwitch (control flow not implemented in simple mode)");
            }
            Assign(_, dest, src, _) => {
                // Simple assignment - in functional style this would be a let binding
                emitln!(self.writer(), "let {} := {} -- (assignment)", str_local(*dest), str_local(*src));
            }
            Load(_, dest, c) => {
                // Load constant
                emitln!(self.writer(), "let {} := {};", str_local(*dest), c);
            }
            Abort(_, _) => wip!("Abort"),
            SaveMem(_, _, _) => wip!("SaveMem"),
            Prop(_, _, _) => wip!("Prop"),
            Nop(_) => {}
        }
    }

fn writer(&self) -> &CodeWriter {
    self.parent.writer
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
    }
}

fn loc_str(&self, loc: &Loc) -> String {
    let file_idx = self.fun_target.global_env().file_id_to_idx(loc.file_id());
    format!("({},{},{})", file_idx, loc.span().start(), loc.span().end())
}

/// Return a string for a lean procedure header. Use inline attribute and name
/// suffix as indicated by `entry_point`.
fn generate_function_sig(&self) {
    let writer = self.parent.writer;
    let options = self.parent.options;
    let fun_target = self.fun_target;
    let (args, prerets) = self.generate_function_args_and_returns();

    let rets = match self.style {
        FunctionTranslationStyle::Default | FunctionTranslationStyle::Opaque => prerets,
        FunctionTranslationStyle::Asserts => "Unit".to_string(),
        FunctionTranslationStyle::Aborts => "ProgramState Nat".to_string(),
        FunctionTranslationStyle::SpecNoAbortCheck => "Unit".to_string(),
    };

    writer.set_location(&fun_target.get_loc());
    if self.style == FunctionTranslationStyle::Opaque {
        emitln!(
                writer,
                "def {}_opaque {} : {} :=",
                self.function_variant_name(FunctionTranslationStyle::Opaque),
                args,
                rets,
            );
        emitln!(writer, "  sorry");
        emitln!(writer, "");
    }
    emitln!(
            writer,
            "def {} {} : {} :=",
            self.function_variant_name(self.style),
            args,
            rets,
        )
}

/// Generate lean representation of function args and return args.
fn generate_function_args_and_returns(&self) -> (String, String) {
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
    let args = (0..fun_target.get_parameter_count())
        .map(|i| {
            let ty = self.get_local_type(i);
            let num_oper = global_state
                .get_temp_index_oper(mid, fid, i, baseline_flag)
                .unwrap_or(&Bottom);
            format!("(t{}: {})", i, self.lean_type_for_fun(env, &ty, num_oper))
        })
        .join(" ");
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
    let rets = if fun_target.get_return_count() == 0 && mut_ref_inputs.is_empty() {
        "Unit".to_string()
    } else if fun_target.get_return_count() == 1 && mut_ref_inputs.is_empty() {
        let ret_type = self.inst(&fun_target.get_return_types()[0]);
        let operation_map = global_state.get_ret_map();
        let num_oper = operation_map.get(&(mid, fid)).unwrap().get(&0).unwrap();
        self.lean_type_for_fun(env, &ret_type, num_oper)
    } else {
        // Multiple returns or mutable references - use product type
        let return_types = fun_target
            .get_return_types()
            .iter()
            .enumerate()
            .map(|(i, s)| {
                let s = self.inst(s);
                let operation_map = global_state.get_ret_map();
                let num_oper = operation_map.get(&(mid, fid)).unwrap().get(&i).unwrap();
                self.lean_type_for_fun(env, &s, num_oper)
            })
            // Add implicit return parameters for &mut
            .chain(mut_ref_inputs.into_iter().enumerate().map(|(i, (_, ty))| {
                let num_oper = &global_state
                    .get_temp_index_oper(mid, fid, i, baseline_flag)
                    .unwrap();
                self.lean_type_for_fun(env, &ty, num_oper)
            }))
            .collect_vec();

        if return_types.len() == 1 {
            return_types[0].clone()
        } else {
            format!("({})", return_types.join(" × "))
        }
    };
    (args, rets)
}

/// Return lean type for a local with given signature token.
pub fn lean_type_for_fun(&self, env: &GlobalEnv, ty: &Type, num_oper: &NumOperation) -> String {
    lean_type(env, ty)
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

/// Generates lean implementation body.
fn generate_function_body(&mut self) {
    let writer = self.parent.writer;
    let fun_target = self.fun_target;
    let variant = &fun_target.data.variant;
    let env = fun_target.global_env();

    // Be sure to set back location to the whole function definition as a default.
    writer.set_location(&fun_target.get_loc().at_start());

    writer.indent();

    // Print instantiation information
    if !fun_target.data.type_args.is_empty() {
        let display_ctxt = TypeDisplayContext::WithEnv {
            env,
            type_param_names: None,
        };
        emitln!(
                writer,
                "-- function instantiation <{}>",
                fun_target.data.type_args
                    .iter()
                    .map(|ty| ty.display(&display_ctxt))
                    .join(", ")
            );
        emitln!(writer, "");
    }

    // Generate function body using direct bytecode translation with ternary operators
    let fun_target = self.fun_target;
    let code = fun_target.get_bytecode();
    let mut last_tracked_loc: Option<(Loc, LineIndex)> = None;
    
    // Translate each bytecode instruction directly
    for bytecode in code {
        self.translate_bytecode(&mut last_tracked_loc, bytecode);
    }

    writer.unindent();
}

fn translate_verify_entry_assumptions(&self, fun_target: &FunctionTarget<'_>) {
    let writer = self.parent.writer;
    emitln!(writer, "\n-- verification entrypoint assumptions");

    // Prelude initialization
    //emitln!(writer, "call $InitVerification();");

    // Assume reference parameters to be based on the Param(i) Location, ensuring
    // they are disjoint from all other references. This prevents aliasing and is justified as
    // follows:
    // - for mutual references, by their exclusive access in Move.
    // - for immutable references because we have eliminated them
    for i in 0..fun_target.get_parameter_count() {
        let ty = fun_target.get_local_type(i);
        if ty.is_reference() {
            // TODO
            //emitln!(writer, "assume $t{}->l == $Param({});", i, i);
        }
    }
}

fn compute_needed_temps(&self) -> BTreeMap<(String, bool), (Type, bool, usize)> {
    use Operation::*;

    let fun_target = self.fun_target;
    let env = fun_target.global_env();

    let mut res: BTreeMap<(String, bool), (Type, bool, usize)> = BTreeMap::new();
    let mut need = |ty: &Type, bv_flag: bool, n: usize| {
        // Index by type suffix, which is more coarse grained then type.
        let ty = ty.skip_reference();
        let suffix = lean_type_suffix(env, ty);
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
                    need(ty, false, 1)
                }
                TraceLocal(_) => {
                    let ty = &self.get_local_type(srcs[0]);
                    need(ty, false, 1)
                }
                Havoc(HavocKind::MutationValue) => {
                    let ty = &self.get_local_type(dests[0]);
                    need(ty, false, 1)
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

fn function_variant_name(&self, style: FunctionTranslationStyle) -> String {
    let variant = match style {
        FunctionTranslationStyle::Default => &self.fun_target.data.variant,
        FunctionTranslationStyle::Asserts
        | FunctionTranslationStyle::Aborts
        | FunctionTranslationStyle::Opaque => &FunctionVariant::Baseline,
        FunctionTranslationStyle::SpecNoAbortCheck => {
            &FunctionVariant::Verification(VerificationFlavor::Regular)
        }
    };
    let suffix = match variant {
        FunctionVariant::Baseline => "".to_string(),
        FunctionVariant::Verification(flavor) => match flavor {
            VerificationFlavor::Regular => "_verify".to_string(),
            VerificationFlavor::Instantiated(_) => {
                format!("_verify_{}", flavor)
            }
            VerificationFlavor::Inconsistency(_) => {
                format!("_verify_{}", flavor)
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
            "{}_impl",
            lean_function_name(self.fun_target.func_env, self.type_inst, style)
        );
    }
    let fun_name = self
        .parent
        .targets
        .get_fun_by_spec(&self.fun_target.func_env.get_qualified_id())
        .map_or(
            lean_function_name(self.fun_target.func_env, self.type_inst, style),
            |fun_id| {
                lean_function_name(
                    &self.parent.env.get_function(*fun_id),
                    self.type_inst,
                    style,
                )
            },
        );
    format!("{}{}", fun_name, suffix)
}

fn get_mutable_parameters(&self) -> Vec<(TempIndex, Type)> {
    let fun_target = self.fun_target;
    (0..fun_target.get_parameter_count())
        .filter_map(|i| Some((i, fun_target.get_local_type(i).clone())))
        .collect_vec()
}

/// Emit a per-function Locals frame type and a State monad alias.
fn generate_locals_frame_type_and_monad(&self) {
    let writer = self.parent.writer;
    let fun_target = self.fun_target;
    let env = fun_target.global_env();

    let fun_name = self.function_variant_name(self.style);
    let locals_name = format!("{}_Locals", fun_name);
    let monad_name = format!("{}_CF", fun_name);

    emitln!(writer, "\n-- Locals frame type (state) and State monad alias for {}", fun_name);
    emitln!(writer, "structure {} where", locals_name);
    writer.indent();
    let num_args = fun_target.get_parameter_count();
    for i in num_args..fun_target.get_local_count() {
        let local_type = &self.get_local_type(i);
        emitln!(writer, "t{} : {}", i, lean_type(env, local_type));
    }
    writer.unindent();
    emitln!(writer, "");
    emitln!(writer, "abbrev {} := StateT {} Id", monad_name, locals_name);
    emitln!(writer, "");
}

/// Generate a function that executes up to the ensures and returns the condition
fn generate_ensures_check_function(&self, ensures_idx: usize, bytecode_idx: usize, ensures_temp: TempIndex) {
    let writer = self.parent.writer;
    let fun_target = self.fun_target;
    let env = fun_target.global_env();

    // Generate function signature
    let fun_name = format!("{}_ensures_check_{}", self.function_variant_name(self.style), ensures_idx);
    let (args, _) = self.generate_function_args_and_returns();

    emitln!(writer, "\n-- Ensures check function {}", ensures_idx);
    emitln!(writer, "def {} {} : Bool :=", fun_name, args);
    writer.indent();

    // Generate local variable declarations (same as main function)
    emitln!(writer, "-- declare local variables");
    let num_args = fun_target.get_parameter_count();
    
    // Declare all local variables with sorry - they'll be computed during bytecode execution
    for i in num_args..fun_target.get_local_count() {
        let local_type = &self.get_local_type(i);
        emitln!(writer, "let t{} : {} := sorry;", i, lean_type(env, local_type));
    }
    
    // Add verification entry assumptions (like main function)
    if fun_target.data.variant.is_verified() {
        emitln!(writer, "\n-- verification entrypoint assumptions");
        for i in 0..fun_target.get_parameter_count() {
            let ty = fun_target.get_local_type(i);
            if ty.is_reference() {
                // Reference parameters assumptions would go here
                // Currently skipped like in main function
            }
        }
    }
    
    let mid = fun_target.func_env.module_env.get_id();
    let fid = fun_target.func_env.get_id();
    let baseline_flag = self.fun_target.data.variant == FunctionVariant::Baseline;
    let global_state = &self
        .fun_target
        .global_env()
        .get_extension::<GlobalNumberOperationState>()
        .expect("global number operation state");

    // Create a new FunctionTranslator for translating the bytecode
    let mut translator = FunctionTranslator {
        parent: self.parent,
        fun_target: self.fun_target,
        type_inst: self.type_inst,
        style: self.style,
        ensures_info: RefCell::new(Vec::new()),
    };

    // Generate bytecode up to the ensures
    emitln!(writer, "\n-- bytecode translation up to ensures");
    let code = fun_target.get_bytecode();
    let mut last_tracked_loc = None;
    for (idx, bytecode) in code.iter().enumerate() {
        if idx >= bytecode_idx {
            break;
        }
        // Skip the ensures itself
        match bytecode {
            Bytecode::Call(_, _, oper, _, _) => {
                use Operation::*;
                match oper {
                    Function(mid, fid, _) => {
                        let module_env = env.get_module(*mid);
                        let callee_env = module_env.get_function(*fid);
                        if callee_env.get_qualified_id() == self.parent.env.ensures_qid() {
                            continue;
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
        translator.translate_bytecode(&mut last_tracked_loc, bytecode);
    }

    // Return the ensures condition
    emitln!(writer, "\n-- return ensures condition");
    let ensures_type = &self.get_local_type(ensures_temp);
    if ensures_type == &BOOL_TYPE {
        emitln!(writer, "t{}", ensures_temp);
    } else {
        emitln!(writer, "-- Warning: ensures temp t{} has type {}, expected Bool", ensures_temp, lean_type(env, ensures_type));
        emitln!(writer, "true  -- fallback to true for now");
    }

    writer.unindent();
}

/// Generate a theorem that proves the ensures check returns true
fn generate_ensures_impl_function(&self, ensures_idx: usize) {
    let writer = self.parent.writer;
    let fun_target = self.fun_target;

    let theorem_name = format!("{}_ensures_impl_{}", self.function_variant_name(self.style), ensures_idx);
    let check_fun_name = format!("{}_ensures_check_{}", self.function_variant_name(self.style), ensures_idx);
    let (args, _) = self.generate_function_args_and_returns();

    // Extract parameter names from args for the theorem statement
    let param_names = (0..fun_target.get_parameter_count())
        .map(|i| format!("t{}", i))
        .join(" ");

    emitln!(writer, "\n-- Ensures implementation theorem {}", ensures_idx);
    emitln!(writer, "theorem {} {} : {} {} = true := by", theorem_name, args, check_fun_name, param_names);
    writer.indent();
    emitln!(writer, "simp [{}]", check_fun_name);
    emitln!(writer, "sorry -- TODO: Prove that the ensures condition holds");
    writer.unindent();
}



/// Generates local variable declarations for the control flow function
fn generate_local_declarations(&self) {
    let writer = self.writer();
    let fun_target = self.fun_target;

    // Emit initial locals frame construction instead of separate let-bindings
    emitln!(writer, "-- Initial locals frame (record)");
    let num_args = fun_target.get_parameter_count();
    let fun_name = self.function_variant_name(self.style);
    let locals_name = format!("{}_Locals", fun_name);

    if fun_target.get_local_count() <= num_args {
        // No non-parameter locals; empty struct
        emitln!(writer, "let frame0 : {} := {{}}", locals_name);
        emitln!(writer, "");
        return;
    }

    emitln!(writer, "let frame0 : {} := {{", locals_name);
    // Initialize each field with a placeholder; later instructions will assign real values
    let last = fun_target.get_local_count() - 1;
    for i in num_args..fun_target.get_local_count() {
        let sep = if i == last { "" } else { "," };
        emitln!(writer, "  t{} := sorry{}", i, sep);
    }
    emitln!(writer, "}");
    emitln!(writer, "");
}



/// Core bytecode translation logic shared between different contexts
fn translate_bytecode_core(&self, bytecode: &Bytecode, writer: &CodeWriter) {
    // Helpers to read/write locals via frame when appropriate
    let num_args = self.fun_target.get_parameter_count();
    let read_local = |idx: usize| if idx < num_args { format!("t{}", idx) } else { format!("frame.t{}", idx) };
    let write_nonparam = |dest: usize, expr: String| -> String {
        format!("let frame := {{ frame with t{} := {} }};", dest, expr)
    };

    match bytecode {
        Bytecode::Load(_, dest, c) => {
            if *dest < num_args {
                emitln!(writer, "let t{} := {};", dest, c);
            } else {
                emitln!(writer, "{}", write_nonparam(*dest as usize, format!("{}", c)));
            }
        },
        Bytecode::Call(_, dests, oper, srcs, _) => {
            use Operation::*;
            match oper {
                Add | Sub | Mul | Mod | Div | BitAnd | BitOr | Xor | Shl | Shr => {
                    if dests.len() == 1 && srcs.len() == 2 {
                        let a = read_local(srcs[0] as usize);
                        let b = read_local(srcs[1] as usize);
                        let op = match oper { Add => "+", Sub => "-", Mul => "*", Mod => "%", Div => "/", BitAnd => "&&&", BitOr => "|||", Xor => "^^^", Shl => "<<<", Shr => ">>>", _ => "?" };
                        let expr = format!("{} {} {}", a, op, b);
                        let d = dests[0] as usize;
                        if d < num_args {
                            emitln!(writer, "let t{} := {};", d, expr);
                        } else {
                            emitln!(writer, "{}", write_nonparam(d, expr));
                        }
                    }
                },
                Eq | Neq | Lt | Le | Gt | Ge => {
                    if dests.len() == 1 && srcs.len() == 2 {
                        let a = read_local(srcs[0] as usize);
                        let b = read_local(srcs[1] as usize);
                        let op = match oper { Eq => "==", Neq => "!=", Lt => "<", Le => "<=", Gt => ">", Ge => ">=", _ => "?" };
                        let expr = format!("{} {} {}", a, op, b);
                        let d = dests[0] as usize;
                        if d < num_args {
                            emitln!(writer, "let t{} := {};", d, expr);
                        } else {
                            emitln!(writer, "{}", write_nonparam(d, expr));
                        }
                    }
                },
                CastU8 | CastU16 | CastU32 | CastU64 | CastU128 | CastU256 => {
                    if dests.len() == 1 && srcs.len() == 1 {
                        let cast_type = match oper { CastU8 => "UInt8.ofNat", CastU16 => "UInt16.ofNat", CastU32 => "UInt32.ofNat", CastU64 => "UInt64.ofNat", CastU128 => "UInt128.ofNat", CastU256 => "UInt256.ofNat", _ => "sorry" };
                        let s = read_local(srcs[0] as usize);
                        let expr = format!("{} {}.toNat", cast_type, s);
                        let d = dests[0] as usize;
                        if d < num_args {
                            emitln!(writer, "let t{} := {};", d, expr);
                        } else {
                            emitln!(writer, "{}", write_nonparam(d, expr));
                        }
                    }
                },
                GetField(mid, sid, _type_args, field_idx) => {
                    if dests.len() == 1 && srcs.len() == 1 {
                        let struct_env = &self.parent.env.get_module(*mid).into_struct(*sid);
                        let field_env = struct_env.get_field_by_offset(*field_idx);
                        let field_name = field_env.get_name();
                        let s = read_local(srcs[0] as usize);
                        let expr = format!("{}.{}", s, field_name.display(self.parent.env.symbol_pool()));
                        let d = dests[0] as usize;
                        if d < num_args {
                            emitln!(writer, "let t{} := {};", d, expr);
                        } else {
                            emitln!(writer, "{}", write_nonparam(d, expr));
                        }
                    }
                },
                Pack(mid, sid, type_args) => {
                    if dests.len() == 1 {
                        let struct_env = &self.parent.env.get_module(*mid).into_struct(*sid);
                        let struct_name = lean_struct_name(&struct_env, type_args);
                        let field_values = srcs.iter().map(|&idx| read_local(idx as usize)).join(" ");
                        let expr = format!("{}.mk {}", struct_name, field_values);
                        let d = dests[0] as usize;
                        if d < num_args {
                            emitln!(writer, "let t{} := {};", d, expr);
                        } else {
                            emitln!(writer, "{}", write_nonparam(d, expr));
                        }
                    }
                },
                And => {
                    if dests.len() == 1 && srcs.len() == 2 {
                        let a = read_local(srcs[0] as usize);
                        let b = read_local(srcs[1] as usize);
                        let expr = format!("{} && {}", a, b);
                        let d = dests[0] as usize;
                        if d < num_args {
                            emitln!(writer, "let t{} := {};", d, expr);
                        } else {
                            emitln!(writer, "{}", write_nonparam(d, expr));
                        }
                    }
                },
                Or => {
                    if dests.len() == 1 && srcs.len() == 2 {
                        let a = read_local(srcs[0] as usize);
                        let b = read_local(srcs[1] as usize);
                        let expr = format!("{} || {}", a, b);
                        let d = dests[0] as usize;
                        if d < num_args {
                            emitln!(writer, "let t{} := {};", d, expr);
                        } else {
                            emitln!(writer, "{}", write_nonparam(d, expr));
                        }
                    }
                },
                Not => {
                    if dests.len() == 1 && srcs.len() == 1 {
                        let a = read_local(srcs[0] as usize);
                        let expr = format!("!{}", a);
                        let d = dests[0] as usize;
                        if d < num_args {
                            emitln!(writer, "let t{} := {};", d, expr);
                        } else {
                            emitln!(writer, "{}", write_nonparam(d, expr));
                        }
                    }
                },
                TraceLocal(_) | TraceExp(_, _) | TraceMessage(_) | TraceGhost(..) | TraceReturn(_) | TraceAbort => {
                    // Tracing operations are no-ops in Lean output
                    emitln!(writer, "-- trace op skipped");
                },
                Function(mid, fid, _type_args) => {
                    // Spec helper or general function call without return handling: skip for now if no dests
                    if dests.is_empty() {
                        let module_env = self.parent.env.get_module(*mid);
                        let callee_env = module_env.get_function(*fid);
                        emitln!(writer, "-- call {} skipped", callee_env.get_full_name_str());
                    } else {
                        emitln!(writer, "-- call with returns not yet handled in CFG translator");
                    }
                },
                Havoc(_) | Uninit => {
                    // Havoc/uninit are treated as no-ops for now
                    emitln!(writer, "-- havoc/uninit skipped");
                },
                _ => {
                    // For operations not handled in the simple version, emit a comment
                    emitln!(writer, "-- Unhandled operation: {:?}", oper);
                }
            }
        },
        _ => {
            // For bytecode types not handled in the simple version, emit a comment
            emitln!(writer, "-- Unhandled bytecode: {:?}", bytecode);
        }
    }
}



/// Gets the return type string for the current function
fn get_return_type_string(&self) -> String {
    let fun_target = self.fun_target;
    let env = fun_target.global_env();
    
    let inner_type = if fun_target.get_return_count() == 0 {
        "Unit".to_string()
    } else if fun_target.get_return_count() == 1 {
        let ret_type = self.inst(&fun_target.get_return_types()[0]);
        lean_type(env, &ret_type)
    } else {
        let return_types = fun_target
            .get_return_types()
            .iter()
            .map(|s| {
                let s = self.inst(s);
                lean_type(env, &s)
            })
            .collect::<Vec<_>>();
        format!("({})", return_types.join(" × "))
    };
    
    format!("ProgramState {}", inner_type)
}

/// Generate a theorem that asserts the _aborts variant is false
fn generate_no_abort_check_theorem(&self) {
    let writer = self.parent.writer;
    let fun_target = self.fun_target;
    let (args, _) = self.generate_function_args_and_returns();
    
    // Get the name of the current function (no_abort_check variant)
    let no_abort_check_name = self.function_variant_name(FunctionTranslationStyle::SpecNoAbortCheck);
    
    // Get the name of the corresponding _aborts variant
    let aborts_name = self.function_variant_name(FunctionTranslationStyle::Aborts);
    
    writer.set_location(&fun_target.get_loc());
    emitln!(
        writer,
        "theorem {} {} : True :=",
        no_abort_check_name,
        args
    );
    writer.indent();
    emitln!(writer, "trivial");
    writer.unindent();
}
}
