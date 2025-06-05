use crate::lean_backend::lean_helpers::{
    lean_enum_name, lean_function_name, lean_modifies_memory_name, lean_resource_memory_name,
    lean_struct_name, lean_temp_from_suffix, lean_type, lean_type_param, lean_type_suffix,
    lean_type_suffix_bv, FunctionTranslationStyle,
};
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
    EnumEnv, FunId, FunctionEnv, GlobalEnv, Loc, QualifiedId, RefType, StructEnv,
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
use move_stackless_bytecode::stackless_bytecode::Operation::{
    Add, And, BitAnd, BitOr, BorrowLoc, CastU128, CastU16, CastU256, CastU32, CastU64, CastU8,
    Destroy, Div, EmitEvent, Eq, EventStoreDiverge, FreezeRef, Ge, Gt, Le, Lt, Mod, Mul, Neq, Not,
    Or, PackRef, PackRefDeep, ReadRef, Shl, Shr, Stop, Sub, TraceAbort, Uninit, UnpackRef,
    UnpackRefDeep, WriteRef, Xor,
};
use move_stackless_bytecode::stackless_bytecode::{
    AbortAction, BorrowEdge, BorrowNode, Bytecode, HavocKind, Operation, PropKind,
};
use move_stackless_bytecode::{
    mono_analysis, spec_global_variable_analysis, verification_analysis,
};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::str::FromStr;

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

            for ref fun_env in module_env.get_functions() {
                if fun_env.is_native() || intrinsic_fun_ids.contains(&fun_env.get_qualified_id()) {
                    continue;
                }

                if self.targets.is_spec(&fun_env.get_qualified_id()) {
                    verified_functions_count += 1;

                    if self
                        .targets
                        .scenario_specs()
                        .contains(&fun_env.get_qualified_id())
                    {
                        if self.targets.has_target(
                            fun_env,
                            &FunctionVariant::Verification(VerificationFlavor::Regular),
                        ) {
                            let fun_target = self.targets.get_target(
                                fun_env,
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
                        continue;
                    }

                    self.translate_function_style(fun_env, FunctionTranslationStyle::Default);
                    self.translate_function_style(fun_env, FunctionTranslationStyle::Asserts);
                    self.translate_function_style(fun_env, FunctionTranslationStyle::Aborts);
                    self.translate_function_style(
                        fun_env,
                        FunctionTranslationStyle::SpecNoAbortCheck,
                    );
                    self.translate_function_style(fun_env, FunctionTranslationStyle::Opaque);
                } else {
                    let fun_target = self.targets.get_target(fun_env, &FunctionVariant::Baseline);
                    if !verification_analysis::get_info(&fun_target).inlined {
                        continue;
                    }

                    if let Some(spec_qid) =
                        self.targets.get_spec_by_fun(&fun_env.get_qualified_id())
                    {
                        if !self.targets.no_verify_specs().contains(spec_qid) {
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
        // Emit any finalization items required by spec translation.
        self.spec_translator.finalize();
        info!("{} verification conditions", verified_functions_count);
    }

    fn translate_function_style(&self, fun_env: &FunctionEnv, style: FunctionTranslationStyle) {
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
            return;
        }
        let spec_fun_target = self.targets.get_target(&fun_env, &variant);
        if !variant.is_verified() && !verification_analysis::get_info(&spec_fun_target).inlined {
            return;
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
        let mut dummy_targets = FunctionTargetsHolder::new();
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
            FunctionTranslator {
                parent: self,
                fun_target: &fun_target,
                type_inst: &[],
                style,
                ensures_info: RefCell::new(Vec::new()),
            }
            .translate();
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
                    .translate();
                });
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

        if struct_env.is_native() || struct_env.is_intrinsic() {
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

        // Emit data type
        let struct_name = boogie_struct_name(struct_env, self.type_inst);
        emitln!(writer, "datatype {} {{", struct_name);

        // Emit constructor
        let fields = struct_env
            .get_fields()
            .map(|field| {
                format!(
                    "${}: {}",
                    field.get_name().display(env.symbol_pool()),
                    self.boogie_type_for_struct_field(
                        &field.get_id(),
                        env,
                        &self.inst(&field.get_type())
                    )
                )
            })
            .join(", ");
        emitln!(writer, "    {}({})", struct_name, fields);
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
                    let args = fields
                        .iter()
                        .enumerate()
                        .map(|(p, f)| {
                            if p == pos {
                                "x".to_string()
                            } else {
                                format!("s->{}", boogie_field_sel(f, self.type_inst))
                            }
                        })
                        .join(", ");
                    emitln!(writer, "{}({})", struct_name, args);
                },
            );
        }

        // Emit $IsValid function.
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

    /// Translates the given struct.
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

impl FunctionTranslator<'_> {
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
            "-- fun {} [{}] {}",
            env.display(&qid),
            fun_target.data.variant,
            fun_target.get_loc().display(env)
        );
        self.generate_function_sig();

        if self.fun_target.func_env.get_qualified_id() == self.parent.env.global_qid() {
            todo!()
        } else if self.fun_target.func_env.get_qualified_id() == self.parent.env.havoc_global_qid()
        {
            todo!()
        } else {
            self.generate_function_body();
        }
        emitln!(self.parent.writer);
        
        // Generate additional functions for ensures if found
        let ensures_info = self.ensures_info.borrow().clone();
        if !ensures_info.is_empty() && self.style == FunctionTranslationStyle::Default {
            for (idx, (bytecode_idx, ensures_temp)) in ensures_info.iter().enumerate() {
                // Generate the first function: copy up to ensures and return the condition
                self.generate_ensures_check_function(idx, *bytecode_idx, *ensures_temp);
                
                // Generate the second function: empty with todo
                self.generate_ensures_impl_function(idx);
            }
        }
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

        // Helper function to get a a string for a local
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
                    WriteBack(node, edge) => {
                        todo!()
                    }
                    IsParent(node, edge) => {
                        todo!()
                    }
                    BorrowLoc => {
                        todo!()
                    }
                    ReadRef => {
                        todo!()
                    }
                    WriteRef => {
                        todo!()
                    }
                    Function(mid, fid, inst) => {
                        let inst = &self.inst_slice(inst);
                        let module_env = env.get_module(*mid);
                        let callee_env = module_env.get_function(*fid);

                        let mut args_str = srcs.iter().cloned().map(str_local).join(" ");
                        let dest_str = dests
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
                            .join(" ");

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
                            todo!()
                        }

                        if callee_env.get_qualified_id() == self.parent.env.asserts_qid()
                            && self.style == FunctionTranslationStyle::Aborts
                        {
                            todo!()
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
                                emitln!(
                                    self.writer(),
                                    "let abort_if_cond := {} {};",
                                    self.function_variant_name(FunctionTranslationStyle::Aborts),
                                    args_str,
                                );
                                emitln!(self.writer(), "-- abort_flag := !abort_if_cond");
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
                                    &ProverOptions::get(self.fun_target.global_env()).verify_scope,
                                );
                            let mut fun_name = lean_function_name(
                                &callee_env,
                                inst,
                                FunctionTranslationStyle::Default,
                            );

                            if self
                                .parent
                                .targets
                                .get_fun_by_spec(&self.fun_target.func_env.get_qualified_id())
                                == Some(&QualifiedId {
                                    module_id: *mid,
                                    id: *fid,
                                })
                            {
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
                        todo!()
                    }
                    Unpack(mid, sid, inst) => {
                        todo!()
                    }
                    PackVariant(mid, eid, vid, inst) => {
                        todo!()
                    }
                    UnpackVariant(mid, eid, vid, _inst, ref_type) => {
                        todo!()
                    }
                    BorrowField(mid, sid, inst, field_offset) => {
                        todo!()
                    }
                    GetField(mid, sid, inst, field_offset) => {
                        todo!()
                    }
                    Exists(mid, sid, inst) => {
                        todo!()
                    }
                    BorrowGlobal(mid, sid, inst) => {
                        todo!()
                    }
                    GetGlobal(mid, sid, inst) => {
                        todo!()
                    }
                    MoveTo(mid, sid, inst) => {
                        todo!()
                    }
                    MoveFrom(mid, sid, inst) => {
                        todo!()
                    }
                    Havoc(HavocKind::Value) | Havoc(HavocKind::MutationAll) => {
                        todo!()
                    }
                    Havoc(HavocKind::MutationValue) => {
                        todo!()
                    }
                    Stop => {
                        todo!()
                    }
                    CastU8 | CastU16 | CastU32 | CastU64 | CastU128 | CastU256 => {
                        todo!()
                    }
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
                        let sh_oper_str = if oper == &Shl { "Left" } else { "Right" };

                        emitln!(
                            self.writer(),
                            "let {} := Nat.shift{} {} {};",
                            str_local(dest),
                            sh_oper_str,
                            str_local(op1),
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
                            Xor => "^",
                            BitOr => "|",
                            BitAnd => "&",
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
                    Uninit => {
                        todo!()
                    }
                    Destroy => {}
                    TraceLocal(idx) => {
                        
                    }
                    TraceReturn(i) => {
                        
                    }
                    TraceAbort =>
                        todo!(),
                    TraceExp(kind, node_id) => {
                        todo!()
                    }
                    TraceMessage(message) =>
                        todo!(),
                    TraceGhost(ghost_type, value_type) => {
                        todo!()
                    }
                    EmitEvent => {
                        todo!()
                    }
                    EventStoreDiverge => {
                        todo!()
                    }
                    TraceGlobalMem(mem) => {
                        todo!()
                    }
                }
                match aa {
                    Some(AbortAction::Jump(target, code)) => {
                        
                    }
                    Some(AbortAction::Check) => {
                        todo!()
                    }
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
            }
            Jump(_, _) => {
                // Jumps are control flow, not directly translated in functional style
            }
            Branch(_, _, _, _) => {
                // Branches are control flow, not directly translated in functional style
            }
            Assign(_, dest, src, _) => {
                // Simple assignment - in functional style this would be a let binding
                emitln!(self.writer(), "-- let {} := {} (assignment)", str_local(*dest), str_local(*src));
            }
            Load(_, dest, c) => {
                // Load constant
                emitln!(self.writer(), "let {} := {};", str_local(*dest), c);
            }
            un => {
                println!("Unimplemented bytecode: {:?}", un)
            }
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
            FunctionTranslationStyle::Aborts => "Bool".to_string(),
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

    /// Generate boogie representation of function args and return args.
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
        let instantiation = &fun_target.data.type_args;
        let env = fun_target.global_env();
        let baseline_flag = self.fun_target.data.variant == FunctionVariant::Baseline;
        let global_state = &self
            .fun_target
            .global_env()
            .get_extension::<GlobalNumberOperationState>()
            .expect("global number operation state");

        // Be sure to set back location to the whole function definition as a default.
        writer.set_location(&fun_target.get_loc().at_start());

        writer.indent();

        // Print instantiation information
        if !instantiation.is_empty() {
            let display_ctxt = TypeDisplayContext::WithEnv {
                env,
                type_param_names: None,
            };
            emitln!(
                writer,
                "-- function instantiation <{}>",
                instantiation
                    .iter()
                    .map(|ty| ty.display(&display_ctxt))
                    .join(", ")
            );
            emitln!(writer, "");
        }

        // Generate local variable declarations. They need to appear first in lean.
        emitln!(writer, "-- declare local variables");
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
            // Skip local variable declarations for now in Lean - we'll declare them inline
        }

        // Generate declarations for modifies condition.
        let mut mem_inst_seen = BTreeSet::new();
        for qid in fun_target.get_modify_ids() {
            let memory = qid.instantiate(self.type_inst);
            if !mem_inst_seen.contains(&memory) {
                // Skip modifies declarations for now
                mem_inst_seen.insert(memory);
            }
        }

        // Generate memory snapshot variable declarations.
        let code = fun_target.get_bytecode();
        let labels = code
            .iter()
            .filter_map(|bc| match bc {
                SaveMem(_, lab, mem) => Some((lab, mem)),
                _ => None,
            })
            .collect::<BTreeSet<_>>();

        // Initial assumptions
        if variant.is_verified() {
            self.translate_verify_entry_assumptions(fun_target);
        }

        // Generate bytecode
        emitln!(writer, "\n-- bytecode translation starts here");
        let mut last_tracked_loc = None;
        for bytecode in code.iter() {
            self.translate_bytecode(&mut last_tracked_loc, bytecode);
        }

        // The return value will be handled by the Ret bytecode instruction
        // No need to add an explicit return here

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
                todo!()
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
        
        // Generate local variable declarations
        emitln!(writer, "-- declare local variables");
        let num_args = fun_target.get_parameter_count();
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
        emitln!(writer, "t{}", ensures_temp);
        
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
        emitln!(writer, "-- TODO: Prove that the ensures condition holds");
        writer.unindent();
    }
}
