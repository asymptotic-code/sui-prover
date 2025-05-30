// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use std::{collections::BTreeSet, fs};

use itertools::Itertools;
#[allow(unused_imports)]
use log::{debug, info, warn};
use serde::{Deserialize, Serialize};
use tera::{Context, Tera};

use move_model::{
    code_writer::CodeWriter,
    emit, emitln,
    model::{DatatypeId, FunId, GlobalEnv, QualifiedId},
    ty::{PrimitiveType, Type},
};
use move_stackless_bytecode::{
    dynamic_field_analysis::{self, NameValueInfo},
    function_target_pipeline::FunctionVariant,
    mono_analysis::{self, MonoInfo},
};

use crate::boogie_backend::{
    boogie_helpers::{boogie_bv_type, boogie_module_name, boogie_type, boogie_type_suffix_bv},
    bytecode_translator::has_native_equality,
    options::{BoogieOptions, VectorTheory},
};

const PRELUDE_TEMPLATE: &[u8] = include_bytes!("prelude/prelude.bpl");
const NATIVE_TEMPLATE: &[u8] = include_bytes!("prelude/native.bpl");
const VECTOR_ARRAY_THEORY: &[u8] = include_bytes!("prelude/vector-array-theory.bpl");
const VECTOR_ARRAY_INTERN_THEORY: &[u8] = include_bytes!("prelude/vector-array-intern-theory.bpl");
const VECTOR_SMT_SEQ_THEORY: &[u8] = include_bytes!("prelude/vector-smt-seq-theory.bpl");
const VECTOR_SMT_ARRAY_THEORY: &[u8] = include_bytes!("prelude/vector-smt-array-theory.bpl");
const VECTOR_SMT_ARRAY_EXT_THEORY: &[u8] =
    include_bytes!("prelude/vector-smt-array-ext-theory.bpl");
const MULTISET_ARRAY_THEORY: &[u8] = include_bytes!("prelude/multiset-array-theory.bpl");
const TABLE_ARRAY_THEORY: &[u8] = include_bytes!("prelude/table-array-theory.bpl");

// TODO use named addresses
const BCS_MODULE: &str = "0x1::bcs";
const EVENT_MODULE: &str = "0x1::event";

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, Default)]
struct TypeInfo {
    name: String,
    suffix: String,
    has_native_equality: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, Default)]
struct BvInfo {
    base: usize,
    max: String,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, Default)]
struct TableImpl {
    struct_name: String,
    insts: Vec<(TypeInfo, TypeInfo)>,
    fun_new: String,
    fun_add: String,
    fun_borrow: String,
    fun_borrow_mut: String,
    fun_remove: String,
    fun_contains: String,
    fun_length: String,
    fun_is_empty: String,
    fun_destroy_empty: String,
    fun_drop: String,
    fun_value_id: String,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, Default)]
struct DynamicFieldInfo {
    struct_name: String,
    insts: Vec<(TypeInfo, TypeInfo)>,
    fun_add: String,
    fun_borrow: String,
    fun_borrow_mut: String,
    fun_remove: String,
    // fun_exists: String,
    fun_exists_with_type: String,
}

/// Help generating vector functions for bv types
fn bv_helper() -> Vec<BvInfo> {
    let mut bv_info = vec![];
    let bv_8 = BvInfo {
        base: 8,
        max: "255".to_string(),
    };
    bv_info.push(bv_8);
    let bv_16 = BvInfo {
        base: 16,
        max: "65535".to_string(),
    };
    bv_info.push(bv_16);
    let bv_32 = BvInfo {
        base: 32,
        max: "2147483647".to_string(),
    };
    bv_info.push(bv_32);
    let bv_64 = BvInfo {
        base: 64,
        max: "18446744073709551615".to_string(),
    };
    bv_info.push(bv_64);
    let bv_128 = BvInfo {
        base: 128,
        max: "340282366920938463463374607431768211455".to_string(),
    };
    bv_info.push(bv_128);
    let bv_256 = BvInfo {
        base: 256,
        max: "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            .to_string(),
    };
    bv_info.push(bv_256);
    bv_info
}

/// Adds the prelude to the generated output.
pub fn add_prelude(
    env: &GlobalEnv,
    options: &BoogieOptions,
    writer: &CodeWriter,
) -> anyhow::Result<()> {
    emit!(writer, "\n// ** Expanded prelude\n\n");
    let templ = |name: &'static str, cont: &[u8]| (name, String::from_utf8_lossy(cont).to_string());

    // Add the prelude template.
    let mut templates = vec![
        templ("native", NATIVE_TEMPLATE),
        templ("prelude", PRELUDE_TEMPLATE),
        // Add the basic array theory to make it available for inclusion in other theories.
        templ("vector-array-theory", VECTOR_ARRAY_THEORY),
    ];

    // Bind the chosen vector and multiset theory
    let vector_theory = match options.vector_theory {
        VectorTheory::BoogieArray => VECTOR_ARRAY_THEORY,
        VectorTheory::BoogieArrayIntern => VECTOR_ARRAY_INTERN_THEORY,
        VectorTheory::SmtArray => VECTOR_SMT_ARRAY_THEORY,
        VectorTheory::SmtArrayExt => VECTOR_SMT_ARRAY_EXT_THEORY,
        VectorTheory::SmtSeq => VECTOR_SMT_SEQ_THEORY,
    };
    templates.push(templ("vector-theory", vector_theory));
    templates.push(templ("multiset-theory", MULTISET_ARRAY_THEORY));
    templates.push(templ("table-theory", TABLE_ARRAY_THEORY));

    let mut context = Context::new();
    context.insert("options", options);

    let mono_info = mono_analysis::get_info(env);
    // Add vector instances implicitly used by the prelude.
    let implicit_vec_inst = vec![TypeInfo::new(
        env,
        options,
        &Type::Primitive(PrimitiveType::U8),
        false,
    )];
    // Used for generating functions for bv types in prelude
    let mut sh_instances = vec![8, 16, 32, 64, 128, 256];
    let mut bv_instances = bv_helper();
    // Skip bv for cvc5
    if options.use_cvc5 {
        sh_instances = vec![];
        bv_instances = vec![];
    }
    context.insert("sh_instances", &sh_instances);
    context.insert("bv_instances", &bv_instances);
    let mut vec_instances = mono_info
        .vec_inst
        .iter()
        .map(|ty| TypeInfo::new(env, options, ty, false))
        .chain(implicit_vec_inst)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect_vec();
    let mut table_instances = vec![];
    if let Some(table_qid) = env.table_qid() {
        table_instances.push(TableImpl::table(env, options, &mono_info, table_qid, false));
    }
    if let Some(object_table_qid) = env.object_table_qid() {
        table_instances.push(TableImpl::object_table(
            env,
            options,
            &mono_info,
            object_table_qid,
            false,
        ));
    }
    let mut dynamic_field_instances = vec![];
    for info in dynamic_field_analysis::get_env_info(env).dynamic_fields() {
        let (struct_qid, type_inst) = info.0.get_datatype().unwrap();
        if mono_info
            .structs
            .get(&struct_qid)
            .is_some_and(|type_inst_set| type_inst_set.contains(type_inst))
        {
            dynamic_field_instances.push(DynamicFieldInfo::dynamic_field(
                env, options, info.0, info.1, false,
            ));
            dynamic_field_instances.push(DynamicFieldInfo::object_dynamic_field(
                env, options, info.0, info.1, false,
            ));
        }
    }

    // let mut table_instances = mono_info
    //     .table_inst
    //     .iter()
    //     .map(|(qid, ty_args)| TableImpl::new(env, options, *qid, ty_args, false))
    //     .collect_vec();
    // If not using cvc5, generate vector functions for bv types
    if !options.use_cvc5 {
        let mut bv_vec_instances = mono_info
            .vec_inst
            .iter()
            .map(|ty| TypeInfo::new(env, options, ty, true))
            .filter(|ty_info| !vec_instances.contains(ty_info))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect_vec();
        // let mut bv_table_instances = mono_info
        //     .table_inst
        //     .iter()
        //     .map(|(qid, ty_args)| {
        //         let v_ty = ty_args.iter().map(|(_, vty)| vty).collect_vec();
        //         let bv_flag = v_ty.iter().all(|ty| ty.skip_reference().is_number());
        //         TableImpl::new(env, options, *qid, ty_args, bv_flag)
        //     })
        //     .filter(|map_impl| !table_instances.contains(map_impl))
        //     .collect_vec();
        vec_instances.append(&mut bv_vec_instances);
        // table_instances.append(&mut bv_table_instances);
    }
    context.insert("vec_instances", &vec_instances);

    if let Some(vec_set_module_env) = env.find_module_by_name(env.symbol_pool().make("vec_set")) {
        let vec_set_struct_env = vec_set_module_env
            .find_struct(env.symbol_pool().make("VecSet"))
            .unwrap();
        let vec_set_instances = mono_info
            .all_types
            .iter()
            .filter_map(|ty| match ty.get_datatype() {
                Some((did, tys)) if did == vec_set_struct_env.get_qualified_id() => Some(&tys[0]),
                _ => None,
            })
            .map(|ty| TypeInfo::new(env, options, ty, false))
            .collect_vec();
        context.insert("vec_set_instances", &vec_set_instances);
    }

    if let Some(vec_map_module_env) = env.find_module_by_name(env.symbol_pool().make("vec_map")) {
        let vec_map_struct_env = vec_map_module_env
            .find_struct(env.symbol_pool().make("VecMap"))
            .unwrap();
        let vec_map_instances = mono_info
            .all_types
            .iter()
            .filter_map(|ty| match ty.get_datatype() {
                Some((did, tys)) if did == vec_map_struct_env.get_qualified_id() => {
                    Some((&tys[0], &tys[1]))
                }
                _ => None,
            })
            .map(|(ty0, ty1)| {
                (
                    TypeInfo::new(env, options, ty0, false),
                    TypeInfo::new(env, options, ty1, false),
                )
            })
            .collect_vec();
        context.insert("vec_map_instances", &vec_map_instances);
    }

    context.insert("table_instances", &table_instances);
    context.insert("dynamic_field_instances", &dynamic_field_instances);
    let table_key_instances = table_instances
        .iter()
        .flat_map(|table| table.insts.iter().map(|(kty, _)| kty))
        .chain(
            dynamic_field_instances
                .iter()
                .flat_map(|dynamic_field| dynamic_field.insts.iter().map(|(kty, _)| kty)),
        )
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect_vec();
    context.insert("table_key_instances", &table_key_instances);
    let table_value_instances = table_instances
        .iter()
        .flat_map(|table| table.insts.iter().map(|(_, vty)| vty))
        .chain(
            dynamic_field_instances
                .iter()
                .flat_map(|dynamic_field| dynamic_field.insts.iter().map(|(_, vty)| vty)),
        )
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect_vec();
    context.insert("table_value_instances", &table_value_instances);

    let filter_native = |module: &str| {
        mono_info
            .native_inst
            .iter()
            .filter(|(id, _)| env.get_module(**id).get_full_name_str() == module)
            .flat_map(|(_, insts)| {
                insts.iter().map(|inst| {
                    inst.iter()
                        .map(|i| TypeInfo::new(env, options, i, false))
                        .collect::<Vec<_>>()
                })
            })
            .sorted()
            .collect_vec()
    };
    // make sure that all natives have only one type instantiations
    // because of this assertion, this function returns a `Vec<TypeInfo>`
    let filter_native_ensure_one_inst = |module: &str| {
        filter_native(module)
            .into_iter()
            .map(|mut insts| {
                assert_eq!(insts.len(), 1);
                insts.pop().unwrap()
            })
            .sorted()
            .collect_vec()
    };
    // make sure that all natives have exactly the same number of type instantiations,
    // this function returns a `Vec<Vec<TypeInfo>>`
    let filter_native_check_consistency = |module: &str| {
        let filtered = filter_native(module);
        let size = match filtered.first() {
            None => 0,
            Some(insts) => insts.len(),
        };
        assert!(filtered.iter().all(|insts| insts.len() == size));
        filtered
    };

    let bcs_instances = filter_native_ensure_one_inst(BCS_MODULE);
    context.insert("bcs_instances", &bcs_instances);
    let event_instances = filter_native_ensure_one_inst(EVENT_MODULE);
    context.insert("event_instances", &event_instances);

    // TODO: we have defined {{std}} for adaptable resolution of stdlib addresses but
    //   not used it yet in the templates.
    let std_addr = format!("${}", env.get_stdlib_address());
    let ext_addr = format!("${}", env.get_extlib_address());
    context.insert("std", &std_addr);
    context.insert("Ext", &ext_addr);

    // If a custom Boogie template is provided, add it as part of the templates and
    // add all type instances that use generic functions in the provided modules to the context.
    if let Some(custom_native_options) = options.custom_natives.clone() {
        templates.push(templ(
            "custom-natives",
            &custom_native_options.template_bytes,
        ));
        for (module_name, instance_name, expect_single_type_inst) in
            custom_native_options.module_instance_names
        {
            if expect_single_type_inst {
                context.insert(instance_name, &filter_native_ensure_one_inst(&module_name));
            } else {
                context.insert(
                    instance_name,
                    &filter_native_check_consistency(&module_name),
                );
            }
        }
    }

    let mut tera = Tera::default();
    tera.add_raw_templates(templates)?;

    let expanded_content = tera.render("prelude", &context)?;
    emitln!(writer, &expanded_content);

    if let Some(path) = &options.prelude_extra {
        if let Ok(content) = fs::read_to_string(path) {
            emitln!(writer, &content);
        }
    }

    Ok(())
}

impl TypeInfo {
    fn new(env: &GlobalEnv, options: &BoogieOptions, ty: &Type, bv_flag: bool) -> Self {
        let name_fun = if bv_flag { boogie_bv_type } else { boogie_type };
        Self {
            name: name_fun(env, ty),
            suffix: boogie_type_suffix_bv(env, ty, bv_flag),
            has_native_equality: has_native_equality(env, options, ty),
        }
    }
}

impl TableImpl {
    fn table(
        env: &GlobalEnv,
        options: &BoogieOptions,
        mono_info: &MonoInfo,
        struct_qid: QualifiedId<DatatypeId>,
        bv_flag: bool,
    ) -> Self {
        let insts = mono_info
            .structs
            .get(&struct_qid)
            .into_iter()
            .flat_map(|type_insts| {
                type_insts.iter().map(|tys| {
                    (
                        TypeInfo::new(env, options, &tys[0], false),
                        TypeInfo::new(env, options, &tys[1], bv_flag),
                    )
                })
            })
            .collect();

        let struct_env = env.get_struct(env.table_qid().unwrap());
        let struct_name = format!(
            "${}_{}",
            boogie_module_name(&struct_env.module_env),
            struct_env.get_name().display(struct_env.symbol_pool()),
        );

        TableImpl {
            struct_name,
            insts,
            fun_new: if env
                .table_new_qid()
                .map(|fun_qid| {
                    mono_info
                        .funs
                        .contains_key(&(fun_qid, FunctionVariant::Baseline))
                })
                .unwrap_or_default()
            {
                Self::triple_opt_to_name(env, env.table_new_qid())
            } else {
                "".to_string()
            },
            fun_add: Self::triple_opt_to_name(env, env.table_add_qid()),
            fun_borrow: Self::triple_opt_to_name(env, env.table_borrow_qid()),
            fun_borrow_mut: Self::triple_opt_to_name(env, env.table_borrow_mut_qid()),
            fun_remove: Self::triple_opt_to_name(env, env.table_remove_qid()),
            fun_contains: Self::triple_opt_to_name(env, env.table_contains_qid()),
            fun_length: Self::triple_opt_to_name(env, env.table_length_qid()),
            fun_is_empty: Self::triple_opt_to_name(env, env.table_is_empty_qid()),
            fun_destroy_empty: Self::triple_opt_to_name(env, env.table_destroy_empty_qid()),
            fun_drop: Self::triple_opt_to_name(env, env.table_drop_qid()),
            fun_value_id: "".to_string(),
        }
    }

    fn object_table(
        env: &GlobalEnv,
        options: &BoogieOptions,
        mono_info: &MonoInfo,
        struct_qid: QualifiedId<DatatypeId>,
        bv_flag: bool,
    ) -> Self {
        let insts = mono_info
            .structs
            .get(&struct_qid)
            .into_iter()
            .flat_map(|type_insts| {
                type_insts.iter().map(|tys| {
                    (
                        TypeInfo::new(env, options, &tys[0], false),
                        TypeInfo::new(env, options, &tys[1], bv_flag),
                    )
                })
            })
            .collect();

        let struct_env = env.get_struct(env.object_table_qid().unwrap());
        let struct_name = format!(
            "${}_{}",
            boogie_module_name(&struct_env.module_env),
            struct_env.get_name().display(struct_env.symbol_pool()),
        );

        TableImpl {
            struct_name,
            insts,
            fun_new: if env
                .object_table_new_qid()
                .map(|fun_qid| {
                    mono_info
                        .funs
                        .contains_key(&(fun_qid, FunctionVariant::Baseline))
                })
                .unwrap_or_default()
            {
                Self::triple_opt_to_name(env, env.object_table_new_qid())
            } else {
                "".to_string()
            },
            fun_add: Self::triple_opt_to_name(env, env.object_table_add_qid()),
            fun_borrow: Self::triple_opt_to_name(env, env.object_table_borrow_qid()),
            fun_borrow_mut: Self::triple_opt_to_name(env, env.object_table_borrow_mut_qid()),
            fun_remove: Self::triple_opt_to_name(env, env.object_table_remove_qid()),
            fun_contains: Self::triple_opt_to_name(env, env.object_table_contains_qid()),
            fun_length: Self::triple_opt_to_name(env, env.object_table_length_qid()),
            fun_is_empty: Self::triple_opt_to_name(env, env.object_table_is_empty_qid()),
            fun_destroy_empty: Self::triple_opt_to_name(env, env.object_table_destroy_empty_qid()),
            fun_drop: "".to_string(),
            fun_value_id: Self::triple_opt_to_name(env, env.object_table_value_id_qid()),
        }
    }

    fn triple_opt_to_name(env: &GlobalEnv, triple_opt: Option<QualifiedId<FunId>>) -> String {
        triple_opt
            .map(|fun_qid| {
                let fun = env.get_function(fun_qid);
                format!(
                    "${}_{}_{}",
                    fun.module_env.get_name().addr().to_str_radix(16),
                    fun.module_env.get_name().name().display(fun.symbol_pool()),
                    fun.get_name_str(),
                )
            })
            .unwrap_or_default()
    }
}

impl DynamicFieldInfo {
    fn dynamic_field(
        env: &GlobalEnv,
        options: &BoogieOptions,
        tp: &Type,
        name_value_infos: &BTreeSet<NameValueInfo>,
        bv_flag: bool,
    ) -> Self {
        let insts = name_value_infos
            .iter()
            .filter_map(|name_value_info| name_value_info.as_name_value())
            .unique()
            .map(|(name, value)| {
                (
                    TypeInfo::new(env, options, name, false),
                    TypeInfo::new(env, options, value, bv_flag),
                )
            })
            .collect();

        DynamicFieldInfo {
            struct_name: boogie_type_suffix_bv(env, tp, bv_flag),
            insts,
            fun_add: Self::triple_opt_to_name(env, env.dynamic_field_add_qid()),
            fun_borrow: Self::triple_opt_to_name(env, env.dynamic_field_borrow_qid()),
            fun_borrow_mut: Self::triple_opt_to_name(env, env.dynamic_field_borrow_mut_qid()),
            fun_remove: Self::triple_opt_to_name(env, env.dynamic_field_remove_qid()),
            fun_exists_with_type: Self::triple_opt_to_name(
                env,
                env.dynamic_field_exists_with_type_qid(),
            ),
        }
    }

    fn object_dynamic_field(
        env: &GlobalEnv,
        options: &BoogieOptions,
        tp: &Type,
        name_value_infos: &BTreeSet<NameValueInfo>,
        bv_flag: bool,
    ) -> Self {
        let insts = name_value_infos
            .iter()
            .filter_map(|name_value_info| name_value_info.as_name_value())
            .unique()
            .map(|(name, value)| {
                (
                    TypeInfo::new(env, options, name, false),
                    TypeInfo::new(env, options, value, bv_flag),
                )
            })
            .collect();

        DynamicFieldInfo {
            struct_name: boogie_type_suffix_bv(env, tp, bv_flag),
            insts,
            fun_add: Self::triple_opt_to_name(env, env.dynamic_object_field_add_qid()),
            fun_borrow: Self::triple_opt_to_name(env, env.dynamic_object_field_borrow_qid()),
            fun_borrow_mut: Self::triple_opt_to_name(
                env,
                env.dynamic_object_field_borrow_mut_qid(),
            ),
            fun_remove: Self::triple_opt_to_name(env, env.dynamic_object_field_remove_qid()),
            fun_exists_with_type: Self::triple_opt_to_name(
                env,
                env.dynamic_object_field_exists_with_type_qid(),
            ),
        }
    }

    fn triple_opt_to_name(env: &GlobalEnv, triple_opt: Option<QualifiedId<FunId>>) -> String {
        triple_opt
            .map(|fun_qid| {
                let fun = env.get_function(fun_qid);
                format!(
                    "${}_{}_{}",
                    fun.module_env.get_name().addr().to_str_radix(16),
                    fun.module_env.get_name().name().display(fun.symbol_pool()),
                    fun.get_name_str(),
                )
            })
            .unwrap_or_default()
    }
}
