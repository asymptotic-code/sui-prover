use itertools::Itertools;
use move_model::model::{
    DatatypeId, EnclosingEnv, EnumEnv, FieldEnv, FunctionEnv, GlobalEnv, ModuleEnv,
    QualifiedInstId, StructEnv, StructOrEnumEnv, SCRIPT_MODULE_NAME,
};
use move_model::ty::PrimitiveType::{
    Address, Bool, EventStore, Num, Range, Signer, U128, U16, U256, U32, U64, U8,
};
use move_model::ty::Type;
use move_stackless_bytecode::ast::MemoryLabel;

/// This file is nearly identical to Boogie's boogie_helpers.rs, with minor var name changes.

/// Return lean name of given structure.
pub fn lean_struct_name(struct_env: &StructEnv<'_>, inst: &[Type]) -> String {
    lean_struct_name_bv(struct_env, inst, false)
}

pub fn lean_struct_name_bv(struct_env: &StructEnv<'_>, inst: &[Type], _bv_flag: bool) -> String {
    // if struct_env.is_intrinsic_of(INTRINSIC_TYPE_MAP) {
    //     // Map to the theory type representation, which is `Table int V`. The key
    //     // is encoded as an integer to avoid extensionality problems, and to support
    //     // $Mutation paths, which are sequences of ints.
    //     let env = struct_env.module_env.env;
    //     let type_fun = if bv_flag { lean_bv_type } else { lean_type };
    //     format!("Table int ({})", type_fun(env, &inst[1]))
    // } else {
    format!(
        "{}{}",
        lean_struct_name_prefix(struct_env),
        lean_inst_suffix(struct_env.module_env.env, inst)
    )
    // }
}

pub fn lean_struct_name_prefix(struct_env: &StructEnv<'_>) -> String {
    format!(
        "{}_{}",
        lean_module_name(&struct_env.module_env),
        struct_env.get_name().display(struct_env.symbol_pool()),
    )
}

/// Return lean name of given enum.
pub fn lean_enum_name(enum_env: &EnumEnv<'_>, inst: &[Type]) -> String {
    format!(
        "{}{}",
        lean_enum_name_prefix(enum_env),
        lean_inst_suffix(enum_env.module_env.env, inst)
    )
}

pub fn lean_enum_name_prefix(enum_env: &EnumEnv<'_>) -> String {
    format!(
        "{}_{}",
        lean_module_name(&enum_env.module_env),
        enum_env.get_name().display(enum_env.symbol_pool()),
    )
}

pub fn lean_inst_suffix(env: &GlobalEnv, inst: &[Type]) -> String {
    if inst.is_empty() {
        "".to_owned()
    } else {
        format!(
            "{}",
            inst.iter().map(|ty| lean_type_suffix(env, ty)).join("_")
        )
    }
}

/// Return lean name of given module.
pub fn lean_module_name(env: &ModuleEnv<'_>) -> String {
    let mod_name = env.get_name();
    let mod_sym = env.symbol_pool().string(mod_name.name());
    if mod_sym.as_str() == SCRIPT_MODULE_NAME {
        // <SELF> is not accepted by lean as a symbol
        "#SELF#".to_string()
    } else {
        // qualify module by address, prefixing with 'm' to ensure it starts with a letter
        format!("m{}_{}", mod_name.addr().to_str_radix(16), mod_sym)
    }
}

/// Return the suffix to specialize a name for the given type instance.
pub fn lean_type_suffix(env: &GlobalEnv, ty: &Type) -> String {
    lean_type_suffix_bv(env, ty, false)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FunctionTranslationStyle {
    Default,
    Asserts,
    Aborts,
    SpecNoAbortCheck,
    Opaque,
}

/// Return lean name of given function.
pub fn lean_function_name(
    fun_env: &FunctionEnv<'_>,
    inst: &[Type],
    style: FunctionTranslationStyle,
) -> String {
    let style_suffix = match style {
        FunctionTranslationStyle::Default => "",
        FunctionTranslationStyle::Opaque => "",
        FunctionTranslationStyle::Asserts => "_asserts",
        FunctionTranslationStyle::Aborts => "_aborts",
        FunctionTranslationStyle::SpecNoAbortCheck => "_spec_no_abort_check",
    };
    let non_empty_inst = if inst.is_empty() {
        (0..fun_env.get_type_parameter_count())
            .map(|i| Type::TypeParameter(i as u16))
            .collect()
    } else {
        inst.to_vec()
    };
    format!(
        "{}_{}{}{}",
        lean_module_name(&fun_env.module_env),
        fun_env.get_name().display(fun_env.symbol_pool()),
        lean_inst_suffix(fun_env.module_env.env, &non_empty_inst),
        style_suffix,
    )
}

/// Creates the name of the resource memory for the given struct.
pub fn lean_resource_memory_name(
    env: &GlobalEnv,
    memory: &QualifiedInstId<DatatypeId>,
    memory_label: &Option<MemoryLabel>,
) -> String {
    let struct_env = env.get_struct_qid(memory.to_qualified_id());
    format!(
        "{}_memory{}",
        lean_struct_name(&struct_env, &memory.inst),
        lean_memory_label(memory_label)
    )
}

pub fn lean_temp_from_suffix(_env: &GlobalEnv, suffix: &str, instance: usize) -> String {
    format!("temp_{}_{}", instance, suffix)
}

/// Return lean type for a local with given signature token.
pub fn lean_type(env: &GlobalEnv, ty: &Type) -> String {
    use Type::*;
    match ty {
        Primitive(p) => match p {
            U8 => "UInt8".to_string(),
            U16 => "UInt16".to_string(),
            U32 => "UInt32".to_string(),
            U64 => "UInt64".to_string(),
            U128 => "UInt128".to_string(),
            U256 => "UInt256".to_string(),
            Num => "Int".to_string(),
            Address => "Address".to_string(),
            Signer => "Signer".to_string(),
            Bool => "Bool".to_string(),
            Range | EventStore => panic!("unexpected type"),
        },
        Vector(et) => format!("Vec ({})", lean_type(env, et)),
        Datatype(mid, did, inst) => match env.get_struct_or_enum_qid(mid.qualified(*did)) {
            StructOrEnumEnv::Struct(struct_env) => lean_struct_name(&struct_env, inst),
            StructOrEnumEnv::Enum(enum_env) => lean_enum_name(&enum_env, inst),
        },
        Reference(_, bt) => format!("Mutation ({})", lean_type(env, bt)),
        TypeParameter(idx) => lean_type_param(env, *idx),
        Fun(..) | Tuple(..) | TypeDomain(..) | ResourceDomain(..) | Error | Var(..) => {
            format!("<<unsupported: {:?}>>", ty)
        }
    }
}

/// Creates the name of the resource memory domain for any function for the given struct.
/// This variable represents a local variable of the lean translation of this function.
pub fn lean_modifies_memory_name(env: &GlobalEnv, memory: &QualifiedInstId<DatatypeId>) -> String {
    let struct_env = &env.get_struct_qid(memory.to_qualified_id());
    format!("{}_modifies", lean_struct_name(struct_env, &memory.inst))
}

/// Creates a string for a memory label.
fn lean_memory_label(memory_label: &Option<MemoryLabel>) -> String {
    if let Some(l) = memory_label {
        format!("#{}", l.as_usize())
    } else {
        "".to_string()
    }
}

/// Returns the suffix to specialize a name for the given type instance.
pub fn lean_type_suffix_bv(env: &GlobalEnv, ty: &Type, bv_flag: bool) -> String {
    use Type::*;

    match ty {
        Primitive(p) => match p {
            U8 => lean_num_type_string("8", bv_flag),
            U16 => lean_num_type_string("16", bv_flag),
            U32 => lean_num_type_string("32", bv_flag),
            U64 => lean_num_type_string("64", bv_flag),
            U128 => lean_num_type_string("128", bv_flag),
            U256 => lean_num_type_string("256", bv_flag),
            Num => {
                if bv_flag {
                    "<<num is not unsupported here>>".to_string()
                } else {
                    "num".to_string()
                }
            }
            Address => "address".to_string(),
            Signer => "signer".to_string(),
            Bool => "Bool".to_string(),
            Range => "range".to_string(),
            EventStore => format!("<<unsupported {:?}>>", ty),
        },
        Vector(et) => format!(
            "vec{}",
            lean_inst_suffix_bv(env, &[et.as_ref().to_owned()], &[bv_flag])
        ),
        Datatype(mid, did, inst) => match env.get_struct_or_enum_qid(mid.qualified(*did)) {
            StructOrEnumEnv::Struct(struct_env) => {
                lean_type_suffix_for_struct(&struct_env, inst, bv_flag)
            }
            StructOrEnumEnv::Enum(enum_env) => lean_enum_name(&enum_env, inst),
        },
        TypeParameter(idx) => lean_type_param(env, *idx),
        Fun(..) | Tuple(..) | TypeDomain(..) | ResourceDomain(..) | Error | Var(..)
        | Reference(..) => format!("<<unsupported {:?}>>", ty),
    }
}

/// Return field selector for given field.
pub fn lean_field_sel(field_env: &FieldEnv<'_>, _inst: &[Type]) -> String {
    let EnclosingEnv::Struct(struct_env) = &field_env.parent_env else {
        unreachable!();
    };
    format!("{}", lean_struct_field_name(field_env))
}

fn lean_struct_field_name(field_env: &FieldEnv<'_>) -> String {
    let EnclosingEnv::Struct(struct_env) = &field_env.parent_env else {
        unreachable!();
    };
    if (Some(struct_env.get_qualified_id()) == struct_env.module_env.env.table_qid()
        || Some(struct_env.get_qualified_id()) == struct_env.module_env.env.object_table_qid())
        && field_env.get_offset() == 1
    {
        return "contents".to_string();
    }
    field_env
        .get_name()
        .display(struct_env.symbol_pool())
        .to_string()
}

pub fn lean_type_param(_env: &GlobalEnv, idx: u16) -> String {
    format!("T{}", idx)
}

pub fn lean_type_suffix_for_struct(
    struct_env: &StructEnv<'_>,
    inst: &[Type],
    _bv_flag: bool,
) -> String {
    // if struct_env.is_intrinsic_of(INTRINSIC_TYPE_MAP) {
    //     format!(
    //         "${}_{}{}",
    //         lean_module_name(&struct_env.module_env),
    //         struct_env.get_name().display(struct_env.symbol_pool()),
    //         lean_inst_suffix_bv_pair(struct_env.module_env.env, inst, &[false, bv_flag])
    //     )
    // } else {
    lean_struct_name(struct_env, inst)
    // }
}

/// Generate suffix after instantiation of type parameters
pub fn lean_inst_suffix_bv(env: &GlobalEnv, inst: &[Type], bv_flag: &[bool]) -> String {
    if inst.is_empty() {
        "".to_owned()
    } else {
        let suffix = if bv_flag.len() == 1 {
            inst.iter()
                .map(|ty| lean_type_suffix_bv(env, ty, bv_flag[0]))
                .join("_")
        } else {
            assert_eq!(inst.len(), bv_flag.len());
            inst.iter()
                .zip(bv_flag.iter())
                .map(|(ty, flag)| lean_type_suffix_bv(env, ty, *flag))
                .join("_")
        };
        format!("'{}'", suffix)
    }
}

pub fn lean_num_type_string(num: &str, bv_flag: bool) -> String {
    let pre = if bv_flag { "bv" } else { "u" };
    [pre, num].join("")
}
