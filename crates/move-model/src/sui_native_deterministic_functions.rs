use crate::model::{FunId, GlobalEnv, QualifiedId};

// Returns None if the package is not in the list of native packages, otherwise returns true if deterministic
pub fn is_deterministic(env: &GlobalEnv, qid: QualifiedId<FunId>) -> Option<bool> {
    let module_env = env.get_module(qid.module_id);
    let module_name = module_env.get_full_name_str();

    let package_name = if let Some(pos) = module_name.find("::") {
        &module_name[..pos]
    } else {
        &module_name
    };

    if !ALL_PACKAGES.contains(&package_name) {
        return None;
    }

    if DETERMINISTIC_MODULES.contains(&module_name.as_str()) {
        return Some(true);
    }

    let function_env = module_env.into_function(qid.id);
    let function_name = function_env
        .get_name()
        .display(env.symbol_pool())
        .to_string();

    // Name of the no-op unit test function
    const UNIT_TEST_POISON_FUN_NAME: &str = "unit_test_poison";
    if UNIT_TEST_POISON_FUN_NAME == function_name {
        return Some(true);
    }

    let full_function_name = format!("{}::{}", module_name, function_name);

    Some(DETERMINISTIC_FUNCTIONS.contains(&full_function_name.as_str()))
}

const ALL_PACKAGES: &[&str] = &["0x0", "0x1", "0x2"]; // prover, std, sui

const PROVER_PROVER_MODULE_NAME: &'static str = "0x0::prover";
const PROVER_LOG_MODULE_NAME: &'static str = "0x0::log";
const PROVER_GHOST_MODULE_NAME: &'static str = "0x0::ghost";

const STD_ADDRESS_MODULE_NAME: &'static str = "0x1::address";
const STD_ASCII_MODULE_NAME: &'static str = "0x1::ascii";
const STD_BCS_MODULE_NAME: &'static str = "0x1::bcs";
const STD_BIT_VECTOR_MODULE_NAME: &'static str = "0x1::bit_vector";
const STD_BOOL_MODULE_NAME: &'static str = "0x1::bool";
const STD_DEBUG_MODULE_NAME: &'static str = "0x1::Debug";
const STD_FIXED_POINT32_MODULE_NAME: &'static str = "0x1::fixed_point32";
const STD_HASH_MODULE_NAME: &'static str = "0x1::hash";
const STD_INTEGER_MODULE_NAME: &'static str = "0x1::integer";
const STD_MACROS_MODULE_NAME: &'static str = "0x1::macros";
const STD_OPTION_MODULE_NAME: &'static str = "0x1::option";
const STD_REAL_MODULE_NAME: &'static str = "0x1::real";
const STD_STRING_MODULE_NAME: &'static str = "0x1::string";
const STD_TYPE_NAME_MODULE_NAME: &'static str = "0x1::type_name";
const STD_U8_MODULE_NAME: &'static str = "0x1::u8";
const STD_U16_MODULE_NAME: &'static str = "0x1::u16";
const STD_U32_MODULE_NAME: &'static str = "0x1::u32";
const STD_U64_MODULE_NAME: &'static str = "0x1::u64";
const STD_U128_MODULE_NAME: &'static str = "0x1::u128";
const STD_U256_MODULE_NAME: &'static str = "0x1::u256";
const STD_UNIT_TEST_MODULE_NAME: &'static str = "0x1::unit_test";
const STD_UQ32_32_MODULE_NAME: &'static str = "0x1::uq32_32";
const STD_UQ64_64_MODULE_NAME: &'static str = "0x1::uq64_64";
const STD_VECTOR_MODULE_NAME: &'static str = "0x1::vector";

const SUI_TYPES_MODULE_NAME: &'static str = "0x2::types";
const SUI_VEC_SET_MODULE_NAME: &'static str = "0x2::vec_set";
const SUI_VEC_MAP_MODULE_NAME: &'static str = "0x2::vec_map";
const SUI_URL_MODULE_NAME: &'static str = "0x2::url";
const SUI_MATH_MODULE_NAME: &'static str = "0x2::math";
const SUI_HEX_MODULE_NAME: &'static str = "0x2::hex";
const SUI_BCS_MODULE_NAME: &'static str = "0x2::bcs";
const SUI_ADDRESS_MODULE_NAME: &'static str = "0x2::address";

const SUI_HASH_MODULE_NAME: &'static str = "0x2::hash";
const SUI_HMAC_MODULE_NAME: &'static str = "0x2::hmac";
const SUI_ED25519_MODULE_NAME: &'static str = "0x2::ed25519";
const SUI_ECDSA_K1_MODULE_NAME: &'static str = "0x2::ecdsa_k1";
const SUI_ECDSA_R1_MODULE_NAME: &'static str = "0x2::ecdsa_r1";
const SUI_ECVRF_MODULE_NAME: &'static str = "0x2::ecvrf";
const SUI_BLS12381_MODULE_NAME: &'static str = "0x2::bls12381";
const SUI_GROUP_OPS_MODULE_NAME: &'static str = "0x2::group_ops";
const SUI_GROTH16_MODULE_NAME: &'static str = "0x2::groth16";
const SUI_POSEIDON_MODULE_NAME: &'static str = "0x2::poseidon";
const SUI_VDF_MODULE_NAME: &'static str = "0x2::vdf";
const SUI_NITRO_ATTESTATION_MODULE_NAME: &'static str = "0x2::nitro_attestation";
const SUI_PRIORITY_QUEUE_MODULE_NAME: &'static str = "0x2::priority_queue";
const SUI_PARTY_MODULE_NAME: &'static str = "0x2::party";

static DETERMINISTIC_MODULES: &[&str] = &[
    // Prover modules
    PROVER_PROVER_MODULE_NAME,
    PROVER_LOG_MODULE_NAME,
    PROVER_GHOST_MODULE_NAME,
    // STD modules
    STD_ADDRESS_MODULE_NAME,
    STD_ASCII_MODULE_NAME,
    STD_BCS_MODULE_NAME,
    STD_BIT_VECTOR_MODULE_NAME,
    STD_BOOL_MODULE_NAME,
    STD_DEBUG_MODULE_NAME,
    STD_FIXED_POINT32_MODULE_NAME,
    STD_HASH_MODULE_NAME,
    STD_INTEGER_MODULE_NAME,
    STD_MACROS_MODULE_NAME,
    STD_OPTION_MODULE_NAME,
    STD_REAL_MODULE_NAME,
    STD_STRING_MODULE_NAME,
    STD_TYPE_NAME_MODULE_NAME,
    STD_U8_MODULE_NAME,
    STD_U16_MODULE_NAME,
    STD_U32_MODULE_NAME,
    STD_U64_MODULE_NAME,
    STD_U128_MODULE_NAME,
    STD_U256_MODULE_NAME,
    STD_UNIT_TEST_MODULE_NAME,
    STD_UQ32_32_MODULE_NAME,
    STD_UQ64_64_MODULE_NAME,
    STD_VECTOR_MODULE_NAME,
    // Sui framework deterministic modules
    SUI_TYPES_MODULE_NAME,
    SUI_VEC_SET_MODULE_NAME,
    SUI_VEC_MAP_MODULE_NAME,
    SUI_URL_MODULE_NAME,
    SUI_MATH_MODULE_NAME,
    SUI_HEX_MODULE_NAME,
    SUI_BCS_MODULE_NAME,
    SUI_ADDRESS_MODULE_NAME,
    SUI_PRIORITY_QUEUE_MODULE_NAME,
    SUI_PARTY_MODULE_NAME,
    // Sui crypto modules
    SUI_HASH_MODULE_NAME,
    SUI_HMAC_MODULE_NAME,
    SUI_ED25519_MODULE_NAME,
    SUI_ECDSA_K1_MODULE_NAME,
    SUI_ECDSA_R1_MODULE_NAME,
    SUI_ECVRF_MODULE_NAME,
    SUI_BLS12381_MODULE_NAME,
    SUI_GROUP_OPS_MODULE_NAME,
    SUI_GROTH16_MODULE_NAME,
    SUI_POSEIDON_MODULE_NAME,
    SUI_VDF_MODULE_NAME,
    SUI_NITRO_ATTESTATION_MODULE_NAME,
];

static DETERMINISTIC_FUNCTIONS: &[&str] = &[
    // Transfer
    "0x2::transfer::receiving_object_id",
    "0x2::transfer::make_receiver",
    "0x2::transfer::receiving_id",
    // Table
    "0x2::table::length",
    "0x2::table::is_empty",
    "0x2::table_vec::is_empty",
    // Package
    "0x2::package::published_module",
    "0x2::package::published_package",
    "0x2::package::upgrade_package",
    "0x2::package::version",
    "0x2::package::upgrade_policy",
    "0x2::package::ticket_package",
    "0x2::package::ticket_policy",
    "0x2::package::ticket_digest",
    "0x2::package::receipt_cap",
    "0x2::package::receipt_package",
    "0x2::package::compatible_policy",
    "0x2::package::additive_policy",
    "0x2::package::dep_only_policy",
    "0x2::package::from_package",
    "0x2::package::from_module",
    // Object
    "0x2::object::id_to_bytes",
    "0x2::object::id_to_address",
    "0x2::object::id_from_bytes",
    "0x2::object::id_from_address",
    "0x2::object::clock",
    "0x2::object::authenticator_state",
    "0x2::object::randomness_state",
    "0x2::object::sui_deny_list_object_id",
    "0x2::object::sui_accumulator_root_object_id",
    "0x2::object::sui_accumulator_root_address",
    "0x2::object::bridge",
    "0x2::object::uid_as_inner",
    "0x2::object::uid_to_inner",
    "0x2::object::uid_to_bytes",
    "0x2::object::uid_to_address",
    // Object table
    "0x2::object_table::length",
    "0x2::object_table::is_empty",
    // Linked table
    "0x2::linked_table::front",
    "0x2::linked_table::back",
    "0x2::linked_table::length",
    "0x2::linked_table::is_empty",
    // Display
    "0x2::display::version",
    "0x2::display::fields",
    // Deny list
    "0x2::deny_list::v1_contains",
    "0x2::deny_list::v1_per_type_list_contains",
    "0x2::deny_list::reserved_addresses",
    // Coin
    "0x2::coin::get_decimals",
    "0x2::coin::get_name",
    "0x2::coin::get_symbol",
    "0x2::coin::get_description",
    "0x2::coin::get_icon_url",
    "0x2::coin::supply_immut",
    "0x2::coin::value",
    "0x2::coin::balance",
    "0x2::coin::total_supply",
    // Clock
    "0x2::clock::timestamp_ms",
    // Balance
    "0x2::balance::value",
    "0x2::balance::supply_value",
    "0x2::balance::create_supply",
    "0x2::balance::increase_supply",
    "0x2::balance::decrease_supply",
    "0x2::balance::zero",
    "0x2::balance::join",
    "0x2::balance::split",
    "0x2::balance::withdraw_all",
    "0x2::balance::destroy_zero",
    // Bag
    "0x2::bag::length",
    "0x2::bag::is_empty",
    // ZK id
    "0x2::zklogin_verified_id::owner",
    "0x2::zklogin_verified_id::key_claim_name",
    "0x2::zklogin_verified_id::key_claim_value",
    "0x2::zklogin_verified_id::issuer",
    "0x2::zklogin_verified_id::audience",
    // ZK issuer
    "0x2::zklogin_verified_id::owner",
    "0x2::zklogin_verified_id::issuer",
];
