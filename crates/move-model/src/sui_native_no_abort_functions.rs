use anyhow::bail;

use crate::model::{FunId, GlobalEnv, QualifiedId};

// Returns Error if function is not native, otherwise returns true if function does not abort
pub fn does_not_abort(env: &GlobalEnv, qid: QualifiedId<FunId>) -> Result<bool, anyhow::Error> {
    let module_env = env.get_module(qid.module_id);
    let func_env = module_env.get_function(qid.id);

    if !func_env.is_native() {
        bail!("Warning: Function {} is not native", func_env.get_full_name_str());
    }

    let module_name = module_env.get_full_name_str();

    if NO_ABORT_MODULES.contains(&module_name.as_str()) {
        return Ok(true);
    }

    let function_env = module_env.into_function(qid.id);
    let function_name = function_env
        .get_name()
        .display(env.symbol_pool())
        .to_string();

    // Name of the no-op unit test function
    const UNIT_TEST_POISON_FUN_NAME: &str = "unit_test_poison";
    if UNIT_TEST_POISON_FUN_NAME == function_name {
        return Ok(true);
    }

    let full_function_name = format!("{}::{}", module_name, function_name);

    Ok(NO_ABORT_FUNCTIONS.contains(&full_function_name.as_str()))
}

const PROVER_LOG_MODULE_NAME: &'static str = "0x0::log";
const PROVER_GHOST_MODULE_NAME: &'static str = "0x0::ghost";

const STD_BSC_MODULE_NAME: &'static str = "0x1::bsc";
const STD_DEBUG_MODULE_NAME: &'static str = "0x1::debug";
const STD_HASH_MODULE_NAME: &'static str = "0x1::hash";
const STD_STRING_MODULE_NAME: &'static str = "0x1::string";
const STD_TYPE_NAME_MODULE_NAME: &'static str = "0x1::type_name";
const STD_UNIT_TEST_MODULE_NAME: &'static str = "0x1::unit_test";

const SUI_ACCUMULATOR_MODULE_NAME: &'static str = "0x2::accumulator";
const SUI_EVENT_MODULE_NAME: &'static str = "0x2::event";
const SUI_TYPES_MODULE_NAME: &'static str = "0x2::types";
const SUI_OBJECT_MODULE_NAME: &'static str = "0x2::object";
const SUI_TX_CONTEXT_MODULE_NAME: &'static str = "0x2::tx_context";
const SUI_BLS12381_MODULE_NAME: &'static str = "0x2::bls12381";
const SUI_GROUP_OPS_MODULE_NAME: &'static str = "0x2::group_ops";
const SUI_HASH_MODULE_NAME: &'static str = "0x2::hash";
const SUI_HMAC_MODULE_NAME: &'static str = "0x2::hmac";
const SUI_NITRO_ATTESTATION_MODULE_NAME: &'static str = "0x2::nitro_attestation";
const SUI_VDF_MODULE_NAME: &'static str = "0x2::vdf";

// Modules that contain only non-aborting functions
static NO_ABORT_MODULES: &[&str] = &[
    // Prover modules
    PROVER_GHOST_MODULE_NAME,
    PROVER_LOG_MODULE_NAME,
    // STD modules
    STD_BSC_MODULE_NAME,
    STD_DEBUG_MODULE_NAME,
    STD_HASH_MODULE_NAME,
    STD_STRING_MODULE_NAME,
    STD_TYPE_NAME_MODULE_NAME,
    STD_UNIT_TEST_MODULE_NAME,
    // Sui framework
    SUI_ACCUMULATOR_MODULE_NAME,
    SUI_EVENT_MODULE_NAME,
    SUI_TYPES_MODULE_NAME,
    SUI_OBJECT_MODULE_NAME,
    SUI_TX_CONTEXT_MODULE_NAME,
    SUI_BLS12381_MODULE_NAME,
    SUI_GROUP_OPS_MODULE_NAME,
    SUI_HASH_MODULE_NAME,
    SUI_HMAC_MODULE_NAME,
    SUI_NITRO_ATTESTATION_MODULE_NAME,
    SUI_VDF_MODULE_NAME,
];

// Individual functions that don't abort (from modules that can have aborting functions)
static NO_ABORT_FUNCTIONS: &[&str] = &[
    "0x0::prover::requires",
    "0x0::prover::invariant_begin",
    "0x0::prover::invariant_end",
    "0x0::prover::val",
    "0x0::prover::ref",
    "0x0::prover::drop",
    "0x0::prover::fresh",
    "0x0::prover::type_inv",

    "0x1::vector::empty",
    "0x1::vector::length",
    "0x1::address::to_u256",
    "0x1::integer::from_u8",
    "0x1::integer::from_u16",
    "0x1::integer::from_u32",
    "0x1::integer::from_u64",
    "0x1::integer::from_u128",
    "0x1::integer::from_u256",
    "0x1::integer::add",
    "0x1::integer::sub",
    "0x1::integer::neg",
    "0x1::integer::mul",
    "0x1::integer::bit_or",
    "0x1::integer::bit_and",
    "0x1::integer::bit_xor",
    "0x1::integer::bit_not",
    "0x1::integer::lt",
    "0x1::integer::gt",
    "0x1::integer::lte",
    "0x1::integer::gte",
    "0x1::real::from_integer",
    "0x1::real::to_integer",
    "0x1::real::add",
    "0x1::real::sub",
    "0x1::real::neg",
    "0x1::real::mul",
    "0x1::real::lt",
    "0x1::real::gt",
    "0x1::real::lte",
    "0x1::real::gte",

    "0x2::ecdsa_k1::secp256k1_verify",
    "0x2::ecdsa_k1::secp256k1_sign",
    "0x2::ecdsa_r1::secp256r1_verify",
    "0x2::ed25519::ed25519_verify",
];
