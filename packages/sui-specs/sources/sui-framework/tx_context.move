module specs::tx_context_spec;

use sui::tx_context::{
    derive_id,
    fresh_object_address,
    TxContext,
    sender,
    digest,
    epoch,
    epoch_timestamp_ms,
    fresh_id,
    native_ids_created,
    native_gas_budget,
    last_created_id,
    native_sponsor
};

#[spec_only]
use prover::prover::{ensures, clone};

#[spec(target = sui::tx_context::fresh_object_address)]
fun fresh_object_address_spec(ctx: &mut TxContext): address {
    let old_ctx = clone!(ctx);
    let result = fresh_object_address(ctx);
    ensures(ctx.digest() == old_ctx.digest());
    result
}

#[spec(target = sui::tx_context::derive_id)]
fun derive_id_spec(tx_hash: vector<u8>, ids_created: u64): address {
    derive_id(tx_hash, ids_created)
}

#[spec(target = sui::tx_context::fresh_id)]
fun fresh_id_spec(): address {
    fresh_id()
}

#[spec(target = sui::tx_context::native_ids_created)]
fun native_ids_created_spec(): u64 {
    native_ids_created()
}

#[spec(target = sui::tx_context::native_gas_budget)]
fun native_gas_budget_spec(): u64 {
    native_gas_budget()
}

#[spec(target = sui::tx_context::last_created_id)]
fun last_created_id_spec(): address {
    last_created_id()
}

#[spec(target = sui::tx_context::native_sponsor)]
fun native_sponsor_spec(): vector<address> {
    native_sponsor()
}
