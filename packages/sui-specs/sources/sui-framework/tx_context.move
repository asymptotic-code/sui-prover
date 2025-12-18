module specs::tx_context_spec;

use sui::tx_context::{
    derive_id,
    fresh_object_address,
    TxContext,
    sender,
    digest,
    epoch,
    epoch_timestamp_ms,
    native_sender,
    native_epoch,
    native_epoch_timestamp_ms,
    fresh_id,
    native_rgp,
    native_ids_created,
    native_gas_budget,
    native_gas_price,
    last_created_id,
    native_sponsor,
};
#[spec_only]
use prover::prover::{ensures, clone};

#[spec(target = sui::tx_context::fresh_object_address)]
fun fresh_object_address_spec(ctx: &mut TxContext): address {
    let old_ctx = clone!(ctx);
    let result = fresh_object_address(ctx);
    // ensures(ctx.sender() == old_ctx.sender());
    ensures(ctx.digest() == old_ctx.digest());
    // ensures(ctx.epoch() == old_ctx.epoch());
    // ensures(ctx.epoch_timestamp_ms() == old_ctx.epoch_timestamp_ms());
    result
}

#[spec(target = sui::tx_context::derive_id)]
fun derive_id_spec(tx_hash: vector<u8>, ids_created: u64): address {
    derive_id(tx_hash, ids_created)
}

#[spec(target = sui::tx_context::native_sender)]
fun native_sender_spec(): address {
    native_sender()
}

#[spec(target = sui::tx_context::native_epoch)]
fun native_epoch_spec(): u64 {
    native_epoch()
}

#[spec(target = sui::tx_context::native_epoch_timestamp_ms)]
fun native_epoch_timestamp_ms_spec(): u64 {
    native_epoch_timestamp_ms()
}

#[spec(target = sui::tx_context::fresh_id)]
fun fresh_id_spec(): address {
    fresh_id()
}

#[spec(target = sui::tx_context::native_rgp)]
fun native_rgp_spec(): u64 {
    native_rgp()
}

#[spec(target = sui::tx_context::native_gas_price)]
fun native_gas_price_spec(): u64 {
    native_gas_price()
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
