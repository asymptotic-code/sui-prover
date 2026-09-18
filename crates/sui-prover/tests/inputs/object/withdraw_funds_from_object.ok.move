// `balance::withdraw_funds_from_object` reaches the native
// `funds_accumulator::reserve_object_funds_for_withdrawal` (new in the sui
// `next` framework), which needs a spec in `sui-specs`. The feature-flag native
// `protocol_config::is_feature_enabled` it is gated on is not modelled by the
// prover, so it is declared in the extra BPL file.
module 0x42::foo;

use prover::prover::{requires, ensures};
use sui::balance::{Self, Balance};

public struct Vault has key {
    id: UID,
    total: u64,
}

fun withdraw<T>(vault: &mut Vault, amount: u64): Balance<T> {
    vault.total = vault.total + 1;
    balance::redeem_funds(balance::withdraw_funds_from_object<T>(&mut vault.id, amount))
}

#[mode(spec), ext(spec(prove, extra_bpl = b"withdraw_funds_from_object.ok.bpl"))]
fun withdraw_spec<T>(vault: &mut Vault, amount: u64): Balance<T> {
    requires(vault.total < 100);
    let old_id = object::id(vault);
    let old_total = vault.total;
    let result = withdraw<T>(vault, amount);
    ensures(object::id(vault) == old_id);
    ensures(vault.total == old_total + 1);
    result
}
