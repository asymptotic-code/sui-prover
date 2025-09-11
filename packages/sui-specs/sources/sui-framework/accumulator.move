module specs::accumulator_spec;

use sui::accumulator::{emit_deposit_event, emit_withdraw_event};

#[spec(target = sui::accumulator::emit_deposit_event)]
public fun emit_deposit_event_spec<T>(
    accumulator: address,
    recipient: address,
    amount: u64,
) {
    emit_deposit_event<T>(accumulator, recipient, amount)
}

#[spec(target = sui::accumulator::emit_withdraw_event)]
public fun emit_withdraw_event_spec<T>(
    accumulator: address,
    owner: address,
    amount: u64,
) {
    emit_withdraw_event<T>(accumulator, owner, amount)
}
