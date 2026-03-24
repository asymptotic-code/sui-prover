module specs::accumulator_spec;

use sui::accumulator::{emit_deposit_event, emit_withdraw_event, accumulator_address};

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

#[spec(target = sui::accumulator::accumulator_address)]
public fun accumulator_address_spec<T>(address: address): address {
    accumulator_address<T>(address)
}
