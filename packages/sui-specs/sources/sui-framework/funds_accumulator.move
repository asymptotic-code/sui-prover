module specs::funds_accumulator_spec;

use sui::funds_accumulator::{
    add_to_accumulator_address,
    withdraw_from_accumulator_address,
    reserve_object_funds_for_withdrawal
};


#[mode(spec), ext(spec(target = sui::funds_accumulator::add_to_accumulator_address))]
public fun add_to_accumulator_address_spec<T: store>(
    accumulator: address,
    recipient: address,
    value: T,
) {
    add_to_accumulator_address(accumulator, recipient, value)
}

#[mode(spec), ext(spec(target = sui::funds_accumulator::withdraw_from_accumulator_address))]
public fun withdraw_from_accumulator_address_spec<T: store>(
    accumulator: address,
    owner: address,
    value: u256,
): T {
    withdraw_from_accumulator_address(accumulator, owner, value)
}

#[mode(spec), ext(spec(target = sui::funds_accumulator::reserve_object_funds_for_withdrawal))]
public fun reserve_object_funds_for_withdrawal_spec<T: store>(owner: address, limit: u256) {
    reserve_object_funds_for_withdrawal<T>(owner, limit)
}
