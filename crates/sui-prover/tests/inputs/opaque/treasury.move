module 0x42::opaque_tests;

use prover::prover::asserts;
use std::u64;

const EOverflow: u64 = 1;

public struct TreasuryCap<phantom T> {
    total_supply: Supply<T>,
}

public struct Supply<phantom T> {
    value: u64,
}

public struct Balance<phantom T> {
    value: u64,
}

public fun supply_value<T>(supply: &Supply<T>): u64 {
    supply.value
}

public fun increase_supply<T>(self: &mut Supply<T>, value: u64): Balance<T> {
    assert!(value < (18446744073709551615u64 - self.value), EOverflow);
    self.value = self.value + value;
    Balance { value }
}

public fun total_supply<T>(cap: &TreasuryCap<T>): u64 {
    cap.total_supply.supply_value()
}

public fun mint_balance<T>(cap: &mut TreasuryCap<T>, value: u64): Balance<T> {
    cap.total_supply.increase_supply(value)
}

#[spec(prove)]
public fun mint_balance_spec<T>(cap: &mut TreasuryCap<T>, value: u64): Balance<T> {
    asserts(cap.total_supply() < u64::max_value!() - value);

    cap.mint_balance(value)
}
