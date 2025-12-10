module 0x42::foo;

use prover::prover::{requires, ensures};
use sui::dynamic_field as df;

public struct Market has key, store {
    id: UID,
}

public fun uid(market: &Market): &UID { 
    &market.id 
}

public fun uid_mut_delegated(market: &mut Market, _: u64): &mut UID { 
    &mut market.id 
}

public fun uid_mut(market: &mut Market): &mut UID { 
    &mut market.id 
}

public struct SupplyLimitKey has copy, store, drop {}
public struct BorrowFeeKey has copy, store, drop {}
public struct ExtraKey has copy, store, drop {}

fun test_add_with_uid_getter_var(market: &mut Market, value: u64) {
    let borrow_fee_key = BorrowFeeKey {};
    let uid_ref = uid_mut(market);
    df::add<BorrowFeeKey, u64>(uid_ref, borrow_fee_key, value);
}

fun test_add_with_uid_getter(market: &mut Market, value: u64) {
    let extra_key = ExtraKey {};
    let _b = 0u32;
    let c = extra_key;
    df::add<ExtraKey, u64>(uid_mut(market), c, value);
}

fun test_add_with_uid_getter_del(market: &mut Market, value: u64) {
    let supply_limit_key = SupplyLimitKey {};
    let id = uid_mut_delegated(market, value);
    df::add<SupplyLimitKey, u64>(id, supply_limit_key, value);
}

#[spec(prove)]
fun test_spec(market: &mut Market) {
    let supply_value = 1000;
    let fee_value = 50;
    let extra_value = 25;

    requires(!df::exists_with_type<SupplyLimitKey, u64>(&market.id, SupplyLimitKey {}));
    requires(!df::exists_with_type<BorrowFeeKey, u64>(uid(market), BorrowFeeKey {}));
    requires(!df::exists_with_type<ExtraKey, u64>(&market.id, ExtraKey {}));
    
    // Test all three UID getter patterns:
    test_add_with_uid_getter_var(market, fee_value);         // uid_mut stored in variable
    test_add_with_uid_getter_del(market, supply_value);      // uid_mut_delegated with multiple params  
    test_add_with_uid_getter(market, extra_value);           // uid_mut called directly
    
    ensures(df::exists_with_type<SupplyLimitKey, u64>(uid(market), SupplyLimitKey {}));
    ensures(df::exists_with_type<BorrowFeeKey, u64>(&market.id, BorrowFeeKey {}));
    ensures(df::exists_with_type<ExtraKey, u64>(&market.id, ExtraKey {}));
    
    // Verify all values are stored correctly
    ensures(*df::borrow<SupplyLimitKey, u64>(uid(market), SupplyLimitKey {}) == supply_value);
    ensures(*df::borrow<BorrowFeeKey, u64>(&market.id, BorrowFeeKey {}) == fee_value);
    ensures(*df::borrow<ExtraKey, u64>(&market.id, ExtraKey {}) == extra_value);
}
