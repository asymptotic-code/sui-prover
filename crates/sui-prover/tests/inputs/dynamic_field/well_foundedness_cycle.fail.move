module 0x42::foo;

use sui::dynamic_field as df;
use sui::table;

public struct GlobalConfig has key {
    id: UID,
}

public struct FeeKey has copy, store, drop {}

public fun set_fee(config: &mut GlobalConfig, amount: u64, ctx: &mut TxContext) {
    let uid = &mut config.id;
    let key = FeeKey {};

    if (!df::exists_(uid, key)) {
        df::add(uid, key, table::new<u64, u64>(ctx));
    };

    let fee_table: &mut table::Table<u64, u64> = df::borrow_mut(uid, key);

    if (!table::contains(fee_table, 0)) {
        table::add(fee_table, 0, 0);
    };

    let coin_fee = table::borrow_mut(fee_table, 0);
    *coin_fee = amount;
}

#[spec(prove)]
public fun set_fee_spec(config: &mut GlobalConfig, amount: u64, ctx: &mut TxContext) {
    set_fee(config, amount, ctx);
}
