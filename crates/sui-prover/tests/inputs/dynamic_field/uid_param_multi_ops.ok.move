module 0x42::foo;

use prover::prover::{requires, ensures};
use sui::dynamic_field as df;

public struct NameKey has copy, store, drop {}
public struct CountKey has copy, store, drop {}

public struct MyObject has key {
    id: UID,
}

public fun initialize(uid: &mut UID, count: u64) {
    df::add<NameKey, bool>(uid, NameKey {}, true);
    df::add<CountKey, u64>(uid, CountKey {}, count);
}

#[spec(prove)]
fun verify_initialize(obj: &mut MyObject, count: u64) {
    requires(!df::exists_with_type<NameKey, bool>(&obj.id, NameKey {}));
    requires(!df::exists_with_type<CountKey, u64>(&obj.id, CountKey {}));
    initialize(&mut obj.id, count);
    ensures(df::exists_with_type<NameKey, bool>(&obj.id, NameKey {}));
    ensures(df::exists_with_type<CountKey, u64>(&obj.id, CountKey {}));
    ensures(*df::borrow<CountKey, u64>(&obj.id, CountKey {}) == count);
}
