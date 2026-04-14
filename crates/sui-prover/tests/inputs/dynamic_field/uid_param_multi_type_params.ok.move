module 0x42::foo;

use prover::prover::{requires, ensures};
use sui::dynamic_field as df;

public struct MyObject has key {
    id: UID,
}

public fun generic_add<K: copy + store + drop, V: store>(uid: &mut UID, key: K, val: V) {
    df::add<K, V>(uid, key, val);
}

public fun generic_exists<K: copy + store + drop, V: store>(uid: &UID, key: K): bool {
    df::exists_with_type<K, V>(uid, key)
}

#[spec(prove)]
fun generic_add_u64_bool_spec(obj: &mut MyObject, key: u64, val: bool) {
    requires(!df::exists_with_type<u64, bool>(&obj.id, key));
    generic_add<u64, bool>(&mut obj.id, key, val);
    ensures(df::exists_with_type<u64, bool>(&obj.id, key));
    ensures(*df::borrow<u64, bool>(&obj.id, key) == val);
}
