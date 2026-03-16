module 0x42::foo;

use prover::prover::{requires, ensures};
use sui::dynamic_field as df;

public struct MyObject has key {
    id: UID,
}

public fun has_field<K: copy + store + drop, V: store>(uid: &UID, key: K): bool {
    df::exists_with_type<K, V>(uid, key)
}

public fun get_field<K: copy + store + drop, V: store + copy + drop>(uid: &UID, key: K, default: V): V {
    if (has_field<K, V>(uid, key)) {
        *df::borrow<K, V>(uid, key)
    } else {
        default
    }
}

#[spec(prove)]
fun verify_get_field(obj: &MyObject, key: u64): u64 {
    requires(df::exists_with_type<u64, u64>(&obj.id, key));
    requires(*df::borrow<u64, u64>(&obj.id, key) == 42);
    let result = get_field<u64, u64>(&obj.id, key, 0);
    ensures(result == 42);
    result
}
