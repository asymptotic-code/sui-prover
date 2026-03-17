module 0x42::foo;

use sui::dynamic_field as df;

public struct WhitelistKey has copy, store, drop {
    address: address,
}

public struct MyObject has key {
    id: UID,
}

public fun in_whitelist(uid: &UID, addr: address): bool {
    df::exists_with_type<WhitelistKey, bool>(uid, WhitelistKey { address: addr })
}

#[spec(prove)]
fun check_in_whitelist(obj: &MyObject, addr: address): bool {
    in_whitelist(&obj.id, addr)
}
