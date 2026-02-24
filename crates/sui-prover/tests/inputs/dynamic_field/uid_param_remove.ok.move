module 0x42::foo;

use sui::dynamic_field as df;

public struct WhitelistKey has copy, store, drop {
    address: address,
}

public struct MyObject has key {
    id: UID,
}

public fun remove_whitelist_address(uid: &mut UID, addr: address) {
    df::remove_if_exists<WhitelistKey, bool>(uid, WhitelistKey { address: addr });
}

#[spec(prove)]
fun remove_whitelist_spec(obj: &mut MyObject, addr: address) {
    remove_whitelist_address(&mut obj.id, addr);
}
