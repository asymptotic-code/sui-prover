module 0x42::foo;

use sui::dynamic_field as df;
use prover::prover::asserts;

public struct WhitelistKey has copy, store, drop {
    address: address,
}

public struct AllowAllKey has copy, store, drop {}

public struct MyObject has key {
    id: UID,
}

public fun add_whitelist_address(uid: &mut UID, addr: address) {
    df::add(uid, WhitelistKey { address: addr }, true);
}

public fun allow_all(uid: &mut UID) {
    df::add(uid, AllowAllKey {}, true);
}

public fun whitelist_key(addr: address): WhitelistKey {
    WhitelistKey { address: addr }
}

public fun allow_all_key(): AllowAllKey {
    AllowAllKey {}
}

#[spec(prove, target = add_whitelist_address)]
fun add_whitelist_address_spec(uid: &mut UID, addr: address) {
    asserts(!df::exists_with_type<WhitelistKey, bool>(uid, whitelist_key(addr)));
    add_whitelist_address(uid, addr);
}

#[spec(prove, target = allow_all)]
fun allow_all_spec(uid: &mut UID) {
    asserts(!df::exists_with_type<AllowAllKey, bool>(uid, allow_all_key()));
    allow_all(uid);
}
