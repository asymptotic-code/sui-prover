module 0x42::foo;

use prover::prover::{requires, ensures};
use sui::dynamic_field as df;

public struct WhitelistKey has copy, store, drop {
    address: address,
}

public struct MyObject has key {
    id: UID,
}

public fun add_whitelist_address(uid: &mut UID, addr: address) {
    df::add(uid, WhitelistKey { address: addr }, true);
}

#[spec(prove)]
fun add_whitelist_spec(obj: &mut MyObject, addr: address) {
    requires(!df::exists_with_type<WhitelistKey, bool>(&obj.id, WhitelistKey { address: addr }));
    add_whitelist_address(&mut obj.id, addr);
    ensures(df::exists_with_type<WhitelistKey, bool>(&obj.id, WhitelistKey { address: addr }));
    ensures(*df::borrow<WhitelistKey, bool>(&obj.id, WhitelistKey { address: addr }) == true);
}
