module 0x42::foo;

use sui::dynamic_field as df;
use sui::event;

public struct Key has copy, store, drop {
    address: address,
}

public struct Event has copy, drop {
    id: ID,
    address: address,
}

public fun add_address(uid: &mut UID, address: address) {
    df::add(uid, Key { address }, true);
    event::emit(Event { address, id: object::uid_to_inner(uid) });
}

#[spec]
fun add_address_spec(uid: &mut UID, address: address) {
    add_address(uid, address);
}

