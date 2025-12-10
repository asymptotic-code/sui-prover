module 0x42::foo;

use std::string::{Self, String};
use std::type_name::{Self, TypeName};
use sui::dynamic_object_field;
use sui::table::{Self, Table};

public struct Pools has key, store {
    id: UID,
}

public struct Whitelist has key, store {
    id: UID,
    list: Table<TypeName, bool>,
}

public fun add_whitelist<Coin>(pools: &mut Pools) {
    let c_type = type_name::get<Coin>();
    let coin_list = dynamic_object_field::borrow_mut<String, Whitelist>(
        &mut pools.id,
        string::utf8(b"asdf"),
    );
    table::add(&mut coin_list.list, c_type, true);
}


#[spec(prove, ignore_abort)]
public fun add_whitelist_spec<Coin>(pools: &mut Pools) {
    add_whitelist<Coin>(pools)
}
