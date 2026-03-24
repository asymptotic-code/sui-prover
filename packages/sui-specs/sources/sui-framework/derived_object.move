module specs::derived_object_specs;

use sui::derived_object::derive_address;

#[spec(target = sui::derived_object::derive_address)]
public fun derive_address_spec<K: copy + drop + store>(parent: ID, key: K): address {
    derive_address(parent, key)
}
