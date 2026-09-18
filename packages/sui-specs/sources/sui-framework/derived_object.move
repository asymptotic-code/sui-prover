module specs::derived_object_spec;

use sui::derived_object::derive_address;

#[mode(spec), ext(spec(target = sui::derived_object::derive_address))]
public fun derive_address_spec<K: copy + drop + store>(parent: ID, key: K): address {
    derive_address(parent, key)
}
