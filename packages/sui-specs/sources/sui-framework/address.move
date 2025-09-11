module specs::address_spec;

use sui::address::{to_u256, from_u256, from_bytes};

#[spec(target = sui::address::to_u256)]
public fun to_u256_spec(a: address): u256 {
    to_u256(a)
}

#[spec(target = sui::address::from_u256)]
public fun from_u256_spec(n: u256): address {
    from_u256(n)
}

#[spec(target = sui::address::from_bytes)]
public fun from_bytes_spec(bytes: vector<u8>): address {
    from_bytes(bytes)
}
