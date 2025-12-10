module specs::crypto_hash_spec;

use sui::hash::{blake2b256, keccak256};

#[spec(target = sui::hash::blake2b256)]
public fun blake2b256_spec(data: &vector<u8>): vector<u8> {
    blake2b256(data)
}

#[spec(target = sui::hash::keccak256)]
public fun keccak256_spec(data: &vector<u8>): vector<u8> {
    keccak256(data)
}
