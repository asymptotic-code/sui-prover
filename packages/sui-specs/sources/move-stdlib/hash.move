module specs::hash_spec;

use std::hash::{sha3_256, sha2_256};

#[spec(target = std::hash::sha3_256)]
public fun sha3_256_spec(data: vector<u8>): vector<u8> {
    sha3_256(data)
}

#[spec(target = std::hash::sha2_256)]
public fun sha2_256_spec(data: vector<u8>): vector<u8> {
    sha2_256(data)
}
