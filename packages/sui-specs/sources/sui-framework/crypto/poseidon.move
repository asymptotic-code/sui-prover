module specs::poseidon_spec;

use sui::poseidon::poseidon_bn254_internal;

#[spec(target = sui::poseidon::poseidon_bn254_internal)]
public fun poseidon_bn254_internal_spec(data: &vector<vector<u8>>): vector<u8> {
    poseidon_bn254_internal(data)
}
