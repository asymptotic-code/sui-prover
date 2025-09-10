module specs::vdf_spec;

use sui::vdf::{hash_to_input_internal, vdf_verify_internal};

#[spec(target = sui::vdf::hash_to_input_internal)]
public fun hash_to_input_internal_spec(message: &vector<u8>): vector<u8> {
    hash_to_input_internal(message)
}

#[spec(target = sui::vdf::vdf_verify_internal)]
public fun vdf_verify_internal_spec(
    input: &vector<u8>,
    output: &vector<u8>,
    proof: &vector<u8>,
    iterations: u64,
): bool {
    vdf_verify_internal(input, output, proof, iterations)
}
