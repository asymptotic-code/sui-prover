module specs::ecvrf_spec;

use sui::ecvrf::ecvrf_verify;

#[spec(target = sui::ecvrf::ecvrf_verify)]
public fun ecvrf_verify_spec(
    hash: &vector<u8>,
    alpha_string: &vector<u8>,
    public_key: &vector<u8>,
    proof: &vector<u8>,
): bool {
    ecvrf_verify(hash, alpha_string, public_key, proof)
}
