module specs::bls12381_spec;

use sui::bls12381::{bls12381_min_sig_verify, bls12381_min_pk_verify};

#[spec(target = sui::bls12381::bls12381_min_sig_verify)]
public fun bls12381_min_sig_verify_spec(
    signature: &vector<u8>,
    public_key: &vector<u8>,
    msg: &vector<u8>,
): bool {
    bls12381_min_sig_verify(signature, public_key, msg)
}

#[spec(target = sui::bls12381::bls12381_min_pk_verify)]
public fun bls12381_min_pk_verify_spec(
    signature: &vector<u8>,
    public_key: &vector<u8>,
    msg: &vector<u8>,
): bool {
    bls12381_min_pk_verify(signature, public_key, msg)
}
