module specs::ecdsa_r1_spec;

use sui::ecdsa_r1::{
    secp256r1_ecrecover, secp256r1_verify,
};

#[spec(target = sui::ecdsa_r1::secp256r1_ecrecover)]
public fun secp256r1_ecrecover_spec(
    signature: &vector<u8>,
    msg: &vector<u8>,
    hash: u8,
): vector<u8> {
    secp256r1_ecrecover(signature, msg, hash)
}

#[spec(target = sui::ecdsa_r1::secp256r1_verify)]
public fun secp256r1_verify_spec(
    signature: &vector<u8>,
    public_key: &vector<u8>,
    msg: &vector<u8>,
    hash: u8,
): bool {
    secp256r1_verify(signature, public_key, msg, hash)
}
