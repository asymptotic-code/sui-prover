module specs::ecdsa_k1_spec;

use sui::ecdsa_k1::{
    secp256k1_ecrecover, decompress_pubkey, secp256k1_verify,
    secp256k1_sign, secp256k1_keypair_from_seed, KeyPair,
};

#[spec(target = sui::ecdsa_k1::secp256k1_ecrecover)]
public fun secp256k1_ecrecover_spec(
    signature: &vector<u8>,
    msg: &vector<u8>,
    hash: u8,
): vector<u8> {
    secp256k1_ecrecover(signature, msg, hash)
}

#[spec(target = sui::ecdsa_k1::decompress_pubkey)]
public fun decompress_pubkey_spec(pubkey: &vector<u8>): vector<u8> {
    decompress_pubkey(pubkey)
}

#[spec(target = sui::ecdsa_k1::secp256k1_verify)]
public fun secp256k1_verify_spec(
    signature: &vector<u8>,
    public_key: &vector<u8>,
    msg: &vector<u8>,
    hash: u8,
): bool {
    secp256k1_verify(signature, public_key, msg, hash)
}

#[spec(target = sui::ecdsa_k1::secp256k1_sign)]
public fun secp256k1_sign_spec(
    private_key: &vector<u8>,
    msg: &vector<u8>,
    hash: u8,
    recoverable: bool,
): vector<u8> {
    secp256k1_sign(private_key, msg, hash, recoverable)
}

#[spec(target = sui::ecdsa_k1::secp256k1_keypair_from_seed)]
public fun secp256k1_keypair_from_seed_spec(seed: &vector<u8>): KeyPair {
    secp256k1_keypair_from_seed(seed)
}
