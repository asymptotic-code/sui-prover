module specs::ed25519_spec;

use sui::ed25519::ed25519_verify;

#[spec(target = sui::ed25519::ed25519_verify)]
public fun ed25519_verify_spec(
    signature: &vector<u8>,
    public_key: &vector<u8>,
    msg: &vector<u8>,
): bool {
    ed25519_verify(signature, public_key, msg)
}
