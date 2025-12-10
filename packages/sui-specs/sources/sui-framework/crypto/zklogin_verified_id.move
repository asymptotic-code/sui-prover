module specs::zklogin_verified_id_spec;

use sui::zklogin_verified_id::check_zklogin_id_internal;

#[spec(target = sui::zklogin_verified_id::check_zklogin_id_internal)]
public fun check_zklogin_id_internal_spec(
    address: address,
    key_claim_name: &vector<u8>,
    key_claim_value: &vector<u8>,
    issuer: &vector<u8>,
    audience: &vector<u8>,
    pin_hash: u256,
): bool {
    check_zklogin_id_internal(address, key_claim_name, key_claim_value, issuer, audience, pin_hash)
}
