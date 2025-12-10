module specs::zklogin_verified_issuer_spec;

use sui::zklogin_verified_issuer::check_zklogin_issuer_internal;

#[spec(target = sui::zklogin_verified_issuer::check_zklogin_issuer_internal)]
public fun check_zklogin_issuer_internal_spec(
    address: address,
    address_seed: u256,
    issuer: &vector<u8>,
): bool {
    check_zklogin_issuer_internal(address, address_seed, issuer)
}
