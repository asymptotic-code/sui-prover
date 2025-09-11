module specs::hmac_spec;

use sui::hmac::hmac_sha3_256;

#[spec(target = sui::hmac::hmac_sha3_256)]
public fun hmac_sha3_256_spec(key: &vector<u8>, msg: &vector<u8>): vector<u8> {
    hmac_sha3_256(key, msg)
}
