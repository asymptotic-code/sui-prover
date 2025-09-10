module specs::bsc_spec;

use std::bcs::to_bytes;

#[spec(target = std::bcs::to_bytes)]
public fun to_bytes_spec<MoveValue>(v: &MoveValue): vector<u8> {
    to_bytes(v)
}
