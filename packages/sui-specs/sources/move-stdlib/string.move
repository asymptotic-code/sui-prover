module specs::string_spec;

use std::string::{internal_check_utf8, internal_is_char_boundary, internal_sub_string, internal_index_of};

#[spec(target = std::string::internal_check_utf8)]
public fun internal_check_utf8_spec(v: &vector<u8>): bool {
    internal_check_utf8(v)
}

#[spec(target = std::string::internal_is_char_boundary)]
public fun internal_is_char_boundary_spec(v: &vector<u8>, i: u64): bool {
    internal_is_char_boundary(v, i)
}

#[spec(target = std::string::internal_sub_string)]
public fun internal_sub_string_spec(v: &vector<u8>, i: u64, j: u64): vector<u8> {
    internal_sub_string(v, i, j)
}

#[spec(target = std::string::internal_index_of)]
public fun internal_index_of_spec(v: &vector<u8>, r: &vector<u8>): u64 {
    internal_index_of(v, r)
}
