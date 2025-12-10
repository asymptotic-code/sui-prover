module specs::group_ops_spec;

use sui::group_ops::{
    internal_validate, internal_add, internal_sub, internal_mul, internal_div,
    internal_hash_to, internal_multi_scalar_mul, internal_pairing,
    internal_convert, internal_sum,
};

#[spec(target = sui::group_ops::internal_validate)]
public fun internal_validate_spec(type_: u8, bytes: &vector<u8>): bool {
    internal_validate(type_, bytes)
}

#[spec(target = sui::group_ops::internal_add)]
public fun internal_add_spec(type_: u8, e1: &vector<u8>, e2: &vector<u8>): vector<u8> {
    internal_add(type_, e1, e2)
}

#[spec(target = sui::group_ops::internal_sub)]
public fun internal_sub_spec(type_: u8, e1: &vector<u8>, e2: &vector<u8>): vector<u8> {
    internal_sub(type_, e1, e2)
}

#[spec(target = sui::group_ops::internal_mul)]
public fun internal_mul_spec(type_: u8, e1: &vector<u8>, e2: &vector<u8>): vector<u8> {
    internal_mul(type_, e1, e2)
}

#[spec(target = sui::group_ops::internal_div)]
public fun internal_div_spec(type_: u8, e1: &vector<u8>, e2: &vector<u8>): vector<u8> {
    internal_div(type_, e1, e2)
}

#[spec(target = sui::group_ops::internal_hash_to)]
public fun internal_hash_to_spec(type_: u8, m: &vector<u8>): vector<u8> {
    internal_hash_to(type_, m)
}

#[spec(target = sui::group_ops::internal_multi_scalar_mul)]
public fun internal_multi_scalar_mul_spec(
    type_: u8,
    scalars: &vector<u8>,
    elements: &vector<u8>,
): vector<u8> {
    internal_multi_scalar_mul(type_, scalars, elements)
}

#[spec(target = sui::group_ops::internal_pairing)]
public fun internal_pairing_spec(type_: u8, e1: &vector<u8>, e2: &vector<u8>): vector<u8> {
    internal_pairing(type_, e1, e2)
}

#[spec(target = sui::group_ops::internal_convert)]
public fun internal_convert_spec(from_type_: u8, to_type_: u8, e: &vector<u8>): vector<u8> {
    internal_convert(from_type_, to_type_, e)
}

#[spec(target = sui::group_ops::internal_sum)]
public fun internal_sum_spec(type_: u8, e: &vector<vector<u8>>): vector<u8> {
    internal_sum(type_, e)
}
