module specs::object_spec;

use sui::object::{delete_impl, record_new_uid_from_hash};

#[spec(target = sui::object::delete_impl)]
fun delete_impl_spec(id: address) {
    delete_impl(id)
}

#[spec(target = sui::object::record_new_uid_from_hash)]
fun record_new_uid_from_hash_spec(parent: address, bytes: address) {
    record_new_uid_from_hash(parent, bytes)
}