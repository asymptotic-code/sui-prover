module 0x42::foo;

use prover::prover::{requires, ensures};
use sui::dynamic_field as df;

public struct Foo has key {
    id: UID,
}

fun store_list(x: &mut Foo, key: u64, items: vector<u64>) {
    df::add<u64, vector<u64>>(&mut x.id, key, items);
}

#[spec(prove)]
fun store_list_spec(x: &mut Foo, key: u64, items: vector<u64>) {
    requires(!df::exists_with_type<u64, vector<u64>>(&x.id, key));
    store_list(x, key, items);
    ensures(df::exists_with_type<u64, vector<u64>>(&x.id, key));
    ensures(*df::borrow<u64, vector<u64>>(&x.id, key) == items);
}
