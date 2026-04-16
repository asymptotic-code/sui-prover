#[allow(unused)]
module 0x42::object_table_ext_add_pure_ok;

use sui::object_table::ObjectTable;

#[spec_only]
use prover::prover::{ensures, requires, clone};

#[spec_only]
use sui::object_table::add_pure;

public struct Foo has key, store {
    id: UID,
}

#[spec(prove)]
fun test_add_matches(t: &mut ObjectTable<u64, Foo>, k: u64, v: Foo) {
    requires(!t.contains(k));
    let old_t = clone!(t);
    let old_v = clone!(&v);
    t.add(k, v);
    ensures(t == add_pure(old_t, k, old_v));
}
