#[allow(unused)]
module 0x42::object_table_ext_remove_pure_ok;

use sui::object_table::ObjectTable;

#[spec_only]
use prover::prover::{ensures, requires, clone};

#[spec_only]
use prover::object_table_ext::remove_pure;

public struct Foo has key, store {
    id: UID,
}

#[spec(prove)]
fun test_remove_matches(t: &mut ObjectTable<u64, Foo>, k: u64) {
    requires(t.contains(k));
    let old_t = clone!(t);
    let _ = t.remove(k);
    ensures(t == remove_pure(old_t, k));
}
