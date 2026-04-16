#[allow(unused)]
module 0x42::table_ext_remove_pure_ok;

use sui::table::Table;

#[spec_only]
use prover::prover::{ensures, requires, clone};

#[spec_only]
use sui::table::remove_pure;

#[spec(prove)]
fun test_remove_matches(t: &mut Table<u64, u8>, k: u64) {
    requires(t.contains(k));
    let old_t = clone!(t);
    let _ = t.remove(k);
    ensures(t == remove_pure(old_t, k));
}
