module 0x42::foo_tmp;

use sui::vec_set;
use prover::prover::{requires, ensures};

fun foo(s: &mut vec_set::VecSet<u64>) {
    s.insert(10);
}


#[spec(prove)]
fun foo_spec(s: &mut vec_set::VecSet<u64>) {
    requires(!s.contains(&10));
    foo(s);
    ensures(s.contains(&10));
}