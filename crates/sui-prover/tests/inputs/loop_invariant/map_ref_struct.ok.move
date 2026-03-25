#[allow(unused_field)]
module 0x42::map_ref_struct;

use prover::prover::{ensures, forall};
use prover::vector_iter::map;

public struct Entry has copy, drop, store {
    id: u64,
    amount: u64,
}

public struct MySet has drop {
    validators: vector<Entry>,
}

#[ext(pure)]
fun get_id(e: &Entry): u64 {
    e.id
}

/// The function under test: map_ref over struct field
public fun active_ids(set: &MySet): vector<u64> {
    let mut r = vector[];
    let mut i = 0;
    let len = set.validators.length();
    while (i < len) {
        r.push_back(set.validators[i].id);
        i = i + 1;
    };
    r
}

#[spec_only(loop_inv(target = active_ids)), ext(pure)]
fun active_ids_invariant(i: u64, len: u64, set: &MySet, r: &vector<u64>): bool {
       i <= len
    && len == set.validators.length()
    && r.length() == i
    && forall!(|j| mapped_to_i(*j, i, &set.validators, r))
}

#[ext(pure)]
fun mapped_to_i(j: u64, i: u64, v: &vector<Entry>, r: &vector<u64>): bool {
    r.length() >= i &&
    v.length() >= i &&
    (j >= i || r[j] == v[j].id)
}

#[spec(prove)]
fun active_ids_spec(set: &MySet): vector<u64> {
   let r = active_ids(set);
   ensures(r == map!(&set.validators, |e| get_id(e)));
   r
}
