#[allow(unused_field, unused_function)]
module 0x42::pure_callee_with_loop_inv;

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

/// Function with a loop invariant attached
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

#[spec_only(loop_inv(target = active_ids)), ext(no_abort)]
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

/// A pure function that calls active_ids — this should fail because
/// active_ids has loop invariants which inject `ensures` into its bytecode,
/// making it incompatible with pure callee requirements.
#[ext(pure)]
fun uses_active_ids(set: &MySet): bool {
    active_ids(set).length() > 0
}

#[spec(prove)]
fun active_ids_spec(set: &MySet): vector<u64> {
   let r = active_ids(set);
   ensures(r == map!(&set.validators, |e| get_id(e)));
   r
}
