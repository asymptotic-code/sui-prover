module 0x42::asserts_loop_mutating_quantified_fail;

use prover::prover::{ensures, asserts, invariant, clone, forall};

// The body mutates each vector element in place by adding 1. The
// function-level asserts says no element of the original vector is
// `u64::max` (so `+ 1` cannot overflow).
//
// The Check direction works: with the asserts assumed and the
// invariant tracking `v` against `old_v`, the body's `+ 1` is safe.
//
// The Assume direction fails: the invariant `forall j, safe_at(j, old_v)`
// is exactly the negation of the spec's asserts (initially `v == old_v`),
// so it cannot hold on loop entry when `!asserts` is assumed. Nothing
// abort-able runs before the loop entry, so the prover cannot discharge
// the loop-entry obligation by a prior abort.
//
// In other words: the "asserts-up-to-i" pattern requires the invariant
// to be derivable from `asserts AND state-so-far`, not equivalent to the
// asserts at iteration 0.

#[ext(pure)]
fun safe_at(j: u64, v: &vector<u64>): bool {
    j >= v.length() || v[j] < std::u64::max_value!()
}

#[ext(pure)]
fun element_state(
    j: u64,
    i: u64,
    v: &vector<u64>,
    old_v: &vector<u64>,
): bool {
    v.length() == old_v.length()
        && (j >= v.length()
            || (j < i && v[j].to_int() == old_v[j].to_int().add(1u64.to_int()))
            || (j >= i && v[j] == old_v[j]))
}

fun increment_all(v: &mut vector<u64>) {
    let old_v = clone!(v);
    let n = v.length();
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
        ensures(v.length() == n);
        ensures(forall!(|j| element_state(*j, i, v, old_v)));
        ensures(forall!(|j| safe_at(*j, old_v)));
    });
    while (i < n) {
        let elem = v.borrow_mut(i);
        *elem = *elem + 1;
        i = i + 1;
    };
}

#[spec(prove)]
fun increment_all_spec(v: &mut vector<u64>) {
    asserts(forall!(|j| safe_at(*j, v)));
    increment_all(v);
}
