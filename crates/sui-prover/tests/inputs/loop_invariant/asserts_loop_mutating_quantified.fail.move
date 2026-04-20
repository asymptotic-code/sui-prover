module 0x42::asserts_loop_mutating_quantified_fail;

use prover::prover::{ensures, asserts, invariant, clone, forall};

// Same body as `asserts_loop_mutating_quantified.move` but the invariant
// uses the un-guarded `forall j, safe_at(j, old_v)` instead of the
// `j < i`-guarded variant. This invariant is exactly the spec's asserts
// (initially `v == old_v`), so under Assume mode (asserts negated) it
// cannot hold on loop entry — nothing abort-able runs before the loop
// to discharge the obligation.
//
// The fix is to use the `j < i` guard so the forall is vacuous at
// iteration 0 and accumulates per-iteration. See the passing variant
// in `asserts_loop_mutating_quantified.move`.

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
