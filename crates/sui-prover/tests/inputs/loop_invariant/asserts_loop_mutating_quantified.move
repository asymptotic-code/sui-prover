module 0x42::asserts_loop_mutating_quantified;

use prover::prover::{ensures, asserts, invariant, clone, forall};

// Body mutates each vector element by adding 1. The function-level
// asserts says no element of the original vector is `u64::max`.
//
// The "asserts-up-to-i" invariant uses the standard `j < i` guard so it
// is vacuously true at iteration 0 and accumulates per-iteration:
//   `forall j < i, safe(old_v[j])`
// At loop exit `i == n`, the invariant becomes `forall j < n, safe(old_v[j])`,
// which contradicts `!asserts` (some `j < v.length() = n` has
// `v[j] == u64::max`, equivalently `old_v[j] == u64::max` since
// `v == old_v` at spec entry). The loop must therefore abort under
// `!asserts`, closing the Assume direction.
//
// `element_state` carries the relation between current `v` and `old_v`
// so the body can derive `v[i] == old_v[i]` and use the asserts on `old_v`.

#[ext(pure)]
fun safe_at(j: u64, v: &vector<u64>): bool {
    j >= v.length() || v[j] < std::u64::max_value!()
}

#[ext(pure)]
fun visited_safe(j: u64, i: u64, old_v: &vector<u64>): bool {
    j >= i || (j < old_v.length() && old_v[j] < std::u64::max_value!())
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
        ensures(forall!(|j| visited_safe(*j, i, old_v)));
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
