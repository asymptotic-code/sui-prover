module 0x42::loop_invariant_asserts_tests;

use prover::prover::{ensures, asserts, invariant, clone, forall};

// Tests for the pattern where:
//   * a function-level `asserts` covers per-iteration abort conditions
//     in an implementation loop, and
//   * the loop invariant uses `ensures` to carry information needed in
//     two directions:
//       (a) the Check direction: discharge the body's per-iteration
//           assertion under the assumption that the function-level
//           asserts holds.
//       (b) the Assume direction: when the function-level asserts is
//           negated, force the loop to be unable to exit normally — so
//           the prover concludes the function must abort.
//
// Direction (b) is the subtle one. The invariant carries the fact that
// the per-iteration assertion has held for all completed iterations
// (`forall j < i, P(j)`). Combined with loop exit `i == n` and the
// negation of the function-level asserts, that gives a contradiction at
// loop exit, forcing abort.

// === Test 1: per-iteration assert constrained by the iteration variable ===

fun bounded_loop(n: u64) {
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
        ensures(i <= 100); // (b): closes the Assume direction
    });
    while (i < n) {
        assert!(i < 100);
        i = i + 1;
    };
}

#[spec(prove)]
fun bounded_loop_spec(n: u64) {
    asserts(n <= 100);
    bounded_loop(n);
}

// === Test 2: underflow on a mutable counter ===

fun decrement_loop(mut x: u64, n: u64): u64 {
    let old_x = clone!(&x);
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
        ensures((x as u128) + (i as u128) == (*old_x as u128));
    });
    while (i < n) {
        x = x - 1;
        i = i + 1;
    };
    x
}

#[spec(prove)]
fun decrement_loop_spec(x: u64, n: u64): u64 {
    asserts(x >= n);
    let result = decrement_loop(x, n);
    ensures((result as u128) + (n as u128) == (x as u128));
    result
}

// === Test 3: overflow on a u8 counter inside a u64-bounded loop ===

fun count_u8_loop(n: u64): u8 {
    let mut count: u8 = 0;
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
        ensures(count.to_int() == i.to_int());
    });
    while (i < n) {
        count = count + 1;
        i = i + 1;
    };
    count
}

#[spec(prove)]
fun count_u8_loop_spec(n: u64): u8 {
    asserts(n <= 255);
    count_u8_loop(n)
}

// === Test 4: vector index inside the loop, no asserts needed ===

fun visit_vec(v: &vector<u64>) {
    let n = v.length();
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
    });
    while (i < n) {
        let _x = v[i];
        i = i + 1;
    };
}

#[spec(prove)]
fun visit_vec_spec(v: &vector<u64>) {
    visit_vec(v);
}

// === Test 5: per-iteration assert from prior-iteration state ===

fun progressive_loop(n: u64) {
    let mut prev: u64 = 0;
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
        ensures(prev == i);
    });
    while (i < n) {
        assert!(prev <= i);
        prev = prev + 1;
        i = i + 1;
    };
}

#[spec(prove)]
fun progressive_loop_spec(n: u64) {
    progressive_loop(n);
}

// === Test 6: function-level forall asserts on an immutable input ===
//
// The invariant carries `forall j < i, v[j] > 0` via a guarded helper.
// The guard `v.length() >= i` makes the helper abort-free.

#[ext(pure)]
fun positive_at(j: u64, v: &vector<u64>): bool {
    j >= v.length() || v[j] > 0
}

#[ext(pure)]
fun visited_implies_positive(j: u64, i: u64, v: &vector<u64>): bool {
    v.length() >= i && (j >= i || v[j] > 0)
}

fun positive_check(v: &vector<u64>) {
    let n = v.length();
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
        ensures(forall!(|j| visited_implies_positive(*j, i, v)));
    });
    while (i < n) {
        assert!(v[i] > 0);
        i = i + 1;
    };
}

#[spec(prove)]
fun positive_check_spec(v: &vector<u64>) {
    asserts(forall!(|j| positive_at(*j, v)));
    positive_check(v);
}
