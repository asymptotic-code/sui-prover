// Stress test: find_indices on a larger concrete vector. find_indices uses
// compound-trigger recursive axioms (which break the matching loop for
// suffix-invariant loop proofs — see find_indices_suffix_loop), so concrete
// exact-value equality can't be proved via recursive unfolding here.
// Instead we assert properties that follow from the main and sorted-order
// axioms alone: length bound, in-range indices, predicate holds at each,
// and strict ordering.
//
// (An ext(axiom) lemma that would pin down the exact length was tried but
// didn't pan out — the per-spec scenario analyzer doesn't bring axiom
// functions into scope unless the spec directly calls them, and an axiom
// that references macro-expanded iterator helpers doesn't plug into the
// scenario's dependency graph cleanly. Left as a future enhancement.)

#[allow(unused)]
module 0x42::quantifiers_find_indices_big_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::find_indices;

#[ext(pure)]
fun is_even(x: &u64): bool {
    *x % 2 == 0
}

#[spec(prove)]
fun test_find_indices_big() {
    let v = vector[1u64, 2, 3, 4, 5, 6, 7, 8];
    let indices = find_indices!<u64>(&v, |x| is_even(x));
    let len = vector::length(indices);

    // Length bound — from main axiom.
    ensures(len <= vector::length(&v));

    // Each result index is in range and points to an even-valued element —
    // from the main axiom's in-range and predicate-holds clauses.
    if (len > 0) {
        let idx0 = *vector::borrow(indices, 0);
        ensures(idx0 < vector::length(&v));
        ensures(*vector::borrow(&v, idx0) % 2 == 0);
    };
    if (len > 1) {
        let idx0 = *vector::borrow(indices, 0);
        let idx1 = *vector::borrow(indices, 1);
        ensures(idx1 < vector::length(&v));
        ensures(*vector::borrow(&v, idx1) % 2 == 0);
        // Strict ordering — from the sorted-order axiom.
        ensures(idx0 < idx1);
    };
}
