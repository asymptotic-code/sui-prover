// Stress test: find_indices on a larger concrete vector.
//
// find_indices normally uses compound-trigger recursive axioms (so the
// matching loop for suffix-invariant loop proofs is broken), which means
// concrete exact-value equality isn't provable via recursive unfolding out
// of the box. This test pairs with the per-spec `extra_bpl` file
// `find_indices_big.ok.bpl`, which supplies a *single-trigger* end-step
// axiom for this specific find_indices helper instance, letting Z3 unfold
// from a fresh call to prove the exact result. The single-trigger axiom is
// scoped to this spec only — it doesn't affect any other test.

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

#[spec(prove, extra_bpl = b"find_indices_big.ok.bpl")]
fun test_find_indices_big() {
    let v = vector[1u64, 2, 3, 4, 5, 6, 7, 8];
    // Even elements are at indices 1, 3, 5, 7.
    ensures(*find_indices!<u64>(&v, |x| is_even(x)) == vector[1, 3, 5, 7]);
}
