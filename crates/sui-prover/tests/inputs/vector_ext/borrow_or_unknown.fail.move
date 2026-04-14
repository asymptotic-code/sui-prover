// Out-of-range borrow_or_unknown returns an uninterpreted value, so we
// cannot conclude any specific value for it. Claiming a specific value
// must fail to verify.

#[allow(unused)]
module 0x42::vector_ext_borrow_or_unknown_fail;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_ext::borrow_or_unknown;

#[spec(prove)]
fun test_out_of_range_not_specific() {
    let v = vector[10u64, 20, 30];
    // FAIL: for i=5 (out of range), the result is uninterpreted —
    // cannot be pinned to any specific value.
    ensures(*borrow_or_unknown(&v, 5) == 0);
}
