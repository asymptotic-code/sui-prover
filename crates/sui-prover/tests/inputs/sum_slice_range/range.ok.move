#[allow(unused)]
module 0x42::range_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::range;

#[spec(prove)]
fun test_spec() {
    ensures(range(1, 0) == vector[]);
    ensures(range(0, 1) == vector[0]);
    ensures(range(709, 713) == vector[709, 710, 711, 712]);
}
