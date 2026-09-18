#[allow(unused)]
module 0x42::range_ok;

#[mode(spec), ext(spec_only)]
use prover::prover::ensures;

#[mode(spec), ext(spec_only)]
use prover::vector_iter::range;

#[mode(spec), ext(spec(prove))]
fun test_spec() {
    ensures(range(1, 0) == vector[]);
    ensures(range(0, 1) == vector[0]);
    ensures(range(709, 713) == vector[709, 710, 711, 712]);
}
