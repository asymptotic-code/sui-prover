#[allow(unused)]
module 0x42::quantifiers_not_function_param_fail;

#[mode(spec)]
use prover::prover::ensures;

#[mode(spec)]
use prover::vector_iter::map;


#[spec(prove)]
fun test_spec() {
    let v = vector[10, 20, 10, 30];
    ensures(map!<u64, u64>(&v, |x| *x + 10) == vector[20, 30, 20, 40]);
}
