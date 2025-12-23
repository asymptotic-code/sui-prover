#[allow(unused)]
module 0x42::quantifiers_map_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::map;

#[ext(no_abort)]
fun x_plus_10(x: &u64): u64 {
    if (*x < 100000) {
        *x + 10
    } else {
        100000
    }
}

#[spec(prove)]
fun test_spec() {
    let v = vector[10, 20, 10, 30];
    ensures(map!<u64, u64>(&v, |x| x_plus_10(x)) == vector[20, 30, 20, 40]);
}
