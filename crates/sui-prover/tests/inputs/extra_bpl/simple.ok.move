#[allow(unused)]
module 0x42::extra_bpl_test;

#[mode(spec), ext(spec_only)]
use prover::prover::ensures;

// Native function that will be defined in the extra BPL file
#[mode(spec), ext(spec_only)]
native fun custom_add(x: u64, y: u64): u64;

#[mode(spec), ext(spec(prove, extra_bpl = b"simple.ok.bpl"))]
fun test_custom_add_spec() {
    ensures(custom_add(2, 3) == 5);
    ensures(custom_add(10, 20) == 30);
}
