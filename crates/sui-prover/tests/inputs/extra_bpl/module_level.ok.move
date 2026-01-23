#[allow(unused)]
#[spec_only(extra_bpl = b"module_level.ok.bpl")]
module 0x42::extra_bpl_module_test;

#[spec_only]
use prover::prover::ensures;

// Native function defined in the module-level extra BPL file
#[spec_only]
native fun custom_multiply(x: u64, y: u64): u64;

#[spec(prove)]
fun test_custom_multiply_spec() {
    ensures(custom_multiply(2, 3) == 6);
    ensures(custom_multiply(5, 4) == 20);
}
