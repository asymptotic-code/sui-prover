#[allow(unused)]
#[mode(spec)]
module 0x42::extra_bpl_module_test;

#[mode(spec)]
use prover::prover::ensures;

// Native function defined in the module-level extra BPL file
#[mode(spec)]
native fun custom_multiply_1(x: u64, y: u64): u64;

// Native function defined in the module-level extra BPL file
#[mode(spec)]
native fun custom_multiply_2(x: u64, y: u64): u64;

#[spec(prove, extra_bpl = b"m_1.ok.bpl", extra_bpl = b"m_2.ok.bpl")]
fun test_custom_multiply_spec() {
    ensures(custom_multiply_1(2, 3) == 7);
    ensures(custom_multiply_2(5, 4) == 19);
}
