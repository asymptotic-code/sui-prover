#[allow(unused)]
#[mode(spec), ext(spec_only)]
module 0x42::extra_bpl_module_test;

#[mode(spec), ext(spec_only)]
use prover::prover::ensures;

// Native function defined in the module-level extra BPL file
#[mode(spec), ext(spec_only)]
native fun custom_multiply_1(x: u64, y: u64): u64;

// Native function defined in the module-level extra BPL file
#[mode(spec), ext(spec_only)]
native fun custom_multiply_2(x: u64, y: u64): u64;

#[mode(spec), ext(spec(prove, extra_bpl(a = b"m_1.ok.bpl", b = b"m_2.ok.bpl")))]
fun test_custom_multiply_spec() {
    ensures(custom_multiply_1(2, 3) == 7);
    ensures(custom_multiply_2(5, 4) == 19);
}
