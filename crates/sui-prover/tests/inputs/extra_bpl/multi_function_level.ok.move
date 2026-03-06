#[allow(unused)]
module 0x42::extra_bpl_multi;

#[spec_only]
use prover::prover::ensures;

// Native functions defined in separate extra BPL files
#[spec_only]
native fun custom_a(x: u8): u8;

#[spec_only]
native fun custom_b(x: u8): u8;

#[spec(prove, extra_bpl = b"multi_a.bpl,multi_b.bpl")]
fun test_multi_extra_bpl() {
    ensures(custom_a(0) == 0);
    ensures(custom_b(0) == 1);
}
