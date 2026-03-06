#[allow(unused)]
#[spec_only(extra_bpl = b"multi_module_a.bpl,multi_module_b.bpl")]
module 0x42::extra_bpl_multi_module;

#[spec_only]
use prover::prover::ensures;

// Native functions defined in separate module-level extra BPL files
#[spec_only]
native fun custom_a(x: u8): u8;

#[spec_only]
native fun custom_b(x: u8): u8;

#[spec(prove)]
fun test_multi_module_extra_bpl() {
    ensures(custom_a(0) == 0);
    ensures(custom_b(0) == 1);
}
