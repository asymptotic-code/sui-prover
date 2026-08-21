#[allow(unused)]
module 0x42::extra_bpl_invalid_ext;

#[mode(spec)]
use prover::prover::ensures;

// This should fail because the file doesn't have .bpl extension
#[spec(prove, extra_bpl = b"simple.ok.move")]
fun test_invalid_extension_spec() {
    ensures(true);
}
