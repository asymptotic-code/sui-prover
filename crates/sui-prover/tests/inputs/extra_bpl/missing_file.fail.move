#[allow(unused)]
module 0x42::extra_bpl_missing;

#[spec_only]
use prover::prover::ensures;

// This should fail because the file doesn't exist
#[spec(prove, extra_bpl = b"nonexistent.bpl")]
fun test_missing_file_spec() {
    ensures(true);
}
