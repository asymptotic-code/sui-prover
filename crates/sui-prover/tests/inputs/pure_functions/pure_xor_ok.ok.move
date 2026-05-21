/// Regression test: XOR in a pure-translated function previously panicked
/// with "unexpected operation Xor" in bytecode_translator.rs.
/// Mirrors integer-mate's u32_neg pattern (v ^ 0xffffffff for bitwise NOT).
module 0x42::pure_xor_ok;

#[spec_only]
use prover::prover::ensures;

#[ext(pure)]
fun u32_neg(v: u32): u32 {
    v ^ 0xffffffff
}

#[spec(prove, target = u32_neg)]
public fun u32_neg_spec(v: u32): u32 {
    let result = u32_neg(v);
    ensures(result <= std::u32::max_value!());
    result
}
