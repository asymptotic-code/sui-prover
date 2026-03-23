module 0x42::simple_axiom;

use prover::prover::ensures;

#[spec_only(axiom)]
fun f_axiom(x: u64): bool {
    bar() && x > 4 && x.to_int().sqrt().gt(2u64.to_int())
}

// This function has a real abort, so it can't be a pure callee.
public fun bar(): bool {
    assert!(1u8 > 2u8);
    true
}

#[spec(prove)]
public fun bar_spec(): bool {
    let res = bar();
    ensures(16u8.to_int().sqrt().gt(2u64.to_int()));
    res
}
