module 0x42::loop_invariant_inline_wrong_place;

use prover::prover::{ensures, invariant};

public fun f(x: u8): u8 {
    invariant!(|| ensures(true) );
    x + 1
}

#[spec(prove)]
public fun f_spec(x: u8): u8 {
    f(x)
}
