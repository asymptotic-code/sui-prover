module 0x42::pure_single_field_unpack;

#[spec_only]
use prover::prover::{requires, val};

public struct S(u8) has copy, drop;

#[ext(pure)]
public fun unwrap(s: S): u8 {
    let S(x) = s;
    x
}

public fun f(s: S): u8 {
    s.unwrap() + 1
}

#[spec(prove)]
public fun f_spec(s: S): u8 {
    let s0 = val(&s);
    requires(s0.unwrap() < 255);
    f(s)
}
