module 0x42::pure_enum_pack;

#[spec_only]
use prover::prover::{ensures, exists};

public enum E has copy, drop {
    A,
    B(u8),
}

#[ext(pure)]
public fun is_b(v: u8, e: E): bool {
    e == E::B(v)
}

#[ext(pure)]
public fun is_a_or_some_b(e: E): bool {
    e == E::A || exists!(|v| is_b(*v, e))
}

#[spec(prove)]
fun test_b() {
    ensures(is_a_or_some_b(E::B(1)))
}

#[spec(prove)]
fun test_a() {
    ensures(is_a_or_some_b(E::A))
}
